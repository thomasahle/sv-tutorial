<script>
  import { onDestroy, onMount } from 'svelte';

  let { vcd = null, hasRun = false, darkMode = false, signalsReady = $bindable(false) } = $props();

  let iframeEl = $state(null);
  let iframeLoaded = $state(false);
  let surferReady = $state(false);
  let waveReadySource = $state('none');
  let selectedSignal = $state('');
  // null = checking, true = available, false = not installed
  let surferAvailable = $state(null);

  let _blobUrl = null;
  let _cmdBlobUrl = null;
  let _retryTimers = [];
  let _readyFallbackTimer = null;
  // Stores the VisibleItemIndex of the last signal we focused via FocusItem.
  // Re-sent before transition commands because clicking a toolbar button in the
  // parent page blurs the iframe, causing Surfer to lose its focused-variable state.
  let _focusedVisibleIdx = undefined;
  // Two quick retries absorb transient startup races on slower hosts.
  const LOAD_RETRY_MS = [0, 500];
  // Extra chrome-hiding passes after iframe load — WASM may still be initialising.
  const CHROME_HIDE_RETRY_MS = [0, 600, 1800];
  // Extra wait after last load retry before sending the scope command file.
  const CMD_EXTRA_DELAY_MS = 500;
  // Fallback delay to mark signals ready if Surfer never emits waves-loaded.
  const READY_FALLBACK_MS = 2000;

  function clearLoadRetries() {
    for (const t of _retryTimers) clearTimeout(t);
    _retryTimers = [];
  }

  function clearReadyFallback() {
    if (_readyFallbackTimer) {
      clearTimeout(_readyFallbackTimer);
      _readyFallbackTimer = null;
    }
  }

  function clearWaveBlobs() {
    if (_blobUrl) {
      URL.revokeObjectURL(_blobUrl);
      _blobUrl = null;
    }
    if (_cmdBlobUrl) {
      URL.revokeObjectURL(_cmdBlobUrl);
      _cmdBlobUrl = null;
    }
    _focusedVisibleIdx = undefined;
  }

  import { base } from '$app/paths';
  // Ensure surfer paths are always absolute regardless of base ('' vs '/foo').
  const BASE = base ? `${base}/` : '/';

  // Probe surfer.js with GET and MIME check. Vite preview can return SPA fallback
  // HTML with a false-positive 200 for missing assets.
  $effect(() => {
    fetch(`${BASE}surfer/surfer.js`, { method: 'GET', cache: 'force-cache' })
      .then((r) => {
        const contentType = (r.headers.get('content-type') || '').toLowerCase();
        const isScriptMime = /javascript|ecmascript/.test(contentType);
        surferAvailable = r.ok && isScriptMime;
      })
      .catch(() => { surferAvailable = false; });
  });

  // Re-send whenever VCD data or iframe readiness changes.
  $effect(() => {
    const text = vcd;
    const el = iframeEl;
    const loaded = iframeLoaded;
    if (!text || !el || !loaded) return;
    sendVcd(el, text);
  });

  // When no VCD is available, clear pending loads and release blob URLs so
  // stale waveform data cannot leak into the next lesson/run.
  $effect(() => {
    if (vcd) return;
    clearLoadRetries();
    clearReadyFallback();
    clearWaveBlobs();
    signalsReady = false;
    waveReadySource = 'none';
    selectedSignal = '';
  });

  // App warm palette — must stay in sync with src/app.css custom color tokens.
  // Colors are 6-char hex strings (no '#') as required by Surfer's TOML parser.
  const SURFER_THEME = [
    'foreground = "1e2a2c"',
    'border_color = "d5cbb2"',
    'canvas_colors = { background = "fff4ef", alt_background = "f5f1e6", foreground = "1e2a2c" }',
    'primary_ui_color = { background = "fffdf7", foreground = "1e2a2c" }',
    'secondary_ui_color = { background = "efe8d7", foreground = "1e2a2c" }',
    'selected_elements_colors = { background = "d5cbb2", foreground = "1e2a2c" }',
    'highlight_background = "e7f6f4"',
    'clock_highlight_cycle = "f0ebe0"',
    'clock_highlight_line = { color = "d5cbb2", width = 1 }',
    'variable_default = "0d6f72"',
    'cursor = { color = "0d6f72", width = 2 }',
    'gesture = { color = "0d6f72", width = 2 }',
  ].join('\n');

  function surferMsg(cw, msg) {
    cw.postMessage({ command: 'InjectMessage', message: JSON.stringify(msg) }, '*');
  }

  // Exported so parent can call via bind:this={waveformRef}; waveformRef.sendCmd('zoom_in')
  export function sendCmd(cmd) {
    const cw = iframeEl?.contentWindow;
    if (!cw) return;

    if (cmd === 'transition_next' || cmd === 'transition_previous') {
      // Dispatch a synthetic arrow-key event directly to the Surfer iframe
      // (same-origin access).  This mirrors what happens when the user presses
      // ← / → with the iframe focused, and avoids the async race between the
      // WCP command-file fetch and the iframe-blur event clearing Surfer's
      // focused-variable state.
      //
      // We also re-send FocusItem first so Surfer's focused variable is correct
      // even if it was cleared by the blur event.  postMessage is async, so we
      // delay the key dispatch by 50 ms to ensure FocusItem is processed by
      // Surfer before the keyboard event fires.
      if (_focusedVisibleIdx !== undefined) {
        surferMsg(cw, { FocusItem: _focusedVisibleIdx });
      }
      const key = cmd === 'transition_next' ? 'ArrowRight' : 'ArrowLeft';
      setTimeout(() => {
        const el = iframeEl;
        if (!el) return;
        const canvas = el.contentDocument?.getElementById('the_canvas_id');
        const target = canvas ?? el.contentWindow;
        if (!target) return;
        // Create the event in the iframe's realm to avoid cross-realm prototype issues.
        const IframeKBEvent = el.contentWindow?.KeyboardEvent ?? KeyboardEvent;
        target.dispatchEvent(
          new IframeKBEvent('keydown', { key, code: key, bubbles: true, cancelable: true })
        );
      }, 50);
      return;
    }

    const url = URL.createObjectURL(new Blob([cmd + '\n'], { type: 'text/plain' }));
    surferMsg(cw, { LoadCommandFileFromUrl: url });
    setTimeout(() => URL.revokeObjectURL(url), 5000);
  }

  // Open the current VCD in a new browser tab showing the full Surfer UI.
  // Blob URLs are same-origin to the popup so Surfer can fetch them directly.
  export function openInNewWindow() {
    const text = vcd;
    if (!text) return;

    const vcdBlobUrl = URL.createObjectURL(new Blob([text], { type: 'text/plain' }));
    const popup = window.open(`${BASE}surfer/index.html?svtutorial=20260223#dev`, '_blank');
    if (!popup) {
      URL.revokeObjectURL(vcdBlobUrl);
      return;
    }

    const rootScope = text.match(/\$scope\s+\w+\s+(\w+)\s*\$end/)?.[1];
    let scopeBlobUrl = null;
    if (rootScope) {
      const cmd = `scope_add_recursive ${rootScope}\nzoom_fit\n`;
      scopeBlobUrl = URL.createObjectURL(new Blob([cmd], { type: 'text/plain' }));
    }

    // Progressive retries to absorb popup launch + Surfer WASM init time.
    // Unlike the embedded iframe, a new tab can take several seconds to load.
    for (const ms of [1000, 2500, 5000, 9000]) {
      setTimeout(() => {
        if (popup.closed) return;
        popup.postMessage({ command: 'LoadUrl', url: vcdBlobUrl }, '*');
        if (scopeBlobUrl) {
          setTimeout(() => {
            if (!popup.closed) {
              popup.postMessage(
                { command: 'InjectMessage', message: JSON.stringify({ LoadCommandFileFromUrl: scopeBlobUrl }) },
                '*'
              );
            }
          }, 1200);
        }
      }, ms);
    }

    // Keep blob URLs alive long enough for Surfer to fetch them.
    setTimeout(() => {
      URL.revokeObjectURL(vcdBlobUrl);
      if (scopeBlobUrl) URL.revokeObjectURL(scopeBlobUrl);
    }, 9000 + 30000);
  }

  function applyChrome(cw, dark = false) {
    // All messages are idempotent — safe to call on every retry.
    surferMsg(cw, { SetMenuVisible: false });
    surferMsg(cw, { SetToolbarVisible: false });
    surferMsg(cw, { SetStatusbarVisible: false });
    surferMsg(cw, { SetSidePanelVisible: false });
    // Increase UI zoom so signal rows are readable at typical pane heights.
    surferMsg(cw, { SetUIZoomFactor: 1.5 });
    if (dark) {
      surferMsg(cw, { SelectTheme: 'dark+' });
    } else {
      surferMsg(cw, { SelectTheme: 'light+' });
      surferMsg(cw, { SetConfigFromString: SURFER_THEME });
    }
  }

  // Parse VCD and return { id, name, fullPath } for the variable with the EARLIEST
  // first transition after the initial $dumpvars block (ignoring pure-initialization
  // changes).  Ties broken by VCD declaration order.  Returns null if no signal
  // transitions at all.
  //
  // fullPath is the dot-joined scope hierarchy required by Surfer's id_of_name()
  // (e.g. "tb.req", not just "req").
  function firstTransitioningVar(vcdText) {
    // Collect {id (identifier code), name, fullPath} in declaration order,
    // tracking the scope stack to build the full dot-path for each variable.
    const vars = [];
    const scopeStack = [];
    const headerText = vcdText.slice(0, Math.max(0, vcdText.search(/\$enddefinitions\b/)));
    const tokenRe = /\$scope\s+\w+\s+(\w+)\s*\$end|\$upscope\s*\$end|\$var\s+\w+\s+\d+\s+(\S+)\s+(\S+)[^$]*\$end/g;
    for (const m of headerText.matchAll(tokenRe)) {
      if (m[0].startsWith('$scope')) {
        scopeStack.push(m[1]);
      } else if (m[0].startsWith('$upscope')) {
        scopeStack.pop();
      } else {
        // $var — m[2]=identifier code, m[3]=leaf name
        vars.push({ id: m[2], name: m[3], fullPath: [...scopeStack, m[3]].join('.') });
      }
    }
    if (vars.length === 0) return null;

    // Find $enddefinitions and skip past the $dumpvars initial-state block.
    const enddefs = vcdText.search(/\$enddefinitions\b/);
    if (enddefs === -1) return null;
    let rest = vcdText.slice(enddefs);
    const dumpStart = rest.indexOf('$dumpvars');
    if (dumpStart !== -1) {
      const dumpEnd = rest.indexOf('$end', dumpStart);
      if (dumpEnd !== -1) rest = rest.slice(dumpEnd + 4);
    }

    // Walk timestamps one by one; for each timestamp collect which identifiers
    // change.  Track the first timestamp at which each identifier changes.
    // We stop once every declared identifier has been seen at least once (to
    // avoid scanning the entire VCD on large traces).
    const firstChangeAt = new Map(); // id → first timestamp with a value change
    let currentTime = -1;
    const lines = rest.split('\n');
    let unseen = new Set(vars.map((v) => v.id));

    for (const line of lines) {
      if (unseen.size === 0) break;
      const trimmed = line.trim();
      if (trimmed.startsWith('#')) {
        currentTime = parseInt(trimmed.slice(1), 10);
        continue;
      }
      if (currentTime < 0) continue;
      const m = trimmed.match(/^[01xzXZ]([!-~]+)|^b[01xzXZ]+\s+([!-~]+)/);
      if (m) {
        const id = m[1] ?? m[2];
        if (!firstChangeAt.has(id)) firstChangeAt.set(id, currentTime);
        unseen.delete(id);
      }
    }

    if (firstChangeAt.size === 0) return null;

    // Return the var with the smallest first-change timestamp (ties → first
    // in declaration order, which is the natural loop order over vars).
    let best = null;
    let bestTime = Infinity;
    for (const v of vars) {
      const t = firstChangeAt.get(v.id);
      if (t !== undefined && t < bestTime) {
        bestTime = t;
        best = v;
      }
    }
    return best;
  }

  function sendVcd(el, text) {
    clearLoadRetries();
    clearReadyFallback();
    clearWaveBlobs();
    signalsReady = false;
    waveReadySource = 'none';

    const blob = new Blob([text], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    _blobUrl = url;

    // Progressive retries absorb Surfer's WASM init time on slower hosts.
    // Chrome-hiding messages are sent alongside LoadUrl on each attempt.
    const dark = darkMode;
    for (const ms of LOAD_RETRY_MS) {
      const t = setTimeout(() => {
        const cw = el?.contentWindow;
        if (!cw) return;
        applyChrome(cw, dark);
        cw.postMessage({ command: 'LoadUrl', url }, '*');
      }, ms);
      _retryTimers.push(t);
    }

    // After VCD is fully loaded, auto-populate with all signals from the root
    // scope and zoom to fit. Parse the VCD to find the first top-level scope
    // name, then build the command file dynamically via a blob URL.
    const rootScope = text.match(/\$scope\s+\w+\s+(\w+)\s*\$end/)?.[1];
    if (rootScope) {
      const cmd = `scope_add_recursive ${rootScope}\nzoom_fit\n`;
      _cmdBlobUrl = URL.createObjectURL(new Blob([cmd], { type: 'text/plain' }));
      const cmdUrl = _cmdBlobUrl;
      const cmdDelay = LOAD_RETRY_MS[LOAD_RETRY_MS.length - 1] + CMD_EXTRA_DELAY_MS;
      const t = setTimeout(() => {
        const cw = el?.contentWindow;
        if (!cw) return;
        surferMsg(cw, { LoadCommandFileFromUrl: cmdUrl });
      // Fire after the last load retry + parse time (VCDs are tiny, <20ms to parse).
      }, cmdDelay);
      _retryTimers.push(t);
      // Auto-focus the first signal that has actual transitions so that
      // transition_next/prev work without requiring the user to click a row.
      //
      // Surfer's transition_next/prev navigate on the KEYBOARD-FOCUSED signal,
      // set via FocusItem(VisibleItemIndex).  The visual index equals the value
      // returned by id_of_name() (DisplayedItemRef) because Surfer assigns IDs
      // sequentially in display order (scope header = 0, then signals in alpha order).
      // We also call SetItemSelected so the user can see which signal is active.
      //
      // id_of_name() requires the full dot-separated scope path (e.g. "tb.req")
      // and returns undefined if the signal isn't in the display yet (scope_add_recursive
      // may still be processing), so we poll with retries.
      const firstVar = firstTransitioningVar(text);
      const focusTimer = setTimeout(async () => {
        if (!firstVar) return;
        const cw = el?.contentWindow;
        if (!cw) return;
        // id_of_name  → DisplayedItemRef (for SetItemSelected)
        // index_of_name → VisibleItemIndex (for FocusItem — keyboard nav)
        const hasIndexFn = typeof cw.index_of_name === 'function';
        const hasIdFn    = typeof cw.id_of_name    === 'function';
        if (!hasIndexFn && !hasIdFn) return;

        // Poll until scope_add_recursive has finished adding signals to the display.
        for (let attempt = 0; attempt < 16; attempt++) {
          if (attempt > 0) await new Promise((r) => setTimeout(r, 250));
          const cw2 = el?.contentWindow;
          if (!cw2) return;
          try {
            // Use index_of_name for FocusItem (VisibleItemIndex).
            // Fall back to id_of_name if index_of_name is unavailable (older Surfer builds
            // where DisplayedItemRef happened to equal VisibleItemIndex for flat scopes).
            const visibleIdx = hasIndexFn
              ? await cw2.index_of_name(firstVar.fullPath)
              : await cw2.id_of_name(firstVar.fullPath);
            if (visibleIdx === undefined) continue;
            // FocusItem sets keyboard focus — required for transition_next/prev.
            surferMsg(cw2, { FocusItem: visibleIdx });
            _focusedVisibleIdx = visibleIdx;
            // SetItemSelected gives the visual blue highlight.
            // Prefer id_of_name (DisplayedItemRef) for SetItemSelected when available.
            const itemRef = hasIdFn
              ? (await cw2.id_of_name(firstVar.fullPath) ?? visibleIdx)
              : visibleIdx;
            surferMsg(cw2, { SetItemSelected: { item: itemRef, selected: true } });
            selectedSignal = firstVar.name;
            return;
          } catch { /* keep polling */ }
        }
      }, cmdDelay + 400);
      _retryTimers.push(focusTimer);
      // Keep the UI responsive if an older Surfer build does not emit
      // waves-loaded integration events.
      _readyFallbackTimer = setTimeout(() => {
        signalsReady = true;
        waveReadySource = 'fallback';
        _readyFallbackTimer = null;
      }, cmdDelay + READY_FALLBACK_MS);
    } else {
      _readyFallbackTimer = setTimeout(() => {
        signalsReady = true;
        waveReadySource = 'fallback';
        _readyFallbackTimer = null;
      }, READY_FALLBACK_MS);
    }
  }

  function onIframeLoad() {
    iframeLoaded = true;
    surferReady = false;
    // Hide chrome as soon as possible after load, even before VCD arrives.
    // Retried because WASM may not be ready yet.
    for (const ms of CHROME_HIDE_RETRY_MS) {
      setTimeout(() => {
        const cw = iframeEl?.contentWindow;
        if (cw) applyChrome(cw, darkMode);
      }, ms);
    }
  }

  // Re-apply theme when dark mode is toggled while the iframe is alive.
  $effect(() => {
    const dark = darkMode;
    const cw = iframeEl?.contentWindow;
    if (!cw || !surferReady) return;
    applyChrome(cw, dark);
  });

  function onParentMessage(event) {
    const frameWindow = iframeEl?.contentWindow;
    if (!frameWindow || event.source !== frameWindow) return;
    const data = event.data || {};
    if (data?.source !== 'surfer') return;
    if (data.type === 'listener-ready' || data.type === 'engine-ready') {
      surferReady = true;
    }
    if (data.type === 'waves-loaded') {
      clearReadyFallback();
      signalsReady = true;
      waveReadySource = 'surfer';
    }
  }

  onMount(() => {
    window.addEventListener('message', onParentMessage);
    return () => {
      window.removeEventListener('message', onParentMessage);
    };
  });

  onDestroy(() => {
    clearLoadRetries();
    clearReadyFallback();
    clearWaveBlobs();
  });
</script>

{#if surferAvailable === false}
  <div class="h-full flex flex-col items-center justify-center gap-3 text-muted-foreground text-sm text-center p-4">
    <p class="m-0">Surfer waveform viewer is not installed.</p>
    <p class="m-0">Run the setup script to download the web build:</p>
    <pre class="m-0 bg-logs-bg text-logs-text rounded-[8px] px-4 py-2 font-mono text-[0.8rem]">scripts/setup-surfer.sh</pre>
  </div>

{:else if surferAvailable}
  {#if vcd}
    <div
      data-testid="waveform-frame-wrapper"
      data-wave-state={signalsReady ? 'ready' : 'loading'}
      data-wave-ready-source={waveReadySource}
      data-selected-signal={selectedSignal}
      class="relative w-full h-full"
    >
      <iframe
        bind:this={iframeEl}
        src="{BASE}surfer/index.html?svtutorial=20260223#dev"
        title="Surfer Waveform Viewer"
        onload={onIframeLoad}
        data-testid="waveform-iframe"
        class="w-full h-full border-none"
      ></iframe>
      {#if !signalsReady}
        <div data-testid="waveform-loading-overlay" class="absolute inset-0 flex items-center justify-center
                    bg-surface text-muted-foreground text-sm
                    pointer-events-none">
          Loading waveform…
        </div>
      {/if}
    </div>
  {:else}
    <div data-testid="no-waveform-message" class="h-full flex items-center justify-center text-muted-foreground text-sm text-center p-4">
      <span>{hasRun ? 'no waveform vcd found' : 'Run the simulation to generate waveform data.'}</span>
    </div>
  {/if}

{:else}
  <div class="h-full flex items-center justify-center text-muted-foreground text-sm">
    <span>Checking for Surfer…</span>
  </div>
{/if}

