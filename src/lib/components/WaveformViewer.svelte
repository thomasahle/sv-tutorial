<script>
  import { onDestroy, onMount } from 'svelte';

  let { vcd = null, hasRun = false } = $props();

  let iframeEl = $state(null);
  let iframeLoaded = $state(false);
  let surferReady = $state(false);
  let signalsReady = $state(false);
  // null = checking, true = available, false = not installed
  let surferAvailable = $state(null);

  let _blobUrl = null;
  let _cmdBlobUrl = null;
  let _retryTimers = [];
  // sendVcd() is only called once surferReady=true (engine-ready received),
  // so Surfer's WASM is already initialised. Two quick retries are enough to
  // handle any lingering race between the message queue and the WASM runtime.
  const LOAD_RETRY_MS = [0, 500];

  function clearLoadRetries() {
    for (const t of _retryTimers) clearTimeout(t);
    _retryTimers = [];
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
  }

  // Probe surfer.js (a real asset) rather than index.html — Vite's SPA fallback
  // would serve a false-positive 200 for index.html in dev mode.
  $effect(() => {
    fetch('/surfer/surfer.js', { method: 'HEAD' })
      .then(r => { surferAvailable = r.ok; })
      .catch(() => { surferAvailable = false; });
  });

  // Re-send whenever VCD data or iframe readiness changes.
  $effect(() => {
    const text = vcd;
    const el = iframeEl;
    const loaded = iframeLoaded;
    if (!text || !el || !loaded || !surferReady) return;
    sendVcd(el, text);
  });

  // When no VCD is available, clear pending loads and release blob URLs so
  // stale waveform data cannot leak into the next lesson/run.
  $effect(() => {
    if (vcd) return;
    clearLoadRetries();
    clearWaveBlobs();
    signalsReady = false;
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

  function applyChrome(cw) {
    // All messages are idempotent — safe to call on every retry.
    surferMsg(cw, { SetMenuVisible: false });
    surferMsg(cw, { SetToolbarVisible: false });
    surferMsg(cw, { SetStatusbarVisible: false });
    surferMsg(cw, { SetSidePanelVisible: false });
    // Increase UI zoom so signal rows are readable at typical pane heights.
    surferMsg(cw, { SetUIZoomFactor: 1.5 });
    // Apply warm theme to match the app's color palette.
    surferMsg(cw, { SelectTheme: 'light+' });
    surferMsg(cw, { SetConfigFromString: SURFER_THEME });
  }

  function sendVcd(el, text) {
    clearLoadRetries();
    clearWaveBlobs();
    signalsReady = false;

    const blob = new Blob([text], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    _blobUrl = url;

    // Progressive retries absorb Surfer's WASM init time on slower hosts.
    // Chrome-hiding messages are sent alongside LoadUrl on each attempt.
    for (const ms of LOAD_RETRY_MS) {
      const t = setTimeout(() => {
        const cw = el?.contentWindow;
        if (!cw) return;
        applyChrome(cw);
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
      const cmdDelay = LOAD_RETRY_MS[LOAD_RETRY_MS.length - 1] + 500;
      const t = setTimeout(() => {
        const cw = el?.contentWindow;
        if (!cw) return;
        surferMsg(cw, { LoadCommandFileFromUrl: cmdUrl });
      // Fire after the last load retry + parse time (VCDs are tiny, <20ms to parse).
      }, cmdDelay);
      _retryTimers.push(t);
      // Dismiss the loading overlay after signals have had time to render.
      const tReady = setTimeout(() => { signalsReady = true; }, cmdDelay + 400);
      _retryTimers.push(tReady);
    } else {
      // No root scope found — nothing to load, dismiss overlay immediately.
      signalsReady = true;
    }
  }

  function onIframeLoad() {
    iframeLoaded = true;
    surferReady = false;
    // Hide chrome as soon as possible after load, even before VCD arrives.
    // Retried because WASM may not be ready yet.
    for (const ms of [0, 600, 1800]) {
      setTimeout(() => {
        const cw = iframeEl?.contentWindow;
        if (cw) applyChrome(cw);
      }, ms);
    }
  }

  function onParentMessage(event) {
    const frameWindow = iframeEl?.contentWindow;
    if (!frameWindow || event.source !== frameWindow) return;
    const data = event.data || {};
    if (data?.source !== 'surfer') return;
    if (data.type === 'listener-ready' || data.type === 'engine-ready') {
      surferReady = true;
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
    <div class="relative w-full h-full">
      <iframe
        bind:this={iframeEl}
        src="/surfer/index.html?svtutorial=20260223#dev"
        title="Surfer Waveform Viewer"
        onload={onIframeLoad}
        class="w-full h-full border-none rounded-[10px]"
      ></iframe>
      {#if !signalsReady}
        <div class="absolute inset-0 flex items-center justify-center
                    bg-surface text-muted-foreground text-sm rounded-[10px]
                    pointer-events-none">
          Loading waveform…
        </div>
      {/if}
    </div>
  {:else}
    <div class="h-full flex items-center justify-center text-muted-foreground text-sm text-center p-4">
      <span>{hasRun ? 'no waveform vcd found' : 'Run the simulation to generate waveform data.'}</span>
    </div>
  {/if}

{:else}
  <div class="h-full flex items-center justify-center text-muted-foreground text-sm">
    <span>Checking for Surfer…</span>
  </div>
{/if}
