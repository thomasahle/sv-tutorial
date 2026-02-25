<script>
  import { onMount } from 'svelte';
  import { browser } from '$app/environment';
  import { beforeNavigate, goto } from '$app/navigation';
  import { base } from '$app/paths';
  import { getCirctWasmAdapter } from '$lib/circt.js';
  import { darkMode, vimMode } from '$lib/stores/settings.js';
  import { completedSlugs } from '$lib/stores/completed.js';
  import { cloneFiles, mergeFiles, normalize, topNameFromFocus } from '$lib/lesson-utils.js';
  import { termCard } from '$lib/actions/term-card.js';
  import { Tabs, TabsList, TabsTrigger } from '$lib/components/ui/tabs';
  import CodeEditor from '$lib/components/CodeEditor.svelte';
  import WaveformViewer from '$lib/components/WaveformViewer.svelte';

  let { data } = $props();
  let lesson = $derived(data.lesson);

  // Panel split state
  let hSplit = $state(33);      // lesson pane % of main section width
  let vSplit = $state(65);      // editor pane % of lab section height
  let hSplitEditor = $state(50); // left pane % within split editor

  // Workspace state
  let workspace = $state({});
  let selectedFile = $state('');
  let logs = $state([]);
  let activeRuntimeTab = $state('logs');
  let running = $state(false);
  let runMode = $state('sim');
  let runPhase = $state('idle');
  let checkingRuntime = $state(false);
  let runtimeOk = $state(null);
  let lastWaveform = $state(null);
  let hasRunOnce = $state(false);
  let splitView = $state(false);
  let showOptions = $state(false);
  let copyEnabled = $state(false);
  let showCopyModal = $state(false);
  let copyEnableChecked = $state(false);
  let didAnnounceTrimThisRun = $state(false);
  let circt = $state(null);
  let glossaryCard = $state(null); // { body, top, left }
  let waveformRef = $state(null);
  let waveSignalsReady = $state(false);

  // Parse error/warning lines from simulator output after each run.
  // Only active when not running (errors are final).
  const diagnosticsByFile = $derived.by(() => {
    if (running) return {};
    const byFile = {};
    // Regex: optional path prefix, filename, line, optional col, severity, message
    const re = /^(?:[^:]*\/)?([^/:]+\.(?:sv|v|py)):(\d+)(?::\d+)?:\s*(error|warning)(?:\s*\[[^\]]*\])?:\s*(.+)/;
    for (const entry of logs) {
      const payload = typeof entry === 'string' && (entry.startsWith('[stdout] ') || entry.startsWith('[stderr] '))
        ? entry.slice(entry.indexOf('] ') + 2) : null;
      if (!payload) continue;
      for (const line of payload.split('\n')) {
        const m = line.match(re);
        if (!m) continue;
        const [, basename, lineNum, severity, message] = m;
        // Match to a workspace file by basename
        const key = Object.keys(workspace).find(k => k.endsWith('/' + basename) || k === basename);
        if (!key) continue;
        (byFile[key] ??= []).push({ line: Number(lineNum), severity, message });
      }
    }
    return byFile;
  });

  function showCard(body, rect) {
    const cardWidth = 340;
    const margin = 16;
    const left = Math.max(margin, Math.min(rect.left, window.innerWidth - cardWidth - margin));
    const top = rect.bottom + 8;
    glossaryCard = { body, top, left };
  }

  function hideCard() { glossaryCard = null; }

  // Clear card when navigating between lessons
  $effect(() => { lesson.slug; glossaryCard = null; });

  const MAX_NON_STREAM_LOG_ENTRIES = 400;
  const MAX_STREAM_CHARS = 200_000;
  const LOG_TRIM_NOTICE = `# log buffer trimmed: keeping the most recent ${MAX_NON_STREAM_LOG_ENTRIES} non-stream lines`;
  const STREAM_TRIM_NOTICE = `[output truncated: showing last ${MAX_STREAM_CHARS} chars]`;

  // Derived values
  let starterFiles = $derived(cloneFiles(lesson.files.a));
  let solutionFiles = $derived(mergeFiles(cloneFiles(lesson.files.a), cloneFiles(lesson.files.b)));
  let hasSolution = $derived(Object.keys(lesson.files.b).length > 0);
  // Pre-normalize solution so per-keystroke comparison avoids re-processing solution files.
  let solutionNormalized = $derived.by(() => {
    if (!hasSolution) return {};
    return Object.fromEntries(Object.entries(solutionFiles).map(([k, v]) => [k, normalize(v)]));
  });
  let completed = $derived.by(() => {
    if (!hasSolution) return false;
    const wsKeys = Object.keys(workspace).sort();
    const solKeys = Object.keys(solutionNormalized).sort();
    if (wsKeys.length !== solKeys.length) return false;
    for (let i = 0; i < wsKeys.length; i++) {
      if (wsKeys[i] !== solKeys[i]) return false;
      if (normalize(workspace[wsKeys[i]]) !== solutionNormalized[solKeys[i]]) return false;
    }
    return true;
  });
  let hasWaveform = $derived(typeof lastWaveform?.text === 'string' && lastWaveform.text.length > 0);
  let canSplit = $derived(Object.keys(workspace).length === 2);

  // Track current slug to detect lesson navigation
  let _currentSlug = $state('');
  let lessonArticleEl = $state(null);
  let _saveTimer = null;

  function reconcileWorkspace(savedWorkspace, starter) {
    if (!savedWorkspace || typeof savedWorkspace !== 'object') return starter;
    const out = {};
    for (const [path, content] of Object.entries(starter)) {
      out[path] = typeof savedWorkspace[path] === 'string' ? savedWorkspace[path] : content;
    }
    return out;
  }

  function _loadWorkspace(l) {
    const starter = cloneFiles(l.files.a);
    try {
      const saved = browser ? localStorage.getItem(`svt:ws:${l.slug}`) : null;
      const parsed = saved ? JSON.parse(saved) : null;
      workspace = reconcileWorkspace(parsed, starter);
    } catch {
      workspace = starter;
    }
    selectedFile = workspace[l.focus] != null ? l.focus : Object.keys(workspace)[0] || l.focus;
    splitView = Object.keys(workspace).length === 2 && (browser ? window.innerWidth >= 980 : false);
    logs = [];
    didAnnounceTrimThisRun = false;
    activeRuntimeTab = 'logs';
    runtimeOk = null;
    lastWaveform = null;
    hasRunOnce = false;
  }

  onMount(() => {
    circt = getCirctWasmAdapter();
    if (browser && sessionStorage.getItem('copyEnabled') === 'true') copyEnabled = true;
    _currentSlug = lesson.slug;
    _loadWorkspace(lesson);
  });

  // Detect lesson navigation (same route component, data changes)
  $effect(() => {
    const slug = lesson.slug;
    if (slug !== _currentSlug && browser && _currentSlug !== '') {
      _currentSlug = slug;
      _loadWorkspace(lesson);
      if (lessonArticleEl) lessonArticleEl.scrollTop = 0;
    }
  });

  // Continuously save workspace — debounced to avoid localStorage thrashing on every keystroke.
  $effect(() => {
    const ws = workspace;
    const slug = _currentSlug;
    if (!browser || !slug || Object.keys(ws).length === 0) return;
    if (_saveTimer) clearTimeout(_saveTimer);
    _saveTimer = setTimeout(() => {
      try { localStorage.setItem(`svt:ws:${slug}`, JSON.stringify(ws)); } catch {}
    }, 1000);
  });

  // Track completion
  $effect(() => {
    if (completed && hasSolution) {
      completedSlugs.update(s => new Set([...s, lesson.slug]));
    }
  });

  // Auto-switch away from waves tab if no waveform
  $effect(() => {
    if (!hasWaveform && activeRuntimeTab === 'waves') activeRuntimeTab = 'logs';
  });

  // Save workspace before navigating away
  beforeNavigate(() => {
    if (browser && _currentSlug && Object.keys(workspace).length > 0) {
      try { localStorage.setItem(`svt:ws:${_currentSlug}`, JSON.stringify(workspace)); } catch {}
    }
  });

  function onEdit(newValue) {
    workspace = { ...workspace, [selectedFile]: newValue };
  }

  function toggleSolve() {
    if (!hasSolution) return;
    if (completed) {
      workspace = cloneFiles(starterFiles);
      logs = [...logs, 'Reset to starter files'];
    } else {
      workspace = cloneFiles(solutionFiles);
      logs = [...logs, 'Applied solution files'];
    }
  }

  function isStdoutEntry(entry) {
    return typeof entry === 'string' && entry.startsWith('[stdout] ');
  }

  function isStderrEntry(entry) {
    return typeof entry === 'string' && entry.startsWith('[stderr] ');
  }

  function stripStreamPrefix(entry) {
    if (isStdoutEntry(entry)) return entry.slice('[stdout] '.length);
    if (isStderrEntry(entry)) return entry.slice('[stderr] '.length);
    return entry;
  }

  function appendLogEntry(entry) {
    const text = String(entry ?? '');
    const isStdout = isStdoutEntry(text);
    const isStderr = isStderrEntry(text);
    if (!isStdout && !isStderr) {
      logs = trimLogEntries([...logs, text]);
      return;
    }

    const isTargetStream = isStdout ? isStdoutEntry : isStderrEntry;
    const prefix = isStdout ? '[stdout] ' : '[stderr] ';
    const payload = stripStreamPrefix(text);
    const existingIndex = logs.findIndex((item) => isTargetStream(item));

    if (existingIndex >= 0) {
      const current = stripStreamPrefix(logs[existingIndex]);
      const merged = trimStreamPayload(current ? `${current}\n${payload}` : payload);
      logs = trimLogEntries([
        ...logs.slice(0, existingIndex),
        `${prefix}${merged}`,
        ...logs.slice(existingIndex + 1)
      ]);
      return;
    }

    if (isStdout) {
      const stderrIndex = logs.findIndex(isStderrEntry);
      if (stderrIndex >= 0) {
        logs = trimLogEntries([
          ...logs.slice(0, stderrIndex),
          `${prefix}${trimStreamPayload(payload)}`,
          ...logs.slice(stderrIndex),
        ]);
        return;
      }
    }

    logs = trimLogEntries([...logs, `${prefix}${trimStreamPayload(payload)}`]);
  }

  function trimStreamPayload(payload) {
    if (payload.length <= MAX_STREAM_CHARS) return payload;
    return `${STREAM_TRIM_NOTICE}\n${payload.slice(-MAX_STREAM_CHARS)}`;
  }

  function trimLogEntries(entries) {
    let nonStreamCount = 0;
    for (const item of entries) {
      if (!isStdoutEntry(item) && !isStderrEntry(item)) nonStreamCount += 1;
    }

    if (nonStreamCount <= MAX_NON_STREAM_LOG_ENTRIES) return entries;

    let toDrop = nonStreamCount - MAX_NON_STREAM_LOG_ENTRIES;
    const trimmed = [];
    for (const item of entries) {
      const isStream = isStdoutEntry(item) || isStderrEntry(item);
      if (!isStream && toDrop > 0) {
        toDrop -= 1;
        continue;
      }
      trimmed.push(item);
    }

    if (!didAnnounceTrimThisRun) {
      didAnnounceTrimThisRun = true;
      trimmed.unshift(LOG_TRIM_NOTICE);
    }

    return trimmed;
  }

  function startNarrowResize(e) {
    e.preventDefault();
    const section = e.currentTarget.parentElement;
    const totalH = section.getBoundingClientRect().height;
    const startY = e.clientY, startSplit = hSplit;
    const onMove = ev => {
      const raw = startSplit + (ev.clientY - startY) / totalH * 100;
      hSplit = Math.min(Math.max(raw, 15), 75);
    };
    const onUp = () => {
      window.removeEventListener('pointermove', onMove);
      window.removeEventListener('pointerup', onUp);
    };
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  function startHResize(e) {
    e.preventDefault();
    const section = e.currentTarget.parentElement;
    const totalW = section.getBoundingClientRect().width;
    const startX = e.clientX, startSplit = hSplit;
    const onMove = ev => {
      const raw = startSplit + (ev.clientX - startX) / totalW * 100;
      hSplit = Math.min(Math.max(raw, 200 / totalW * 100), (totalW - 300) / totalW * 100);
    };
    const onUp = () => {
      window.removeEventListener('pointermove', onMove);
      window.removeEventListener('pointerup', onUp);
    };
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  function startVResize(e) {
    e.preventDefault();
    const lab = e.currentTarget.parentElement;
    const totalH = lab.getBoundingClientRect().height;
    const startY = e.clientY, startSplit = vSplit;
    const onMove = ev => {
      const raw = startSplit + (ev.clientY - startY) / totalH * 100;
      vSplit = Math.min(Math.max(raw, 150 / totalH * 100), (totalH - 150) / totalH * 100);
    };
    const onUp = () => {
      window.removeEventListener('pointermove', onMove);
      window.removeEventListener('pointerup', onUp);
    };
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  function startEditorHResize(e) {
    e.preventDefault();
    const pane = e.currentTarget.parentElement;
    const totalW = pane.getBoundingClientRect().width;
    const startX = e.clientX, startSplit = hSplitEditor;
    const onMove = ev => {
      const raw = startSplit + (ev.clientX - startX) / totalW * 100;
      hSplitEditor = Math.min(Math.max(raw, 200 / totalW * 100), (totalW - 200) / totalW * 100);
    };
    const onUp = () => {
      window.removeEventListener('pointermove', onMove);
      window.removeEventListener('pointerup', onUp);
    };
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  async function runSim(mode = 'sim') {
    if (running || !circt) return;
    running = true;
    runMode = mode;
    runPhase = 'compiling';
    lastWaveform = null;
    logs = [];
    didAnnounceTrimThisRun = false;

    const useBmc = mode === 'bmc';
    const useLec = mode === 'lec';

    try {
      const onStatus = (status) => {
        if (status === 'compiling') { runPhase = 'compiling'; return; }
        if (status === 'running') { runPhase = 'running'; }
      };
      let streamedEntries = 0;
      const onLog = (entry) => { streamedEntries += 1; appendLogEntry(entry); };
      const mergeNonStreamResultLogs = (resultLogs) => {
        const seen = new Set(logs);
        for (const entry of resultLogs || []) {
          if (isStdoutEntry(entry) || isStderrEntry(entry)) continue;
          if (!seen.has(entry)) { appendLogEntry(entry); seen.add(entry); }
        }
      };

      if (lesson.runner === 'cocotb') {
        const result = await circt.runCocotb({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          onStatus, onLog
        });
        if (streamedEntries === 0) for (const entry of result.logs || []) appendLogEntry(entry);
        else mergeNonStreamResultLogs(result.logs);
      } else if (useLec) {
        const result = await circt.runLec({
          files: workspace,
          module1: lesson.module1 || 'Spec',
          module2: lesson.module2 || 'Impl',
          onStatus, onLog
        });
        if (streamedEntries === 0) for (const entry of result.logs || []) appendLogEntry(entry);
        else mergeNonStreamResultLogs(result.logs);
      } else if (useBmc) {
        const result = await circt.runBmc({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          onStatus, onLog
        });
        if (streamedEntries === 0) for (const entry of result.logs || []) appendLogEntry(entry);
        else mergeNonStreamResultLogs(result.logs);
      } else {
        const result = await circt.run({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          simulate: lesson.simulate,
          onStatus, onLog
        });
        if (streamedEntries === 0) for (const entry of result.logs || []) appendLogEntry(entry);
        else mergeNonStreamResultLogs(result.logs);
        lastWaveform = result.waveform;
      }
    } finally {
      hasRunOnce = true;
      running = false;
      runMode = 'sim';
      runPhase = 'idle';
    }
  }

  function cancelRun() {
    if (!running || !circt) return;
    circt.cancel();
    appendLogEntry('# run cancelled');
  }

  function onKeydown(e) {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      if (running) cancelRun(); else runSim();
    }
  }

  function handleCopy(e) {
    if (!copyEnabled && e.target?.closest('.lesson-body')) {
      e.preventDefault();
      copyEnableChecked = false;
      showCopyModal = true;
    }
  }

  function onCopyModalOk() {
    if (copyEnableChecked) {
      copyEnabled = true;
      if (browser) sessionStorage.setItem('copyEnabled', 'true');
    }
    showCopyModal = false;
  }

  function onCopyModalKeydown(e) {
    if (e.key === 'Escape') { onCopyModalOk(); return; }
    if (e.key !== 'Tab') return;
    const focusable = Array.from(e.currentTarget.querySelectorAll('input, button'));
    const first = focusable[0];
    const last = focusable[focusable.length - 1];
    if (e.shiftKey && document.activeElement === first) {
      e.preventDefault(); last.focus();
    } else if (!e.shiftKey && document.activeElement === last) {
      e.preventDefault(); first.focus();
    }
  }
</script>

<svelte:head>
  <title>{lesson.title} – SV Tutorial</title>
  <meta name="description" content="{lesson.title} — Interactive SystemVerilog Tutorial" />
  <meta property="og:title" content="{lesson.title} – SV Tutorial" />
  <meta property="og:type" content="article" />
</svelte:head>

<svelte:window onkeydown={onKeydown} oncopy={handleCopy} />

<section class="flex-1 min-h-0 flex max-narrow:flex-col">
  <article bind:this={lessonArticleEl} style="flex: 0 0 {hSplit}%; min-width: 200px"
           class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 flex flex-col p-[0.9rem] gap-3 overflow-y-auto [scrollbar-gutter:stable] max-narrow:rounded-none max-narrow:border-x-0 max-narrow:border-t-0">
    <h2 data-testid="lesson-title" class="m-0 text-[1.15rem] font-bold leading-tight text-foreground">{lesson.title}</h2>
    <div class="lesson-body" use:termCard={{ onShow: showCard, onHide: hideCard }}>
      {@html lesson.html}
    </div>
    <div class="mt-auto flex flex-col gap-3">
      <a
        href="https://github.com/thomasnormal/sv-tutorial/tree/main/src/lessons/{lesson.slug}"
        target="_blank"
        rel="noopener noreferrer"
        class="flex items-center gap-1 text-[0.78rem] text-muted-foreground hover:text-foreground transition-colors self-start"
      >
        <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
          <path d="M11 4H4a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2v-7"/>
          <path d="M18.5 2.5a2.121 2.121 0 0 1 3 3L12 15l-4 1 1-4Z"/>
        </svg>
        Edit this page on GitHub
      </a>

      <div class="border-t border-border pt-3 flex justify-between items-center gap-2">
        {#if data.lessons.indexOf(lesson) > 0}
          {@const prevLesson = data.lessons[data.lessons.indexOf(lesson) - 1]}
          <button
            onclick={() => { const [p,n] = prevLesson.slug.split('/'); goto(`${base}/lesson/${p}/${n}`); }}
            class="flex items-center gap-1 text-[0.8rem] text-muted-foreground hover:text-teal transition-colors text-left cursor-pointer"
          >
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m15 18-6-6 6-6"/></svg>
            <span class="truncate">{prevLesson.title}</span>
          </button>
        {:else}
          <div></div>
        {/if}
        {#if data.lessons.indexOf(lesson) < data.lessons.length - 1}
          {@const nextLesson = data.lessons[data.lessons.indexOf(lesson) + 1]}
          <button
            onclick={() => { const [p,n] = nextLesson.slug.split('/'); goto(`${base}/lesson/${p}/${n}`); }}
            class="flex items-center gap-1 text-[0.8rem] text-muted-foreground hover:text-teal transition-colors text-right ml-auto cursor-pointer"
          >
            <span class="truncate">{nextLesson.title}</span>
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m9 18 6-6-6-6"/></svg>
          </button>
        {/if}
      </div>
    </div>
  </article>

  <!-- Horizontal drag handle — wide only -->
  <div role="separator" aria-label="Resize panels" aria-orientation="vertical"
       class="max-narrow:hidden flex-none w-[0.7rem] flex items-center justify-center cursor-col-resize select-none group"
       style="touch-action:none"
       onpointerdown={startHResize}>
    <div class="w-[2px] h-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
  </div>
  <!-- Vertical drag handle — narrow only -->
  <div role="separator" aria-label="Resize panels" aria-orientation="horizontal"
       class="hidden max-narrow:flex flex-none h-[0.7rem] items-center justify-center cursor-row-resize select-none group"
       style="touch-action:none"
       onpointerdown={startNarrowResize}>
    <div class="h-[2px] w-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
  </div>

  <section style="flex: 1 1 0%; min-width: 300px" class="min-h-0 flex flex-col">

    <!-- Options button snippet (reused in both split and single view) -->
    {#snippet optionsButton()}
      <div class="relative flex-shrink-0">
        <button
          onclick={() => (showOptions = !showOptions)}
          data-testid="options-button"
          class="flex items-center justify-center w-8 h-8 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground {showOptions ? 'bg-surface-2' : ''}"
          aria-label="Editor options" title="Editor options"
        >
          <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <path d="M12.22 2h-.44a2 2 0 0 0-2 2v.18a2 2 0 0 1-1 1.73l-.43.25a2 2 0 0 1-2 0l-.15-.08a2 2 0 0 0-2.73.73l-.22.38a2 2 0 0 0 .73 2.73l.15.1a2 2 0 0 1 1 1.72v.51a2 2 0 0 1-1 1.74l-.15.09a2 2 0 0 0-.73 2.73l.22.38a2 2 0 0 0 2.73.73l.15-.08a2 2 0 0 1 2 0l.43.25a2 2 0 0 1 1 1.73V20a2 2 0 0 0 2 2h.44a2 2 0 0 0 2-2v-.18a2 2 0 0 1 1-1.73l.43-.25a2 2 0 0 1 2 0l.15.08a2 2 0 0 0 2.73-.73l.22-.39a2 2 0 0 0-.73-2.73l-.15-.08a2 2 0 0 1-1-1.74v-.5a2 2 0 0 1 1-1.74l.15-.09a2 2 0 0 0 .73-2.73l-.22-.38a2 2 0 0 0-2.73-.73l-.15.08a2 2 0 0 1-2 0l-.43-.25a2 2 0 0 1-1-1.73V4a2 2 0 0 0-2-2z"/>
            <circle cx="12" cy="12" r="3"/>
          </svg>
        </button>
        {#if showOptions}
          <!-- svelte-ignore a11y_click_events_have_key_events a11y_no_static_element_interactions -->
          <div class="fixed inset-0 z-40" onclick={() => (showOptions = false)}></div>
          <div class="absolute right-0 top-[calc(100%+0.4rem)] z-50 bg-surface border border-border rounded-[12px] shadow-app p-2 flex flex-col min-w-[160px]">
            {#if hasSolution}
              <button
                onclick={() => { toggleSolve(); showOptions = false; }}
                data-testid="solve-button"
                class="flex items-center gap-3 px-2 py-[0.35rem] rounded-[8px] hover:bg-surface-2 text-left text-[0.85rem] w-full"
              >
                {completed ? 'Reset to starter' : 'Show solution'}
              </button>
              <hr class="my-1 border-border">
            {/if}
            <label class="flex items-center gap-3 px-2 py-[0.35rem] rounded-[8px] hover:bg-surface-2 cursor-pointer select-none text-[0.85rem]">
              <input
                type="checkbox"
                checked={$vimMode}
                onchange={(e) => { vimMode.set(e.currentTarget.checked); }}
                class="w-4 h-4 accent-teal"
              />
              Vim mode
            </label>
          </div>
        {/if}
      </div>
    {/snippet}

    <!-- Run button(s) — floating circular buttons overlaid on the code area -->
    {#snippet runButtons()}
      <div class="absolute bottom-3 right-3 z-10 flex gap-[0.4rem]">
        {#if lesson.runner !== 'bmc' && lesson.runner !== 'lec'}
          <button
            onclick={() => (running && runMode === 'sim') ? cancelRun() : runSim('sim')}
            disabled={running && runMode !== 'sim'}
            data-testid="run-button"
            aria-label="{(running && runMode === 'sim') ? 'Cancel' : (lesson.runner === 'cocotb' ? 'Test' : 'Run')} (Ctrl+Enter)"
            title="{(running && runMode === 'sim') ? 'Cancel' : (lesson.runner === 'cocotb' ? 'Test' : 'Run')} (Ctrl+Enter)"
            class="w-10 h-10 rounded-full bg-teal text-white flex items-center justify-center [box-shadow:0_4px_16px_rgba(0,0,0,0.25),0_2px_6px_rgba(0,0,0,0.15)] hover:opacity-90 transition-opacity disabled:opacity-50 disabled:cursor-not-allowed"
          >
            {#if running && runMode === 'sim'}
              <svg class="animate-spin" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" aria-hidden="true">
                <path d="M21 12a9 9 0 1 1-6.219-8.56"/>
              </svg>
            {:else}
              <svg width="14" height="14" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                <polygon points="6,3 20,12 6,21"/>
              </svg>
            {/if}
          </button>
        {/if}
        {#if lesson.runner === 'bmc' || lesson.runner === 'both'}
          <button
            onclick={() => (running && runMode === 'bmc') ? cancelRun() : runSim('bmc')}
            disabled={running && runMode !== 'bmc'}
            data-testid="verify-button"
            aria-label="{running && runMode === 'bmc' ? 'Cancel' : 'Verify'}"
            title="{running && runMode === 'bmc' ? 'Cancel' : 'Verify'}"
            class="w-10 h-10 rounded-full bg-teal text-white flex items-center justify-center [box-shadow:0_4px_16px_rgba(0,0,0,0.25),0_2px_6px_rgba(0,0,0,0.15)] hover:opacity-90 transition-opacity disabled:opacity-50 disabled:cursor-not-allowed"
          >
            {#if running && runMode === 'bmc'}
              <svg class="animate-spin" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" aria-hidden="true">
                <path d="M21 12a9 9 0 1 1-6.219-8.56"/>
              </svg>
            {:else}
              <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
                <polyline points="20 6 9 17 4 12"/>
              </svg>
            {/if}
          </button>
        {/if}
        {#if lesson.runner === 'lec'}
          <button
            onclick={() => (running && runMode === 'lec') ? cancelRun() : runSim('lec')}
            disabled={running && runMode !== 'lec'}
            data-testid="verify-button"
            aria-label="{running && runMode === 'lec' ? 'Cancel' : 'Verify (LEC)'}"
            title="{running && runMode === 'lec' ? 'Cancel' : 'Verify (LEC)'}"
            class="w-10 h-10 rounded-full bg-teal text-white flex items-center justify-center [box-shadow:0_4px_16px_rgba(0,0,0,0.25),0_2px_6px_rgba(0,0,0,0.15)] hover:opacity-90 transition-opacity disabled:opacity-50 disabled:cursor-not-allowed"
          >
            {#if running && runMode === 'lec'}
              <svg class="animate-spin" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" aria-hidden="true">
                <path d="M21 12a9 9 0 1 1-6.219-8.56"/>
              </svg>
            {:else}
              <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
                <polyline points="20 6 9 17 4 12"/>
              </svg>
            {/if}
          </button>
        {/if}
      </div>
    {/snippet}

    <!-- Editor pane -->
    <div style="flex: 0 0 {vSplit}%; min-height: 150px"
         class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 overflow-hidden flex flex-col max-narrow:rounded-none max-narrow:border-x-0 max-narrow:border-t-0">

      {#if splitView && canSplit}
        <!-- Split view: two editors side by side -->
        {@const fileA = lesson.focus}
        {@const fileB = Object.keys(workspace).find(f => f !== fileA)}
        <!-- Editors with per-pane pill headers -->
        <div class="flex-1 min-h-0 flex flex-row">
          <!-- Left pane -->
          <div class="relative min-w-0 overflow-hidden flex flex-col" style="flex: 0 0 {hSplitEditor}%">
            <div data-testid="split-header-left" class="flex-none flex items-center h-10 px-[0.5rem]">
              <span class="font-mono text-[0.8rem] rounded-[10px] border border-teal text-teal bg-tab-selected-bg px-[0.55rem] py-[0.25rem] whitespace-nowrap">{fileA}</span>
            </div>
            <div class="flex-1 min-h-0">
              <CodeEditor filePath={fileA} vimMode={$vimMode} darkMode={$darkMode} value={workspace[fileA] || ''} onchange={(v) => { workspace = { ...workspace, [fileA]: v }; }} diagnostics={diagnosticsByFile[fileA] ?? []} />
            </div>
            {@render runButtons()}
          </div>
          <!-- Drag handle -->
          <div role="separator" aria-orientation="vertical"
               class="flex-none w-[0.7rem] flex items-center justify-center cursor-col-resize select-none group"
               style="touch-action:none"
               onpointerdown={startEditorHResize}>
            <div class="w-[2px] h-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
          </div>
          <!-- Right pane -->
          <div class="flex-1 min-w-0 grid grid-rows-[auto_1fr]">
            <div data-testid="split-header-right" class="flex items-center gap-2 h-10 px-[0.5rem]">
              <span class="font-mono text-[0.8rem] rounded-[10px] border border-border bg-surface-2 px-[0.55rem] py-[0.25rem] whitespace-nowrap">{fileB}</span>
              <div class="flex-1"></div>
              <div class="flex items-center flex-shrink-0">
                <button
                  onclick={() => (splitView = false)}
                  class="flex items-center justify-center w-8 h-8 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground"
                  aria-label="Switch to tab view" title="Switch to tab view"
                >
                  <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                    <rect x="2" y="7" width="20" height="14" rx="2"/>
                    <path d="M2 11h20"/>
                    <path d="M2 7h4v4H2z" fill="currentColor" stroke="none"/>
                  </svg>
                </button>
                {@render optionsButton()}
              </div>
            </div>
            <CodeEditor filePath={fileB} vimMode={$vimMode} darkMode={$darkMode} value={workspace[fileB] || ''} onchange={(v) => { workspace = { ...workspace, [fileB]: v }; }} diagnostics={diagnosticsByFile[fileB] ?? []} />
          </div>
        </div>

      {:else}
        <!-- Single tabbed view -->
        <div class="flex-1 min-h-0 min-w-0 grid grid-rows-[auto_1fr]">
          <div class="flex items-center gap-2 px-[0.5rem] pt-[0.4rem] pb-[0.3rem]">
            <div class="flex-1 overflow-x-auto">
              <Tabs value={selectedFile} onValueChange={(v) => (selectedFile = v)}>
                <TabsList class="h-auto flex-nowrap gap-[0.35rem] bg-transparent p-0 w-max">
                  {#each Object.keys(workspace) as filename}
                    <TabsTrigger
                      value={filename}
                      class="font-mono text-[0.8rem] rounded-[10px] border border-border data-[state=active]:border-teal data-[state=active]:text-teal data-[state=active]:bg-tab-selected-bg data-[state=inactive]:bg-surface-2"
                    >
                      {filename}
                    </TabsTrigger>
                  {/each}
                </TabsList>
              </Tabs>
            </div>
            {#if canSplit}
              <button
                onclick={() => (splitView = true)}
                class="flex-shrink-0 flex items-center justify-center w-6 h-6 rounded-[6px] hover:bg-surface-2 transition-colors text-muted-foreground"
                aria-label="Split editor" title="Split editor"
              >
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="3" width="18" height="18" rx="2"/><path d="M12 3v18"/></svg>
              </button>
            {/if}
            {@render optionsButton()}
          </div>

          <div class="relative min-h-0 overflow-hidden">
            <CodeEditor filePath={selectedFile} vimMode={$vimMode} darkMode={$darkMode} value={workspace[selectedFile] || ''} onchange={onEdit} diagnostics={diagnosticsByFile[selectedFile] ?? []} />
            {@render runButtons()}
          </div>
        </div>
      {/if}
    </div>

    <!-- Vertical drag handle -->
    <div role="separator" aria-label="Resize panels" aria-orientation="horizontal"
         class="flex-none h-[0.7rem] flex items-center justify-center cursor-row-resize select-none group"
         style="touch-action:none"
         onpointerdown={startVResize}>
      <div class="h-[2px] w-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
    </div>

    <!-- Runtime pane -->
    <div style="flex: 1 1 0%; min-height: 220px"
         class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 overflow-hidden flex flex-col max-narrow:rounded-none max-narrow:border-x-0 max-narrow:border-t-0">

      <!-- Header: Logs/Waves tab switcher + waveform toolbar -->
      {#if hasWaveform}
        <div class="flex items-center gap-[0.4rem] px-[0.5rem] py-[0.35rem]">
          <Tabs value={activeRuntimeTab} onValueChange={(v) => (activeRuntimeTab = v)}>
            <TabsList class="h-auto gap-[0.35rem] bg-transparent p-0">
              <TabsTrigger value="logs" data-testid="runtime-tab-logs"
                class="text-[0.8rem] rounded-[10px] border border-border data-[state=active]:border-teal data-[state=active]:text-teal data-[state=active]:bg-tab-selected-bg data-[state=inactive]:bg-surface-2">
                Logs
              </TabsTrigger>
              <TabsTrigger value="waves" data-testid="runtime-tab-waves"
                class="text-[0.8rem] rounded-[10px] border border-border data-[state=active]:border-teal data-[state=active]:text-teal data-[state=active]:bg-tab-selected-bg data-[state=inactive]:bg-surface-2">
                Waves
              </TabsTrigger>
            </TabsList>
          </Tabs>
          {#if activeRuntimeTab === 'waves'}
            <div class="wave-toolbar">
              <button class="wtb-btn" onclick={() => waveformRef?.sendCmd('goto_start')}           title="Go to start"           disabled={!waveSignalsReady}>⏮</button>
              <button class="wtb-btn" onclick={() => waveformRef?.sendCmd('transition_previous')}  title="Previous transition"   disabled={!waveSignalsReady}>◀</button>
              <button class="wtb-btn" onclick={() => waveformRef?.sendCmd('transition_next')}      title="Next transition"       disabled={!waveSignalsReady}>▶</button>
              <button class="wtb-btn" onclick={() => waveformRef?.sendCmd('goto_end')}             title="Go to end"             disabled={!waveSignalsReady}>⏭</button>
              <div class="wtb-sep"></div>
              <button class="wtb-btn" onclick={() => waveformRef?.sendCmd('zoom_out')}  title="Zoom out"    disabled={!waveSignalsReady}>−</button>
              <button class="wtb-btn" onclick={() => waveformRef?.sendCmd('zoom_in')}   title="Zoom in"     disabled={!waveSignalsReady}>+</button>
              <button class="wtb-btn" onclick={() => waveformRef?.sendCmd('zoom_fit')}  title="Zoom to fit" disabled={!waveSignalsReady}>Fit</button>
              <div class="wtb-sep"></div>
              <button class="wtb-btn" onclick={() => waveformRef?.openInNewWindow()} title="Open in Surfer" disabled={!waveSignalsReady}>🏄</button>
            </div>
          {/if}
        </div>
      {/if}

      <!-- Logs tab content -->
      <div
        data-testid="runtime-logs"
        class="m-0 bg-logs-bg text-logs-text p-[0.6rem] overflow-auto font-mono text-[0.78rem]
               {activeRuntimeTab === 'waves' ? 'hidden' : 'flex-1 min-h-0'}"
      >
        {#if logs.length === 0}
          <div class="text-muted-foreground opacity-60 select-none">press ▶ to run</div>
        {:else}
          <div class="flex flex-col gap-2">
            {#each logs as entry}
              {#if isStdoutEntry(entry)}
                <details open>
                  <summary class="cursor-pointer select-none text-logs-text">stdout</summary>
                  <pre class="m-0 mt-1 whitespace-pre-wrap break-words">{stripStreamPrefix(entry)}</pre>
                </details>
              {:else if isStderrEntry(entry)}
                <details open>
                  <summary class="cursor-pointer select-none text-logs-text">stderr</summary>
                  <pre class="m-0 mt-1 whitespace-pre-wrap break-words">{stripStreamPrefix(entry)}</pre>
                </details>
              {:else}
                <div class="whitespace-pre-wrap break-words">{entry}</div>
              {/if}
            {/each}
          </div>
        {/if}
      </div>

      <!-- Waves tab content — always mounted so Surfer doesn't reload on tab switch -->
      {#if hasWaveform}
        <div class="{activeRuntimeTab === 'waves' ? 'flex-1 min-h-0' : 'hidden'}">
          <WaveformViewer
            bind:this={waveformRef}
            bind:signalsReady={waveSignalsReady}
            vcd={lastWaveform.text}
            hasRun={hasRunOnce}
            darkMode={$darkMode}
          />
        </div>
      {/if}
    </div>

  </section>
</section>

{#if glossaryCard}
  <div
    class="fixed z-50 w-[340px] bg-surface border border-border rounded-[14px] shadow-app p-4 text-[0.84rem] leading-relaxed text-foreground pointer-events-none"
    style="top: {glossaryCard.top}px; left: {glossaryCard.left}px"
  >
    {glossaryCard.body}
  </div>
{/if}

{#if showCopyModal}
  <!-- svelte-ignore a11y_click_events_have_key_events a11y_no_static_element_interactions -->
  <div class="fixed inset-0 bg-black/50 flex items-center justify-center z-50"
       onclick={(e) => e.target === e.currentTarget && onCopyModalOk()}>
    <div role="dialog" aria-modal="true" aria-labelledby="copy-modal-title"
         onkeydown={onCopyModalKeydown}
         class="bg-surface rounded-[14px] shadow-xl p-8 max-w-[440px] mx-4 flex flex-col gap-4 border border-border">
      <h2 id="copy-modal-title" class="m-0 text-[1.2rem] font-semibold leading-snug">Copy is currently disabled!</h2>
      <p class="m-0 text-[0.88rem] text-muted-foreground leading-relaxed">
        We recommend typing the code into the editor to complete each exercise,
        as this results in better retention and understanding.
      </p>
      <label class="flex items-center gap-2 text-[0.87rem] cursor-pointer select-none">
        <input type="checkbox" bind:checked={copyEnableChecked} class="w-4 h-4 accent-teal" />
        enable copy for the duration of this session
      </label>
      <button
        autofocus
        onclick={onCopyModalOk}
        class="self-start px-6 py-[0.45rem] bg-teal text-white rounded-[8px] font-medium text-[0.9rem] hover:opacity-90 transition-opacity"
      >OK</button>
    </div>
  </div>
{/if}

<style>
  .wave-toolbar {
    display: flex;
    align-items: center;
    gap: 3px;
    margin-left: 4px;
  }
  .wtb-btn {
    padding: 2px 7px;
    min-width: 26px;
    border-radius: 4px;
    border: 1px solid var(--color-bg-accent);
    background: transparent;
    color: var(--color-ink);
    font-size: 12px;
    line-height: 20px;
    cursor: pointer;
  }
  .wtb-btn:hover:not(:disabled) {
    background: var(--color-surface-2);
  }
  .wtb-btn:disabled {
    opacity: 0.35;
    cursor: default;
  }
  .wtb-sep {
    width: 1px;
    height: 16px;
    background: var(--color-bg-accent);
    margin: 0 4px;
    flex-shrink: 0;
  }
</style>
