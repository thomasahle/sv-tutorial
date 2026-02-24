<script>
  import { lessons, parts } from './tutorial-data.js';
  import { createCirctWasmAdapter } from './runtime/circt-adapter.js';
  import { afterUpdate, onMount } from 'svelte';
  import { Button } from '$lib/components/ui/button';
  import { Tabs, TabsList, TabsTrigger } from '$lib/components/ui/tabs';
  import CodeEditor from '$lib/components/CodeEditor.svelte';
  import WaveformViewer from '$lib/components/WaveformViewer.svelte';

  const circt = createCirctWasmAdapter();

  let hSplit = 33;  // lesson pane % of main section width
  let vSplit = 65;  // editor pane % of lab section height

  // Initialise from the ?lesson=N URL param synchronously so the reactive URL
  // updater (which runs before onMount) sees the correct index from the start
  // and does not strip the query param before onMount can read it.
  function _parseLessonParam() {
    if (typeof window === 'undefined') return 0;
    const n = Number(new URLSearchParams(window.location.search).get('lesson'));
    return (Number.isFinite(n) && n >= 1 && n <= lessons.length) ? n - 1 : 0;
  }
  let lessonIndex = _parseLessonParam();
  let lesson = lessons[lessonIndex];
  let starterFiles = cloneFiles(lesson.files.a);
  let solutionFiles = mergeFiles(starterFiles, lesson.files.b);

  let selectedFile = lesson.focus;
  let workspace = cloneFiles(starterFiles);
  let logs = lessonBootLogs(lesson.title);
  let activeRuntimeTab = 'logs'; // 'logs' | 'waves'
  let running = false;
  let runMode = 'sim';   // 'sim' | 'bmc' | 'lec' — which button triggered the current run
  let runPhase = 'idle'; // 'idle' | 'compiling' | 'running'
  let checkingRuntime = false;
  let runtimeOk = null;
  let lastWaveform = null;
  let hasRunOnce = false;
  let splitView = false;
  let hSplitEditor = 50; // left pane % within split editor
  let vimMode = false;
  let darkMode = false;
  let showOptions = false;
  let completedSlugs = new Set();
  let sidebarOpen = true;
  let expandedChapters = new Set([lessons[lessonIndex].chapterTitle]);
  let sidebarInnerEl;
  let copyEnabled = false;
  let showCopyModal = false;
  let copyEnableChecked = false;
  let lastSidebarScrollLessonIndex = -1;
  let didAnnounceTrimThisRun = false;

  const MAX_NON_STREAM_LOG_ENTRIES = 400;
  const MAX_STREAM_CHARS = 200_000;
  const LOG_TRIM_NOTICE = `# log buffer trimmed: keeping the most recent ${MAX_NON_STREAM_LOG_ENTRIES} non-stream lines`;
  const STREAM_TRIM_NOTICE = `[output truncated: showing last ${MAX_STREAM_CHARS} chars]`;

  afterUpdate(() => {
    if (lastSidebarScrollLessonIndex === lessonIndex) return;
    lastSidebarScrollLessonIndex = lessonIndex;
    sidebarInnerEl?.querySelector('[data-active="true"]')?.scrollIntoView({ block: 'nearest' });
  });

  onMount(() => {
    if (sessionStorage.getItem('copyEnabled') === 'true') copyEnabled = true;

    const params = new URLSearchParams(window.location.search);
    const n = Number(params.get('lesson'));
    if (Number.isFinite(n) && n >= 1 && n <= lessons.length) {
      lessonIndex = n - 1;
      ensureChapterVisible(n - 1);
    }

    try {
      const done = localStorage.getItem('svt:done');
      if (done) completedSlugs = new Set(JSON.parse(done));
    } catch {}

    try {
      if (localStorage.getItem('svt:vimMode') === 'true') vimMode = true;
    } catch {}

    try {
      const savedDark = localStorage.getItem('svt:darkMode');
      if (savedDark !== null) darkMode = savedDark === 'true';
      else darkMode = window.matchMedia('(prefers-color-scheme: dark)').matches;
    } catch {}
  });

  $: {
    if (typeof document !== 'undefined') {
      document.documentElement.classList.toggle('dark', darkMode);
    }
  }

  function toggleDarkMode() {
    darkMode = !darkMode;
    try { localStorage.setItem('svt:darkMode', String(darkMode)); } catch {}
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
      sessionStorage.setItem('copyEnabled', 'true');
    }
    showCopyModal = false;
  }

  $: {
    const url = new URL(window.location.href);
    if (lessonIndex === 0) {
      url.searchParams.delete('lesson');
    } else {
      url.searchParams.set('lesson', String(lessonIndex + 1));
    }
    history.replaceState(null, '', url.toString());
  }

  function onKeydown(e) {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      runSim();
    }
  }

  $: lesson = lessons[lessonIndex];
  $: starterFiles = cloneFiles(lesson.files.a);
  $: solutionFiles = mergeFiles(starterFiles, lesson.files.b);
  $: hasSolution = Object.keys(lesson.files.b).length > 0;
  $: completed = hasSolution && filesEqual(workspace, solutionFiles);
  $: breadcrumbs = `${lesson.partTitle} / ${lesson.chapterTitle} / ${lesson.title}`;
  $: hasWaveform = typeof lastWaveform?.text === 'string' && lastWaveform.text.length > 0;
  $: if (!hasWaveform && activeRuntimeTab === 'waves') activeRuntimeTab = 'logs';

  $: canSplit = Object.keys(workspace).length === 2;

  $: {
    lesson;
    selectedFile = lesson.focus;
    try {
      const saved = localStorage.getItem(`svt:ws:${lesson.slug}`);
      workspace = saved ? JSON.parse(saved) : cloneFiles(starterFiles);
    } catch {
      workspace = cloneFiles(starterFiles);
    }
    splitView = Object.keys(lesson.files.a).length === 2 && window.innerWidth >= 980;
    logs = lessonBootLogs(lesson.title);
    didAnnounceTrimThisRun = false;
    activeRuntimeTab = 'logs';
    runtimeOk = null;
    lastWaveform = null;
    hasRunOnce = false;
  }

  $: try {
    localStorage.setItem(`svt:ws:${lesson.slug}`, JSON.stringify(workspace));
  } catch {}

  $: if (completed && hasSolution) {
    completedSlugs = new Set([...completedSlugs, lesson.slug]);
    try {
      localStorage.setItem('svt:done', JSON.stringify([...completedSlugs]));
    } catch {}
  }

  function cloneFiles(files) {
    return JSON.parse(JSON.stringify(files));
  }

  function lessonBootLogs(_title) {
    return [];
  }

  function mergeFiles(a, b) {
    return { ...cloneFiles(a), ...cloneFiles(b) };
  }

  function topNameFromFocus(path) {
    const filename = path.split('/').pop() || 'top.sv';
    return filename.replace(/\.[^.]+$/, '');
  }

  function normalize(text) {
    return String(text).replace(/\s+/g, ' ').trim();
  }

  function filesEqual(a, b) {
    const aKeys = Object.keys(a).sort();
    const bKeys = Object.keys(b).sort();

    if (aKeys.length !== bKeys.length) return false;

    for (let i = 0; i < aKeys.length; i += 1) {
      const aKey = aKeys[i];
      const bKey = bKeys[i];
      if (aKey !== bKey) return false;
      if (normalize(a[aKey]) !== normalize(b[bKey])) return false;
    }

    return true;
  }

  function toggleChapter(title) {
    if (expandedChapters.has(title)) {
      expandedChapters = new Set([...expandedChapters].filter(t => t !== title));
    } else {
      expandedChapters = new Set([...expandedChapters, title]);
    }
  }

  function ensureChapterVisible(idx) {
    const chapterTitle = lessons[idx]?.chapterTitle;
    if (chapterTitle && !expandedChapters.has(chapterTitle)) {
      expandedChapters = new Set([...expandedChapters, chapterTitle]);
    }
  }

  function step(delta) {
    const nextIndex = lessonIndex + delta;
    if (nextIndex < 0 || nextIndex >= lessons.length) return;
    lessonIndex = nextIndex;
    ensureChapterVisible(nextIndex);
  }

  function toggleSolve() {
    if (!hasSolution) return;

    if (completed) {
      workspace = cloneFiles(starterFiles);
      logs = [...logs, 'Reset to starter files'];
      return;
    }

    workspace = cloneFiles(solutionFiles);
    logs = [...logs, 'Applied solution files'];
  }

  function onEdit(newValue) {
    workspace = { ...workspace, [selectedFile]: newValue };
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

    // Always place stdout before stderr: if adding stdout and stderr already exists,
    // insert the new stdout entry immediately before the first stderr entry.
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
    if (running) return;
    running = true;
    runMode = mode;
    runPhase = 'compiling';
    lastWaveform = null;
    logs = []; // clear terminal on each new run
    didAnnounceTrimThisRun = false;

    const useBmc = mode === 'bmc';
    const useLec = mode === 'lec';

    try {
      const onStatus = (status) => {
        if (status === 'compiling') {
          runPhase = 'compiling';
          return;
        }
        if (status === 'running') {
          runPhase = 'running';
        }
      };
      let streamedEntries = 0;
      const onLog = (entry) => {
        streamedEntries += 1;
        appendLogEntry(entry);
      };
      const mergeNonStreamResultLogs = (resultLogs) => {
        const seen = new Set(logs);
        for (const entry of resultLogs || []) {
          if (isStdoutEntry(entry) || isStderrEntry(entry)) continue;
          if (!seen.has(entry)) {
            appendLogEntry(entry);
            seen.add(entry);
          }
        }
      };

      if (lesson.runner === 'cocotb') {
        const result = await circt.runCocotb({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          onStatus,
          onLog
        });
        if (streamedEntries === 0) for (const entry of result.logs || []) appendLogEntry(entry);
        else mergeNonStreamResultLogs(result.logs);
      } else if (mode === 'lec') {
        const result = await circt.runLec({
          files: workspace,
          module1: lesson.module1 || 'Spec',
          module2: lesson.module2 || 'Impl',
          onStatus,
          onLog
        });
        if (streamedEntries === 0) for (const entry of result.logs || []) appendLogEntry(entry);
        else mergeNonStreamResultLogs(result.logs);
      } else if (useBmc) {
        const result = await circt.runBmc({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          onStatus,
          onLog
        });
        if (streamedEntries === 0) for (const entry of result.logs || []) appendLogEntry(entry);
        else mergeNonStreamResultLogs(result.logs);
      } else {
        const result = await circt.run({
          files: workspace,
          top: topNameFromFocus(lesson.focus),
          simulate: lesson.simulate,
          onStatus,
          onLog
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

  async function selfCheckRuntime() {
    if (checkingRuntime) return;
    checkingRuntime = true;

    try {
      const result = await circt.selfCheck({ lesson });
      runtimeOk = result.ok;
      logs = [...logs, ...result.logs];
    } finally {
      checkingRuntime = false;
    }
  }
</script>

<svelte:window on:keydown={onKeydown} on:copy={handleCopy} />
<main class="h-dvh p-3 flex flex-col gap-[0.7rem] font-sans overflow-hidden">
  <header class="bg-surface border border-border rounded-[14px] shadow-app flex flex-col">
    <!-- Row 1: title + utility buttons -->
    <div class="flex items-center justify-between px-4 py-[0.6rem]">
      <div class="flex items-center gap-2">
        <a href="https://www.normalcomputing.com/" target="_blank" rel="noopener noreferrer"
           class="flex items-center flex-shrink-0" style="color:#d4342a" aria-label="Normal Computing">
          <svg height="15" viewBox="0 0 164 25" fill="none" xmlns="http://www.w3.org/2000/svg" aria-hidden="true">
            <path d="M18.9693 24.5947C18.4393 24.5947 17.9313 24.3393 17.6102 23.9119L8.24226 11.4092V24.5933H0V0.550934H8.74128C9.2777 0.550934 9.78832 0.810239 10.1081 1.24545L18.4819 12.6184V0.550934H26.7241V24.5933H18.968L18.9693 24.5947Z" fill="currentColor"/>
            <path d="M41.0535 25C39.1152 25 37.4158 24.814 36.0034 24.4471C34.5974 24.0815 33.3866 23.5819 32.4032 22.9613C31.4249 22.346 30.6186 21.6304 30.0073 20.8381C29.3935 20.0419 28.9076 19.1845 28.5652 18.2894C28.2214 17.3892 27.9849 16.4719 27.8622 15.5626C27.7381 14.6401 27.6748 13.7555 27.6748 12.9332V11.9341C27.6748 11.0897 27.7381 10.1933 27.8622 9.27092C27.9849 8.35762 28.2214 7.45212 28.5639 6.57915C28.905 5.70748 29.387 4.85923 29.997 4.05912C30.6005 3.26681 31.4004 2.56557 32.3734 1.97492C33.3633 1.37385 34.5755 0.889883 35.9776 0.537313C37.3913 0.180839 39.0996 0 41.0548 0H42.2437C44.2002 0 45.9073 0.180839 47.3197 0.537313C48.7257 0.892485 49.9378 1.37646 50.9225 1.97622C51.9007 2.57208 52.7006 3.27331 53.299 4.06042C53.9076 4.85923 54.3909 5.70748 54.7321 6.58045C55.0758 7.45993 55.3123 8.36542 55.4338 9.27222C55.5565 10.1881 55.6199 11.0832 55.6199 11.9354V12.9345C55.6199 13.7529 55.5578 14.6375 55.4338 15.5639C55.311 16.4772 55.0745 17.3944 54.7308 18.2894C54.3909 19.1793 53.9089 20.038 53.299 20.8407C52.6955 21.633 51.893 22.3473 50.9173 22.9613C49.9339 23.5806 48.7192 24.0802 47.3055 24.4471C45.884 24.814 44.1795 25 42.2424 25H41.0535ZM41.6234 7.11126C40.5922 7.11126 39.7173 7.26218 39.0221 7.5588C38.3204 7.85803 37.7531 8.25744 37.3344 8.74662C36.9196 9.23059 36.6211 9.78481 36.4466 10.3924C36.2786 10.9778 36.1934 11.5633 36.1934 12.1331V12.5325C36.1934 13.1219 36.2825 13.7294 36.4583 14.3409C36.6379 14.9654 36.9467 15.5456 37.3771 16.0634C37.8113 16.5851 38.3799 17.0119 39.0699 17.3332C39.7587 17.6559 40.618 17.8185 41.6234 17.8185C42.6288 17.8185 43.5037 17.6611 44.1937 17.3514C44.8838 17.0418 45.4537 16.6255 45.8879 16.1155C46.3169 15.6107 46.627 15.0356 46.8092 14.406C46.985 13.7958 47.0742 13.1882 47.0742 12.5976V12.1305C47.0742 11.562 46.985 10.9752 46.808 10.3859C46.6257 9.77961 46.3195 9.22669 45.8969 8.74271C45.4718 8.25614 44.9006 7.85803 44.2002 7.5588C43.5049 7.26218 42.6378 7.11126 41.6234 7.11126Z" fill="currentColor"/>
            <path d="M77.1279 13.2599C79.2653 13.726 80.6049 15.9175 81.1711 18.0555C81.7373 20.1923 81.7914 22.4683 82.6124 24.5191C80.4299 24.5191 78.2487 24.5191 76.0663 24.5204C75.6017 24.5204 75.087 24.5022 74.7511 24.1767C74.5169 23.9514 74.4191 23.622 74.3291 23.3082C73.9533 21.9905 73.5763 20.6714 73.2005 19.3537C73.0011 18.6558 72.7604 17.8993 72.1608 17.5008C71.6666 17.1727 71.0387 17.1636 70.448 17.1649C68.6104 17.1688 66.7741 17.1727 64.9365 17.1766L64.9108 24.5947L56.7021 24.592V0.593093C62.6267 0.57877 68.5538 0.564447 74.4796 0.551426C75.6674 0.548821 76.8654 0.547519 78.0274 0.798824C79.1894 1.05013 80.3257 1.57878 81.1093 2.48244C81.8531 3.34052 82.225 4.47464 82.3576 5.60747C82.5737 7.45384 82.2533 9.80413 80.9935 11.2325C80.0812 12.2573 78.8587 12.9461 77.5165 13.1909L77.1279 13.2612V13.2599ZM64.925 11.6258H71.8687C72.5288 11.6258 73.0255 11.4213 73.3485 11.0177H73.3691L73.4823 10.825C73.7603 10.3471 73.8903 9.80413 73.8903 9.11792C73.8903 8.43172 73.7461 7.83145 73.4617 7.37832C73.2417 7.02806 72.7862 6.61139 71.8687 6.61139H64.925V11.6245V11.6258Z" fill="currentColor"/>
            <path d="M101.783 24.5947H96.1292L91.7075 10.4736V24.5947H83.5645V0.550934H93.626C94.2775 0.550934 94.8776 0.935331 95.159 1.53082L98.9408 13.7767L102.724 1.49955C103.01 0.922301 103.603 0.550934 104.241 0.550934H114.358V24.5933H106.192V10.4723L101.782 24.5933L101.783 24.5947Z" fill="currentColor"/>
            <path d="M133.313 21.0796H123.621L122.553 24.5894H115.037L122.652 0.550934L134.297 0.550934L141.897 24.5907L134.42 24.5947L133.313 21.0796ZM125.421 15.5739H131.513L128.468 5.82218L125.421 15.5739Z" fill="currentColor"/>
            <path d="M142.709 24.5947V0.550934H150.951V17.9022H163.193V24.5947H142.709Z" fill="currentColor"/>
          </svg>
        </a>
        <h1 class="m-0 text-[1.05rem] font-semibold tracking-[0.01em]">System Verilog Tutorial</h1>
      </div>
      <div class="flex items-center gap-1">
        <a
          href="https://github.com/thomasnormal/sv-tutorial"
          target="_blank"
          rel="noopener noreferrer"
          class="flex items-center justify-center w-8 h-8 rounded-[8px] hover:bg-surface-2 transition-colors text-muted-foreground"
          aria-label="View on GitHub" title="View on GitHub"
        >
          <svg width="16" height="16" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
            <path d="M12 2C6.477 2 2 6.484 2 12.017c0 4.425 2.865 8.18 6.839 9.504.5.092.682-.217.682-.483 0-.237-.008-.868-.013-1.703-2.782.605-3.369-1.343-3.369-1.343-.454-1.158-1.11-1.466-1.11-1.466-.908-.62.069-.608.069-.608 1.003.07 1.531 1.032 1.531 1.032.892 1.53 2.341 1.088 2.91.832.092-.647.35-1.088.636-1.338-2.22-.253-4.555-1.113-4.555-4.951 0-1.093.39-1.988 1.029-2.688-.103-.253-.446-1.272.098-2.65 0 0 .84-.27 2.75 1.026A9.564 9.564 0 0 1 12 6.844a9.59 9.59 0 0 1 2.504.337c1.909-1.296 2.747-1.027 2.747-1.027.546 1.379.202 2.398.1 2.651.64.7 1.028 1.595 1.028 2.688 0 3.848-2.339 4.695-4.566 4.943.359.309.678.92.678 1.855 0 1.338-.012 2.419-.012 2.747 0 .268.18.58.688.482A10.02 10.02 0 0 0 22 12.017C22 6.484 17.522 2 12 2z"/>
          </svg>
        </a>
        <button
          on:click={toggleDarkMode}
          class="flex items-center justify-center w-8 h-8 rounded-[8px] hover:bg-surface-2 transition-colors text-muted-foreground"
          aria-label={darkMode ? 'Switch to light mode' : 'Switch to dark mode'}
          title={darkMode ? 'Switch to light mode' : 'Switch to dark mode'}
        >
          {#if darkMode}
            <!-- sun -->
            <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
              <circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.93 4.93l1.41 1.41M17.66 17.66l1.41 1.41M2 12h2M20 12h2M4.93 19.07l1.41-1.41M17.66 6.34l1.41-1.41"/>
            </svg>
          {:else}
            <!-- moon -->
            <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
              <path d="M12 3a6 6 0 0 0 9 9 9 9 0 1 1-9-9Z"/>
            </svg>
          {/if}
        </button>
      </div>
    </div>
    <!-- Row 2: navigation -->
    <div class="flex items-center gap-2 px-3 py-[0.35rem] border-t border-border">
      <button
        on:click={() => (sidebarOpen = !sidebarOpen)}
        class="flex items-center justify-center w-7 h-7 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground flex-shrink-0"
        aria-label={sidebarOpen ? 'Close sidebar' : 'Open sidebar'}
        title={sidebarOpen ? 'Close sidebar' : 'Open sidebar'}
      >
        {#if sidebarOpen}
          <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <rect x="3" y="3" width="18" height="18" rx="2"/><path d="M9 3v18"/><path d="m15 9-3 3 3 3"/>
          </svg>
        {:else}
          <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <rect x="3" y="3" width="18" height="18" rx="2"/><path d="M9 3v18"/><path d="m13 15 3-3-3-3"/>
          </svg>
        {/if}
      </button>
      <button
        on:click={() => step(-1)}
        disabled={lessonIndex === 0}
        class="flex items-center justify-center w-7 h-7 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground disabled:opacity-30 disabled:cursor-default"
        aria-label="Previous lesson" title="Previous lesson"
      >
        <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="m15 18-6-6 6-6"/></svg>
      </button>
      <button
        on:click={() => step(1)}
        disabled={lessonIndex === lessons.length - 1}
        class="flex items-center justify-center w-7 h-7 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground disabled:opacity-30 disabled:cursor-default"
        aria-label="Next lesson" title="Next lesson"
      >
        <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="m9 18 6-6-6-6"/></svg>
      </button>
      <span class="text-[0.82rem] text-muted-foreground">{breadcrumbs}</span>
    </div>
  </header>

  <div class="flex-1 min-h-0 flex">
    <!-- Lesson sidebar -->
    <nav
      class="overflow-hidden bg-surface border border-border rounded-[14px] shadow-app flex-shrink-0 min-h-0"
      style="width: {sidebarOpen ? '220px' : '0'}; margin-right: {sidebarOpen ? '0.7rem' : '0'}; opacity: {sidebarOpen ? '1' : '0'}; border-width: {sidebarOpen ? '1px' : '0'}; transition: width 0.2s ease, margin-right 0.2s ease, opacity 0.15s ease"
    >
      <div bind:this={sidebarInnerEl} class="w-[220px] h-full overflow-y-auto p-2 flex flex-col">
        {#each parts as part, pi}
          {#if pi > 0}<div class="border-t border-border mx-1 my-2"></div>{/if}
          <div class="text-[0.6rem] font-bold uppercase tracking-widest text-muted-foreground px-2 py-[0.3rem] mt-1 select-none">
            {part.title}
          </div>
          {#each part.chapters as chapter}
            <button
              class="w-full flex items-center justify-between px-2 py-[0.28rem] rounded-[7px] transition-colors hover:bg-surface-2 text-left mt-[0.15rem]"
              on:click={() => toggleChapter(chapter.title)}
            >
              <span class="text-[0.71rem] text-muted-foreground italic">{chapter.title}</span>
              <span class="text-[0.6rem] text-muted-foreground opacity-60 ml-1 flex-shrink-0">
                {expandedChapters.has(chapter.title) ? '▾' : '▸'}
              </span>
            </button>
            {#if expandedChapters.has(chapter.title)}
              {#each chapter.lessons as item}
                {@const idx = lessons.findIndex(l => l.slug === item.slug)}
                <button
                  class="w-full text-left text-[0.79rem] pl-[1.1rem] pr-2 py-[0.22rem] rounded-[7px] transition-colors leading-snug flex items-center gap-1 {idx === lessonIndex ? 'bg-tab-selected-bg text-teal font-medium' : 'text-foreground hover:bg-surface-2'}"
                  data-active={idx === lessonIndex}
                  on:click={() => { lessonIndex = idx; ensureChapterVisible(idx); }}
                >
                  <span class="flex-1 truncate">{idx + 1}. {item.title}</span>
                  {#if completedSlugs.has(item.slug)}
                    <span class="text-teal flex-shrink-0 ml-1">✓</span>
                  {/if}
                </button>
              {/each}
            {/if}
          {/each}
        {/each}
      </div>
    </nav>

    <section class="flex-1 min-h-0 flex max-narrow:flex-col">
    <article style="flex: 0 0 {hSplit}%; min-width: 200px"
             class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 flex flex-col p-[0.9rem] gap-3 overflow-y-auto [scrollbar-gutter:stable]">
      <h2 data-testid="lesson-title" class="m-0 text-[1.15rem] font-bold leading-tight text-foreground">{lesson.title}</h2>
      <div class="lesson-body">
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
          {#if lessonIndex > 0}
            <button
              on:click={() => step(-1)}
              class="flex items-center gap-1 text-[0.8rem] text-muted-foreground hover:text-teal transition-colors text-left"
            >
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m15 18-6-6 6-6"/></svg>
              <span class="truncate">{lessons[lessonIndex - 1].title}</span>
            </button>
          {:else}
            <div></div>
          {/if}
          {#if lessonIndex < lessons.length - 1}
            <button
              on:click={() => step(1)}
              class="flex items-center gap-1 text-[0.8rem] text-muted-foreground hover:text-teal transition-colors text-right ml-auto"
            >
              <span class="truncate">{lessons[lessonIndex + 1].title}</span>
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m9 18 6-6-6-6"/></svg>
            </button>
          {/if}
        </div>
      </div>
    </article>

    <!-- Horizontal drag handle — hidden on narrow -->
    <div role="separator" aria-label="Resize panels" aria-orientation="vertical"
         class="max-narrow:hidden flex-none w-[0.7rem] flex items-center justify-center cursor-col-resize select-none group"
         style="touch-action:none"
         on:pointerdown={startHResize}>
      <div class="w-[2px] h-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
    </div>

    <section style="flex: 1 1 0%; min-width: 300px" class="min-h-0 flex flex-col">

      <!-- Options button snippet (reused in both split and single view) -->
      {#snippet optionsButton()}
        <div class="relative flex-shrink-0">
          <button
            on:click={() => (showOptions = !showOptions)}
            class="flex items-center justify-center w-8 h-8 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground {showOptions ? 'bg-surface-2' : ''}"
            aria-label="Editor options" title="Editor options"
          >
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
              <path d="M12.22 2h-.44a2 2 0 0 0-2 2v.18a2 2 0 0 1-1 1.73l-.43.25a2 2 0 0 1-2 0l-.15-.08a2 2 0 0 0-2.73.73l-.22.38a2 2 0 0 0 .73 2.73l.15.1a2 2 0 0 1 1 1.72v.51a2 2 0 0 1-1 1.74l-.15.09a2 2 0 0 0-.73 2.73l.22.38a2 2 0 0 0 2.73.73l.15-.08a2 2 0 0 1 2 0l.43.25a2 2 0 0 1 1 1.73V20a2 2 0 0 0 2 2h.44a2 2 0 0 0 2-2v-.18a2 2 0 0 1 1-1.73l.43-.25a2 2 0 0 1 2 0l.15.08a2 2 0 0 0 2.73-.73l.22-.39a2 2 0 0 0-.73-2.73l-.15-.08a2 2 0 0 1-1-1.74v-.5a2 2 0 0 1 1-1.74l.15-.09a2 2 0 0 0 .73-2.73l-.22-.38a2 2 0 0 0-2.73-.73l-.15.08a2 2 0 0 1-2 0l-.43-.25a2 2 0 0 1-1-1.73V4a2 2 0 0 0-2-2z"/>
              <circle cx="12" cy="12" r="3"/>
            </svg>
          </button>
          {#if showOptions}
            <!-- svelte-ignore a11y-click-events-have-key-events a11y-no-static-element-interactions -->
            <div class="fixed inset-0 z-40" on:click={() => (showOptions = false)}></div>
            <div class="absolute right-0 top-[calc(100%+0.4rem)] z-50 bg-surface border border-border rounded-[12px] shadow-app p-2 flex flex-col min-w-[160px]">
              <label class="flex items-center gap-3 px-2 py-[0.35rem] rounded-[8px] hover:bg-surface-2 cursor-pointer select-none text-[0.85rem]">
                <input
                  type="checkbox"
                  checked={vimMode}
                  on:change={(e) => {
                    vimMode = e.currentTarget.checked;
                    try { localStorage.setItem('svt:vimMode', String(vimMode)); } catch {}
                  }}
                  class="w-4 h-4 accent-teal"
                />
                Vim mode
              </label>
            </div>
          {/if}
        </div>
      {/snippet}

      <!-- Editor pane -->
      <div style="flex: 0 0 {vSplit}%; min-height: 150px"
           class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 overflow-hidden {splitView && canSplit ? 'flex flex-row' : 'grid grid-rows-[auto_1fr]'}">

        {#if splitView && canSplit}
          <!-- Split view: two editors side by side -->
          {@const fileA = lesson.focus}
          {@const fileB = Object.keys(workspace).find(f => f !== fileA)}
          <!-- Left pane -->
          <div class="min-w-0 grid grid-rows-[auto_1fr]" style="flex: 0 0 {hSplitEditor}%">
            <div class="flex items-center gap-2 px-[0.5rem] pt-[0.4rem] pb-[0.3rem]">
              <span class="font-mono text-[0.8rem] text-teal truncate flex-1">{fileA}</span>
              {#if hasSolution}
                <Button variant="outline" size="sm" onclick={toggleSolve} data-testid="solve-button" class="flex-shrink-0">
                  {completed ? 'reset' : 'solve'}
                </Button>
              {/if}
            </div>
            <CodeEditor {vimMode} {darkMode} value={workspace[fileA] || ''} onchange={(v) => { workspace = { ...workspace, [fileA]: v }; }} />
          </div>
          <!-- Drag handle -->
          <div role="separator" aria-orientation="vertical"
               class="flex-none w-[0.7rem] flex items-center justify-center cursor-col-resize select-none group"
               style="touch-action:none"
               on:pointerdown={startEditorHResize}>
            <div class="w-[2px] h-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
          </div>
          <!-- Right pane -->
          <div class="flex-1 min-w-0 grid grid-rows-[auto_1fr]">
            <div class="flex items-center gap-2 px-[0.5rem] pt-[0.4rem] pb-[0.3rem]">
              <span class="font-mono text-[0.8rem] text-teal truncate flex-1">{fileB}</span>
              <div class="flex items-center flex-shrink-0">
                <button
                  on:click={() => (splitView = false)}
                  class="flex items-center justify-center w-8 h-8 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground"
                  aria-label="Switch to tab view" title="Switch to tab view"
                >
                  <!-- tabs icon -->
                  <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                    <rect x="2" y="7" width="20" height="14" rx="2"/>
                    <path d="M2 11h20"/>
                    <path d="M2 7h4v4H2z" fill="currentColor" stroke="none"/>
                  </svg>
                </button>
                {@render optionsButton()}
              </div>
            </div>
            <CodeEditor {vimMode} {darkMode} value={workspace[fileB] || ''} onchange={(v) => { workspace = { ...workspace, [fileB]: v }; }} />
          </div>

        {:else}
          <!-- Single tabbed view -->
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
                on:click={() => (splitView = true)}
                class="flex-shrink-0 flex items-center justify-center w-6 h-6 rounded-[6px] hover:bg-surface-2 transition-colors text-muted-foreground"
                aria-label="Split editor" title="Split editor"
              >
                <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="3" width="18" height="18" rx="2"/><path d="M12 3v18"/></svg>
              </button>
            {/if}
            {#if hasSolution}
              <Button variant="outline" size="sm" onclick={toggleSolve} data-testid="solve-button" class="flex-shrink-0">
                {completed ? 'reset' : 'solve'}
              </Button>
            {/if}
            {@render optionsButton()}
          </div>

          <CodeEditor {vimMode} {darkMode} value={workspace[selectedFile] || ''} onchange={onEdit} />
        {/if}
      </div>

      <!-- Vertical drag handle -->
      <div role="separator" aria-label="Resize panels" aria-orientation="horizontal"
           class="flex-none h-[0.7rem] flex items-center justify-center cursor-row-resize select-none group"
           style="touch-action:none"
           on:pointerdown={startVResize}>
        <div class="h-[2px] w-8 rounded-full bg-border group-hover:bg-teal transition-colors"></div>
      </div>

      <!-- Runtime pane -->
      <div style="flex: 1 1 0%; min-height: 220px"
           class="bg-surface border border-border rounded-[14px] shadow-app min-h-0 overflow-hidden flex flex-col">

        <!-- Header: tab switcher + action buttons -->
        <div class="flex justify-between items-center gap-[0.7rem] px-[0.5rem] py-[0.35rem]">
          {#if hasWaveform}
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
          {:else}
            <div></div>
          {/if}

          <div class="flex gap-[0.4rem]">
            {#if lesson.runner !== 'bmc' && lesson.runner !== 'lec'}
              <Button variant="outline" size="sm" onclick={() => runSim('sim')} disabled={running} data-testid="run-button">
                {#if running && runMode === 'sim'}
                  {runPhase === 'running' ? (lesson.runner === 'cocotb' ? 'testing...' : 'running...') : 'compiling...'}
                {:else}
                  {lesson.runner === 'cocotb' ? 'test' : 'run'}
                {/if}
              </Button>
            {/if}
            {#if lesson.runner === 'bmc' || lesson.runner === 'both'}
              <Button variant="outline" size="sm" onclick={() => runSim('bmc')} disabled={running} data-testid="verify-button">
                {#if running && runMode === 'bmc'}
                  {runPhase === 'running' ? 'verifying...' : 'compiling...'}
                {:else}
                  verify
                {/if}
              </Button>
            {/if}
            {#if lesson.runner === 'lec'}
              <Button variant="outline" size="sm" onclick={() => runSim('lec')} disabled={running} data-testid="verify-button">
                {#if running && runMode === 'lec'}
                  {runPhase === 'running' ? 'verifying...' : 'compiling...'}
                {:else}
                  verify (LEC)
                {/if}
              </Button>
            {/if}
          </div>
        </div>

        <!-- Logs tab content -->
        <div
          data-testid="runtime-logs"
          class="m-0 bg-logs-bg text-logs-text p-[0.6rem] overflow-auto font-mono text-[0.78rem]
                 {activeRuntimeTab === 'waves' ? 'hidden' : 'flex-1 min-h-0'}"
        >
          {#if logs.length === 0}
            <div class="text-muted-foreground">no output yet</div>
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
              vcd={lastWaveform.text}
              hasRun={hasRunOnce}
              {darkMode}
            />
          </div>
        {/if}
      </div>

    </section>
  </section>
  </div>

  {#if showCopyModal}
    <!-- svelte-ignore a11y-click-events-have-key-events a11y-no-static-element-interactions -->
    <div class="fixed inset-0 bg-black/50 flex items-center justify-center z-50"
         on:click|self={onCopyModalOk}>
      <div class="bg-surface rounded-[14px] shadow-xl p-8 max-w-[440px] mx-4 flex flex-col gap-4 border border-border">
        <h2 class="m-0 text-[1.2rem] font-semibold leading-snug">Copy is currently disabled!</h2>
        <p class="m-0 text-[0.88rem] text-muted-foreground leading-relaxed">
          We recommend typing the code into the editor to complete each exercise,
          as this results in better retention and understanding.
        </p>
        <label class="flex items-center gap-2 text-[0.87rem] cursor-pointer select-none">
          <input type="checkbox" bind:checked={copyEnableChecked} class="w-4 h-4 accent-teal" />
          enable copy for the duration of this session
        </label>
        <button
          on:click={onCopyModalOk}
          class="self-start px-6 py-[0.45rem] bg-teal text-white rounded-[8px] font-medium text-[0.9rem] hover:opacity-90 transition-opacity"
        >OK</button>
      </div>
    </div>
  {/if}
</main>
