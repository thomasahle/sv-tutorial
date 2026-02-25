<script>
  import { page } from '$app/stores';
  import { goto } from '$app/navigation';
  import { base } from '$app/paths';
  import { browser } from '$app/environment';
  import { onMount, untrack } from 'svelte';
  import '../app.css';
  import { getCirctRuntimeConfig, Z3_SCRIPT_URL } from '../runtime/circt-config.js';
  import {
    OFFLINE_APP_CACHE_PREFIX,
    OFFLINE_RUNTIME_CACHE,
    OFFLINE_STATE_KEY,
    offlineReadySentinelUrl,
    PYODIDE_MANIFEST_RELATIVE_PATH,
    UVM_MANIFEST_RELATIVE_PATH,
    buildConfiguredRuntimeUrls,
    dedupeStrings,
    joinBasePath,
  } from '$lib/offline-cache.js';
  import { darkMode } from '$lib/stores/settings.js';
  import { completedSlugs } from '$lib/stores/completed.js';
  import {
    SidebarProvider,
    Sidebar,
    SidebarContent,
    SidebarTrigger,
  } from '$lib/components/ui/sidebar/index.js';

  let { data, children } = $props();

  let currentSlug = $derived(
    $page.params.part ? `${$page.params.part}/${$page.params.name}` : null
  );
  let lessonIndex = $derived(data.lessons.findIndex(l => l.slug === currentSlug));
  let lesson = $derived(data.lessons[lessonIndex]);
  let breadcrumbs = $derived(lesson ? `${lesson.partTitle} / ${lesson.chapterTitle} / ${lesson.title}` : '');

  let sidebarOpen = $state(true);
  let expandedChapters = $state(new Set());
  let sidebarInnerEl = $state(null);
  let offlineMode = $state('idle');
  let offlineDone = $state(0);
  let offlineTotal = $state(0);
  let offlineMessage = $state('');
  const offlineFeatureEnabled = import.meta.env.PROD;

  function runtimeBasePath() {
    return base ? `${base}/` : '/';
  }

  function formatBytes(bytes) {
    const value = Number(bytes) || 0;
    if (value < 1024 * 1024) return `${Math.round(value / 1024)} KB`;
    return `${(value / (1024 * 1024)).toFixed(1)} MB`;
  }

  function isSameOriginAssetUrl(url) {
    try {
      return new URL(url, window.location.href).origin === window.location.origin;
    } catch {
      return false;
    }
  }

  function toAbsolute(url) {
    return new URL(String(url), window.location.href).href;
  }

  function offlineReadyMarkerUrl() {
    return toAbsolute(offlineReadySentinelUrl(runtimeBasePath()));
  }

  async function hasOfflineReadyMarker() {
    if (!browser || !('caches' in window)) return false;
    try {
      const cache = await caches.open(OFFLINE_RUNTIME_CACHE);
      const marker = await cache.match(offlineReadyMarkerUrl());
      return Boolean(marker);
    } catch {
      return false;
    }
  }

  async function fetchJson(url) {
    const response = await fetch(url, { cache: 'reload' });
    if (!response.ok) throw new Error(`${url}: HTTP ${response.status}`);
    return response.json();
  }

  async function ensureOfflineServiceWorker() {
    if (!offlineFeatureEnabled) return null;
    if (!browser || !('serviceWorker' in navigator)) return null;
    const swUrl = `${base || ''}/service-worker.js`;
    const registration = await navigator.serviceWorker.register(swUrl, {
      type: 'module',
      updateViaCache: 'none'
    });
    await navigator.serviceWorker.ready;
    return registration;
  }

  async function clearOfflineArtifactsForDev() {
    if (!browser) return;
    localStorage.removeItem(OFFLINE_STATE_KEY);
    offlineMode = 'idle';
    offlineDone = 0;
    offlineTotal = 0;
    offlineMessage = '';

    if ('serviceWorker' in navigator) {
      const scopeRoot = new URL(`${base || ''}/`, window.location.href).href;
      const registrations = await navigator.serviceWorker.getRegistrations();
      await Promise.all(
        registrations
          .filter((registration) => registration.scope.startsWith(scopeRoot))
          .map((registration) => registration.unregister().catch(() => false))
      );
    }

    if ('caches' in window) {
      const keys = await caches.keys();
      await Promise.all(
        keys
          .filter((key) => key === OFFLINE_RUNTIME_CACHE || key.startsWith(OFFLINE_APP_CACHE_PREFIX))
          .map((key) => caches.delete(key))
      );
    }
  }

  async function resolveOfflineAssetUrls(config) {
    const basePath = runtimeBasePath();
    const urls = buildConfiguredRuntimeUrls({
      basePath,
      runtimeConfig: config,
      z3ScriptUrl: Z3_SCRIPT_URL,
    });

    const uvmManifestUrl = toAbsolute(joinBasePath(basePath, UVM_MANIFEST_RELATIVE_PATH));
    urls.push(uvmManifestUrl);
    try {
      const uvmManifest = await fetchJson(uvmManifestUrl);
      const srcBaseUrl = new URL('src/', uvmManifestUrl).href;
      for (const relPath of uvmManifest.files || []) {
        const rel = String(relPath || '').replace(/^\/+/, '');
        if (!rel || rel.includes('..')) continue;
        urls.push(new URL(rel, srcBaseUrl).href);
      }
    } catch {
      // Best-effort: UVM sources are only needed for UVM lessons.
    }

    const pyodideManifestUrl = toAbsolute(joinBasePath(basePath, PYODIDE_MANIFEST_RELATIVE_PATH));
    try {
      const pyodideManifest = await fetchJson(pyodideManifestUrl);
      const manifestBase = new URL(String(pyodideManifest.basePath || './'), pyodideManifestUrl).href;
      for (const relPath of pyodideManifest.files || []) {
        const rel = String(relPath || '').replace(/^\/+/, '');
        if (!rel || rel.includes('..')) continue;
        urls.push(new URL(rel, manifestBase).href);
      }
    } catch {
      // If no local manifest is present, we'll still cache configured pyodide URLs.
    }

    urls.push(toAbsolute(runtimeBasePath()));
    urls.push(toAbsolute(joinBasePath(basePath, '404.html')));
    urls.push(toAbsolute(joinBasePath(basePath, 'service-worker.js')));
    return dedupeStrings(urls);
  }

  function offlineButtonTitle() {
    if (!offlineFeatureEnabled) {
      return 'Offline bundle download is available in preview/prod builds';
    }
    if (offlineMode === 'downloading') {
      const total = offlineTotal || '?';
      return `Downloading offline bundle (${offlineDone}/${total})`;
    }
    if (offlineMode === 'ready') {
      return offlineMessage || 'Offline bundle is ready';
    }
    if (offlineMode === 'error') {
      return offlineMessage || 'Offline bundle download failed';
    }
    return 'Download offline bundle';
  }

  function offlineButtonLabel() {
    if (!offlineFeatureEnabled) return 'Offline bundle unavailable in dev mode';
    if (offlineMode === 'downloading') return 'Downloading offline bundle';
    if (offlineMode === 'ready') return 'Offline bundle ready';
    if (offlineMode === 'error') return 'Retry offline bundle download';
    return 'Download offline bundle';
  }

  function offlineProgressText() {
    if (offlineMode === 'downloading') {
      const total = offlineTotal || '?';
      return `${offlineDone}/${total}`;
    }
    if (offlineMode === 'ready') return 'offline ready';
    if (offlineMode === 'error') return 'download failed';
    return '';
  }

  async function downloadOfflineBundle() {
    if (!browser || !offlineFeatureEnabled || offlineMode === 'downloading') return;
    offlineMode = 'downloading';
    offlineDone = 0;
    offlineTotal = 0;
    offlineMessage = 'Preparing offline bundle...';

    try {
      await ensureOfflineServiceWorker();
      const config = getCirctRuntimeConfig();
      const allUrls = await resolveOfflineAssetUrls(config);
      const urls = allUrls.filter((url) => isSameOriginAssetUrl(url));
      const skippedCrossOrigin = allUrls.length - urls.length;
      if (urls.length === 0) {
        throw new Error('No same-origin assets were found to cache');
      }

      offlineTotal = urls.length;
      const cache = await caches.open(OFFLINE_RUNTIME_CACHE);
      const readyMarkerRequest = new Request(offlineReadyMarkerUrl(), { method: 'GET' });
      const failures = [];
      let skippedMissing = 0;
      let bytes = 0;
      let success = 0;

      for (const url of urls) {
        try {
          const request = new Request(url, { method: 'GET' });
          const response = await fetch(request, { cache: 'reload' });
          if (response.status === 404) {
            skippedMissing += 1;
            continue;
          }
          if (!response.ok && response.type !== 'opaque') {
            throw new Error(`HTTP ${response.status}`);
          }
          const contentLength = Number(response.headers.get('content-length') || 0);
          if (contentLength > 0) bytes += contentLength;
          await cache.put(request, response.clone());
          success += 1;
        } catch (error) {
          failures.push(`${url}: ${String(error?.message || error)}`);
        } finally {
          offlineDone += 1;
        }
      }

      if (failures.length > 0) {
        await cache.delete(readyMarkerRequest);
        offlineMode = 'error';
        offlineMessage = `Cached ${success}/${offlineTotal} files. ${failures.length} failed.`;
        localStorage.removeItem(OFFLINE_STATE_KEY);
      } else {
        await cache.put(
          readyMarkerRequest,
          new Response('ready', {
            headers: { 'content-type': 'text/plain; charset=utf-8' }
          })
        );
        offlineMode = 'ready';
        offlineMessage = `Cached ${success} files (${formatBytes(bytes)}).`;
        if (skippedMissing > 0) {
          offlineMessage += ` Skipped ${skippedMissing} missing optional files.`;
        }
        if (skippedCrossOrigin > 0) {
          offlineMessage += ` Skipped ${skippedCrossOrigin} cross-origin URLs.`;
        }
        localStorage.setItem(OFFLINE_STATE_KEY, 'ready');
      }
    } catch (error) {
      offlineMode = 'error';
      offlineMessage = String(error?.message || error || 'Offline download failed');
      localStorage.removeItem(OFFLINE_STATE_KEY);
      if ('caches' in window) {
        caches
          .open(OFFLINE_RUNTIME_CACHE)
          .then((cache) => cache.delete(offlineReadyMarkerUrl()))
          .catch(() => {});
      }
    }
  }

  function toggleChapter(title) {
    if (expandedChapters.has(title)) {
      expandedChapters = new Set([...expandedChapters].filter(t => t !== title));
    } else {
      expandedChapters = new Set([...expandedChapters, title]);
    }
  }

  function navigateTo(l) {
    const [part, name] = l.slug.split('/');
    goto(`${base}/lesson/${part}/${name}`);
  }

  function step(delta) {
    const nextIndex = lessonIndex + delta;
    if (nextIndex < 0 || nextIndex >= data.lessons.length) return;
    navigateTo(data.lessons[nextIndex]);
  }

  // Apply dark mode class on <html>
  $effect(() => {
    if (browser) document.documentElement.classList.toggle('dark', $darkMode);
  });

  // Expand active chapter in sidebar on navigation.
  $effect(() => {
    const chap = lesson?.chapterTitle;
    if (chap) untrack(() => {
      if (!expandedChapters.has(chap)) {
        expandedChapters = new Set([...expandedChapters, chap]);
      }
    });
  });

  // Auto-scroll active sidebar item into view
  $effect(() => {
    lessonIndex;
    sidebarInnerEl?.querySelector('[data-active="true"]')?.scrollIntoView({ block: 'nearest' });
  });

  function toggleDarkMode() {
    darkMode.update(v => !v);
  }

  function getPartLessons(part) {
    return part.chapters.flatMap((chapter) => chapter.lessons);
  }

  function getPartCompletedCount(part) {
    return getPartLessons(part).filter((lessonItem) => $completedSlugs.has(lessonItem.slug)).length;
  }

  onMount(() => {
    if (!window.matchMedia('(min-width: 980px)').matches) sidebarOpen = false;
    if (localStorage.getItem('svt:darkMode') === null) {
      darkMode.set(window.matchMedia('(prefers-color-scheme: dark)').matches);
    }
    if (!offlineFeatureEnabled) {
      clearOfflineArtifactsForDev().catch(() => {});
      return;
    }
    if (localStorage.getItem(OFFLINE_STATE_KEY) === 'ready') {
      hasOfflineReadyMarker()
        .then((ready) => {
          if (ready) {
            offlineMode = 'ready';
            offlineMessage = 'Offline bundle is ready';
            return;
          }
          localStorage.removeItem(OFFLINE_STATE_KEY);
        })
        .catch(() => {
          localStorage.removeItem(OFFLINE_STATE_KEY);
        });
    }
    ensureOfflineServiceWorker().catch(() => {});
  });
</script>

{#snippet navItems()}
  <div bind:this={sidebarInnerEl} class="flex flex-col p-2 gap-0">
    {#each data.parts as part, pi}
      {#if pi > 0}<div class="border-t border-sidebar-border mx-1 my-2"></div>{/if}
      <div class="text-[0.6rem] font-bold uppercase tracking-widest text-muted-foreground px-2 py-[0.3rem] mt-1 select-none flex items-center">
        <span>{part.title}</span>
        {#if getPartCompletedCount(part) > 0}
          <span class="text-[0.55rem] text-teal ml-auto flex-shrink-0">
            {getPartCompletedCount(part)}/{getPartLessons(part).length}
          </span>
        {/if}
      </div>
      {#each part.chapters as chapter}
        <button
          class="w-full flex items-center justify-between px-2 py-[0.28rem] rounded-[7px] transition-colors hover:bg-sidebar-accent text-left mt-[0.15rem]"
          onclick={() => toggleChapter(chapter.title)}
        >
          <span class="text-[0.71rem] text-muted-foreground italic">{chapter.title}</span>
          <span class="text-[0.6rem] text-muted-foreground opacity-60 ml-1 flex-shrink-0">
            {expandedChapters.has(chapter.title) ? '▾' : '▸'}
          </span>
        </button>
        {#if expandedChapters.has(chapter.title)}
          {#each chapter.lessons as item}
            {@const idx = data.lessons.findIndex(l => l.slug === item.slug)}
            <button
              class="w-full text-left text-[0.79rem] pl-[1.1rem] pr-2 py-[0.22rem] rounded-[7px] transition-colors leading-snug flex items-center gap-1 {idx === lessonIndex ? 'bg-tab-selected-bg text-teal font-medium' : 'text-foreground hover:bg-sidebar-accent'}"
              data-active={idx === lessonIndex}
              onclick={() => navigateTo(item)}
            >
              <span class="flex-1 truncate">{idx + 1}. {item.title}</span>
              {#if $completedSlugs.has(item.slug)}
                <span class="text-teal flex-shrink-0 ml-1">✓</span>
              {/if}
            </button>
          {/each}
        {/if}
      {/each}
    {/each}
  </div>
{/snippet}

<SidebarProvider bind:open={sidebarOpen} class="h-dvh overflow-hidden flex-col font-sans p-3 gap-[0.7rem] max-narrow:p-0 max-narrow:gap-0">

  <!-- Header spans full width above the sidebar+content row -->
  <header class="bg-surface border border-border rounded-[14px] shadow-app flex flex-col flex-shrink-0 max-narrow:rounded-none max-narrow:border-x-0 max-narrow:border-t-0">
      <!-- Row 1: logo + title + utility buttons -->
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
            onclick={downloadOfflineBundle}
            disabled={!offlineFeatureEnabled || offlineMode === 'downloading'}
            class="flex items-center justify-center w-8 h-8 rounded-[8px] hover:bg-surface-2 transition-colors disabled:opacity-60 disabled:cursor-default {offlineMode === 'ready' ? 'text-teal' : 'text-muted-foreground'}"
            data-testid="offline-download-button"
            aria-label={offlineButtonLabel()}
            title={offlineButtonTitle()}
          >
            {#if offlineMode === 'downloading'}
              <svg class="animate-spin" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
                <path d="M21 12a9 9 0 1 1-6.219-8.56" />
              </svg>
            {:else if offlineMode === 'ready'}
              <svg width="14" height="14" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                <path d="M12 2a10 10 0 1 0 10 10A10 10 0 0 0 12 2Zm5 7-6 7a1 1 0 0 1-1.5.05l-3-3a1 1 0 0 1 1.4-1.4l2.25 2.25 5.24-6.11A1 1 0 0 1 17 9Z" />
              </svg>
            {:else}
              <svg width="14" height="14" viewBox="0 0 24 24" fill="currentColor" aria-hidden="true">
                <path d="M11 3a1 1 0 0 1 2 0v9.59l2.3-2.29a1 1 0 0 1 1.4 1.41l-4 4a1 1 0 0 1-1.4 0l-4-4a1 1 0 1 1 1.4-1.41L11 12.59V3Zm-7 14a1 1 0 0 1 1-1h14a1 1 0 1 1 0 2H5a1 1 0 0 1-1-1Z" />
              </svg>
            {/if}
          </button>
          {#if offlineMode !== 'idle'}
            <span
              class="text-[0.68rem] leading-none whitespace-nowrap px-2 py-[0.32rem] rounded-[8px] border {offlineMode === 'ready' ? 'text-teal border-teal/40 bg-teal/5' : offlineMode === 'error' ? 'text-destructive border-destructive/40 bg-destructive/5' : 'text-muted-foreground border-border bg-surface-2'}"
              data-testid="offline-download-status"
              aria-live="polite"
              title={offlineButtonTitle()}
            >
              {offlineProgressText()}
            </span>
          {/if}
          <button
            onclick={toggleDarkMode}
            class="flex items-center justify-center w-8 h-8 rounded-[8px] hover:bg-surface-2 transition-colors text-muted-foreground"
            aria-label={$darkMode ? 'Switch to light mode' : 'Switch to dark mode'}
            title={$darkMode ? 'Switch to light mode' : 'Switch to dark mode'}
          >
            {#if $darkMode}
              <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                <circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.93 4.93l1.41 1.41M17.66 17.66l1.41 1.41M2 12h2M20 12h2M4.93 19.07l1.41-1.41M17.66 6.34l1.41-1.41"/>
              </svg>
            {:else}
              <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                <path d="M12 3a6 6 0 0 0 9 9 9 9 0 1 1-9-9Z"/>
              </svg>
            {/if}
          </button>
        </div>
      </div>
      <!-- Row 2: sidebar trigger + prev/next + breadcrumbs -->
      <div class="flex items-center gap-2 px-3 py-[0.35rem] border-t border-border">
        <SidebarTrigger
          class="flex items-center justify-center w-7 h-7 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground flex-shrink-0 [&>svg]:size-[14px]"
        />
        <button
          onclick={() => step(-1)}
          disabled={lessonIndex <= 0}
          class="flex items-center justify-center w-7 h-7 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground disabled:opacity-30 disabled:cursor-default"
          aria-label="Previous lesson" title="Previous lesson"
        >
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="m15 18-6-6 6-6"/></svg>
        </button>
        <button
          onclick={() => step(1)}
          disabled={lessonIndex >= data.lessons.length - 1}
          class="flex items-center justify-center w-7 h-7 rounded-[7px] hover:bg-surface-2 transition-colors text-muted-foreground disabled:opacity-30 disabled:cursor-default"
          aria-label="Next lesson" title="Next lesson"
        >
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="m9 18 6-6-6-6"/></svg>
        </button>
        <span class="text-[0.82rem] text-muted-foreground">{breadcrumbs}</span>
      </div>
  </header>

  <!-- Sidebar + lesson content row (relative so the absolute sidebar is contained here) -->
  <div class="flex flex-1 min-h-0 relative overflow-hidden">
    <Sidebar variant="floating" collapsible="offcanvas">
      <SidebarContent>
        {@render navItems()}
      </SidebarContent>
    </Sidebar>
    <div class="flex-1 min-w-0 flex flex-col">
      {@render children()}
    </div>
  </div>
</SidebarProvider>
