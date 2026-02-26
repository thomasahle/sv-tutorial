<script>
  import { EditorView, basicSetup } from 'codemirror';
  import { EditorState, Compartment } from '@codemirror/state';
  import { StreamLanguage, syntaxHighlighting, HighlightStyle, indentUnit } from '@codemirror/language';
  import { linter, lintGutter, setDiagnostics } from '@codemirror/lint';
  import { verilog } from '@codemirror/legacy-modes/mode/verilog';
  import { python } from '@codemirror/legacy-modes/mode/python';
  import { tags } from '@lezer/highlight';
  import { untrack } from 'svelte';

  // diagnostics: array of { line: number, severity: 'error'|'warning', message: string }
  let { value, onchange, filePath = '', vimMode = false, darkMode = false, diagnostics = [] } = $props();
  let container;

  // Dark-mode syntax highlight palette — colours tuned for the dark green background.
  const darkHighlight = HighlightStyle.define([
    { tag: tags.keyword,                            color: '#7ac4ff' },
    { tag: [tags.lineComment, tags.blockComment],   color: '#577067', fontStyle: 'italic' },
    { tag: [tags.string, tags.regexp],              color: '#7ecfa0' },
    { tag: tags.number,                             color: '#f0a070' },
    { tag: tags.operator,                           color: '#3db5b9' },
    { tag: tags.standard(tags.name),                color: '#64b5f6' },
    { tag: [tags.typeName, tags.className],         color: '#e8c87a' },
    { tag: tags.definition(tags.variableName),      color: '#b794f6' },
    { tag: tags.meta,                               color: '#b794f6' },
    { tag: tags.invalid,                            color: '#fc6767', textDecoration: 'underline' },
  ]);

  function makeTheme(dark) {
    return EditorView.theme({
      '&': {
        height: '100%',
        fontSize: '0.85rem',
        lineHeight: '1.35',
        fontFamily: "'IBM Plex Mono', Menlo, Consolas, monospace",
        backgroundColor: dark ? '#1e2422' : '#faf7ef',
        color:           dark ? '#d4e8e0' : '#162123',
      },
      '.cm-content': { padding: '0.7rem', caretColor: dark ? '#3db5b9' : '#0d6f72' },
      '.cm-cursor, .cm-dropCursor': { borderLeftColor: dark ? '#3db5b9' : '#0d6f72' },
      '.cm-gutters': {
        backgroundColor: dark ? '#181e1c' : '#f0ede4',
        borderRight:     `1px solid ${dark ? '#2d3532' : '#d5cbb2'}`,
        color:           dark ? '#5a7a72' : '#8a8070',
      },
      '.cm-lineNumbers .cm-gutterElement': { padding: '0 0 0 8px' },
      '.cm-activeLineGutter': { backgroundColor: dark ? '#232e2b' : '#e8e4da' },
      '.cm-activeLine':       { backgroundColor: dark ? 'rgba(61,181,185,0.07)' : 'rgba(13,111,114,0.05)' },
      '.cm-selectionBackground, ::selection': {
        backgroundColor: (dark ? 'rgba(61,181,185,0.25)' : 'rgba(13,111,114,0.18)') + ' !important',
      },
      '.cm-focused .cm-selectionBackground': {
        backgroundColor: (dark ? 'rgba(61,181,185,0.30)' : 'rgba(13,111,114,0.22)') + ' !important',
      },
      '&.cm-focused': { outline: 'none' },
      '.cm-scroller': { overflow: 'auto', height: '100%' },
      // Lint gutter
      '.cm-gutter-lint': { width: '0' },
      '.cm-lint-marker-error': { color: '#e05555' },
      '.cm-lint-marker-warning': { color: '#c97a20' },
      // Wavy underlines
      '.cm-lintRange-error': { backgroundImage: 'none', borderBottom: '2px solid #e05555' },
      '.cm-lintRange-warning': { backgroundImage: 'none', borderBottom: '2px dashed #c97a20' },
    }, { dark });
  }

  const themeCompartment = new Compartment();
  const languageCompartment = new Compartment();
  const highlightCompartment = new Compartment();
  const indentCompartment = new Compartment();
  const vimCompartment = new Compartment();

  function languageExtensionForPath(path) {
    const lower = String(path || '').toLowerCase();
    if (lower.endsWith('.py')) return StreamLanguage.define(python);
    return StreamLanguage.define(verilog);
  }

  function indentExtensionForPath(path) {
    const lower = String(path || '').toLowerCase();
    if (lower.endsWith('.py')) return indentUnit.of('    ');
    return [];
  }

  // Setup — runs once. untrack(value) avoids re-creating editor on every keystroke.
  $effect(() => {
    const el = container;
    const initial = untrack(() => value);
    const initialVimMode = untrack(() => vimMode);

    let vimExtension = [];
    const setupVim = async () => {
      if (!initialVimMode) return;
      try {
        const { vim } = await import('@replit/codemirror-vim');
        vimExtension = vim();
      } catch (e) { console.error('vim load error:', e); }
    };

    let view;
    setupVim().then(() => {
      // Read darkMode here (not pre-captured) so we get the value current at
      // creation time — onMount may have already set it from localStorage.
      view = new EditorView({
        state: EditorState.create({
          doc: initial,
          extensions: [
            basicSetup,
            linter(() => []),
            lintGutter(),
            languageCompartment.of(languageExtensionForPath(filePath)),
            indentCompartment.of(indentExtensionForPath(filePath)),
            themeCompartment.of(makeTheme(darkMode)),
            highlightCompartment.of(darkMode ? syntaxHighlighting(darkHighlight) : []),
            vimCompartment.of(vimExtension),
            EditorView.contentAttributes.of({ 'aria-label': filePath ? `Code editor: ${filePath}` : 'Code editor' }),
            EditorView.updateListener.of(u => {
              if (u.docChanged) onchange(u.state.doc.toString());
            }),
          ],
        }),
        parent: el,
      });
      el._cmView = view;
      // `value` may have changed while vim was loading asynchronously (e.g.
      // onMount populated the workspace after this effect started). Sync now
      // so the editor doesn't open empty.
      const latestValue = value;
      if (latestValue !== initial) {
        view.dispatch({ changes: { from: 0, to: initial.length, insert: latestValue } });
      }
    });

    return () => {
      el._cmView = null;
      view?.destroy();
    };
  });

  // Sync — pushes external value changes (file switch, solve/reset) into editor.
  // Read `value` BEFORE the null guard so Svelte 5 always tracks it as a dependency.
  $effect(() => {
    const nextValue = value;
    const v = container?._cmView;
    if (!v) return;
    const current = v.state.doc.toString();
    if (current !== nextValue) {
      v.dispatch({ changes: { from: 0, to: current.length, insert: nextValue } });
    }
  });

  // Toggle dark mode dynamically.
  // Read `darkMode` BEFORE the null guard so Svelte 5 always tracks it as a dependency.
  $effect(() => {
    const dark = darkMode;
    const v = container?._cmView;
    if (!v) return;
    v.dispatch({ effects: [
      themeCompartment.reconfigure(makeTheme(dark)),
      highlightCompartment.reconfigure(dark ? syntaxHighlighting(darkHighlight) : []),
    ]});
  });

  // Reconfigure syntax highlighting based on selected file extension.
  $effect(() => {
    const path = filePath;
    const v = container?._cmView;
    if (!v) return;
    v.dispatch({ effects: [
      languageCompartment.reconfigure(languageExtensionForPath(path)),
      indentCompartment.reconfigure(indentExtensionForPath(path)),
    ]});
  });

  // Push diagnostics (errors/warnings from simulator) into the editor.
  $effect(() => {
    const diags = diagnostics;
    const v = container?._cmView;
    if (!v) return;
    const cmDiags = diags.flatMap(d => {
      try {
        const line = v.state.doc.line(Math.max(1, Math.min(d.line, v.state.doc.lines)));
        return [{ from: line.from, to: line.to, severity: d.severity ?? 'error', message: d.message }];
      } catch { return []; }
    });
    v.dispatch(setDiagnostics(v.state, cmDiags));
  });

  // Toggle vim mode dynamically without recreating the editor.
  // Read `vimMode` BEFORE the null guard AND outside the async so Svelte 5 tracks it.
  $effect(() => {
    const enableVim = vimMode;
    const v = container?._cmView;
    if (!v) return;
    (async () => {
      let ext = [];
      if (enableVim) {
        try {
          const { vim } = await import('@replit/codemirror-vim');
          ext = vim();
        } catch (e) { console.error('vim load error:', e); }
      }
      v.dispatch({ effects: vimCompartment.reconfigure(ext) });
    })();
  });
</script>

<div bind:this={container} class="w-full h-full overflow-hidden"></div>
