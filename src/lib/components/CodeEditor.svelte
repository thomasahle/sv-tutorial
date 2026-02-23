<script>
  import { EditorView, basicSetup } from 'codemirror';
  import { EditorState } from '@codemirror/state';
  import { StreamLanguage } from '@codemirror/language';
  import { verilog } from '@codemirror/legacy-modes/mode/verilog';
  import { untrack } from 'svelte';

  let { value, onchange } = $props();
  let container;

  const warmTheme = EditorView.theme({
    '&': {
      height: '100%',
      fontSize: '0.85rem',
      lineHeight: '1.35',
      fontFamily: "'IBM Plex Mono', Menlo, Consolas, monospace",
      backgroundColor: '#faf7ef',
      color: '#162123',
    },
    '.cm-content': { padding: '0.7rem', caretColor: '#0d6f72' },
    '.cm-cursor, .cm-dropCursor': { borderLeftColor: '#0d6f72' },
    '.cm-gutters': {
      backgroundColor: '#f0ede4',
      borderRight: '1px solid #d5cbb2',
      color: '#8a8070',
    },
    '.cm-activeLineGutter': { backgroundColor: '#e8e4da' },
    '.cm-activeLine': { backgroundColor: 'rgba(13,111,114,0.05)' },
    '.cm-selectionBackground, ::selection': {
      backgroundColor: 'rgba(13,111,114,0.18) !important',
    },
    '.cm-focused .cm-selectionBackground': {
      backgroundColor: 'rgba(13,111,114,0.22) !important',
    },
    '&.cm-focused': { outline: 'none' },
    '.cm-scroller': { overflow: 'auto', height: '100%' },
  });

  // Setup — runs once. untrack(value) avoids re-creating editor on every keystroke.
  $effect(() => {
    const el = container;
    const initial = untrack(() => value);
    const view = new EditorView({
      state: EditorState.create({
        doc: initial,
        extensions: [
          basicSetup,
          StreamLanguage.define(verilog),
          warmTheme,
          EditorView.updateListener.of(u => {
            if (u.docChanged) onchange(u.state.doc.toString());
          }),
        ],
      }),
      parent: el,
    });
    el._cmView = view;
    return () => {
      el._cmView = null;
      view.destroy();
    };
  });

  // Sync — pushes external value changes (file switch, solve/reset) into editor.
  $effect(() => {
    const v = container?._cmView;
    if (!v) return;
    const current = v.state.doc.toString();
    if (current !== value) {
      v.dispatch({ changes: { from: 0, to: current.length, insert: value } });
    }
  });
</script>

<div bind:this={container} class="w-full h-full overflow-hidden"></div>
