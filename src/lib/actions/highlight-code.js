import { highlightTree, tags } from '@lezer/highlight';
import { StreamLanguage } from '@codemirror/language';
import { verilog } from '@codemirror/legacy-modes/mode/verilog';
import { python } from '@codemirror/legacy-modes/mode/python';

const svLang  = StreamLanguage.define(verilog);
const pyLang  = StreamLanguage.define(python);
const defVar  = tags.definition(tags.variableName);

// Each entry: [Tag, CSS-variable string used as inline style]
const TAG_STYLES = [
  [tags.keyword,    'var(--syn-keyword)'],
  [tags.comment,    'var(--syn-comment)'],
  [tags.string,     'var(--syn-string)'],
  [tags.number,     'var(--syn-number)'],
  [tags.meta,       'var(--syn-meta)'],
  [defVar,          'var(--syn-def)'],
];

const highlighter = {
  style(ts) {
    for (const [tag, color] of TAG_STYLES) {
      if (ts.includes(tag)) {
        // Comments get italic too
        const extra = (tag === tags.comment) ? ';font-style:italic' : '';
        return `color:${color}${extra}`;
      }
    }
    return null;
  },
};

function esc(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function applyTo(el) {
  // Detect language from class, default to SystemVerilog
  const lang = el.classList.contains('language-python') ? pyLang : svLang;
  const code = el.textContent;
  const tree = lang.parser.parse(code);

  let html = '';
  let pos = 0;
  highlightTree(tree, highlighter, (from, to, style) => {
    if (from > pos) html += esc(code.slice(pos, from));
    html += `<span style="${style}">${esc(code.slice(from, to))}</span>`;
    pos = to;
  });
  if (pos < code.length) html += esc(code.slice(pos));
  el.innerHTML = html;
}

export function highlightCode(node, _trigger) {
  function apply() {
    node.querySelectorAll('pre code').forEach(applyTo);
  }
  apply();
  return {
    update() { apply(); },
  };
}
