// Auto-discovered lesson content — no per-lesson index.js needed.
// To add a lesson: create src/lessons/<part>/<slug>/ with meta.json,
// description.html, *.sv (starter), *.sol.sv (solution), then add the
// slug to the structure below.

// All lesson metadata in a single import — no glob needed.
// Content files (description.html, .sv, images) stay co-located in each
// lesson directory and are loaded lazily on demand via loadLessonContent().
import metas from './meta.js';

// Lazy content loaders — Vite transforms these only when first requested.
const htmlLoaders     = import.meta.glob('./*/*/description.html',                              { query: '?raw', import: 'default' });
const starterLoaders  = import.meta.glob(['./*/*/*.{sv,py,mlir}', '!./*/*/*.sol.sv'],           { query: '?raw', import: 'default' });
const solutionLoaders = import.meta.glob('./*/*/*.sol.sv',                                      { query: '?raw', import: 'default' });
const imageLoaders    = import.meta.glob('./*/*/*.{png,jpg,jpeg,gif,svg,webp}',                 { query: '?url', import: 'default' });

function buildMetaMap() {
  const map = {};
  for (const [slug, meta] of Object.entries(metas)) {
    map[slug] = { slug, ...meta };
  }
  return map;
}

/**
 * Load the full content for a single lesson on demand.
 * Returns { html, files: { a, b } }.
 * Called by the lesson route's load() function, and can also be called
 * from an "offline download" feature to prefetch all lessons at once.
 */
export async function loadLessonContent(slug) {
  const [p, l] = slug.split('/');
  const prefix = `./${p}/${l}/`;

  const htmlEntry       = Object.entries(htmlLoaders).find(([k]) => k.startsWith(prefix));
  const starterEntries  = Object.entries(starterLoaders).filter(([k]) => k.startsWith(prefix));
  const solutionEntries = Object.entries(solutionLoaders).filter(([k]) => k.startsWith(prefix));
  const imageEntries    = Object.entries(imageLoaders).filter(([k]) => k.startsWith(prefix));

  const [html, ...rest] = await Promise.all([
    htmlEntry ? htmlEntry[1]() : Promise.resolve(''),
    ...starterEntries.map(([k, fn])  => fn().then(content => ({ k, content, type: 'starter' }))),
    ...solutionEntries.map(([k, fn]) => fn().then(content => ({ k, content, type: 'solution' }))),
    ...imageEntries.map(([k, fn])    => fn().then(url     => ({ k, url,     type: 'image' }))),
  ]);

  const files = { a: {}, b: {} };
  const imageMap = {};

  for (const item of rest) {
    if (item.type === 'starter') {
      const m = item.k.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+\.(sv|py|mlir))$/);
      if (m) files.a[`/src/${m[3]}`] = item.content;
    } else if (item.type === 'solution') {
      const m = item.k.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+)\.sol\.sv$/);
      if (m) files.b[`/src/${m[3]}.sv`] = item.content;
    } else if (item.type === 'image') {
      const m = item.k.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+)$/);
      if (m) imageMap[m[3]] = item.url;
    }
  }

  // Rewrite relative image src attributes to Vite-resolved URLs
  const finalHtml = Object.keys(imageMap).length > 0
    ? html.replace(/src="([^"]+)"/g, (match, filename) => imageMap[filename] ? `src="${imageMap[filename]}"` : match)
    : html;

  return { html: finalHtml, files };
}

const metaMap = buildMetaMap();
const L = (slug) => metaMap[slug];

// ── Hierarchy ─────────────────────────────────────────────────────────────────
export const parts = [
  {
    title: 'SystemVerilog Basics',
    chapters: [
      { title: 'Introduction',          lessons: [L('sv/welcome'), L('sv/modules-and-ports'), L('sv/data-types'), L('sv/always-comb')] },
      { title: 'Sequential Logic',      lessons: [L('sv/events'), L('sv/always-ff'), L('sv/counter')] },
      { title: 'Data Types',            lessons: [L('sv/parameters'), L('sv/packed-structs')] },
      { title: 'Interfaces & Procedures', lessons: [L('sv/interfaces'), L('sv/modports'), L('sv/tasks-functions')] },
      { title: 'State Machines',        lessons: [L('sv/enums'), L('sv/fsm')] },
      { title: 'Covergroups',            lessons: [L('sv/covergroup-basics'), L('sv/coverpoint-bins'), L('sv/cross-coverage')] },
    ],
  },
  {
    title: 'SystemVerilog Assertions',
    chapters: [
      { title: 'Runtime Assertions',          lessons: [L('sva/concurrent-sim'), L('sva/vacuous-pass'), L('sva/isunknown')] },
      { title: 'Your First Formal Assertion', lessons: [L('sva/immediate-assert'), L('sva/sequence-basics')] },
      { title: 'Implication & BMC',         lessons: [L('sva/implication'), L('sva/formal-intro')] },
      { title: 'Core Sequences',            lessons: [L('sva/clock-delay'), L('sva/rose-fell'), L('sva/req-ack')] },
      { title: 'Repetition Operators',      lessons: [L('sva/consecutive-rep'), L('sva/nonconsec-rep'), L('sva/nonconsec-eq')] },
      { title: 'Sequence Operators',        lessons: [L('sva/throughout'), L('sva/sequence-ops')] },
      { title: 'Sampled Value Functions',   lessons: [L('sva/stable-past'), L('sva/changed')] },
      { title: 'Protocols & Coverage',      lessons: [L('sva/disable-iff'), L('sva/abort'), L('sva/cover-property')] },
      { title: 'Advanced Properties',       lessons: [L('sva/local-vars'), L('sva/onehot'), L('sva/triggered'), L('sva/checker'), L('sva/recursive')] },
      { title: 'Formal Verification',       lessons: [L('sva/formal-assume'), L('sva/always-eventually'), L('sva/until'), L('sva/lec')] },
    ],
  },
  {
    title: 'Universal Verification Methodology',
    chapters: [
      { title: 'UVM Foundations', lessons: [L('uvm/reporting'), L('uvm/seq-item')] },
      { title: 'Stimulus',        lessons: [L('uvm/sequence'), L('uvm/driver'), L('uvm/constrained-random')] },
      { title: 'Checking',        lessons: [L('uvm/monitor'), L('uvm/env')] },
      {
        title: 'Functional Coverage',
        lessons: [L('uvm/covergroup'), L('uvm/cross-coverage'), L('uvm/coverage-driven')],
      },
      { title: 'Advanced UVM',    lessons: [L('uvm/factory-override')] },
    ],
  },
  {
    title: 'cocotb',
    chapters: [
      { title: 'cocotb Basics', lessons: [L('cocotb/first-test'), L('cocotb/clock-and-timing')] },
      { title: 'Triggers & Clocks', lessons: [L('cocotb/edge-triggers'), L('cocotb/clockcycles-patterns')] },
    ],
  },
  {
    title: 'MLIR & CIRCT',
    chapters: [
      {
        title: 'Inside the Compiler',
        lessons: [L('mlir/intro'), L('mlir/comb'), L('mlir/seq'), L('mlir/lowering')],
      },
    ],
  },
];

export const lessons = parts.flatMap((part) =>
  part.chapters.flatMap((chapter) =>
    chapter.lessons.map((lesson) => ({
      ...lesson,
      partTitle: part.title,
      chapterTitle: chapter.title,
    }))
  )
);
