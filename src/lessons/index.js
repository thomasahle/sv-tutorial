// Auto-discovered lesson content — no per-lesson index.js needed.
// To add a lesson: create src/lessons/<part>/<slug>/ with meta.json,
// description.html, *.sv (starter), *.sol.sv (solution), then add the
// slug to the structure below.

const htmls     = import.meta.glob('./*/*/description.html',                              { query: '?raw', import: 'default', eager: true });
const starters  = import.meta.glob(['./*/*/*.{sv,py}', '!./*/*/*.sol.sv'],               { query: '?raw', import: 'default', eager: true });
const solutions = import.meta.glob('./*/*/*.sol.sv',                                      { query: '?raw', import: 'default', eager: true });
const metas     = import.meta.glob('./*/*/meta.json',                      { eager: true,   import: 'default' });
const images    = import.meta.glob('./*/*/*.{png,jpg,jpeg,gif,svg,webp}',  { query: '?url', import: 'default', eager: true });

function buildLessonMap() {
  const map = {};
  const entry = (slug) => { map[slug] ??= { files: { a: {}, b: {} } }; return map[slug]; };

  // Build per-lesson image URL map (Vite-processed paths, base-URL-aware)
  const imageMap = {};
  for (const [path, url] of Object.entries(images)) {
    const m = path.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+)$/);
    if (m) {
      const [, p, l, file] = m;
      imageMap[`${p}/${l}`] ??= {};
      imageMap[`${p}/${l}`][file] = url;
    }
  }

  for (const [path, html] of Object.entries(htmls)) {
    const [, p, l] = path.match(/^\.\/([\w-]+)\/([\w-]+)\//);
    const slug = `${p}/${l}`;
    const imgs = imageMap[slug];
    // Rewrite relative image src attributes to Vite-resolved URLs
    entry(slug).html = imgs
      ? html.replace(/src="([^"]+)"/g, (match, filename) => imgs[filename] ? `src="${imgs[filename]}"` : match)
      : html;
  }

  for (const [path, meta] of Object.entries(metas)) {
    const [, p, l] = path.match(/^\.\/([\w-]+)\/([\w-]+)\//);
    const slug = `${p}/${l}`;
    Object.assign(entry(slug), { slug, ...meta });
  }

  for (const [path, content] of Object.entries(starters)) {
    const [, p, l, file] = path.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+\.(sv|py))$/);
    entry(`${p}/${l}`).files.a[`/src/${file}`] = content;
  }

  for (const [path, content] of Object.entries(solutions)) {
    const [, p, l, stem] = path.match(/^\.\/([\w-]+)\/([\w-]+)\/(.+)\.sol\.sv$/);
    entry(`${p}/${l}`).files.b[`/src/${stem}.sv`] = content;
  }

  return map;
}

const lessonMap = buildLessonMap();
const L = (slug) => lessonMap[slug];

// ── Hierarchy ─────────────────────────────────────────────────────────────────
export const parts = [
  {
    title: 'SystemVerilog Basics',
    chapters: [
      { title: 'Introduction',          lessons: [L('sv/welcome'), L('sv/modules-and-ports')] },
      { title: 'Combinational Logic',   lessons: [L('sv/always-comb'), L('sv/priority-enc')] },
      { title: 'Sequential Logic',      lessons: [L('sv/always-ff'), L('sv/counter')] },
      { title: 'Parameterized Modules', lessons: [L('sv/parameters')] },
      { title: 'Interfaces & Procedures', lessons: [L('sv/interfaces'), L('sv/tasks-functions')] },
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
      { title: 'Stimulus',        lessons: [L('uvm/sequence'), L('uvm/driver')] },
      { title: 'Checking',        lessons: [L('uvm/monitor'), L('uvm/env')] },
      {
        title: 'Functional Coverage',
        lessons: [L('uvm/covergroup'), L('uvm/cross-coverage'), L('uvm/coverage-driven')],
      },
    ],
  },
  {
    title: 'cocotb',
    chapters: [
      { title: 'cocotb Basics', lessons: [L('cocotb/first-test'), L('cocotb/clock-and-timing')] },
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
