# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
npm install          # Install dependencies
npm run dev          # Start dev server (Vite)
npm run build        # Production build
npm run preview      # Preview production build

scripts/setup-circt.sh          # Clone/update the CIRCT fork into vendor/circt
scripts/setup-circt.sh <dir>    # Clone into a custom directory

scripts/setup-surfer.sh         # Download Surfer waveform viewer web build into public/surfer
scripts/setup-surfer.sh <dir>   # Download into a custom directory
```

There are no tests in this project.

## Architecture

This is a Svelte 5 + Vite single-page app. The entry point is `src/main.js` → `src/App.svelte`.

### Lesson Data (`src/tutorial-data.js`)

Lessons are defined in a `parts → chapters → lessons` hierarchy and exported as a flat `lessons` array. Each lesson has:
- `files.a`: starter files (keyed by virtual path like `/src/top.sv`)
- `files.b`: solution delta (merged onto `a` to produce the solution)
- `focus`: the default file to show in the editor
- `waveform`: `'off'` | `'optional'` | `'required'` — controls waveform pane visibility
- `html`: inline HTML string for the lesson description

### App State (`src/App.svelte`)

All state lives in the single root component. Key derived values:
- `solutionFiles = merge(starterFiles, lesson.files.b)`
- `completed = filesEqual(workspace, solutionFiles)` — drives the "solve"/"reset" toggle
- Lesson navigation mutates `lessonIndex`; reactive blocks reset `workspace`, `logs`, and `lastWaveform` on lesson change

### CIRCT WASM Runtime (`src/runtime/`)

Two files handle the runtime bridge:

**`circt-config.js`** — reads Vite env vars and resolves runtime configuration:
- `VITE_CIRCT_WASM_JS_URL` / `VITE_CIRCT_WASM_JS_URLS` — JS artifact URL(s) (comma-separated for fallback)
- `VITE_CIRCT_WASM_URL` / `VITE_CIRCT_WASM_URLS` — WASM artifact URL(s)
- `VITE_CIRCT_FACTORY_NAME` — optional Emscripten factory function name
- `VITE_CIRCT_TOOL_ARGS` — args for `run` (JSON array preferred, space-split fallback)
- `VITE_CIRCT_SELF_CHECK_ARGS` — args for the self-check smoke test
- Default JS candidates: `/circt/circt.js`, `/circt/circt-bmc.js`
- Default WASM candidates: `/circt/circt.wasm`, `/circt/circt-bmc.wasm`

**`circt-adapter.js`** — `CirctWasmAdapter` class, lazy-initialized on first `run()` or `selfCheck()`:
- Tries each JS candidate URL in order until one loads successfully
- Detects runtime mode automatically:
  - **`custom-runtime`**: `window.CIRCT_WASM_RUNTIME` global exposes `{ init, run, selfCheck? }`
  - **`emscripten-module`**: raw Emscripten output; looks for factory functions (`createCirctBmcModule`, `createModule`, `Module`) then falls back to `window.Module`
- In Emscripten mode, files are written into the module's virtual FS under `/workspace/`, and output waveform is read back from `/workspace/out/waves.vcd`
- Arg templates support `{top}`, `{input}`, `{waveform}` placeholders

### CIRCT WASM Artifacts

Place built artifacts from the CIRCT fork (`git@github.com:thomasnormal/circt.git`) at:
- `public/circt/circt-bmc.js` + `public/circt/circt-bmc.wasm`
- or custom shim: `public/circt/circt.js` + `public/circt/circt.wasm`

Without these files, the runtime will fail gracefully with a log message directing you to run `scripts/setup-circt.sh`.

### Surfer Waveform Viewer (`src/lib/components/WaveformViewer.svelte`)

The waveform pane embeds [Surfer](https://surfer-project.org/) via an `<iframe src="/surfer/">`.

- Surfer must be self-hosted (same origin) so that blob URLs created from in-memory VCD data are fetchable by the iframe.
- When CIRCT produces a VCD string (`lastWaveform.text`), the component creates a `Blob` → `URL.createObjectURL` and sends `{ command: 'LoadUrl', url }` via `postMessage` with progressive retries (0 / 800 / 2200 / 4500 ms) to absorb Surfer's WASM initialization time.
- If `/surfer/index.html` is not found (HEAD 404), the component shows a prompt to run `scripts/setup-surfer.sh`.

Install artifacts:
```bash
scripts/setup-surfer.sh    # downloads from GitLab CI → public/surfer/
```

Copy `.env.example` to `.env` to configure runtime overrides without modifying source.
