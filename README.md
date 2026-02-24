# sv-tutorial

Svelte-based interactive tutorial shell for SystemVerilog, SVA, and UVM.

## Reproducible Requirements

Pinned versions are centralized in `scripts/toolchain.lock.sh`:

- Node major: `22`
- Emscripten (emsdk): `4.0.21`
- CIRCT repo: `https://github.com/thomasnormal/circt.git`
- CIRCT ref: `8e8ca87dcda1c8abd47103ae7789c8ed261d5de3`
- LLVM submodule ref: `972cd847efb20661ea7ee8982dd19730aa040c75`

Host tools:

- `git`
- `node`/`npm` (Node 22.x)
- `cmake` (>= 3.24)
- `ninja` (>= 1.10)
- `python3` (>= 3.10)
- `rsync`
- `unzip`

Check prerequisites:

- `npm run check:req` (frontend/tooling only)
- `npm run check:req:wasm` (includes emsdk/emcc verification)

## Reproducible Local Build

1. Activate emsdk `4.0.21` (or ensure `emcc -v` reports `4.0.21`).
2. Run the one-shot bootstrap:
   - `npm run bootstrap:repro`

Equivalent step-by-step:

1. `npm ci`
2. `scripts/setup-surfer.sh`
3. `npm run setup:circt`
4. `npm run build:circt`
5. `npm run sync:circt`
6. `npm run build`

The CIRCT wasm build script enforces conservative resource limits by default:

- Ninja parallelism: `CIRCT_WASM_JOBS=4`
- Configure timeout: `CIRCT_WASM_CONFIGURE_TIMEOUT_MIN=30`
- Build timeout: `CIRCT_WASM_BUILD_TIMEOUT_MIN=120`
- Force clean build dir first: `CIRCT_WASM_CLEAN_BUILD=1`
- Build targets override: `CIRCT_WASM_TARGETS="circt-verilog circt-sim circt-bmc"`
- Optional virtual memory cap: `CIRCT_WASM_MEMORY_LIMIT_KB=<kb>`

To also build `circt-sim-vpi` (required for cocotb lessons):

```
CIRCT_WASM_TARGETS="circt-verilog circt-sim circt-bmc circt-sim-vpi" npm run build:circt
```

## Scripts

- `npm run dev`
- `npm run preview`
- `npm run test:e2e`
- `npm run setup:circt`
- `npm run build:circt`
- `npm run sync:circt`
- `npm run bootstrap:repro`

## Optional Runtime Overrides

In `.env` (copy `.env.example`):

- `VITE_CIRCT_VERILOG_JS_URL`
- `VITE_CIRCT_VERILOG_WASM_URL`
- `VITE_CIRCT_SIM_JS_URL`
- `VITE_CIRCT_SIM_WASM_URL`
- `VITE_CIRCT_BMC_JS_URL`
- `VITE_CIRCT_BMC_WASM_URL`
- `VITE_CIRCT_SIM_VPI_JS_URL` (cocotb lessons)
- `VITE_CIRCT_SIM_VPI_WASM_URL` (cocotb lessons)
- `VITE_PYODIDE_URL` (cocotb lessons, default: jsdelivr CDN)
- `VITE_CIRCT_VERILOG_ARGS`
- `VITE_CIRCT_SIM_ARGS`
- `VITE_CIRCT_BMC_ARGS`

## Runtime Notes

- Runtime uses a real 2-stage wasm toolchain by default:
  - `circt-verilog` lowers SV/SVA/UVM source to MLIR
  - `circt-sim` executes lowered MLIR and emits VCD for the waveform pane
- Tool invocations run in isolated Web Workers to avoid global Emscripten symbol collisions and re-entry issues.
- UI includes a `self-check` action in the Runtime panel to validate artifact compatibility.
- Waves tab appears automatically only when a valid VCD is generated.

## CI

- `.github/workflows/ci.yml` builds with pinned toolchain requirements:
  1. install Node 22
  2. install emsdk 4.0.21
  3. run `scripts/setup-circt.sh` (pinned CIRCT ref)
  4. run `scripts/build-circt-wasm.sh`
  5. run `npm run sync:circt`
  6. run `npm run build`

## E2E

- `npm run test:e2e -- e2e/waveform.spec.js`
- Includes:
  - non-mock pipeline check (`circt-verilog` + `circt-sim`, waveform generated)
  - Surfer waveform render check when browser WebGL support is available in the test environment
