# sv-tutorial

Svelte-based interactive tutorial shell for SystemVerilog, SVA, and UVM.

## CIRCT Fork

This project is pinned to the CIRCT fork with wasm support:

- `git@github.com:thomasnormal/circt.git`

## Scripts

- `npm install`
- `npm run dev`
- `npm run build`
- `npm run preview`
- `scripts/setup-circt.sh` (clone/update the CIRCT fork checkout)

## CIRCT WASM Runtime Setup

1. Clone/update the fork checkout:
   - `scripts/setup-circt.sh`
2. Build wasm artifacts from that checkout.
3. Copy artifacts into this app:
   - `cp vendor/circt/build-wasm/bin/circt-verilog.js public/circt/circt-verilog.js`
   - `cp vendor/circt/build-wasm/bin/circt-verilog.wasm public/circt/circt-verilog.wasm`
   - `cp vendor/circt/build-wasm/bin/circt-sim.js public/circt/circt-sim.js`
   - `cp vendor/circt/build-wasm/bin/circt-sim.wasm public/circt/circt-sim.wasm`
   - `cp vendor/circt/build-wasm/bin/circt-bmc.js public/circt/circt-bmc.js`
   - `cp vendor/circt/build-wasm/bin/circt-bmc.wasm public/circt/circt-bmc.wasm`
4. Runtime artifact lookup order:
   - `public/circt/circt-verilog.js`
   - `public/circt/circt-verilog.wasm`
   - `public/circt/circt-sim.js`
   - `public/circt/circt-sim.wasm`
   - `public/circt/circt-bmc.js`
   - `public/circt/circt-bmc.wasm`
5. Optional mock shim (explicit opt-in only):
   - `public/circt/circt.js`
   - `public/circt/circt.wasm`
   - not used by default runtime
6. Optional URL overrides in `.env`:
   - `VITE_CIRCT_VERILOG_JS_URL`
   - `VITE_CIRCT_VERILOG_WASM_URL`
   - `VITE_CIRCT_SIM_JS_URL`
   - `VITE_CIRCT_SIM_WASM_URL`
   - `VITE_CIRCT_BMC_JS_URL`
   - `VITE_CIRCT_BMC_WASM_URL`
   - `VITE_CIRCT_VERILOG_ARGS`
   - `VITE_CIRCT_SIM_ARGS`
   - `VITE_CIRCT_BMC_ARGS`

## Notes

- This repo currently includes a starter tutorial UI and lesson data model.
- Runtime uses a real 2-stage wasm toolchain by default:
  - `circt-verilog` lowers SV/SVA/UVM source to MLIR
  - `circt-sim` executes lowered MLIR and emits VCD for the waveform pane
- Tool invocations run in isolated Web Workers to avoid global Emscripten symbol collisions and re-entry issues.
- The UI includes a `self-check` action in the Runtime panel to validate artifact compatibility.
- Waveform pane is metadata-driven (`off`, `optional`, `required`) and prepared for Surfer integration.
