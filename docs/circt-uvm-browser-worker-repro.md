# Browser-Worker UVM Repro (`Malformed attribute storage object`)

This reproduces the CIRCT wasm UVM failure in the **browser worker** path
without using lesson UI clicks.

## Preconditions

1. `vendor/circt` is checked out and wasm artifacts are built.
2. Artifacts are synced into `public/circt`:

```bash
scripts/setup-circt.sh
npm run sync:circt
```

## Repro command

```bash
node scripts/repro-uvm-browser-worker-assert.mjs
```

## What it does

- starts Vite dev server on `http://127.0.0.1:4173` (`--strictPort`)
- opens Chromium headless via Playwright
- imports `createCirctWasmAdapter` from `/src/runtime/circt-adapter.js`
- runs compile-only (`simulate: false`) on minimal UVM files:
  - `/src/my_test.sv`
  - `/src/tb_top.sv`
- uses full UVM path (`--uvm-path /circt/uvm-core -I /circt/uvm-core/src`)

## Expected failure signature

- run result `ok=false`
- logs include both:
  - `Aborted(`
  - `Malformed attribute storage object`
- logs do **not** reach `$ circt-sim`

If this signature appears, the script exits `0` and prints:

`REPRODUCED: browser-worker UVM compile hit malformed-attribute abort`

If not, it exits non-zero.
