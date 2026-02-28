# Bug: circt-sim does not reset global simulation state between `callMain` invocations

## Summary

When `circt-sim` is built as an Emscripten WASM module and `Module.callMain` is called more
than once in the same process/JS context, simulation state (signal tables, memory arrays,
scheduler queues, etc.) from the first invocation persists into subsequent ones. This produces
wrong simulation results and can cause assertion crashes in later runs.

## Reproduction

This is most easily observed when driving circt-sim from JavaScript/Node.js via its WASM build.

```js
// Minimal reproduction in Node.js
const sim = await loadEmscriptenModule('circt-sim.js');

// Run simulation A (writes value 0xBEEF to a register)
sim.invoke({ '/workspace/a.mlir': mlirA }, ['--top', 'tb', '/workspace/a.mlir']);

// Run simulation B — completely unrelated testbench
// Expected: clean initial state for B
// Actual:   stale signal values / memory from A may appear in B's simulation
sim.invoke({ '/workspace/b.mlir': mlirB }, ['--top', 'tb', '/workspace/b.mlir']);
```

### Concrete example observed during lesson regression testing

Running 11 SystemVerilog lessons in sequence with a single circt-sim instance:

1. Lessons 1–4 (always-comb, always-ff, counter, enums) pass correctly.
2. Lesson 5 (fsm) — the FSM lesson's testbench reads `rdata` after writing; it receives 0
   instead of the written value. The lesson passes when run in isolation.
3. Lesson 6 (interfaces) — an `APInt::extractBits: bitPosition < BitWidth` assertion fires
   inside `circt-sim`, crashing the simulation. This lesson also passes in isolation.

Running each lesson with a **freshly loaded** circt-sim instance (re-calling
`loadEmscriptenModule` per lesson, benefiting from V8's WASM binary cache for speed) produces
correct results for all lessons.

## Root cause hypothesis

Emscripten global C++ objects (static storage duration) used by the LLHD interpreter are not
re-initialized between `callMain` calls. Likely candidates:

- Signal value tables / process state (`Simulator`, `State`, signal vectors)
- Memory allocated in the bump/region allocator tied to the module under simulation
- Event queue / time-step scheduler

`callMain` re-enters `main()`, but static/global C++ objects initialized before `main()`, or
mutated during simulation and not explicitly reset, retain their values.

## Impact

- Any test harness that drives multiple simulations through one circt-sim WASM instance will
  silently produce wrong results or crash.
- The bug is invisible when running a single simulation per process (the normal CLI use case),
  so it only manifests in embedding scenarios (Node.js test runners, browser-based playgrounds).

## Suggested fix

Options in rough order of invasiveness:

1. **Re-initialize all relevant globals at the top of `main()`** — identify every global/static
   that carries simulation state and explicitly reset it before each run.
2. **Expose a `circt_sim_reset()` C function** that the embedder can call between invocations.
3. **Document that `callMain` is not re-entrant / not idempotent** and recommend spawning a
   fresh Worker or process per simulation. (Workaround, not a fix.)

## Workaround (embedder side)

Reload the entire WASM module before each simulation. In Node.js with V8, the compiled WASM
binary is cached by content hash, so repeated loads of the same `.wasm` file are fast (~1–3 s
per load on a 2023 MacBook Pro) after the first cold load (~30 s).

```js
// Load a fresh instance per simulation to avoid stale state
for (const lesson of lessons) {
  const sim = await loadEmscriptenModule('circt-sim.js');  // V8 caches the .wasm
  sim.invoke(...);
}
```

## Version

Tested with circt-sim WASM build from CIRCT commit `3f4e18c4b` (LLVM `aa3d6b37c`).
