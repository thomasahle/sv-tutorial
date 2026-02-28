/**
 * Integration tests that load and run the real CIRCT WASM artifacts via Node.js.
 * These tests require `static/circt/` to be populated (run `npm run sync:circt` first).
 *
 * circt-verilog.js uses NODERAWFS (real filesystem in Node.js), so we use a real
 * temp directory as the workspace. circt-sim.js is patched to use MEMFS, so it
 * works with any virtual path.
 */
import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import vm from 'node:vm';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const CIRCT_DIR = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '../../static/circt'
);

const artifactsPresent = fs.existsSync(path.join(CIRCT_DIR, 'circt-verilog.js'));

/**
 * Load a CIRCT WASM tool into an isolated vm context.
 * Returns an object with `invoke(inputFiles, args)` that resets output capture per call.
 */
async function loadTool(toolName, { initTimeout = 45_000 } = {}) {
  const jsPath = path.join(CIRCT_DIR, `${toolName}.js`);
  if (!fs.existsSync(jsPath)) {
    throw new Error(`WASM artifact not found: ${jsPath}\nRun: npm run sync:circt`);
  }
  const source = fs.readFileSync(jsPath, 'utf8');

  // Mutable capture target — reset before each callMain invocation.
  const capture = { out: '', err: '' };

  // Custom require that intercepts `require('fs')` to capture fd=1/2 writes.
  // circt-verilog uses NODERAWFS which calls fs.writeSync(1, ...) for stdout,
  // bypassing Emscripten's `out` function and Module.print entirely.
  const realRequire = createRequire(jsPath);
  const patchedFsRequire = (id) => {
    const mod = realRequire(id);
    if (id !== 'fs') return mod;
    return new Proxy(mod, {
      get(target, prop, receiver) {
        if (prop === 'writeSync') {
          return (fd, buf, off, len, _pos) => {
            const n = typeof len === 'number' ? len : (buf.byteLength ?? buf.length);
            const o = typeof off === 'number' ? off : 0;
            if (fd === 1 || fd === 2) {
              // `buf` may be a cross-realm Uint8Array (vm sandbox); instanceof checks
              // fail across realms, so read via the underlying ArrayBuffer instead.
              const text = buf && buf.buffer
                ? Buffer.from(buf.buffer, (buf.byteOffset ?? 0) + o, n).toString('utf8')
                : Buffer.from(typeof buf === 'string' ? buf : String(buf), 'utf8').toString('utf8');
              if (fd === 1) capture.out += text;
              else capture.err += text;
              return n;
            }
            return target.writeSync(fd, buf, off, len, _pos);
          };
        }
        const val = Reflect.get(target, prop, receiver);
        return typeof val === 'function' ? val.bind(target) : val;
      },
    });
  };

  const context = {
    require: patchedFsRequire,
    process,
    console,
    Buffer,
    URL,
    WebAssembly,
    TextDecoder,
    TextEncoder,
    setTimeout,
    clearTimeout,
    setInterval,
    clearInterval,
    performance,
    __dirname: CIRCT_DIR,
    __filename: jsPath,
  };
  context.globalThis = context;
  context.self = context;
  // Set Module.print / Module.printErr BEFORE running the module so that
  // Emscripten's `out` / `err` variables are bound to our capture functions
  // instead of console.log / console.error.
  context.Module = {
    noInitialRun: true,
    locateFile: (f) => path.join(CIRCT_DIR, f),
    print:    (s) => { capture.out += s + '\n'; },
    printErr: (s) => { capture.err += s + '\n'; },
  };

  vm.runInNewContext(source, context);

  await waitForReady(context, initTimeout);

  // FS may live as Module.FS or as a bare context global.
  const getFS = () => context.Module.FS ?? context.FS;

  return {
    _context: context,

    invoke(inputFiles = {}, args = []) {
      capture.out = '';
      capture.err = '';

      const FS = getFS();
      for (const [p, content] of Object.entries(inputFiles)) {
        const dir = p.slice(0, p.lastIndexOf('/') || 1);
        try { FS.mkdirTree(dir); } catch {}
        FS.writeFile(p, content, { encoding: 'utf8' });
      }

      const callMain = context.Module.callMain ?? context.__svt_callMain;
      let exitCode = 0;
      try {
        exitCode = callMain(args) ?? 0;
      } catch (e) {
        exitCode = e?.status ?? 1;
      }

      return { exitCode, stdout: capture.out, stderr: capture.err };
    },

    readFile(p) {
      return getFS().readFile(p, { encoding: 'utf8' });
    },
  };
}

function waitForReady(context, ms) {
  return new Promise((resolve, reject) => {
    const start = Date.now();
    const tick = () => {
      const mod = context.Module;
      const hasCallMain =
        typeof mod.callMain === 'function' ||
        typeof context.__svt_callMain === 'function';
      if (hasCallMain && mod.calledRun) return resolve();
      if (Date.now() - start > ms) return reject(new Error(`WASM init timeout after ${ms}ms`));
      setTimeout(tick, 50);
    };
    tick();
  });
}

// ---------------------------------------------------------------------------

describe.skipIf(!artifactsPresent)('CIRCT WASM smoke tests', { timeout: 90_000 }, () => {
  let verilog;
  let sim;
  // Real temp directory — required because circt-verilog uses NODERAWFS (real fs).
  let WORK;

  beforeAll(async () => {
    WORK = fs.mkdtempSync(path.join(os.tmpdir(), 'circt-smoke-'));
    [verilog, sim] = await Promise.all([
      loadTool('circt-verilog'),
      loadTool('circt-sim'),
    ]);
  }, 60_000);

  afterAll(() => {
    fs.rmSync(WORK, { recursive: true, force: true });
  });

  // -- circt-verilog --

  it('circt-verilog --version exits 0', () => {
    const { exitCode, stdout, stderr } = verilog.invoke({}, ['--version']);
    expect(exitCode).toBe(0);
    expect(stdout + stderr).toMatch(/circt|CIRCT/i);
  });

  it('circt-verilog compiles a simple combinational module', () => {
    const sv = `
module top (input logic a, b, output logic y);
  assign y = a & b;
endmodule
`;
    const inputPath = `${WORK}/top.sv`;
    const outputPath = `${WORK}/top.mlir`;
    const { exitCode } = verilog.invoke(
      { [inputPath]: sv },
      ['-o', outputPath, inputPath],
    );
    expect(exitCode).toBe(0);
    const mlir = verilog.readFile(outputPath);
    expect(mlir).toContain('hw.module @top');
  });

  // -- circt-sim --

  it('circt-sim --version exits 0', () => {
    const { exitCode, stdout, stderr } = sim.invoke({}, ['--version']);
    expect(exitCode).toBe(0);
    expect(stdout + stderr).toMatch(/circt|CIRCT/i);
  });

  it('circt-sim simulates a minimal testbench end-to-end', () => {
    const sv = `
module tb;
  initial begin
    $display("circt-sim-ok");
    $finish;
  end
endmodule
`;
    // Compile SV → MLIR via circt-verilog (NODERAWFS → real filesystem)
    const svPath   = `${WORK}/tb.sv`;
    const mlirPath = `${WORK}/tb.mlir`;
    const { exitCode: compileExit } = verilog.invoke(
      { [svPath]: sv },
      ['-o', mlirPath, svPath],
    );
    expect(compileExit).toBe(0);
    const mlir = verilog.readFile(mlirPath);

    // Simulate MLIR via circt-sim (MEMFS — NODERAWFS was patched out)
    const { exitCode, stdout, stderr } = sim.invoke(
      { '/workspace/tb.mlir': mlir },
      ['--top', 'tb', '/workspace/tb.mlir'],
    );
    expect(exitCode).toBe(0);
    expect(stdout + stderr).toContain('circt-sim-ok');
  });
});
