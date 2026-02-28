#!/usr/bin/env node
/**
 * test-sv-lessons.mjs
 *
 * Compiles and simulates every SV lesson through the WASM circt tools, checking:
 *   • solution files (.sol.sv substituted for the corresponding .sv)
 *       → simulation output must contain a line starting with "PASS"
 *   • starter files (unmodified .sv, incomplete implementations)
 *       → simulation output must NOT contain such a line
 *
 * Requires static/circt/ to be populated (run `npm run sync:circt` first).
 *
 * Design notes:
 *   - circt-verilog is loaded once and reused (compilation is stateless).
 *   - circt-sim is reloaded for each lesson because callMain does not fully
 *     reset global simulation state between invocations. After the first load
 *     V8 caches the compiled WASM binary, so subsequent loads are fast (~1-3s).
 */

import vm from 'node:vm';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const REPO_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const CIRCT_DIR = path.join(REPO_ROOT, 'static/circt');
const LESSONS_DIR = path.join(REPO_ROOT, 'src/lessons/sv');

// ─── WASM tool loader ─────────────────────────────────────────────────────────

async function loadTool(toolName, { initTimeout = 60_000 } = {}) {
  const jsPath = path.join(CIRCT_DIR, `${toolName}.js`);
  if (!fs.existsSync(jsPath)) {
    throw new Error(`WASM artifact not found: ${jsPath}\nRun: npm run sync:circt`);
  }
  const source = fs.readFileSync(jsPath, 'utf8');
  const capture = { out: '', err: '' };

  // Intercept require('fs') so that NODERAWFS fd=1/2 writes are captured.
  // (circt-verilog.js uses NODERAWFS and calls fs.writeSync(1,...) for stdout.)
  const realRequire = createRequire(jsPath);
  const patchedRequire = (id) => {
    const mod = realRequire(id);
    if (id !== 'fs') return mod;
    return new Proxy(mod, {
      get(target, prop, receiver) {
        if (prop === 'writeSync') {
          return (fd, buf, off, len, _pos) => {
            const n = typeof len === 'number' ? len : (buf.byteLength ?? buf.length);
            const o = typeof off === 'number' ? off : 0;
            if (fd === 1 || fd === 2) {
              // buf may be a cross-realm Uint8Array — read via its ArrayBuffer.
              const text = buf && buf.buffer
                ? Buffer.from(buf.buffer, (buf.byteOffset ?? 0) + o, n).toString('utf8')
                : Buffer.from(typeof buf === 'string' ? buf : String(buf)).toString('utf8');
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
    require: patchedRequire,
    process, console, Buffer, URL, WebAssembly,
    TextDecoder, TextEncoder, setTimeout, clearTimeout,
    setInterval, clearInterval, performance,
    __dirname: CIRCT_DIR,
    __filename: jsPath,
  };
  context.globalThis = context;
  context.self = context;
  context.Module = {
    noInitialRun: true,
    locateFile: (f) => path.join(CIRCT_DIR, f),
    print:    (s) => { capture.out += s + '\n'; },
    printErr: (s) => { capture.err += s + '\n'; },
  };

  vm.runInNewContext(source, context);
  await waitForReady(context, initTimeout);

  const getFS = () => context.Module.FS ?? context.FS;

  return {
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
      try { exitCode = callMain(args) ?? 0; }
      catch (e) { exitCode = e?.status ?? 1; }
      return { exitCode, stdout: capture.out, stderr: capture.err };
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

// ─── lesson file helpers ──────────────────────────────────────────────────────

function getLessonNames() {
  return fs.readdirSync(LESSONS_DIR, { withFileTypes: true })
    .filter(d => d.isDirectory())
    .map(d => d.name)
    .sort();
}

function getLessonFiles(lessonDir) {
  const entries = fs.readdirSync(lessonDir).filter(f => f.endsWith('.sv'));
  return {
    starterFiles: entries.filter(f => !f.endsWith('.sol.sv')).map(f => path.join(lessonDir, f)),
    solFiles:     entries.filter(f =>  f.endsWith('.sol.sv')).map(f => path.join(lessonDir, f)),
  };
}

// For each starter .sv, use the matching .sol.sv if it exists, else the starter.
function buildSolutionFiles(starterFiles, lessonDir) {
  return starterFiles.map(f => {
    const sol = path.join(lessonDir, path.basename(f, '.sv') + '.sol.sv');
    return fs.existsSync(sol) ? sol : f;
  });
}

function hasPass(output) {
  return output.split('\n').some(line => line.startsWith('PASS'));
}

// ─── compile + simulate ───────────────────────────────────────────────────────

const VERILOG_FLAGS = ['--ir-llhd', '--timescale', '1ns/1ns', '--single-unit'];

// Compile sv files to an MLIR file on the real filesystem.
// Returns { ok, mlirPath, output } — mlirPath is set only when ok=true.
function compile(verilog, work, label, svFiles) {
  const mlirPath = path.join(work, `${label}.mlir`);
  const { exitCode, stdout, stderr } =
    verilog.invoke({}, [...VERILOG_FLAGS, '-o', mlirPath, ...svFiles]);
  if (exitCode !== 0) {
    return { ok: false, output: stdout + stderr };
  }
  return { ok: true, mlirPath, output: stdout + stderr };
}

// Simulate an MLIR file (read from real FS, written into sim's MEMFS).
function simulate(sim, mlirPath) {
  let mlir;
  try { mlir = fs.readFileSync(mlirPath, 'utf8'); }
  catch { return { ok: false, reason: 'MLIR output not written', output: '' }; }

  const { stdout, stderr } =
    sim.invoke({ '/workspace/sim.mlir': mlir }, ['--top', 'tb', '/workspace/sim.mlir']);
  return { ok: true, output: stdout + stderr };
}

// ─── main ─────────────────────────────────────────────────────────────────────

const G = '\x1b[32m', R = '\x1b[31m', D = '\x1b[2m', X = '\x1b[0m';

async function main() {
  const work = fs.mkdtempSync(path.join(os.tmpdir(), 'sv-lesson-test-'));
  try {
    await run(work);
  } finally {
    fs.rmSync(work, { recursive: true, force: true });
  }
}

async function run(work) {
  console.log(`\nLoading circt-verilog…`);
  const verilog = await loadTool('circt-verilog');
  console.log('Ready.\n');

  const lessons = getLessonNames();
  let pass = 0, fail = 0, skip = 0;
  const failures = [];

  for (const lesson of lessons) {
    const lessonDir = path.join(LESSONS_DIR, lesson);

    if (!fs.existsSync(path.join(lessonDir, 'tb.sv'))) {
      console.log(`  ${D}SKIP  ${lesson} (no testbench)${X}`);
      skip++;
      continue;
    }

    const { starterFiles, solFiles } = getLessonFiles(lessonDir);
    if (solFiles.length === 0) {
      console.log(`  ${D}SKIP  ${lesson} (no solution file)${X}`);
      skip++;
      continue;
    }

    process.stdout.write(`  ${lesson.padEnd(28)}`);

    // ── compile both variants ────────────────────────────────────────────────
    const solCompile   = compile(verilog, work, `${lesson}-sol`,   buildSolutionFiles(starterFiles, lessonDir));
    const startCompile = compile(verilog, work, `${lesson}-start`, starterFiles);

    // ── load a FRESH circt-sim for this lesson ───────────────────────────────
    // circt-sim doesn't reset all global state between callMain calls, so we
    // create a new instance per lesson. After the first load V8 caches the
    // compiled WASM binary and subsequent loads take ~1-3s.
    const sim = await loadTool('circt-sim');

    // ── solution ─────────────────────────────────────────────────────────────
    if (!solCompile.ok) {
      process.stdout.write(`  ${R}sol=COMPILE_ERROR${X}\n`);
      failures.push({ lesson, mode: 'solution', reason: 'compile error', output: solCompile.output });
      fail++;
    } else {
      const solSim = simulate(sim, solCompile.mlirPath);
      if (hasPass(solSim.output)) {
        process.stdout.write(`  ${G}sol=PASS${X}`);
        pass++;
      } else {
        process.stdout.write(`  ${R}sol=NO_PASS${X}\n`);
        failures.push({ lesson, mode: 'solution', reason: 'no PASS in output', output: solSim.output });
        fail++;
      }
    }

    // ── starter ──────────────────────────────────────────────────────────────
    if (!startCompile.ok) {
      process.stdout.write(`  ${G}start=FAIL(compile)${X}\n`);
      pass++;
    } else {
      const startSim = simulate(sim, startCompile.mlirPath);
      if (!hasPass(startSim.output)) {
        process.stdout.write(`  ${G}start=FAIL${X}\n`);
        pass++;
      } else {
        process.stdout.write(`  ${R}start=UNEXPECTED_PASS${X}\n`);
        failures.push({ lesson, mode: 'starter', reason: 'starter unexpectedly printed PASS', output: startSim.output });
        fail++;
      }
    }
  }

  // ── summary ─────────────────────────────────────────────────────────────────
  if (failures.length > 0) {
    console.log('\n── failures ──────────────────────────────────────');
    for (const { lesson, mode, reason, output } of failures) {
      console.log(`\n${R}FAIL${X} ${lesson} [${mode}]: ${reason}`);
      if (output?.trim()) output.trimEnd().split('\n').forEach(l => console.log(`  ${l}`));
    }
  }

  const bar = '─────────────────────────────────────';
  console.log(`\n${bar}`);
  if (fail === 0) {
    console.log(`${G}ALL PASS${X}  ${pass} checks passed, ${skip} lessons skipped`);
  } else {
    console.log(`${R}FAILURES${X}  ${pass} passed, ${fail} failed, ${skip} skipped`);
  }
  console.log(`${bar}\n`);

  if (fail > 0) process.exit(1);
}

main().catch(e => { console.error(e); process.exit(1); });
