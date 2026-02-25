#!/usr/bin/env node
import { spawn } from 'node:child_process';
import { readdir, readFile } from 'node:fs/promises';
import { access } from 'node:fs/promises';
import { constants as fsConstants } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from '@playwright/test';

const HOST = process.env.REPRO_HOST || '127.0.0.1';
const DEFAULT_PORT = Number(process.env.REPRO_PORT || '43173');
const BASE_URL_OVERRIDE = (process.env.REPRO_BASE_URL || '').trim();
const SERVER_READY_TIMEOUT_MS = 45_000;
const COMPILE_TIMEOUT_MS = 180_000;
const NAVIGATION_TIMEOUT_MS = 30_000;
const NAVIGATION_RETRIES = 4;
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, '..');
const UVM_LESSON_DIR = path.join(REPO_ROOT, 'src', 'lessons', 'uvm');

const REQUIRED_FILES = [
  'static/circt/circt-verilog.js',
  'static/circt/circt-verilog.wasm',
  'static/circt/circt-sim.js',
  'static/circt/circt-sim.wasm',
  'static/circt/uvm-core/uvm-manifest.json'
];

const UVM_FILES = {
  '/src/my_test.sv': [
    'import uvm_pkg::*;',
    '`include "uvm_macros.svh"',
    '',
    'class my_test extends uvm_test;',
    '  `uvm_component_utils(my_test)',
    '  function new(string name, uvm_component parent);',
    '    super.new(name, parent);',
    '  endfunction',
    '  task run_phase(uvm_phase phase);',
    '    phase.raise_objection(this);',
    '    `uvm_info("TEST", "Hello from UVM!", UVM_LOW)',
    '    phase.drop_objection(this);',
    '  endtask',
    'endclass',
    ''
  ].join('\n'),
  '/src/tb_top.sv': [
    'import uvm_pkg::*;',
    '`include "uvm_macros.svh"',
    '`include "my_test.sv"',
    '',
    'module tb_top;',
    '  initial run_test("my_test");',
    'endmodule',
    ''
  ].join('\n')
};

async function loadSolvedLessonFiles(slug) {
  const lessonDir = path.join(UVM_LESSON_DIR, slug);
  const entries = await readdir(lessonDir);
  const out = {};

  for (const fileName of entries) {
    if (!fileName.endsWith('.sv') || fileName.endsWith('.sol.sv')) continue;
    const content = await readFile(path.join(lessonDir, fileName), 'utf8');
    out[`/src/${fileName}`] = content;
  }

  for (const fileName of entries) {
    if (!fileName.endsWith('.sol.sv')) continue;
    const stem = fileName.replace('.sol.sv', '.sv');
    const content = await readFile(path.join(lessonDir, fileName), 'utf8');
    out[`/src/${stem}`] = content;
  }

  if (Object.keys(out).length === 0) {
    throw new Error(`no SystemVerilog files found in lesson ${slug}`);
  }
  return out;
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function isTransientNavigationError(error) {
  const text = String(error && error.stack ? error.stack : error);
  return (
    text.includes('Execution context was destroyed') ||
    text.includes('Cannot find context with specified id') ||
    text.includes('Target page, context or browser has been closed') ||
    text.includes('page.goto: Timeout') ||
    text.includes('Navigation failed')
  );
}

async function gotoWithRetry(page, url) {
  let lastError;
  for (let attempt = 1; attempt <= NAVIGATION_RETRIES; attempt += 1) {
    try {
      await page.goto(url, { waitUntil: 'load', timeout: NAVIGATION_TIMEOUT_MS });
      return;
    } catch (error) {
      lastError = error;
      if (!isTransientNavigationError(error) || attempt === NAVIGATION_RETRIES) {
        throw error;
      }
      await sleep(250 * attempt);
    }
  }
  throw lastError;
}

function parseArgs(argv) {
  const out = {
    expect: 'fail',
    simulate: false,
    lesson: ''
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--expect-pass') {
      out.expect = 'pass';
      continue;
    }
    if (arg === '--expect-fail') {
      out.expect = 'fail';
      continue;
    }
    if (arg === '--simulate') {
      out.simulate = true;
      continue;
    }
    if (arg === '--no-simulate') {
      out.simulate = false;
      continue;
    }
    if (arg === '--lesson') {
      const next = argv[++i];
      if (!next) throw new Error('--lesson requires a slug (e.g. reporting)');
      out.lesson = next;
      continue;
    }
    throw new Error(`unknown argument: ${arg}`);
  }

  return out;
}

async function requireArtifacts() {
  for (const relPath of REQUIRED_FILES) {
    try {
      await access(relPath, fsConstants.R_OK);
    } catch {
      throw new Error(
        `missing required artifact: ${relPath}\n` +
        'run scripts/setup-circt.sh && npm run sync:circt before repro'
      );
    }
  }
}

function startViteDevServer(baseUrl, port) {
  // Start Vite directly to avoid npm wrapper processes that are harder to
  // terminate from this script.
  const child = spawn(
    process.execPath,
    ['./node_modules/vite/bin/vite.js', '--host', HOST, '--port', String(port), '--strictPort'],
    {
      stdio: ['ignore', 'pipe', 'pipe'],
      detached: true
    }
  );

  let ready = false;
  let output = '';

  const readyPromise = new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      reject(new Error(`vite dev server did not become ready within ${SERVER_READY_TIMEOUT_MS}ms\n${output}`));
    }, SERVER_READY_TIMEOUT_MS);

    const onData = (buf) => {
      const text = String(buf);
      output += text;
      if (!ready && text.includes('Local:') && text.includes(baseUrl)) {
        ready = true;
        clearTimeout(timer);
        resolve();
      }
    };

    child.stdout.on('data', onData);
    child.stderr.on('data', onData);

    child.on('exit', (code) => {
      if (!ready) {
        clearTimeout(timer);
        reject(new Error(`vite dev server exited before ready (code=${code})\n${output}`));
      }
    });
  });

  return { child, readyPromise };
}

async function stopProcess(child) {
  if (!child || child.exitCode !== null) return;
  try {
    // Kill the whole process group (Vite + any children).
    process.kill(-child.pid, 'SIGTERM');
  } catch {}
  for (let i = 0; i < 30; i += 1) {
    if (child.exitCode !== null) return;
    await sleep(100);
  }
  try {
    process.kill(-child.pid, 'SIGKILL');
  } catch {}
}

async function runBrowserWorkerCompile(baseUrl, files, simulate) {
  const browser = await chromium.launch({
    headless: true,
    channel: 'chromium',
    args: [
      '--use-angle=swiftshader',
      '--enable-webgl',
      '--enable-unsafe-swiftshader',
      '--ignore-gpu-blocklist'
    ]
  });

  try {
    const page = await browser.newPage({ baseURL: baseUrl });
    await gotoWithRetry(page, '/');

    const runEvaluate = async () =>
      page.evaluate(async ({ files, simulate }) => {
        const { createCirctWasmAdapter } = await import('/src/runtime/circt-adapter.js');
        const circt = createCirctWasmAdapter();

        const streamed = [];
        const result = await circt.run({
          files,
          top: 'tb_top',
          simulate,
          onStatus: (status) => streamed.push(`#status ${status}`),
          onLog: (line) => streamed.push(String(line ?? ''))
        });

        return {
          ok: !!result.ok,
          streamed,
          resultLogs: Array.isArray(result.logs) ? result.logs : []
        };
      }, { files, simulate });

    const evaluatePromise = (async () => {
      let lastError;
      for (let attempt = 1; attempt <= 6; attempt += 1) {
        try {
          return await runEvaluate();
        } catch (error) {
          const text = String(error && error.stack ? error.stack : error);
          const isContextReset =
            text.includes('Execution context was destroyed') ||
            text.includes('Cannot find context with specified id');
          if (!isContextReset || attempt === 6) {
            throw error;
          }
          lastError = error;
          await gotoWithRetry(page, '/').catch(() => {});
          await sleep(250);
        }
      }
      throw lastError;
    })();

    let timer = null;
    const timeoutPromise = new Promise((_, reject) => {
      timer = setTimeout(
        () => reject(new Error(`compile timed out after ${COMPILE_TIMEOUT_MS}ms`)),
        COMPILE_TIMEOUT_MS
      );
    });

    try {
      return await Promise.race([evaluatePromise, timeoutPromise]);
    } finally {
      if (timer) clearTimeout(timer);
    }
  } finally {
    await browser.close();
  }
}

function analyzeLogs(payload) {
  const merged = [...payload.streamed, ...payload.resultLogs].join('\n');
  const hasMalformed = /Malformed attribute storage object/.test(merged);
  const hasAbort = /Aborted\(/.test(merged);
  const hasSim = /\$ circt-sim\b/.test(merged);

  return {
    ok: payload.ok,
    hasMalformed,
    hasAbort,
    hasSim,
    merged
  };
}

(async () => {
  let options;
  let server;
  try {
    options = parseArgs(process.argv.slice(2));
    await requireArtifacts();
    const files = options.lesson ? await loadSolvedLessonFiles(options.lesson) : UVM_FILES;

    const baseUrl = BASE_URL_OVERRIDE || `http://${HOST}:${DEFAULT_PORT}`;
    if (!BASE_URL_OVERRIDE) {
      console.log(`# Starting Vite dev server at ${baseUrl}`);
      server = startViteDevServer(baseUrl, DEFAULT_PORT);
      await server.readyPromise;
    } else {
      console.log(`# Using existing dev server at ${baseUrl}`);
    }

    console.log('# Running minimal browser-worker UVM compile via createCirctWasmAdapter');
    console.log(`# mode: expect-${options.expect}, simulate=${options.simulate}`);
    const payload = await runBrowserWorkerCompile(baseUrl, files, options.simulate);
    const analysis = analyzeLogs(payload);

    console.log('--- Repro Summary ---');
    console.log(`ok=${analysis.ok}`);
    console.log(`hasMalformed=${analysis.hasMalformed}`);
    console.log(`hasAbort=${analysis.hasAbort}`);
    console.log(`hasSim=${analysis.hasSim}`);

    console.log('--- Repro Logs (first 400 lines) ---');
    const firstLines = analysis.merged.split('\n').slice(0, 400).join('\n');
    console.log(firstLines);

    if (options.expect === 'pass') {
      const ok =
        analysis.ok &&
        !analysis.hasMalformed &&
        !analysis.hasAbort &&
        (!options.simulate || analysis.hasSim);
      if (!ok) {
        console.error('ERROR: expected browser-worker UVM compile to pass');
        process.exitCode = 1;
        return;
      }

      console.log('PASS: browser-worker UVM compile completed without malformed-attribute abort');
      return;
    }

    const reproduced = !analysis.ok && analysis.hasMalformed && analysis.hasAbort && !analysis.hasSim;
    if (!reproduced) {
      console.error('ERROR: expected browser-worker malformed-attribute abort was not reproduced');
      process.exitCode = 1;
      return;
    }

    console.log('REPRODUCED: browser-worker UVM compile hit malformed-attribute abort');
  } catch (error) {
    console.error(String(error && error.stack ? error.stack : error));
    process.exitCode = 1;
  } finally {
    await stopProcess(server?.child);
  }
})();
