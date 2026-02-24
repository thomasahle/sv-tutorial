#!/usr/bin/env node
import { spawn } from 'node:child_process';
import { access } from 'node:fs/promises';
import { constants as fsConstants } from 'node:fs';
import { chromium } from '@playwright/test';

const HOST = process.env.REPRO_HOST || '127.0.0.1';
const PORT = Number(process.env.REPRO_PORT || '4173');
const BASE_URL = `http://${HOST}:${PORT}`;
const SERVER_READY_TIMEOUT_MS = 45_000;
const COMPILE_TIMEOUT_MS = 180_000;

const REQUIRED_FILES = [
  'public/circt/circt-verilog.js',
  'public/circt/circt-verilog.wasm',
  'public/circt/circt-sim.js',
  'public/circt/circt-sim.wasm',
  'public/circt/uvm-core/uvm-manifest.json'
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

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
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

function startViteDevServer() {
  const child = spawn(
    'npm',
    ['run', 'dev', '--', '--host', HOST, '--port', String(PORT), '--strictPort'],
    {
      stdio: ['ignore', 'pipe', 'pipe']
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
      if (!ready && text.includes('Local:') && text.includes(BASE_URL)) {
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
  if (!child || child.killed) return;
  child.kill('SIGTERM');
  for (let i = 0; i < 30; i += 1) {
    if (child.exitCode !== null) return;
    await sleep(100);
  }
  child.kill('SIGKILL');
}

async function runBrowserWorkerCompile() {
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
    const page = await browser.newPage({ baseURL: BASE_URL });
    await page.goto('/');

    const evaluatePromise = page.evaluate(async ({ files }) => {
      const { createCirctWasmAdapter } = await import('/src/runtime/circt-adapter.js');
      const circt = createCirctWasmAdapter();

      const streamed = [];
      const result = await circt.run({
        files,
        top: 'tb_top',
        simulate: false,
        onStatus: (status) => streamed.push(`#status ${status}`),
        onLog: (line) => streamed.push(String(line ?? ''))
      });

      return {
        ok: !!result.ok,
        streamed,
        resultLogs: Array.isArray(result.logs) ? result.logs : []
      };
    }, { files: UVM_FILES });

    const timeoutPromise = new Promise((_, reject) => {
      setTimeout(() => reject(new Error(`compile timed out after ${COMPILE_TIMEOUT_MS}ms`)), COMPILE_TIMEOUT_MS);
    });

    return await Promise.race([evaluatePromise, timeoutPromise]);
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
  let server;
  try {
    await requireArtifacts();

    console.log(`# Starting Vite dev server at ${BASE_URL}`);
    server = startViteDevServer();
    await server.readyPromise;

    console.log('# Running minimal browser-worker UVM compile via createCirctWasmAdapter');
    const payload = await runBrowserWorkerCompile();
    const analysis = analyzeLogs(payload);

    console.log('--- Repro Summary ---');
    console.log(`ok=${analysis.ok}`);
    console.log(`hasMalformed=${analysis.hasMalformed}`);
    console.log(`hasAbort=${analysis.hasAbort}`);
    console.log(`hasSim=${analysis.hasSim}`);

    console.log('--- Repro Logs (first 400 lines) ---');
    const firstLines = analysis.merged.split('\n').slice(0, 400).join('\n');
    console.log(firstLines);

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
