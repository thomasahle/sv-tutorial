/**
 * Unit tests for the NODERAWFS process shim used in WORKER_SOURCE and
 * COCOTB_WORKER_SOURCE inside circt-adapter.js.
 *
 * Emscripten tools compiled with NODERAWFS call process.version.match(/v(\d+)/)
 * to detect the Node.js major version.  Before the fix, the shim set
 * proc.versions.node but not proc.version, causing:
 *   "Cannot read properties of undefined (reading 'match')"
 */

import { describe, it, expect } from 'vitest';

// Mirror the shim logic verbatim from both WORKER_SOURCE and COCOTB_WORKER_SOURCE.
function applyProcessShim(existingProcess) {
  const proc = (existingProcess == null) ? {} : existingProcess;
  if (!proc.versions || typeof proc.versions !== 'object') proc.versions = {};
  if (!proc.versions.node) proc.versions.node = '18.0.0';
  if (typeof proc.version !== 'string') proc.version = 'v18.0.0';
  return proc;
}

describe('NODERAWFS process shim', () => {
  it('sets process.version when process is undefined', () => {
    const proc = applyProcessShim(undefined);
    expect(proc.version).toBe('v18.0.0');
  });

  it('sets process.version when process is an empty object', () => {
    const proc = applyProcessShim({});
    expect(proc.version).toBe('v18.0.0');
  });

  it('does not override an existing process.version', () => {
    const proc = applyProcessShim({ version: 'v20.11.0' });
    expect(proc.version).toBe('v20.11.0');
  });

  it('process.version.match works after shimming — Emscripten Node.js version detection', () => {
    // This is the exact call that threw before the fix:
    //   process.version.match(/v(\d+)/)
    const proc = applyProcessShim(undefined);
    const m = proc.version.match(/v(\d+)/);
    expect(m).not.toBeNull();
    expect(Number(m[1])).toBeGreaterThanOrEqual(18);
  });

  it('sets process.versions.node when missing', () => {
    const proc = applyProcessShim({});
    expect(proc.versions.node).toBe('18.0.0');
  });

  it('does not override an existing process.versions.node', () => {
    const proc = applyProcessShim({ versions: { node: '20.11.0' } });
    expect(proc.versions.node).toBe('20.11.0');
  });
});
