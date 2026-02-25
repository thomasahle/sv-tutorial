import { describe, expect, it } from 'vitest';
import { WORKER_RUNTIME_HELPERS_SOURCE } from './worker-runtime-helpers-source.js';

describe('worker runtime helpers source', () => {
  it('provides shared helpers for path + noderawfs loading', () => {
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('var WORKER_PATH_SHIM');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function isNoderawfsScript');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function fetchScriptText');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function installPathRequireOnly');
    expect(WORKER_RUNTIME_HELPERS_SOURCE).toContain('function loadEmscriptenTool');
  });

  it('does not inject a literal backslash-n callMain shim payload', () => {
    // A previous version appended "\\n...\\n" literally, which produced
    // invalid JS tokens when eval() parsed the concatenated tool script.
    expect(WORKER_RUNTIME_HELPERS_SOURCE).not.toContain(
      "\\\\n;try{if(typeof callMain==='function'"
    );
  });
});
