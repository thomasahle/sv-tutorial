import { describe, expect, it } from 'vitest';
import {
  LOCAL_RUNTIME_PATHS,
  PYODIDE_COMPANION_FILES,
  buildConfiguredRuntimeUrls,
  dedupeStrings,
  joinBasePath,
  normalizeBasePath,
  offlineReadySentinelUrl,
  siblingUrls,
  z3WasmFromScriptUrl,
} from './offline-cache.js';

describe('offline-cache helpers', () => {
  it('normalizes and joins base paths', () => {
    expect(normalizeBasePath('')).toBe('/');
    expect(normalizeBasePath('/sv-tutorial')).toBe('/sv-tutorial/');
    expect(normalizeBasePath('sv-tutorial')).toBe('/sv-tutorial/');
    expect(joinBasePath('/sv-tutorial', '/circt/circt-sim.js')).toBe('/sv-tutorial/circt/circt-sim.js');
  });

  it('dedupes string values', () => {
    expect(dedupeStrings(['a', 'b', 'a', '', null, 'b'])).toEqual(['a', 'b']);
  });

  it('derives z3 wasm from script URL', () => {
    expect(z3WasmFromScriptUrl('/z3/z3-built.js')).toBe('/z3/z3-built.wasm');
    expect(z3WasmFromScriptUrl('/z3/z3-built.wasm')).toBe('');
  });

  it('derives sibling URLs from a file URL', () => {
    const urls = siblingUrls('https://cdn.example.com/pyodide/pyodide.js', ['pyodide.asm.wasm', 'repodata.json']);
    expect(urls).toEqual([
      'https://cdn.example.com/pyodide/pyodide.asm.wasm',
      'https://cdn.example.com/pyodide/repodata.json',
    ]);
  });

  it('builds runtime URL list from config and local defaults', () => {
    const urls = buildConfiguredRuntimeUrls({
      basePath: '/sv-tutorial',
      runtimeConfig: {
        toolchain: {
          sim: {
            js: '/custom/sim.js',
            wasm: '/custom/sim.wasm',
          },
        },
        pyodideUrl: 'https://cdn.example.com/pyodide/pyodide.js',
      },
      z3ScriptUrl: '/z3/z3-built.js',
    });

    expect(urls).toContain('/custom/sim.js');
    expect(urls).toContain('/custom/sim.wasm');
    expect(urls).toContain('/z3/z3-built.js');
    expect(urls).toContain('/z3/z3-built.wasm');
    expect(urls).toContain('https://cdn.example.com/pyodide/pyodide.js');
    for (const companion of PYODIDE_COMPANION_FILES) {
      expect(urls).toContain(`https://cdn.example.com/pyodide/${companion}`);
    }
    for (const rel of LOCAL_RUNTIME_PATHS) {
      expect(urls).toContain(joinBasePath('/sv-tutorial', rel));
    }
    expect(new Set(urls).size).toBe(urls.length);
  });

  it('builds offline-ready sentinel URL under the app base path', () => {
    expect(offlineReadySentinelUrl('/sv-tutorial')).toBe('/sv-tutorial/__offline__/ready');
  });
});
