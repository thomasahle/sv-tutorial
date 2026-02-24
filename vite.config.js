import { defineConfig } from 'vite';
import { svelte } from '@sveltejs/vite-plugin-svelte';
import tailwindcss from '@tailwindcss/vite';
import path from 'path';
import fs from 'fs';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const Z3_BUILT_JS = path.resolve(__dirname, 'node_modules/z3-solver/build/z3-built.js');
const Z3_BUILT_WASM = path.resolve(__dirname, 'node_modules/z3-solver/build/z3-built.wasm');
const COI_SW_JS = path.resolve(__dirname, 'node_modules/coi-serviceworker/coi-serviceworker.js');

/**
 * Vite plugin that serves z3-built.js as an unbundled static file.
 *
 * z3-solver's browser entrypoint looks for globalThis.initZ3, which must be
 * set by loading z3-built.js as a plain <script> (not bundled).  The plugin
 * serves it at /z3/z3-built.js in dev mode and copies it into the build
 * output so production works without extra server configuration.
 */
function serveZ3Plugin() {
  return {
    name: 'serve-z3-built',

    configureServer(server) {
      server.middlewares.use('/z3/z3-built.js', (_req, res) => {
        res.setHeader('Content-Type', 'application/javascript');
        fs.createReadStream(Z3_BUILT_JS).pipe(res);
      });
      server.middlewares.use('/z3/z3-built.wasm', (_req, res) => {
        res.setHeader('Content-Type', 'application/wasm');
        fs.createReadStream(Z3_BUILT_WASM).pipe(res);
      });
    },

    generateBundle() {
      this.emitFile({
        type: 'asset',
        fileName: 'z3/z3-built.js',
        source: fs.readFileSync(Z3_BUILT_JS)
      });
      this.emitFile({
        type: 'asset',
        fileName: 'z3/z3-built.wasm',
        source: fs.readFileSync(Z3_BUILT_WASM)
      });
    }
  };
}

/**
 * Serves coi-serviceworker.js so GitHub Pages (which cannot set custom
 * response headers) can still use SharedArrayBuffer via a service worker
 * that injects Cross-Origin-Opener-Policy / Cross-Origin-Embedder-Policy.
 */
function serveCOIPlugin() {
  return {
    name: 'serve-coi-serviceworker',

    configureServer(server) {
      server.middlewares.use('/coi-serviceworker.js', (_req, res) => {
        res.setHeader('Content-Type', 'application/javascript');
        fs.createReadStream(COI_SW_JS).pipe(res);
      });
    },

    generateBundle() {
      this.emitFile({
        type: 'asset',
        fileName: 'coi-serviceworker.js',
        source: fs.readFileSync(COI_SW_JS)
      });
    }
  };
}

export default defineConfig({
  base: process.env.VITE_BASE ?? '/',
  plugins: [svelte(), tailwindcss(), serveZ3Plugin(), serveCOIPlugin()],
  resolve: {
    alias: { '$lib': path.resolve(__dirname, './src/lib') }
  },
  define: {
    // z3-solver references the Node.js `global` object; alias it to globalThis
    // so the package works in browser / Web Worker contexts.
    global: 'globalThis'
  },
  build: {
    // Single chunk is ~218 kB gzipped (CodeMirror + Svelte + CIRCT adapter).
    // The raw size exceeds Rollup's 500 kB default but gzip makes it fine.
    chunkSizeWarningLimit: 800,
    rollupOptions: {
      output: {
        manualChunks(id) {
          if (!id.includes('node_modules')) return;

          // Keep editor code in a dedicated, cacheable chunk so lesson content
          // and runtime updates do not invalidate it.
          if (
            id.includes('/codemirror/') ||
            id.includes('/@codemirror/') ||
            id.includes('/@lezer/')
          ) {
            return 'editor-vendor';
          }

          // Keep framework/UI deps separate from lesson/runtime code.
          if (
            id.includes('/svelte/') ||
            id.includes('/@sveltejs/') ||
            id.includes('/bits-ui/') ||
            id.includes('/tailwind-merge/') ||
            id.includes('/tailwind-variants/')
          ) {
            return 'framework-vendor';
          }
        }
      }
    }
  },
  server: {
    headers: {
      // Required for SharedArrayBuffer (used by z3-solver's threaded WASM).
      'Cross-Origin-Opener-Policy': 'same-origin',
      'Cross-Origin-Embedder-Policy': 'require-corp'
    }
  }
});
