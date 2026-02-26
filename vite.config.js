import { defineConfig } from 'vite';
import { sveltekit } from '@sveltejs/kit/vite';
import tailwindcss from '@tailwindcss/vite';
import { compression } from 'vite-plugin-compression2';
import path from 'path';
import fs from 'fs';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const Z3_BUILT_JS = path.resolve(__dirname, 'node_modules/z3-solver/build/z3-built.js');
const Z3_BUILT_WASM = path.resolve(__dirname, 'node_modules/z3-solver/build/z3-built.wasm');

const COOP_COEP_HEADERS = {
  'Cross-Origin-Opener-Policy': 'same-origin',
  'Cross-Origin-Embedder-Policy': 'require-corp',
};

/**
 * Vite plugin that injects COOP/COEP headers into the preview server.
 * Needed for SharedArrayBuffer (z3-solver WASM) to work in `vite preview`
 * (the server used by Playwright e2e tests).  Without these headers
 * window.crossOriginIsolated is false and coi-serviceworker.js triggers
 * a reload mid-test, destroying Playwright's execution context.
 */
function previewHeadersPlugin() {
  return {
    name: 'preview-coop-coep-headers',
    configurePreviewServer(server) {
      server.middlewares.use((_req, res, next) => {
        for (const [k, v] of Object.entries(COOP_COEP_HEADERS)) res.setHeader(k, v);
        next();
      });
    },
  };
}

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

export default defineConfig({
  plugins: [
    sveltekit(),
    tailwindcss(),
    previewHeadersPlugin(),
    serveZ3Plugin(),
    // Pre-compress JS/CSS/HTML assets at build time.
    // Served automatically by nginx (gzip_static on) or any CDN that looks for
    // .gz sidecar files. GitHub Pages compresses on the fly via its CDN.
    compression({ algorithm: 'gzip',   include: /\.(js|css|html|svg)$/ }),
    compression({ algorithm: 'brotliCompress', include: /\.(js|css|html|svg)$/, threshold: 1024 }),
  ],
  define: {
    // z3-solver references the Node.js `global` object; alias it to globalThis
    // so the package works in browser / Web Worker contexts.
    global: 'globalThis'
  },
  build: {
    target: 'esnext',
    minify: 'esbuild',
    sourcemap: true,
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
  },
  preview: {
    headers: {
      // Same headers for `vite preview` (used by e2e tests).
      // Without these, window.crossOriginIsolated is false and coi-serviceworker.js
      // triggers a page reload mid-test, destroying Playwright's execution context.
      'Cross-Origin-Opener-Policy': 'same-origin',
      'Cross-Origin-Embedder-Policy': 'require-corp'
    }
  }
});
