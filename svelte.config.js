import adapter from '@sveltejs/adapter-static';

const rawBase = process.env.VITE_BASE ?? '';
const base = rawBase.endsWith('/') ? rawBase.slice(0, -1) : rawBase;

export default {
  kit: {
    adapter: adapter({ fallback: '404.html' }),
    paths: { base },
    serviceWorker: {
      // We register manually from +layout.svelte with module mode so dev/prod
      // behavior stays consistent and we can gate offline download in dev.
      register: false
    },
    prerender: {
      // Lesson HTML embeds <img src="waves.png"> which Vite rewrites client-side
      // but not during SSR prerendering — the crawler sees the original relative
      // URL and gets a 404.  Ignore those so the build doesn't fail.
      handleHttpError: ({ path, referrer, message }) => {
        if (/\.(png|jpg|jpeg|gif|svg|webp)$/.test(path)) return;
        throw new Error(message);
      }
    }
  }
};
