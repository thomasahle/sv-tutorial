/// <reference lib="webworker" />

import { build, files, prerendered, version } from '$service-worker';
import {
  HEAVY_STATIC_PREFIXES,
  OFFLINE_APP_CACHE_PREFIX,
  OFFLINE_RUNTIME_CACHE,
  dedupeStrings,
} from './lib/offline-cache.js';

const APP_CACHE = `${OFFLINE_APP_CACHE_PREFIX}${version}`;

function getScopePath() {
  try {
    return new URL(self.registration.scope).pathname;
  } catch {
    return '/';
  }
}

function toScopeRelative(pathname) {
  const scopePath = getScopePath();
  const value = String(pathname || '');
  const trimmed = value.startsWith(scopePath) ? value.slice(scopePath.length) : value;
  return trimmed.replace(/^\/+/, '');
}

function isHeavyPath(pathname) {
  const rel = toScopeRelative(pathname);
  return HEAVY_STATIC_PREFIXES.some((prefix) => rel.startsWith(prefix));
}

function toScopeUrl(path) {
  return new URL(String(path || ''), self.registration.scope).href;
}

const PRECACHE_URLS = dedupeStrings(
  [...build, ...files, ...prerendered]
    .filter((path) => !isHeavyPath(path))
    .map((path) => toScopeUrl(path))
    .concat([toScopeUrl(''), toScopeUrl('404.html')])
);

async function cacheAll(cache, urls) {
  for (const url of urls) {
    try {
      const req = new Request(url, { cache: 'reload' });
      const res = await fetch(req);
      if (!res.ok && res.type !== 'opaque') continue;
      await cache.put(req, res.clone());
    } catch {
      // Best-effort cache warmup; ignore individual failures.
    }
  }
}

self.addEventListener('install', (event) => {
  event.waitUntil(
    (async () => {
      const cache = await caches.open(APP_CACHE);
      await cacheAll(cache, PRECACHE_URLS);
      await self.skipWaiting();
    })()
  );
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    (async () => {
      const keys = await caches.keys();
      await Promise.all(
        keys
          .filter((key) => key.startsWith(OFFLINE_APP_CACHE_PREFIX) && key !== APP_CACHE)
          .map((key) => caches.delete(key))
      );
      await self.clients.claim();
    })()
  );
});

function pickWriteCache(requestUrl) {
  if (requestUrl.origin !== self.location.origin) return OFFLINE_RUNTIME_CACHE;
  if (isHeavyPath(requestUrl.pathname)) return OFFLINE_RUNTIME_CACHE;
  return APP_CACHE;
}

self.addEventListener('fetch', (event) => {
  const req = event.request;
  if (req.method !== 'GET') return;

  const reqUrl = new URL(req.url);
  if (!/^https?:$/.test(reqUrl.protocol)) return;

  event.respondWith(
    (async () => {
      const cached = await caches.match(req);
      if (cached) return cached;

      try {
        const res = await fetch(req);
        if (res && (res.ok || res.type === 'opaque')) {
          const cacheName = pickWriteCache(reqUrl);
          const cache = await caches.open(cacheName);
          cache.put(req, res.clone()).catch(() => {});
        }
        return res;
      } catch (error) {
        if (req.mode === 'navigate') {
          const fallback = await caches.match(toScopeUrl('404.html'));
          if (fallback) return fallback;
        }
        throw error;
      }
    })()
  );
});

