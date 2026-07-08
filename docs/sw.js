// docs/sw.js — offline support for the Factoidal documentation hub
// (issue #69).
//
// Anti-stale-lock design (the owner's hard requirement — a naive
// cache-first SW must never pin a user to an old js/npm bundle):
//
//   1. CACHE is suffixed with BUILD_VERSION, stamped by
//      docs/.eleventy.js from a git short hash at build time. Every
//      deploy gets a *different* cache name.
//   2. `install` calls skipWaiting() — a new SW takes over promptly,
//      it does not wait for every open tab to close first.
//   3. `activate` deletes every cache whose name isn't this build's
//      CACHE, then calls clients.claim(). The instant a new deploy's
//      SW activates, all older-versioned caches are gone — there is
//      nowhere for stale bytes to hide.
//   4. HTML navigations are network-first. An online user's next
//      navigation always fetches the current shell HTML (which
//      references the current bundle URLs by their real paths), so
//      they cannot get stuck on old markup even before activate runs.
//
// Only the js/npm bundle + other same-origin static assets use
// stale-while-revalidate (fast now, refreshed in the background); only
// truly content-hashed filenames (the wasm loader's
// `code-<hash>.wasm`, and other hash-named assets) are cache-first,
// because for those the URL itself changes when the content does.
//
// Do NOT hand-edit the two placeholder constants below (build version
// string, precache URL array literal). docs/.eleventy.js's
// `eleventy.after` hook fills them in after every `eleventy` build,
// probing the real _site output rather than guessing filenames. If a
// deployed sw.js still shows placeholder-looking constants instead of
// a concrete hash and a real URL list, the build step did not run.

const BUILD_VERSION = "__BUILD_VERSION__";
const CACHE = "factoidal-hub-" + BUILD_VERSION;

// Deliberately short: the hub + home shell, and the JS module chain
// the hub's live cells need on first load (Observable runtime/stdlib,
// the project's own reactive-cell compiler, and the default
// non-wasm Factoidal engine bundle). Content-hashed wasm assets are
// NOT precached here — they're large, optional (the wasm engine path
// is opt-in, not the hub's default), and the cache-first route below
// warms them from real traffic on first use instead.
const PRECACHE_URLS = __PRECACHE_URLS__;

// Content-hashed / immutable filename patterns: the URL changes
// whenever the content does, so caching the response forever is safe.
function isImmutableAsset(url) {
  return (
    /\.wasm\.assets\/code-[0-9a-f]{6,}\.wasm(?:[?#]|$)/.test(url.pathname) ||
    /-[0-9a-f]{8,40}\.(?:js|mjs|wasm|css)(?:[?#]|$)/.test(url.pathname)
  );
}

self.addEventListener("install", (event) => {
  self.skipWaiting();
  event.waitUntil(
    caches.open(CACHE).then((cache) =>
      Promise.all(
        PRECACHE_URLS.map((url) =>
          cache.add(url).catch((err) => {
            // A single missing/renamed precache URL must not fail
            // install for the whole SW — that would silently disable
            // offline support entirely on a naming mismatch. Log and
            // move on; stale-while-revalidate/cache-first below still
            // populate the cache from real traffic.
            console.warn("[sw] precache miss:", url, err && err.message);
          })
        )
      )
    )
  );
});

self.addEventListener("activate", (event) => {
  event.waitUntil(
    (async () => {
      // The anti-stale-lock guarantee: every cache that isn't this
      // build's versioned CACHE is deleted the moment the new SW
      // activates, so an old bundle can never keep being served from
      // a leftover cache after a new one has taken over.
      const keys = await caches.keys();
      await Promise.all(
        keys.filter((key) => key !== CACHE).map((key) => caches.delete(key))
      );
      await self.clients.claim();
    })()
  );
});

async function networkFirst(request) {
  const cache = await caches.open(CACHE);
  try {
    const response = await fetch(request);
    if (response && response.ok) cache.put(request, response.clone());
    return response;
  } catch (err) {
    const cached = await cache.match(request);
    if (cached) return cached;
    // Last-resort offline fallback: the precached shell, so a
    // never-before-visited page at least renders something offline
    // instead of the browser's default offline error page.
    const fallback = await cache.match(PRECACHE_URLS[0]);
    if (fallback) return fallback;
    throw err;
  }
}

async function cacheFirst(request) {
  const cache = await caches.open(CACHE);
  const cached = await cache.match(request);
  if (cached) return cached;
  const response = await fetch(request);
  if (response && response.ok) cache.put(request, response.clone());
  return response;
}

function staleWhileRevalidate(event) {
  const request = event.request;
  const cachePromise = caches.open(CACHE);
  const fetchPromise = fetch(request)
    .then(async (response) => {
      if (response && response.ok) {
        const cache = await cachePromise;
        cache.put(request, response.clone());
      }
      return response;
    })
    .catch(() => undefined);
  // Refresh the cache in the background even when we're about to
  // answer from cache below — this is what lets a version-bumped
  // deploy land within a navigation or two instead of being pinned.
  event.waitUntil(fetchPromise);
  return cachePromise
    .then((cache) => cache.match(request))
    .then((cached) => cached || fetchPromise)
    .then((response) => response || Response.error());
}

self.addEventListener("fetch", (event) => {
  const request = event.request;
  if (request.method !== "GET") return; // never intercept writes

  const url = new URL(request.url);
  if (url.origin !== self.location.origin) return; // cross-origin: network only, no caching

  if (request.mode === "navigate") {
    event.respondWith(networkFirst(request));
    return;
  }

  if (isImmutableAsset(url)) {
    event.respondWith(cacheFirst(request));
    return;
  }

  event.respondWith(staleWhileRevalidate(event));
});
