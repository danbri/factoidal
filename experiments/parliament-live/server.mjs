// Parliament-live proxy + static server.
//
// Zero-dep Node http server that fronts a small whitelist of UK Parliament
// APIs, applies a TTL policy informed by what each API advertises (and what
// the data actually changes like), coalesces concurrent requests, and adds
// CORS + Open Parliament Licence v3.0 attribution to every response.
//
// Run:   node server.mjs
// Open:  http://localhost:8787/
//
// Env:
//   PORT      default 8787
//   VERBOSE   "1" to log one line per request (default: quiet)
//   ALLOW_ORIGIN  default "*"  (set to your hosted origin in prod)

import http from 'node:http';
import { readFile } from 'node:fs/promises';
import { existsSync, statSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const WEB_ROOT  = path.join(__dirname, 'web');
const PORT      = Number(process.env.PORT || 8787);
const HOST      = process.env.HOST || '127.0.0.1';
const VERBOSE   = process.env.VERBOSE === '1';
const ALLOW_ORIGIN = process.env.ALLOW_ORIGIN || '*';
// PROXY_PASSWORD: when set, /api/* and /_cache require either
//   Authorization: Bearer <password>   (used by JS fetches)
//   or cookie  fpkg_auth=<password>    (used by image src)
// When unset (e.g. local dev), the proxy is open.
const PROXY_PASSWORD = process.env.PROXY_PASSWORD || '';
const AUTH_COOKIE    = 'fpkg_auth';

const OPL_ATTRIBUTION =
  'Contains Parliamentary information licensed under the Open Parliament Licence v3.0 ' +
  '(https://www.parliament.uk/site-information/copyright-parliament/open-parliament-licence/)';

// ---- Upstream whitelist -----------------------------------------------------

const ROUTES = [
  // /api/now/<zone>/<current|isoDate>
  //   -> https://now-api.parliament.uk/api/Message/message/<zone>/<...>
  { prefix: '/api/now/',
    upstreamHost: 'now-api.parliament.uk',
    upstreamPath: '/api/Message/message/' },

  // /api/members/<...>  ->  https://members-api.parliament.uk/api/<...>
  { prefix: '/api/members/',
    upstreamHost: 'members-api.parliament.uk',
    upstreamPath: '/api/' },

  // /api/hansard/<...>  ->  https://hansard-api.parliament.uk/<...>
  { prefix: '/api/hansard/',
    upstreamHost: 'hansard-api.parliament.uk',
    upstreamPath: '/' },

  // /api/cvotes/<...>   ->  https://commonsvotes-api.parliament.uk/data/<...>
  { prefix: '/api/cvotes/',
    upstreamHost: 'commonsvotes-api.parliament.uk',
    upstreamPath: '/data/' },

  // /api/lvotes/<...>   ->  https://lordsvotes-api.parliament.uk/data/<...>
  { prefix: '/api/lvotes/',
    upstreamHost: 'lordsvotes-api.parliament.uk',
    upstreamPath: '/data/' },

  // /api/sparql?query=...  ->  https://api.parliament.uk/sparql?query=...
  { prefix: '/api/sparql',
    upstreamHost: 'api.parliament.uk',
    upstreamPath: '/sparql',
    exact: true },
];

export function matchRoute(reqPath) {
  for (const r of ROUTES) {
    if (r.exact) {
      if (reqPath === r.prefix) return { route: r, tail: '' };
    } else if (reqPath.startsWith(r.prefix)) {
      return { route: r, tail: reqPath.slice(r.prefix.length) };
    }
  }
  return null;
}

// ---- TTL policy -------------------------------------------------------------
//
// See README at top of file. Returns ms.

export function ttlMsFor(route, tail) {
  if (route.prefix === '/api/now/') {
    // tail looks like "CommonsMain/current" or "CommonsMain/2026-04-29T13:00:00Z"
    const m = tail.match(/^[^/]+\/(.+)$/);
    if (!m) return 5_000;
    const datePart = m[1];
    if (datePart === 'current') return 5_000;
    const t = Date.parse(datePart);
    if (Number.isFinite(t) && Date.now() - t > 24 * 3600_000) {
      return 6 * 3600_000;       // historic slide, effectively immutable
    }
    return 5_000;
  }
  if (route.prefix === '/api/members/') {
    if (/\/Thumbnail($|\?)/.test(tail) || /\/Portrait($|\?)/.test(tail)) {
      return 86_400_000;          // images are stable
    }
    return 300_000;               // matches upstream max-age=300
  }
  if (route.prefix === '/api/hansard/') {
    if (/^overview\/lastsittingdate/.test(tail))   return 600_000;
    if (/^overview\/calendar/.test(tail))          return 3600_000;
    if (/^debates\/debate\//.test(tail))           return 86_400_000;
    if (/^debates\/division\//.test(tail))         return 86_400_000;
    if (/^debates\/divisions\//.test(tail))        return 60_000;
    if (/^overview\/sectionsforday/.test(tail))    return 60_000;
    if (/^search/.test(tail))                      return 60_000;
    return 60_000;
  }
  if (route.prefix === '/api/cvotes/' || route.prefix === '/api/lvotes/') {
    if (/^division\/\d+\.json/.test(tail)) return 86_400_000;  // a recorded vote is immutable
    if (/^divisions\/search/.test(tail))   return 600_000;
    return 60_000;
  }
  if (route.prefix === '/api/sparql') {
    return 60_000;
  }
  return 30_000;
}

// ---- Cache + coalescing -----------------------------------------------------

const cache    = new Map();   // key -> { expires, status, headers, body }
const inflight = new Map();   // key -> Promise<entry>

setInterval(() => {
  const now = Date.now();
  for (const [k, v] of cache) if (v.expires < now) cache.delete(k);
}, 60_000).unref();

export function buildUpstreamUrl(route, tail, search) {
  const host = route.upstreamHost;
  const base = route.upstreamPath;
  const pathOut = route.exact ? base : (base + tail);
  return `https://${host}${pathOut}${search || ''}`;
}

// Re-export for tests
export { ROUTES };

// Per-upstream-host rate limit: enforce a minimum gap between successive
// upstream requests to the same host. Caching + coalescing already prevent
// repeat calls for the same URL; this is the *cross-URL* throttle so that
// a burst of distinct fetches (e.g. 12 thumbnails) doesn't hammer one host.
const HOST_GAP_MS = 200;
const lastHostHit = new Map();           // host -> Promise<void> (chain)
function throttleHost(host) {
  const prev = lastHostHit.get(host) || Promise.resolve();
  let resolveNext;
  const next = new Promise(res => { resolveNext = res; });
  // when the prior call has waited its gap, the next can start
  const waited = prev.then(() => new Promise(r => setTimeout(r, HOST_GAP_MS)));
  lastHostHit.set(host, next);
  // resolve `next` once the prior gap has elapsed AND we've started
  return waited.then(() => { resolveNext(); });
}

async function fetchUpstream(url, acceptHeader) {
  const u = new URL(url);
  await throttleHost(u.host);
  const ac = new AbortController();
  const t  = setTimeout(() => ac.abort(), 30_000);
  try {
    const headers = {};
    if (acceptHeader) headers['accept'] = acceptHeader;
    const res = await fetch(url, { signal: ac.signal, redirect: 'follow', headers });
    const buf = Buffer.from(await res.arrayBuffer());
    const ct  = res.headers.get('content-type') || 'application/octet-stream';
    return {
      status: res.status,
      headers: {
        'content-type': ct,
        'x-upstream-url': url,
      },
      body: buf,
    };
  } finally {
    clearTimeout(t);
  }
}

async function getCached(key, url, ttlMs, acceptHeader) {
  const now = Date.now();
  const hit = cache.get(key);
  if (hit && hit.expires > now) return { entry: hit, source: 'hit' };

  const pending = inflight.get(key);
  if (pending) return { entry: await pending, source: 'coalesced' };

  const p = (async () => {
    const fresh = await fetchUpstream(url, acceptHeader);
    const entry = { ...fresh, expires: Date.now() + ttlMs, fetchedAt: Date.now() };
    if (fresh.status >= 200 && fresh.status < 400) cache.set(key, entry);
    return entry;
  })().finally(() => inflight.delete(key));
  inflight.set(key, p);
  return { entry: await p, source: 'miss' };
}

// ---- Static file serving ----------------------------------------------------

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js':   'text/javascript; charset=utf-8',
  '.mjs':  'text/javascript; charset=utf-8',
  '.css':  'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg':  'image/svg+xml',
  '.png':  'image/png',
  '.jpg':  'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.ico':  'image/x-icon',
  '.woff2':'font/woff2',
};

async function serveStatic(req, res) {
  let p = decodeURIComponent(req.url.split('?')[0]);
  if (p === '/') p = '/index.html';
  const full = path.join(WEB_ROOT, p);
  if (!full.startsWith(WEB_ROOT)) return notFound(res);
  if (!existsSync(full) || !statSync(full).isFile()) return notFound(res);
  const ext = path.extname(full).toLowerCase();
  const body = await readFile(full);
  setCommonHeaders(res);
  // Always revalidate the page itself — we redeploy frequently and a stale
  // cached index.html will keep referring to fixed-and-gone JS. Browsers
  // can revalidate via If-Modified-Since etc.; for now no-cache is fine.
  const headers = { 'content-type': MIME[ext] || 'application/octet-stream' };
  if (ext === '.html') headers['cache-control'] = 'no-cache, must-revalidate';
  res.writeHead(200, headers);
  res.end(body);
}

// ---- Headers + helpers ------------------------------------------------------

function setCommonHeaders(res) {
  res.setHeader('access-control-allow-origin',  ALLOW_ORIGIN);
  res.setHeader('access-control-allow-methods', 'GET, OPTIONS');
  res.setHeader('access-control-allow-headers', 'content-type');
  res.setHeader('access-control-expose-headers',
    'x-cache, x-cache-age, x-ttl, x-upstream-url, x-attribution');
  res.setHeader('x-attribution', OPL_ATTRIBUTION);
}

function notFound(res) {
  setCommonHeaders(res);
  res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
  res.end('not found\n');
}

function authOk(req) {
  if (!PROXY_PASSWORD) return true;
  const h = req.headers['authorization'] || '';
  if (h.startsWith('Bearer ')) {
    if (h.slice(7) === PROXY_PASSWORD) return true;
  }
  const cookies = req.headers['cookie'] || '';
  for (const part of cookies.split(';')) {
    const [k, ...v] = part.trim().split('=');
    if (k === AUTH_COOKIE && decodeURIComponent(v.join('=')) === PROXY_PASSWORD) return true;
  }
  return false;
}

function json(res, status, obj) {
  setCommonHeaders(res);
  res.writeHead(status, { 'content-type': 'application/json; charset=utf-8' });
  res.end(JSON.stringify(obj));
}

// ---- Request handler --------------------------------------------------------

const server = http.createServer(async (req, res) => {
  try {
    if (req.method === 'OPTIONS') {
      setCommonHeaders(res);
      res.writeHead(204);
      res.end();
      return;
    }
    if (req.method !== 'GET') {
      setCommonHeaders(res);
      res.writeHead(405, { 'content-type': 'text/plain' });
      res.end('method not allowed');
      return;
    }

    const u = new URL(req.url, `http://localhost:${PORT}`);

    if (u.pathname === '/_health') {
      return json(res, 200, { ok: true, cacheEntries: cache.size, authRequired: !!PROXY_PASSWORD });
    }
    if (u.pathname === '/_cache') {
      if (!authOk(req)) return json(res, 401, { error: 'unauthorized' });
      const rows = [...cache.entries()].map(([k, v]) => ({
        key: k, status: v.status,
        ageMs: Date.now() - v.fetchedAt,
        ttlRemainingMs: v.expires - Date.now(),
      }));
      return json(res, 200, { entries: rows });
    }

    const m = matchRoute(u.pathname);
    if (!m) return serveStatic(req, res);

    if (!authOk(req)) return json(res, 401, { error: 'unauthorized' });

    const ttlMs  = ttlMsFor(m.route, m.tail);
    const upUrl  = buildUpstreamUrl(m.route, m.tail, u.search);
    // Use Accept header in cache key so JSON / CSV / Turtle don't collide.
    const accept = req.headers['accept'] || '';
    const cKey   = upUrl + '||' + accept;
    const t0     = Date.now();
    const { entry, source } = await getCached(cKey, upUrl, ttlMs, accept);

    if (VERBOSE) {
      const age = Date.now() - entry.fetchedAt;
      process.stderr.write(
        `[${new Date().toISOString()}] ${source.padEnd(9)} ttl=${ttlMs}ms age=${age}ms ${u.pathname}${u.search}\n`
      );
    }

    setCommonHeaders(res);
    res.setHeader('content-type', entry.headers['content-type']);
    res.setHeader('x-cache', source);
    res.setHeader('x-cache-age', String(Date.now() - entry.fetchedAt));
    res.setHeader('x-ttl', String(ttlMs));
    res.setHeader('x-upstream-url', entry.headers['x-upstream-url']);
    res.writeHead(entry.status);
    res.end(entry.body);
  } catch (err) {
    process.stderr.write(`[error] ${err.stack || err}\n`);
    setCommonHeaders(res);
    res.writeHead(502, { 'content-type': 'application/json; charset=utf-8' });
    res.end(JSON.stringify({ error: 'upstream_failure', detail: String(err.message || err) }));
  }
});

// Only start listening when invoked as the entry point. When this module is
// imported (e.g. by tests), the server stays inert.
const invokedAsMain = import.meta.url === `file://${process.argv[1]}`;
if (invokedAsMain) {
  server.listen(PORT, HOST, () => {
    process.stdout.write(`fpkg proxy listening on http://${HOST}:${PORT}/\n`);
    process.stdout.write(`  auth: ${PROXY_PASSWORD ? 'required (PROXY_PASSWORD set)' : 'open (PROXY_PASSWORD unset — dev mode)'}\n`);
    process.stdout.write(`  /api/now/<zone>/<current|isoDate>\n`);
    process.stdout.write(`  /api/members/<MembersApiPath>\n`);
    process.stdout.write(`  /api/hansard/<HansardApiPath>\n`);
    process.stdout.write(`  /api/cvotes/<CommonsVotesPath>  /api/lvotes/<LordsVotesPath>\n`);
    process.stdout.write(`  /api/sparql?query=...\n`);
    process.stdout.write(`  /_health  /_cache\n`);
  });
}

export { server };
