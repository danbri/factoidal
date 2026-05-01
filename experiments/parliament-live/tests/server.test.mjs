// Server tests for the FPKG proxy.
//
// Run from the experiment dir:
//   node --test tests/
//
// These tests are zero-dep: they use Node's built-in test runner and only
// import the proxy module. The proxy is designed to no-op its `listen` call
// when imported, so unit tests don't open ports. The integration test below
// boots the server itself on a random port.

import { test, before, after, describe } from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { setTimeout as sleep } from 'node:timers/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  ROUTES,
  matchRoute,
  ttlMsFor,
  buildUpstreamUrl,
} from '../server.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const SERVER    = path.join(__dirname, '..', 'server.mjs');

// ---------------------------------------------------------------------------
// matchRoute
// ---------------------------------------------------------------------------

describe('matchRoute', () => {
  test('matches /api/now/<zone>/<thing>', () => {
    const m = matchRoute('/api/now/CommonsMain/current');
    assert.ok(m, 'expected a route match');
    assert.equal(m.route.upstreamHost, 'now-api.parliament.uk');
    assert.equal(m.tail, 'CommonsMain/current');
  });

  test('matches /api/members/<…>', () => {
    const m = matchRoute('/api/members/Members/4514/Voting');
    assert.ok(m);
    assert.equal(m.route.upstreamHost, 'members-api.parliament.uk');
    assert.equal(m.tail, 'Members/4514/Voting');
  });

  test('matches /api/hansard/<…>', () => {
    const m = matchRoute('/api/hansard/overview/lastsittingdate.json');
    assert.ok(m);
    assert.equal(m.route.upstreamHost, 'hansard-api.parliament.uk');
  });

  test('matches /api/cvotes/<…> and /api/lvotes/<…>', () => {
    const c = matchRoute('/api/cvotes/division/2347.json');
    assert.equal(c?.route.upstreamHost, 'commonsvotes-api.parliament.uk');
    const l = matchRoute('/api/lvotes/division/100.json');
    assert.equal(l?.route.upstreamHost, 'lordsvotes-api.parliament.uk');
  });

  test('matches /api/sparql exactly (not a prefix)', () => {
    const ok = matchRoute('/api/sparql');
    assert.equal(ok?.route.upstreamHost, 'api.parliament.uk');
    assert.equal(ok?.tail, '');
    // /api/sparql/something must NOT match the exact route
    const off = matchRoute('/api/sparql/something');
    assert.equal(off, null);
  });

  test('rejects unrelated paths', () => {
    assert.equal(matchRoute('/'), null);
    assert.equal(matchRoute('/_health'), null);
    assert.equal(matchRoute('/api/unknown/x'), null);
  });
});

// ---------------------------------------------------------------------------
// ttlMsFor — the heart of the caching policy
// ---------------------------------------------------------------------------

describe('ttlMsFor', () => {
  const route = (prefix) => ROUTES.find(r => r.prefix === prefix);

  test('Now: current is 5s', () => {
    assert.equal(ttlMsFor(route('/api/now/'), 'CommonsMain/current'), 5_000);
  });

  test('Now: recent date is 5s', () => {
    const today = new Date().toISOString();
    assert.equal(ttlMsFor(route('/api/now/'), `CommonsMain/${today}`), 5_000);
  });

  test('Now: past date >24h ago is 6h', () => {
    assert.equal(ttlMsFor(route('/api/now/'), 'CommonsMain/2025-01-01T12:00:00Z'),
                 6 * 3600_000);
  });

  test('Members: search is 300s', () => {
    assert.equal(ttlMsFor(route('/api/members/'), 'Members/Search?Name=Cooper'),
                 300_000);
  });

  test('Members: Thumbnail is 1 day', () => {
    assert.equal(ttlMsFor(route('/api/members/'), 'Members/4514/Thumbnail'),
                 86_400_000);
  });

  test('Members: Portrait is 1 day', () => {
    assert.equal(ttlMsFor(route('/api/members/'), 'Members/4514/Portrait?cropType=ThreeFour'),
                 86_400_000);
  });

  test('Hansard: lastsittingdate is 600s', () => {
    assert.equal(ttlMsFor(route('/api/hansard/'), 'overview/lastsittingdate.json?house=Commons'),
                 600_000);
  });

  test('Hansard: calendar is 1h', () => {
    assert.equal(ttlMsFor(route('/api/hansard/'), 'overview/calendar.json?...'),
                 3600_000);
  });

  test('Hansard: debate text is 1 day (effectively immutable)', () => {
    assert.equal(ttlMsFor(route('/api/hansard/'), 'debates/debate/abc-123.json'),
                 86_400_000);
  });

  test('Hansard: search is 60s (cheap, frequently called)', () => {
    assert.equal(ttlMsFor(route('/api/hansard/'), 'search.json?queryParameters.searchTerm=x'),
                 60_000);
  });

  test('cvotes: division/<id>.json is 1 day (immutable recorded vote)', () => {
    assert.equal(ttlMsFor(route('/api/cvotes/'), 'division/2347.json'),
                 86_400_000);
  });
});

// ---------------------------------------------------------------------------
// buildUpstreamUrl
// ---------------------------------------------------------------------------

describe('buildUpstreamUrl', () => {
  test('non-exact route: appends tail and search', () => {
    const r = ROUTES.find(x => x.prefix === '/api/members/');
    const url = buildUpstreamUrl(r, 'Members/Search', '?Name=Cooper');
    assert.equal(url, 'https://members-api.parliament.uk/api/Members/Search?Name=Cooper');
  });

  test('exact route (sparql): ignores tail, keeps search', () => {
    const r = ROUTES.find(x => x.prefix === '/api/sparql');
    const url = buildUpstreamUrl(r, '', '?query=SELECT+%2A');
    assert.equal(url, 'https://api.parliament.uk/sparql?query=SELECT+%2A');
  });
});

// ---------------------------------------------------------------------------
// Integration: spawn the server, hit it, verify auth + CORS + static.
// No upstream calls — every endpoint here short-circuits before reaching
// parliament.uk.
// ---------------------------------------------------------------------------

describe('integration', { concurrency: false }, () => {
  let proc, baseUrl;

  before(async () => {
    const port = 9000 + Math.floor(Math.random() * 200);
    baseUrl = `http://127.0.0.1:${port}`;
    proc = spawn(process.execPath, [SERVER], {
      env: { ...process.env, PORT: String(port), HOST: '127.0.0.1', PROXY_PASSWORD: 'testpw' },
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    // Wait for the server to advertise readiness.
    await new Promise((resolve, reject) => {
      const t = setTimeout(() => reject(new Error('server boot timeout')), 5000);
      proc.stdout.on('data', (chunk) => {
        if (String(chunk).includes('listening on')) {
          clearTimeout(t); resolve();
        }
      });
      proc.stderr.on('data', (c) => { /* swallow noise */ });
    });
  });

  after(() => {
    if (proc && !proc.killed) proc.kill('SIGTERM');
  });

  test('/_health: 200 + authRequired:true', async () => {
    const r = await fetch(`${baseUrl}/_health`);
    assert.equal(r.status, 200);
    const j = await r.json();
    assert.equal(j.ok, true);
    assert.equal(j.authRequired, true);
  });

  test('CORS preflight on /api/* returns 204 with allow headers', async () => {
    const r = await fetch(`${baseUrl}/api/now/CommonsMain/current`, {
      method: 'OPTIONS',
      headers: {
        'origin': 'https://example.com',
        'access-control-request-method': 'GET',
      },
    });
    assert.equal(r.status, 204);
    assert.equal(r.headers.get('access-control-allow-origin'), '*');
    assert.match(r.headers.get('access-control-allow-methods'), /GET/);
  });

  test('OPL attribution header is on every response', async () => {
    const r = await fetch(`${baseUrl}/_health`);
    const attrib = r.headers.get('x-attribution') || '';
    assert.match(attrib, /Open Parliament Licence v3\.0/);
  });

  test('/api/* without auth: 401', async () => {
    const r = await fetch(`${baseUrl}/api/now/CommonsMain/current`);
    assert.equal(r.status, 401);
  });

  test('/api/* with wrong bearer: 401', async () => {
    const r = await fetch(`${baseUrl}/api/now/CommonsMain/current`, {
      headers: { authorization: 'Bearer notthepassword' },
    });
    assert.equal(r.status, 401);
  });

  test('/_cache requires auth', async () => {
    const r1 = await fetch(`${baseUrl}/_cache`);
    assert.equal(r1.status, 401);
    const r2 = await fetch(`${baseUrl}/_cache`, {
      headers: { authorization: 'Bearer testpw' },
    });
    assert.equal(r2.status, 200);
    const j = await r2.json();
    assert.ok(Array.isArray(j.entries));
  });

  test('static index.html is served with no-cache', async () => {
    const r = await fetch(`${baseUrl}/`);
    assert.equal(r.status, 200);
    assert.match(r.headers.get('content-type'), /text\/html/);
    assert.match(r.headers.get('cache-control') || '', /no-cache/);
    const body = await r.text();
    assert.match(body, /Forgetmeknot Palace/);
  });

  test('cookie auth equivalent to bearer', async () => {
    // /_cache reaches no upstream — clean test of just the auth path.
    const r = await fetch(`${baseUrl}/_cache`, {
      headers: { cookie: 'fpkg_auth=testpw' },
    });
    assert.equal(r.status, 200);
  });

  test('non-GET method on /api/* returns 405', async () => {
    const r = await fetch(`${baseUrl}/api/now/CommonsMain/current`, {
      method: 'POST',
      headers: { authorization: 'Bearer testpw' },
    });
    assert.equal(r.status, 405);
  });
});
