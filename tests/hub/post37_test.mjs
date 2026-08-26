// Pins every live cell in docs/web/hub/37-from-the-registry.md.
//
// Unlike every other hub post test, this one does NOT run its cells
// against npm/factoidal (the in-repo copy). Its whole point is to
// exercise the ACTUAL @factoidal/core@0.1.0 tarball published to
// https://registry.npmjs.org -- so this file `npm pack`s that exact
// spec from the real registry into a scratch temp directory, imports
// THAT package's own index.mjs, and wires it into the post's
// `fn.loadRegistryPackage("0.1.0")` binding (post24's browser-vs-test
// duality pattern: docs/_includes/hub.njk's browser-side
// `loadRegistryPackage` dynamic-`import()`s the package from a CDN;
// this Node-side binding dynamic-`import()`s the SAME package from a
// local npm-pack extraction instead -- same external contract, same
// pinned cell source, different transport).
//
// If the registry is unreachable (offline sandbox, DNS failure, npm
// pack error), every data-dependent test SKIPS with the underlying
// error message -- it must never silently pass on a registry that was
// never actually reached.
//
// The `fn` binding is still the real npm/factoidal typed API (the
// same-origin side of the post's cross-check cell); `Factoidal` is a
// tiny shim exposing just `.version`, matching what
// docs/_includes/hub.njk's module-scope `Factoidal` binding (the raw
// browser.js import) exposes as a plain string constant.
//
// Bundle-env isolation: importing '../_helpers.mjs' (below) sets
// FACTOIDAL_JS_BUNDLE / FACTOIDAL_NPM_ENTRY (and their wasm twins) to
// point at THIS REPO's freshest build (docs/fstar-extracted/) so the
// same-origin `fn`/`Factoidal` side always runs the build of record.
// Those are process-wide env vars, and the temp-installed registry
// package's own engine/entry-bundle resolution (npm/factoidal/lib/
// engine-js.js's resolveBundlePath(), re-read on EVERY call) would
// otherwise pick up the SAME env vars and silently run the REPO's
// bundle instead of the package it actually ships -- defeating the
// entire point of this test. withClearedBundleEnv() wraps every call
// that reaches into the registry package's engine so those four env
// vars are unset only for the duration of that one call, then
// restored immediately afterward for the same-origin side.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.join(__dirname, '..', '..');
const POST_FILE = '37-from-the-registry.md';
const PKG_VERSION = '0.1.0';
const PKG_SPEC = `@factoidal/core@${PKG_VERSION}`;
const REGISTRY_URL = 'https://registry.npmjs.org';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const Factoidal = { version: factoidal.version };

const cells = extractObservableCells(POST_FILE);

// --- Fetch the REAL published tarball into a scratch temp dir --------

let TMP_DIR = null;
let PKG_DIR = null;
let SKIP_REASON = null;

try {
  TMP_DIR = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-registry-'));
  execFileSync('npm', [
    'pack', PKG_SPEC,
    '--registry', REGISTRY_URL,
    '--pack-destination', TMP_DIR,
    '--ignore-scripts',
  ], { stdio: ['ignore', 'pipe', 'pipe'], timeout: 60000 });

  const tarball = fs.readdirSync(TMP_DIR).find((f) => f.endsWith('.tgz'));
  if (!tarball) throw new Error('npm pack produced no .tgz file');

  execFileSync('tar', ['-xzf', path.join(TMP_DIR, tarball), '-C', TMP_DIR], { timeout: 30000 });
  PKG_DIR = path.join(TMP_DIR, 'package');
  if (!fs.existsSync(path.join(PKG_DIR, 'index.mjs'))) {
    throw new Error(`extracted tarball has no index.mjs under ${PKG_DIR}`);
  }
} catch (err) {
  SKIP_REASON = `registry unreachable or npm pack failed for ${PKG_SPEC} ` +
    `from ${REGISTRY_URL}: ${(err && err.message) || err}`;
}

test.after(() => {
  if (TMP_DIR) fs.rmSync(TMP_DIR, { recursive: true, force: true });
});

// --- Provenance: the installed tarball's own gitSha must be reachable
//     from this checkout's HEAD (proves what you install was actually
//     built from THIS repo's history, not a fork or tampered mirror).

let PKG_VERSION_JSON = null;
if (!SKIP_REASON) {
  try {
    PKG_VERSION_JSON = JSON.parse(
      fs.readFileSync(path.join(PKG_DIR, 'version.json'), 'utf8'));
  } catch (err) {
    SKIP_REASON = `installed tarball has no readable version.json: ${err.message}`;
  }
}

test('post37: installed tarball version.json gitSha is an ancestor of (or equal to) HEAD',
  { skip: SKIP_REASON || undefined },
  (t) => {
    assert.ok(PKG_VERSION_JSON && typeof PKG_VERSION_JSON.gitSha === 'string' &&
      /^[0-9a-f]{40}$/.test(PKG_VERSION_JSON.gitSha),
      `expected a 40-hex-char gitSha in version.json, got ${JSON.stringify(PKG_VERSION_JSON)}`);
    // A SHALLOW clone cannot answer this. `git merge-base --is-ancestor`
    // fails when either commit is beyond a graft boundary, and the
    // failure is indistinguishable from a real "not an ancestor". CI
    // runners and container clones are routinely shallow, so asserting
    // here reports the clone's depth as a version.json defect.
    //
    // Measured 2026-08-26: this test failed in a shallow container for a
    // gitSha that IS an ancestor of claude/main -- confirmed by resolving
    // the objects directly once they were present. Five hub tests failed
    // that way and none of them was a real finding.
    //
    // So: check shallowness first and SKIP with a reason. A test that
    // cannot see the thing it asserts must say so, not fail.
    const isShallow = execFileSync('git', ['rev-parse', '--is-shallow-repository'],
      { cwd: REPO_ROOT, encoding: 'utf8' }).trim() === 'true';
    const haveObject = (() => {
      try {
        execFileSync('git', ['cat-file', '-e', PKG_VERSION_JSON.gitSha],
          { cwd: REPO_ROOT, stdio: 'pipe' });
        return true;
      } catch { return false; }
    })();
    if (isShallow && !haveObject) {
      t.skip(`shallow clone: ${PKG_VERSION_JSON.gitSha.slice(0, 12)} is beyond the ` +
        'graft boundary, so ancestry is unanswerable here. Re-run with full history.');
      return;
    }
    // Throws if NOT an ancestor -- that IS the assertion.
    execFileSync('git', ['merge-base', '--is-ancestor', PKG_VERSION_JSON.gitSha, 'HEAD'],
      { cwd: REPO_ROOT, stdio: 'pipe' });
  });

// --- Bundle-env isolation (see file header) ---------------------------

const REGISTRY_ENV_KEYS = [
  'FACTOIDAL_JS_BUNDLE', 'FACTOIDAL_WASM_BUNDLE',
  'FACTOIDAL_NPM_ENTRY', 'FACTOIDAL_NPM_ENTRY_WASM',
];

function withClearedBundleEnv(rawFn) {
  return async (...args) => {
    const saved = {};
    for (const k of REGISTRY_ENV_KEYS) { saved[k] = process.env[k]; delete process.env[k]; }
    try {
      return await rawFn(...args);
    } finally {
      for (const k of REGISTRY_ENV_KEYS) {
        if (saved[k] !== undefined) process.env[k] = saved[k];
      }
    }
  };
}

// --- Node-side `fn.loadRegistryPackage` -- the browser-vs-test twin of
//     docs/_includes/hub.njk's dynamic-import()-from-a-CDN wrapper.

async function loadRegistryPackage(version) {
  if (SKIP_REASON) throw new Error(SKIP_REASON);
  assert.equal(version, PKG_VERSION, 'test only pins one registry version');
  const modUrl = pathToFileURL(path.join(PKG_DIR, 'index.mjs')).href;
  const raw = (await import(modUrl)).default;
  return {
    version: raw.version,
    parse: withClearedBundleEnv(raw.parse),
    query: withClearedBundleEnv(raw.query),
    canonicalize: withClearedBundleEnv(raw.canonicalize),
    registerExtensionFunction: withClearedBundleEnv(raw.registerExtensionFunction),
  };
}

const fn = { ...factoidal, loadRegistryPackage };
const B = { fn, Factoidal, pretty };

test('post37: post has 9 live cells', () => {
  assert.equal(cells.length, 9, `expected 9 live cells, found ${cells.length}`);
});

test('post37 cell 0 (registry): loads @factoidal/core@0.1.0 from the real registry',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const registry = await post.value(post.names[0]);
    assert.equal(registry.unavailable, undefined,
      `expected the registry package to load; got ${JSON.stringify(registry)}`);
    assert.equal(registry.version, PKG_VERSION);
    assert.equal(typeof registry.parse, 'function');
    assert.equal(typeof registry.query, 'function');
    assert.equal(typeof registry.canonicalize, 'function');
    assert.equal(typeof registry.registerExtensionFunction, 'function');
  });

test('post37 cell 1 (versions): registry version matches the published 0.1.0, distinct from the same-origin binding only in name not value',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const versions = await post.value(post.names[1]);
    assert.equal(versions.registryPackageVersion, PKG_VERSION);
    assert.equal(versions.registryStatus, 'loaded from the npm registry CDN');
    assert.equal(versions.siteBundleVersion, Factoidal.version);
  });

test('post37 cell 3 (registryDataset): 4 triples parsed through the registry module',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const dataset = await post.value(post.names[3]);
    assert.equal(dataset.unavailable, undefined);
    assert.equal(dataset.size, 4);
  });

test('post37 cell 4 (SELECT via registry): alice(30) then bob(7)',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const table = await post.value(post.names[4]);
    assert.equal(table.kind, 'table');
    assert.deepEqual(table.columns, ['s', 'age']);
    assert.equal(table.rows.length, 2);
    assert.ok(table.rows[0][0].endsWith('alice'), `row0 ${table.rows[0][0]}`);
    assert.ok(table.rows[1][0].endsWith('bob'), `row1 ${table.rows[1][0]}`);
  });

test('post37 cell 5 (ASK via registry): true (alice is >= 18)',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const answer = await post.value(post.names[5]);
    assert.equal(answer, true);
  });

test('post37 cell 6 (canonicalize via registry): 4 canonical N-Quads lines mentioning alice',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const canon = await post.value(post.names[6]);
    assert.equal(typeof canon, 'string');
    const lines = canon.split('\n').filter((l) => l.trim().length > 0);
    assert.equal(lines.length, 4, `expected 4 quads, got:\n${canon}`);
    assert.ok(canon.includes('Alice'), 'expected literal "Alice" in canonical output');
  });

test('post37 cell 7 (extension function via registry): fn:isAdult keeps only alice',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const table = await post.value(post.names[7]);
    assert.equal(table.kind, 'table');
    assert.equal(table.rows.length, 1);
    assert.ok(table.rows[0][0].endsWith('alice'));
  });

test('post37 cell 8 (cross-check): same-origin and registry query answers agree',
  { skip: SKIP_REASON || undefined },
  async () => {
    const post = runReactivePost(cells, B);
    const result = await post.value(post.names[8]);
    assert.equal(result.unavailable, undefined);
    assert.equal(result.agree, true, `rows diverged: ${JSON.stringify(result)}`);
    assert.equal(result.siteRows.length, 2);
    assert.equal(result.registryRows.length, 2);
  });
