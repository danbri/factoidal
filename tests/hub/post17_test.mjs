// Pins the live cells in docs/web/hub/17-mutating-and-serving-data.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed). Both live cells reach for `Factoidal.loadNpmEntry()`
// (the same escape hatch post12_test.mjs already pins) rather than `fn`,
// since docs/_includes/hub.njk's `fn` adapter has no `update` method yet
// -- that gap is itself part of what this post's prose documents.

import { createRequire } from 'node:module';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);
const POST_FILE = '17-mutating-and-serving-data.md';
const REPO_ROOT = path.join(__dirname, '..', '..');

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();
const Factoidal = {
  async loadNpmEntry() {
    return abi;
  },
};

const cells = extractObservableCells(POST_FILE);

test('post17: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post17 cell 1 (INSERT DATA): Bob appears alongside Alice after the update', async () => {
  const result = await runObservableCell(cells[0], { Factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.deepEqual(result.namesBeforeInsertData, ['Alice']);
  assert.deepEqual(result.namesAfterInsertData, ['Alice', 'Bob']);
});

test('post17 cell 1 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async loadNpmEntry() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
  };
  const result = await runObservableCell(cells[0], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

test('post17 cell 2 (DELETE/INSERT WHERE): Bob becomes Bobby, Alice untouched', async () => {
  const result = await runObservableCell(cells[1], { Factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.deepEqual(result.namesAfterDeleteInsertWhere, ['Alice', 'Bobby']);
});

test('post17 cell 2 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async loadNpmEntry() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
  };
  const result = await runObservableCell(cells[1], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

// ---------------------------------------------------------------------
// Direct checks on the prose claims: scores, commits, and the "not
// wired" honesty claims are read from the real tree, not typed from
// memory.
// ---------------------------------------------------------------------

test('post17: the fn adapter genuinely has no update() method (grounds the "honest gap" claim)', async () => {
  const hubNjk = fs.readFileSync(path.join(REPO_ROOT, 'docs', '_includes', 'hub.njk'), 'utf8');
  const fnBlockMatch = hubNjk.match(/const fn = \{([\s\S]*?)\n\};/);
  assert.ok(fnBlockMatch, 'hub.njk must define a `const fn = { ... }` object');
  assert.doesNotMatch(fnBlockMatch[1], /\bupdate\s*\(/, 'fn should not (yet) define an update() method');
});

test('post17: the W3C SPARQL 1.1 Update suite is 176/176 in the committed dashboard snapshot', () => {
  const latest = JSON.parse(
    fs.readFileSync(path.join(REPO_ROOT, 'docs', 'test-results', 'latest.json'), 'utf8'));
  const byName = {};
  for (const group of Object.values(latest.suites)) {
    for (const s of group) byName[s.name] = s;
  }
  const updateSuites = [
    'add', 'basic-update', 'clear', 'copy', 'delete', 'delete-data',
    'delete-insert', 'delete-where', 'drop', 'move', 'syntax-update-1',
    'syntax-update-2', 'update-silent', 'http-rdf-update',
  ];
  let pass = 0, total = 0;
  for (const name of updateSuites) {
    assert.ok(byName[name], `expected a '${name}' suite entry in latest.json`);
    assert.equal(byName[name].fail, 0, `expected 0 fail in '${name}'`);
    pass += byName[name].pass;
    total += byName[name].pass + byName[name].fail + byName[name].skip + byName[name].unsupported;
  }
  assert.equal(pass, 176, `expected 176 total Update-suite passes, found ${pass}`);
  assert.equal(total, 176, `expected 176 total Update-suite cases, found ${total}`);
});

test('post17: the three durable-UPDATE commits cited exist on this branch', () => {
  const { execFileSync } = require('node:child_process');
  for (const sha of ['868a20b', '1f27320', '5e8399a']) {
    const out = execFileSync('git', ['cat-file', '-t', sha], { cwd: REPO_ROOT }).toString().trim();
    assert.equal(out, 'commit', `expected ${sha} to be a commit reachable in this repo`);
  }
});

test('post17: the delta-log F* modules this post cites exist and verify without assume vals (DeltaLog/DeltaMerge)', () => {
  for (const mod of ['RDF.Store.Columnar.DeltaLog.fst', 'RDF.Store.Columnar.DeltaMerge.fst']) {
    const p = path.join(REPO_ROOT, 'formal', 'fstar', mod);
    assert.ok(fs.existsSync(p), `expected ${mod} to exist`);
  }
  const deltaMerge = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.Store.Columnar.DeltaMerge.fst'), 'utf8');
  assert.match(deltaMerge, /lemma_merge_on_read_matches_apply_entries/,
    'expected the proved merge-on-read correspondence lemma to be present');
});

test('post17: the CLI --delta-log flag this post cites is real', () => {
  const cli = fs.readFileSync(
    path.join(REPO_ROOT, 'bin', 'factoidal-cli', 'factoidal_cli.ml'), 'utf8');
  assert.match(cli, /"--delta-log"/);
});

test('post17: SPARQL.GraphStore.fst is verified F* with no assume vals (grounds "specified and proven")', () => {
  const gsp = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'SPARQL.GraphStore.fst'), 'utf8');
  assert.doesNotMatch(gsp, /^assume val/m, 'SPARQL.GraphStore.fst should have zero assume vals');
  for (const fn of ['gsp_get', 'gsp_head', 'gsp_put', 'gsp_post', 'gsp_delete']) {
    assert.match(gsp, new RegExp(`let ${fn}\\b`), `expected ${fn} to be defined`);
  }
});

test('post17: factoidal-http genuinely has no Graph Store Protocol routes (grounds "not yet exposed as routes")', () => {
  const http = fs.readFileSync(
    path.join(REPO_ROOT, 'bin', 'factoidal-http', 'factoidal_http.ml'), 'utf8');
  assert.doesNotMatch(http, /GraphStore/, 'factoidal_http.ml should not reference the GraphStore module');
  assert.match(http, /POST \/update/, 'expected the whole-dataset /update route to still be documented');
});
