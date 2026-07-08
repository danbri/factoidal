// Pins the live cells in docs/web/hub/18-the-durable-log-live.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed). Cell 1 uses the typed `fn` adapter now
// (`fn.parse`/`fn.update`/`fn.query`, same as post17_test.mjs) --
// `fn` here is the real npm/factoidal typed API. Cells 2-4
// additionally exercise `Factoidal.deltaLogOpen`/`deltaLogAppend`/
// `deltaLogReadAllHex`/`deltaLogMerge`/`deltaLogDestroy`/
// `_deltaLogCorruptLastForTest` -- but Node has no global `indexedDB`,
// so this file follows the "direct-ABI" half of npm/factoidal/test/
// delta-log.test.js's approach: rather than pull in a fake-indexeddb
// dependency (out of territory -- no engine/npm changes), it swaps the
// browser.js's real IndexedDB-backed storage layer for a plain
// in-memory Map, while still routing every byte decision through the
// REAL factoidalNpmEntry ABI's `deltaBatchToHex`/`deltaMergeApplyBrowser`
// -- the same F*-verified RDF_Store_Columnar_DeltaLog/DeltaMerge
// functions the real browser.js calls. Only the storage medium is
// swapped; the cell source pinned below is executed completely
// unmodified (extractObservableCells() + runObservableCell(), the
// same discipline every other post's tests use).

import { createRequire } from 'node:module';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);
const POST_FILE = '18-the-durable-log-live.md';
const REPO_ROOT = path.join(__dirname, '..', '..');

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

/**
 * A test-only stand-in for npm/factoidal/browser.js's deltaLog* export
 * surface: same external contract (same method names, same argument
 * shapes, same return shapes), backed by a plain in-memory Map instead
 * of real IndexedDB. Every byte decision still flows through the real
 * `abi.deltaBatchToHex`/`abi.deltaMergeApplyBrowser` -- this stub only
 * replaces "put a record in an IndexedDB object store" with "push an
 * object into an array."
 */
function makeFactoidalStub() {
  const stores = new Map(); // dbName -> [{seq, epoch, hex}]
  function storeFor(dbName) {
    if (!stores.has(dbName)) stores.set(dbName, []);
    return stores.get(dbName);
  }
  return {
    async loadNpmEntry() {
      return abi;
    },
    async deltaLogOpen(dbName) {
      storeFor(dbName);
      return { dbName };
    },
    async deltaLogAppend(handle, sparqlUpdate, options) {
      if (!handle || typeof handle.dbName !== 'string') {
        throw new TypeError('deltaLogAppend: handle must be the object deltaLogOpen() returned');
      }
      const opts = options || {};
      const epoch = opts.epoch || 0;
      const records = storeFor(handle.dbName);
      const seq = records.length;
      const parsed = JSON.parse(abi.deltaBatchToHex(sparqlUpdate, String(seq), String(epoch)));
      if (!parsed.ok) throw new Error(parsed.error || 'deltaBatchToHex failed');
      records.push({ seq, epoch, hex: parsed.hex });
      return { seq, opCount: parsed.opCount };
    },
    async deltaLogReadAllHex(handle) {
      const records = storeFor(handle.dbName).slice().sort((a, b) => a.seq - b.seq);
      return records.map((r) => r.hex).join('\n');
    },
    async deltaLogMerge(handle, baseNQuads) {
      const hexBlobs = await this.deltaLogReadAllHex(handle);
      const parsed = JSON.parse(abi.deltaMergeApplyBrowser(baseNQuads, hexBlobs));
      if (!parsed.ok) throw new Error(parsed.error || 'deltaMergeApplyBrowser failed');
      return parsed.nquads;
    },
    async deltaLogDestroy(handle) {
      stores.delete(handle.dbName);
    },
    async _deltaLogCorruptLastForTest(handle) {
      const records = storeFor(handle.dbName).slice().sort((a, b) => a.seq - b.seq);
      if (records.length === 0) return false;
      const last = records[records.length - 1];
      last.hex = last.hex.slice(0, Math.max(0, last.hex.length - 8));
      return true;
    },
  };
}

const cells = extractObservableCells(POST_FILE);

test('post18: post has at least 5 live cells (4 lifecycle steps + the runtimes table)', () => {
  assert.ok(cells.length >= 5, `expected >= 5 live cells, found ${cells.length}`);
});

test('post18 cell 1 (parse + in-memory UPDATE): Carol appears alongside Alice/Bob', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.deepEqual(result.namesAfterInsert, ['Alice', 'Bob', 'Carol']);
});

test('post18 cell 1 degrades gracefully when the npm-entry bundle is unavailable', async () => {
  const brokenFn = {
    parse: factoidal.parse,
    async update() {
      throw new Error('update needs the factoidal-npm-entry bundle, which is not present');
    },
    query: factoidal.query,
  };
  const result = await runObservableCell(cells[0], { fn: brokenFn, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /npm-entry bundle/);
});

test('post18 cell 2 (deltaLogAppend): seq starts at 0 in a fresh store, opCount is 1', async () => {
  const Factoidal = makeFactoidalStub();
  const result = await runObservableCell(cells[1], { Factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.equal(result.seq, 0);
  assert.equal(result.opCount, 1);
});

test('post18 cell 2: seq keeps climbing across repeated runs against the SAME store (the reload proof, in miniature)', async () => {
  const Factoidal = makeFactoidalStub();
  const r0 = await runObservableCell(cells[1], { Factoidal, pretty });
  const r1 = await runObservableCell(cells[1], { Factoidal, pretty });
  const r2 = await runObservableCell(cells[1], { Factoidal, pretty });
  assert.deepEqual([r0.seq, r1.seq, r2.seq], [0, 1, 2]);
});

test('post18 cell 2 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async loadNpmEntry() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
    async deltaLogOpen(dbName) {
      return { dbName };
    },
    async deltaLogAppend() {
      // deltaLogAppend calls loadNpmEntry() itself in the real
      // implementation; the stub used elsewhere in this file does
      // too (via `abi`), so a broken loadNpmEntry should surface here.
      const e = new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
      throw e;
    },
  };
  const result = await runObservableCell(cells[1], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

test('post18 cell 3 (deltaLogMerge, after cell 2 appended): reads the batch back and merges it', async () => {
  const Factoidal = makeFactoidalStub();
  await runObservableCell(cells[1], { Factoidal, pretty }); // Step 2 first, same store.
  const result = await runObservableCell(cells[2], { Factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.equal(result.batchesInLog, 1);
  assert.equal(result.containsDana, true);
  assert.ok(Array.isArray(result.mergedPreview));
});

test('post18 cell 3 on a store cell 2 never touched: batchesInLog is 0, containsDana is false (no crash on an empty log)', async () => {
  const Factoidal = makeFactoidalStub();
  const result = await runObservableCell(cells[2], { Factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.equal(result.batchesInLog, 0);
  assert.equal(result.containsDana, false);
});

test('post18 cell 3 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async deltaLogOpen(dbName) {
      return { dbName };
    },
    async deltaLogReadAllHex() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
    async deltaLogMerge() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
  };
  const result = await runObservableCell(cells[2], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

test('post18 cell 4 (torn write): Eve survives, Frank is lost to the corrupted last batch', async () => {
  const Factoidal = makeFactoidalStub();
  const result = await runObservableCell(cells[3], { Factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.equal(result.corruptedARecord, true);
  assert.equal(result.eveSurvivesCorruption, true);
  assert.equal(result.frankWasLostToCorruption, true);
});

test('post18 cell 4 is self-contained: running it twice in a row still reports the same clean-prefix-survives outcome', async () => {
  const Factoidal = makeFactoidalStub();
  const r0 = await runObservableCell(cells[3], { Factoidal, pretty });
  const r1 = await runObservableCell(cells[3], { Factoidal, pretty });
  assert.equal(r0.eveSurvivesCorruption, true);
  assert.equal(r1.eveSurvivesCorruption, true);
  assert.equal(r0.frankWasLostToCorruption, true);
  assert.equal(r1.frankWasLostToCorruption, true);
});

test('post18 cell 4 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async deltaLogDestroy() {},
    async deltaLogOpen(dbName) {
      return { dbName };
    },
    async deltaLogAppend() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
  };
  const result = await runObservableCell(cells[3], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

test('post18 cell 5 (the runtimes pretty() table): four rows, native/js/C/wasm in that order, wasm now proven too', async () => {
  const Factoidal = makeFactoidalStub();
  const result = await runObservableCell(cells[4], { Factoidal, pretty });
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['runtime', 'proves', 'evidence', 'landed']);
  assert.equal(result.rows.length, 4);
  const runtimes = result.rows.map((r) => r[0]);
  assert.deepEqual(runtimes, [
    'Native (OCaml)', 'JavaScript (js_of_ocaml)', 'C (KaRaMeL)', 'WebAssembly (wasm_of_ocaml)',
  ]);
  const wasmRow = result.rows[3];
  assert.doesNotMatch(wasmRow[1], /nothing yet/i,
    'the wasm row was rebuilt to include DeltaLog/DeltaMerge -- update this assertion, not revert the rebuild, if it fails');
});

// ---------------------------------------------------------------------
// Direct checks on the prose claims: the five assume vals, the four
// realisations, the C demo transcript's provenance, the BaseWriter
// honesty section, and the cited commits/files all read from the real
// tree rather than typed from memory.
// ---------------------------------------------------------------------

test('post18: RDF.Store.Columnar.DeltaLog.fst declares exactly five ML-effect I/O assume vals', () => {
  const src = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.Store.Columnar.DeltaLog.fst'), 'utf8');
  const assumeVals = [...src.matchAll(/^assume val (\w+)/gm)].map((m) => m[1]);
  assert.deepEqual(
    assumeVals.sort(),
    ['atomic_rename', 'delta_log_append', 'delta_log_fsync', 'delta_log_read_all', 'fsync_dir'].sort(),
  );
});

test('post18: the native realisation of the five delta-log I/O assume vals exists (issue #282 patch)', () => {
  const p = path.join(
    REPO_ROOT, 'formal', 'fstar', 'minimal_regrettable_glue_code_each_with_an_open_issue',
    '282_delta_log_io.sh');
  assert.ok(fs.existsSync(p), 'expected the #282 delta-log I/O patch to exist');
});

test('post18: browser.js exports the delta-log persistence surface this post\'s cells call', () => {
  const browserJs = fs.readFileSync(
    path.join(REPO_ROOT, 'npm', 'factoidal', 'browser.js'), 'utf8');
  for (const fn of [
    'deltaLogOpen', 'deltaLogAppend', 'deltaLogReadAllHex', 'deltaLogMerge',
    'deltaLogDestroy', '_deltaLogCorruptLastForTest',
  ]) {
    assert.match(browserJs, new RegExp(`export async function ${fn}\\(`), `expected browser.js to export ${fn}`);
  }
});

test('post18: entry_jsoo.ml exports the delta-log ABI AND the toCottas BaseWriter write path (grounds the "base-store write path reaches the browser too" section)', () => {
  const entry = fs.readFileSync(
    path.join(REPO_ROOT, 'bin', 'npm-entry', 'entry_jsoo.ml'), 'utf8');
  assert.match(entry, /"deltaBatchToHex"/);
  assert.match(entry, /"deltaMergeApplyBrowser"/);
  // toCottas was added since an earlier version of this post claimed
  // no BaseWriter existed in the browser. It now does: the export wraps
  // the same pure-Tot serializer the native CLI uses.
  assert.match(entry, /"toCottas"/);
  assert.match(entry, /RDF_CottasStore_BaseWriter\.serialize_cottas_v2/);
});

test('post18: RDF.CottasStore.BaseWriter.fst exists and is the module the zero-Python claim cites', () => {
  const p = path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.CottasStore.BaseWriter.fst');
  assert.ok(fs.existsSync(p), 'expected RDF.CottasStore.BaseWriter.fst to exist');
});

test('post18: the wasm npm-entry bundle now contains the delta-log exports (grounds the "wasm now proven too" update)', () => {
  const wasmCandidates = [
    path.join(REPO_ROOT, 'docs', 'npm', 'foafos', 'factoidal-npm-entry.wasm.js'),
    path.join(REPO_ROOT, 'npm', 'factoidal', 'factoidal-npm-entry.wasm.js'),
  ];
  const wasmPath = wasmCandidates.find((p) => fs.existsSync(p));
  assert.ok(wasmPath, `expected one of ${wasmCandidates.join(', ')} to exist`);
  const wasmSrc = fs.readFileSync(wasmPath, 'utf8');
  assert.match(wasmSrc, /deltaBatchToHex/);
  assert.match(wasmSrc, /deltaMergeApplyBrowser/);
});

test('post18: the js npm-entry bundle DOES contain the delta-log exports (the contrapositive of the wasm check above)', () => {
  const jsCandidates = [
    path.join(REPO_ROOT, 'docs', 'npm', 'foafos', 'factoidal-npm-entry.js'),
    path.join(REPO_ROOT, 'npm', 'factoidal', 'factoidal-npm-entry.js'),
  ];
  const jsPath = jsCandidates.find((p) => fs.existsSync(p));
  assert.ok(jsPath, `expected one of ${jsCandidates.join(', ')} to exist`);
  const jsSrc = fs.readFileSync(jsPath, 'utf8');
  assert.match(jsSrc, /deltaBatchToHex/);
  assert.match(jsSrc, /deltaMergeApplyBrowser/);
});

test('post18: the C demo transcript quoted in this post is real (formal/fstar/c-output/deltalog/demo/delta_log_demo)', () => {
  const demoBin = path.join(
    REPO_ROOT, 'formal', 'fstar', 'c-output', 'deltalog', 'demo', 'delta_log_demo');
  assert.ok(fs.existsSync(demoBin), 'expected the compiled C delta-log demo binary to exist');
  const { execFileSync } = require('node:child_process');
  const out = execFileSync(demoBin, { cwd: path.dirname(demoBin) }).toString();
  assert.match(out, /All checks passed/);
  assert.match(out, /parse_delta_batch\(corrupted bytes\) = None \(checksum rejects it\)\s+OK/);
});

test('post18: the KaRaMeL C output directory this post links to exists', () => {
  const dir = path.join(REPO_ROOT, 'formal', 'fstar', 'c-output', 'deltalog');
  assert.ok(fs.existsSync(path.join(dir, 'Factoidal_DeltaLog.c')));
  assert.ok(fs.existsSync(path.join(dir, 'Factoidal_DeltaLog.h')));
});

test('post18: the delta-log merge correspondence lemma this post cites is present (same lemma post17 cites)', () => {
  const deltaMerge = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.Store.Columnar.DeltaMerge.fst'), 'utf8');
  assert.match(deltaMerge, /lemma_merge_on_read_matches_apply_entries/);
});

test('post18: the commits cited in this post are real, reachable commits', () => {
  const { execFileSync } = require('node:child_process');
  for (const sha of ['8ff60eb', 'bd9e5be', '4f8fc95', 'e8085da']) {
    const out = execFileSync('git', ['cat-file', '-t', sha], { cwd: REPO_ROOT }).toString().trim();
    assert.equal(out, 'commit', `expected ${sha} to be a commit reachable in this repo`);
  }
});

test('post18: the zero-Python DuckDB verdict quoted in this post matches the real commit message', () => {
  const { execFileSync } = require('node:child_process');
  const msg = execFileSync('git', ['log', '-1', '--format=%B', '4f8fc95'], { cwd: REPO_ROOT }).toString();
  assert.match(msg, /DuckDB verdict: ACCEPTED byte-exact on 5-quad, 6,780-quad,\s+and\s+888,949-quad corpora/);
  assert.match(msg, /0 missing, 0 extra vs source/);
});
