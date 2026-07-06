// Unit tests for the in-memory COTTAS bytes store npm-entry ABI
// additions (docs/designissues/2026-07-06-inmemory-bytes-store.md,
// stage 5 "the browser call site"): bin/npm-entry/entry_jsoo.ml's
// `openCottas` / `queryCottas` / `closeCottas` / `toCottas` exports.
//
// Two layers are exercised:
//   1. The raw ABI (JSON in/out), same style as delta-log.test.js.
//   2. index.js's Dataset-shaped wrappers (openCottas/queryCottas/
//      closeCottas/toCottas), which the fn.js / lib/api.js layer
//      builds on.
//
// Correctness is checked by BYTE/VALUE comparison against the SAME
// data parsed into the heap store (index.js's parse()/query()) from
// the source N-Quads the fixture COTTAS artifact was built from
// (tests/local/data/cottas_sample.nq) -- proving the bytes-store
// answers match the heap-store answers for the same underlying data,
// not just "some answer came back".

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const engine = require('..'); // index.js (heap-store + npm-entry ABI)

const PENDING = 'pending npm-entry build (openCottas/queryCottas/closeCottas/toCottas)';

const FIXTURE_COTTAS = path.resolve(
  __dirname, '..', '..', '..', 'tests', 'unit', 'fixtures',
  'store_capabilities_sample.cottas');
const FIXTURE_NQ = path.resolve(
  __dirname, '..', '..', '..', 'tests', 'local', 'data', 'cottas_sample.nq');

function entryCandidates() {
  const c = [];
  if (process.env.FACTOIDAL_NPM_ENTRY) c.push(process.env.FACTOIDAL_NPM_ENTRY);
  c.push(path.join(__dirname, '..', 'factoidal-npm-entry.js'));
  c.push(path.resolve(__dirname, '..', '..', '..', 'docs', 'fstar-extracted', 'factoidal-npm-entry.js'));
  return c;
}

function loadAbi() {
  for (const p of entryCandidates()) {
    if (!p || !fs.existsSync(p)) continue;
    const mod = require(p);
    const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
    if (abi && typeof abi.openCottas === 'function') return abi;
  }
  return null;
}

const abi = loadAbi();
const haveFixtures = fs.existsSync(FIXTURE_COTTAS) && fs.existsSync(FIXTURE_NQ);
const skip = !abi ? PENDING : (!haveFixtures ? 'fixture .cottas/.nq not found' : false);

function hexOfBuffer(buf) {
  return Buffer.from(buf).toString('hex');
}

// ---------------------------------------------------------------------
// Layer 1: raw ABI
// ---------------------------------------------------------------------

test('openCottas + queryCottas (raw ABI): COUNT/ASK/SELECT match the fixture\'s known content', { skip }, () => {
  const bytes = fs.readFileSync(FIXTURE_COTTAS);
  const opened = JSON.parse(abi.openCottas(hexOfBuffer(bytes)));
  assert.equal(opened.ok, true, JSON.stringify(opened));
  const handle = opened.handle;
  assert.match(handle, /^npmcottas:\d+$/);

  // Default graph only: 1 triple (tests/local/data/cottas_sample.nq's
  // lone default-graph line).
  const countDefault = JSON.parse(
    abi.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'));
  assert.equal(countDefault.ok, true, JSON.stringify(countDefault));
  assert.equal(countDefault.kind, 'select');
  assert.equal(countDefault.srj.results.bindings[0].c.value, '1');

  // Named graphs: 4 triples (2 in graph/people, 1 in graph/docs... wait
  // fixture has 3 in graph/people + 1 in graph/docs = 4).
  const countNamed = JSON.parse(
    abi.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }'));
  assert.equal(countNamed.ok, true, JSON.stringify(countNamed));
  assert.equal(countNamed.srj.results.bindings[0].c.value, '4');

  const ask = JSON.parse(abi.queryCottas(handle,
    'ASK { <https://example.org/default-subject> <https://example.org/status> "default" }'));
  assert.equal(ask.ok, true, JSON.stringify(ask));
  assert.equal(ask.kind, 'ask');
  assert.equal(ask.boolean, true);

  const names = JSON.parse(abi.queryCottas(handle,
    'SELECT ?name WHERE { GRAPH <https://example.org/graph/people> { ?s <https://example.org/name> ?name } }'));
  assert.equal(names.ok, true, JSON.stringify(names));
  const nameValues = names.srj.results.bindings.map((b) => b.name.value).sort();
  assert.deepEqual(nameValues, ['Alice', 'Bob']);

  const closed = JSON.parse(abi.closeCottas(handle));
  assert.equal(closed.ok, true);

  // Handle is gone after close.
  const afterClose = JSON.parse(
    abi.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'));
  assert.equal(afterClose.ok, false);
  assert.match(afterClose.error, /unknown handle/i);
});

test('openCottas (raw ABI): garbage bytes open lazily (Bet7); the honest failure surfaces at the first queryCottas() touch', { skip }, () => {
  // cottas_ondisk_open is a lazy, footer-only open (issue Bet7): it does
  // not eagerly decode anything, so 4 junk bytes still open "successfully"
  // here -- this pins that documented behavior rather than asserting the
  // (incorrect) expectation that open itself validates the footer.
  const opened = JSON.parse(abi.openCottas('deadbeef'));
  assert.equal(opened.ok, true, JSON.stringify(opened));

  const queried = JSON.parse(
    abi.queryCottas(opened.handle, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'));
  assert.equal(queried.ok, false);
  assert.match(queried.error, /row-group|footer|Failure/i);
  abi.closeCottas(opened.handle);
});

test('openCottas (raw ABI): odd-length hex is rejected honestly', { skip }, () => {
  const bad = JSON.parse(abi.openCottas('abc'));
  assert.equal(bad.ok, false);
  assert.match(bad.error, /hex/i);
});

test('toCottas + openCottas (raw ABI): round-trip reproduces the same query answers', { skip }, () => {
  const nq = fs.readFileSync(FIXTURE_NQ, 'utf8');
  const written = JSON.parse(abi.toCottas(nq));
  assert.equal(written.ok, true, JSON.stringify(written));
  assert.equal(written.quadCount, 5);
  assert.match(written.cottasHex, /^[0-9a-f]+$/);

  const opened = JSON.parse(abi.openCottas(written.cottasHex));
  assert.equal(opened.ok, true, JSON.stringify(opened));
  const handle = opened.handle;

  const count = JSON.parse(
    abi.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }'));
  assert.equal(count.srj.results.bindings[0].c.value, '4');
  abi.closeCottas(handle);
});

test('queryCottas (raw ABI): CONSTRUCT materializes triples via the backend', { skip }, () => {
  const bytes = fs.readFileSync(FIXTURE_COTTAS);
  const handle = JSON.parse(abi.openCottas(hexOfBuffer(bytes))).handle;
  const r = JSON.parse(abi.queryCottas(handle, 'CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }'));
  assert.equal(r.ok, true, JSON.stringify(r));
  assert.equal(r.kind, 'construct');
  assert.match(r.nquads, /default-subject.*status.*"default"/s);
  abi.closeCottas(handle);
});

test('queryCottas (raw ABI): DESCRIBE is an honest ok:false, not a crash', { skip }, () => {
  const bytes = fs.readFileSync(FIXTURE_COTTAS);
  const handle = JSON.parse(abi.openCottas(hexOfBuffer(bytes))).handle;
  const r = JSON.parse(abi.queryCottas(handle, 'DESCRIBE <https://example.org/alice>'));
  assert.equal(r.ok, false);
  abi.closeCottas(handle);
});

// ---------------------------------------------------------------------
// Layer 2: index.js's Dataset-shaped wrappers, cross-checked against
// the heap store (parse()/query() over the same source N-Quads).
// ---------------------------------------------------------------------

test('index.js openCottas/queryCottas: SELECT/ASK/COUNT match the heap-store answers for the same data', { skip }, async () => {
  const nq = fs.readFileSync(FIXTURE_NQ, 'utf8');
  const bytes = fs.readFileSync(FIXTURE_COTTAS);

  // Heap store: parse the source N-Quads directly.
  const heapDs = await engine.parse(nq, { format: 'nquads' });
  const heapAsk = await engine.query(heapDs,
    'ASK { <https://example.org/default-subject> <https://example.org/status> "default" }');
  const heapNamedCount = await engine.query(heapDs,
    'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }');

  // Bytes store: open the pre-built COTTAS artifact for the same data.
  const handle = await engine.openCottas(bytes);
  const bytesAsk = await engine.queryCottas(handle,
    'ASK { <https://example.org/default-subject> <https://example.org/status> "default" }');
  const bytesNamedCount = await engine.queryCottas(handle,
    'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }');

  assert.equal(bytesAsk, heapAsk);
  assert.equal(bytesAsk, true);
  assert.equal(
    bytesNamedCount[0].get('c').value,
    heapNamedCount[0].get('c').value);
  assert.equal(bytesNamedCount[0].get('c').value, '4');

  await engine.closeCottas(handle);
});

test('index.js queryCottas: CONSTRUCT returns a Dataset equal (as a set) to the heap-store CONSTRUCT result', { skip }, async () => {
  const nq = fs.readFileSync(FIXTURE_NQ, 'utf8');
  const bytes = fs.readFileSync(FIXTURE_COTTAS);
  const q = 'CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }'; // default graph only

  const heapDs = await engine.parse(nq, { format: 'nquads' });
  const heapResult = await engine.query(heapDs, q);

  const handle = await engine.openCottas(bytes);
  const bytesResult = await engine.queryCottas(handle, q);
  await engine.closeCottas(handle);

  const norm = (ds) => [...ds].map((t) =>
    `${t.subject.value}|${t.predicate.value}|${t.object.value}`).sort();
  assert.deepEqual(norm(bytesResult), norm(heapResult));
});

test('index.js toCottas + openCottas: round-trip through the native writer preserves query answers', { skip }, async () => {
  const nq = fs.readFileSync(FIXTURE_NQ, 'utf8');
  const ds = await engine.parse(nq, { format: 'nquads' });
  const cottasBytes = await engine.toCottas(ds);
  assert.ok(cottasBytes instanceof Uint8Array);
  assert.ok(cottasBytes.length > 0);

  const handle = await engine.openCottas(cottasBytes);
  const count = await engine.queryCottas(handle,
    'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }');
  assert.equal(count[0].get('c').value, '4');
  await engine.closeCottas(handle);
});

test('index.js openCottas: rejects a handle after closeCottas()', { skip }, async () => {
  const bytes = fs.readFileSync(FIXTURE_COTTAS);
  const handle = await engine.openCottas(bytes);
  await engine.closeCottas(handle);
  await assert.rejects(
    () => engine.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'),
    /unknown handle/i);
});

test('index.js capabilities(): reports cottasBytesStore', { skip }, async () => {
  const caps = await engine.capabilities();
  assert.equal(caps.cottasBytesStore, true);
});
