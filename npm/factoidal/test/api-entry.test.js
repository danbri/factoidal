// factoidal/api — the bundler-friendly, CSP-safe entry point (issue
// https://github.com/danbri/factoidal/issues/682). createApi() wires
// lib/api.js's typed surface around an ALREADY-LOADED npm-entry ABI
// object: no fetch, no `new Function(src)` eval, so this is the route
// a page under `Content-Security-Policy: script-src 'self'` (and a
// bundler, which needs a statically importable module rather than a
// file to fetch) can use. See api.js's header comment and
// README.md's "Bundlers and Content Security Policy" section.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { createApi } = require('../api.js');
const indexEngine = require('../index.js');
const pkgVersion = require('../package.json').version;

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob" .
`;
const SELECT = `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name }
`;
const ASK = `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  PREFIX ex:   <http://example.org/>
  ASK { ex:alice foaf:knows ex:bob }
`;

function normRows(rows) {
  return rows
    .map((r) => [...r.entries()]
      .map(([k, v]) => `${k}=${v.termType}:${v.value}`)
      .sort()
      .join('|'))
    .sort();
}

test('createApi(entryMod.factoidalNpmEntry): parse/SELECT/ASK match index.js', async () => {
  const entryMod = require('../factoidal-npm-entry.js');
  const factoidal = createApi(entryMod.factoidalNpmEntry);

  const [entryDs, indexDs] = [await factoidal.parse(TTL), await indexEngine.parse(TTL)];
  assert.equal(entryDs.size, indexDs.size);
  assert.equal(await factoidal.serialize(entryDs), await indexEngine.serialize(indexDs));

  const [entryRows, indexRows] = [
    await factoidal.query(TTL, SELECT),
    await indexEngine.query(TTL, SELECT),
  ];
  assert.deepEqual(normRows(entryRows), normRows(indexRows));
  assert.ok(entryRows.length > 0, 'SELECT actually returned rows');

  assert.equal(await factoidal.query(TTL, ASK), await indexEngine.query(TTL, ASK));
  assert.equal(await factoidal.query(TTL, ASK), true);
});

test('createApi accepts a Promise of the entry object', async () => {
  const entryMod = require('../factoidal-npm-entry.js');
  const factoidal = createApi(Promise.resolve(entryMod.factoidalNpmEntry));
  const ds = await factoidal.parse(TTL);
  assert.equal(ds.size, (await indexEngine.parse(TTL)).size);
});

test('createApi accepts a zero-argument thunk returning the entry object', async () => {
  const entryMod = require('../factoidal-npm-entry.js');
  let calls = 0;
  const factoidal = createApi(() => {
    calls++;
    return entryMod.factoidalNpmEntry;
  });
  const ds = await factoidal.parse(TTL);
  assert.equal(ds.size, (await indexEngine.parse(TTL)).size);
  assert.equal(await factoidal.query(TTL, ASK), true);
  // buildApi's entry() caches after the first successful resolution --
  // the thunk should not be re-invoked on every call.
  assert.equal(calls, 1);
});

test('createApi accepts a thunk returning a Promise of the entry object', async () => {
  const entryMod = require('../factoidal-npm-entry.js');
  const factoidal = createApi(() => Promise.resolve(entryMod.factoidalNpmEntry));
  const ds = await factoidal.parse(TTL);
  assert.equal(ds.size, (await indexEngine.parse(TTL)).size);
});

test('createApi: an object without queryDataset throws a TypeError naming factoidalNpmEntry', () => {
  assert.throws(
    () => createApi({ notAnAbi: true }),
    (e) => e instanceof TypeError && /factoidalNpmEntry/.test(e.message));
});

test('createApi: null/undefined also throw a TypeError naming factoidalNpmEntry', () => {
  assert.throws(
    () => createApi(null),
    (e) => e instanceof TypeError && /factoidalNpmEntry/.test(e.message));
  assert.throws(
    () => createApi(undefined),
    (e) => e instanceof TypeError && /factoidalNpmEntry/.test(e.message));
});

test('createApi: entailment-regime queries and queryHdt reject with a clear message (no CLI bundle loaded)', async () => {
  const entryMod = require('../factoidal-npm-entry.js');
  const factoidal = createApi(entryMod.factoidalNpmEntry);
  await assert.rejects(
    () => factoidal.query(TTL, SELECT, { entail: 'RDFS' }),
    (e) => /CLI bundle .* not loaded/.test(e.message) &&
      /entailment-regime queries and queryHdt/.test(e.message));
  await assert.rejects(
    () => factoidal.queryHdt('', 'SELECT * WHERE { ?s ?p ?o }'),
    (e) => /CLI bundle .* not loaded/.test(e.message));
});

// --- version / engine on every driver's typed surface -----------------

test('version matches package.json: index.js', () => {
  assert.equal(indexEngine.version, pkgVersion);
});

test('version matches package.json: api.js (createApi)', () => {
  const entryMod = require('../factoidal-npm-entry.js');
  const factoidal = createApi(entryMod.factoidalNpmEntry);
  assert.equal(factoidal.version, pkgVersion);
});

test('version matches package.json: l4-core.js', () => {
  const l4core = require('../l4-core.js');
  assert.equal(l4core.version, pkgVersion);
});

test('version matches package.json: wasm.js', async (t) => {
  const NODE_MAJOR = Number(process.versions.node.split('.')[0]);
  if (NODE_MAJOR < 22) {
    t.skip(`Node ${process.versions.node} < 22 (WasmGC needed)`);
    return;
  }
  const wasmEngine = require('../wasm.js');
  if (!wasmEngine.wasmAvailable()) {
    t.skip('factoidal.wasm.js / .wasm asset not present ' +
      "(run 'build-ocaml.sh wasm-factoidal', then 'build-ocaml.sh npm')");
    return;
  }
  assert.equal(wasmEngine.version, pkgVersion);
});

test('engine field identifies the driver on every entry point', async (t) => {
  assert.equal(indexEngine.engine, 'js');
  assert.equal(require('../l4-core.js').engine, 'lean4-wasm');

  const entryMod = require('../factoidal-npm-entry.js');
  assert.equal(createApi(entryMod.factoidalNpmEntry).engine, 'entry');
  assert.equal(
    createApi(entryMod.factoidalNpmEntry, { engineName: 'entry-wasm' }).engine,
    'entry-wasm');

  const NODE_MAJOR = Number(process.versions.node.split('.')[0]);
  if (NODE_MAJOR < 22) {
    t.skip(`Node ${process.versions.node} < 22 (WasmGC needed)`);
    return;
  }
  const wasmEngine = require('../wasm.js');
  if (!wasmEngine.wasmAvailable()) {
    t.skip('factoidal.wasm.js / .wasm asset not present ' +
      "(run 'build-ocaml.sh wasm-factoidal', then 'build-ocaml.sh npm')");
    return;
  }
  assert.equal(wasmEngine.engine, 'wasm');
});
