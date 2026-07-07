// Pins every live cell in
// docs/web/hub/23-decentralized-identifiers-did-key.md.
//
// The post's cells call `Factoidal.didKeyResolve` (the raw browser.js
// export backed by the F*-extracted DID_Key.did_key_document) and the
// typed `fn` adapter (fn.parse / fn.query) over the N-Triples it
// returns. As with post12/post18, the Node-side `Factoidal` binding is
// a small stub that mirrors browser.js's didKeyResolve -- it calls the
// SAME npm-entry ABI function (abi.didKeyResolve) the browser build
// loads, just backed by require() instead of fetch(). The `fn` binding
// is the REAL npm/factoidal typed API; `pretty` is the shared node-side
// stub from _helpers.mjs. The last cell renders with Observable Plot;
// the browser has the vendored Plot, so here a tiny echo stub captures
// the marks/data the cell computes so the pinning test can assert the
// node/edge counts derived from the resolved document (the same
// browser-vs-test duality documented for pretty() in hub/README.md).

import { createRequire } from 'node:module';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '23-decentralized-identifiers-did-key.md';

const DID = 'did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK';
const VM = DID + '#z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK';

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

// Mirrors npm/factoidal/browser.js's didKeyResolve(): JSON-parse the
// ABI's envelope, throw on {ok:false}, hand back {ok,did,nquads}.
const Factoidal = {
  async didKeyResolve(didString) {
    assert.equal(typeof abi.didKeyResolve, 'function',
      'the loaded bundle predates the did:key export');
    const parsed = JSON.parse(abi.didKeyResolve(didString));
    if (!parsed.ok) throw new Error(parsed.error || 'didKeyResolve failed');
    return parsed;
  },
};

// Echo stub for the vendored Observable Plot: each mark constructor
// records its (data, options); Plot.plot echoes the spec. Enough to
// assert the node/edge counts the cell derives from the DID Document.
const Plot = {
  plot: (spec) => ({ isPlot: true, ...spec }),
  arrow: (data, options) => ({ mark: 'arrow', data, options }),
  dot: (data, options) => ({ mark: 'dot', data, options }),
  text: (data, options) => ({ mark: 'text', data, options }),
};

const cells = extractObservableCells(POST_FILE);
const B = { Factoidal, fn: factoidal, pretty, Plot };

test('post23: post has 4 live cells', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

test('post23 cell 1 (resolve did:key): 8 triples, no network', async () => {
  const result = await runObservableCell(cells[0], B);
  assert.equal(result, 8);
});

test('post23 cell 2 (DID Document as triples): 8-row s/p/o table', async () => {
  const result = await runObservableCell(cells[1], B);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['s', 'p', 'o']);
  assert.equal(result.rows.length, 8);
  // Order-independent membership checks (the Dataset iterates its quads
  // in sorted order, not the resolver's emission order).
  const has = (row) => result.rows.some((r) => JSON.stringify(r) === JSON.stringify(row));
  assert.ok(has([DID, 'https://w3id.org/security#verificationMethod', VM]),
    'DID --verificationMethod--> method IRI');
  assert.ok(has([VM, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
    'https://w3id.org/security#Ed25519VerificationKey2020']),
    'method a Ed25519VerificationKey2020');
  assert.ok(has([VM, 'https://w3id.org/security#publicKeyMultibase',
    '"z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK"^^https://w3id.org/security#multibase']),
    'method publicKeyMultibase is the typed multibase literal');
});

test('post23 cell 3 (verification method via SPARQL): one row, typed key literal', async () => {
  const result = await runObservableCell(cells[2], B);
  assert.deepEqual(result, {
    kind: 'table',
    columns: ['type', 'controller', 'key'],
    rows: [[
      'https://w3id.org/security#Ed25519VerificationKey2020',
      DID,
      '"z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK"^^https://w3id.org/security#multibase',
    ]],
  });
});

test('post23 cell 4 (node-graph): 4 nodes, 8 edges derived from the document', async () => {
  const result = await runObservableCell(cells[3], B);
  assert.equal(result.isPlot, true);
  const arrow = result.marks.find((m) => m.mark === 'arrow');
  const dots = result.marks.find((m) => m.mark === 'dot');
  assert.ok(arrow, 'expected an arrow mark (the edges)');
  assert.ok(dots, 'expected a dot mark (the nodes)');
  assert.equal(arrow.data.length, 8, 'one arrow per triple');
  assert.equal(dots.data.length, 4, 'DID, method, key-type, key-literal');
  // Every edge carries a shortened predicate label.
  assert.ok(arrow.data.every((e) => typeof e.pred === 'string' && e.pred.length > 0));
});
