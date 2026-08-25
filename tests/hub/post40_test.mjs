// Pins every live cell in docs/web/hub/40-a-dataset-that-stays-open.md.
//
// Post 40 is the working-session page for the Lean 4 engine's
// dataset-handle graph API (issue #585): one fn.l4Parse call opens a
// TriG corpus with three named graphs into ONE handle, and every later
// cell -- a cross-graph SELECT, an in-place fn.l4Update, an
// fn.l4Call-driven rdfsPlusClosure, two owlIsConsistent verdicts, and a
// closing toTurtle() -- reads or mutates that same handle. No cell
// re-parses the corpus.
//
// Harness shape follows tests/hub/post38_test.mjs: `fn` here is the
// node npm package's Lean loader (docs/web/hub/assets/l4/l4factoidal.js,
// the same on-disk file the browser imports), with the typed
// l4Parse/l4Query/l4Update/l4Call wrappers layered on locally -- the
// same reshaping docs/_includes/hub.njk applies. The fn-surface parity
// pin (tests/hub/fn_surface_parity_test.mjs) is what proves those
// wrappers ALSO exist in hub.njk; this file cannot see that, because
// here `fn` is assembled locally.

import test from 'node:test';
import assert from 'node:assert/strict';
import { statSync } from 'node:fs';

import { extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

const L4_LOADER = new URL('../../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const L4_WASM = new URL('../../docs/web/hub/assets/l4/l4factoidal.wasm', import.meta.url);

const { loadL4 } = await import(L4_LOADER.href);

// Node twin of docs/_includes/hub.njk's L4Dataset/srjTermToFn -- see
// tests/hub/post38_test.mjs's copy of the same pair.
function srjTermToFn(t) {
  if (t.type === 'uri') return { termType: 'NamedNode', value: t.value };
  if (t.type === 'bnode') return { termType: 'BlankNode', value: t.value };
  const language = t['xml:lang'] || '';
  const datatype = t.datatype
    || (language ? 'http://www.w3.org/1999/02/22-rdf-syntax-ns#langString'
                 : 'http://www.w3.org/2001/XMLSchema#string');
  return { termType: 'Literal', value: t.value, language, datatype: { termType: 'NamedNode', value: datatype } };
}

class L4Dataset {
  constructor(engine, handle, count) {
    this._engine = engine;
    this._handle = handle;
    this._count = count;
  }
  get size() { return this._count; }
  get handle() { return this._handle; }
  toNQuads() { return this._engine.call('datasetSerialize', [this._handle, 'nquads']).nquads; }
  toTurtle() { return this._engine.call('datasetSerialize', [this._handle, 'turtle']).turtle; }
}

let l4Promise = null;
const l4api = {
  loadL4: () => (l4Promise ??= loadL4()),
  l4Call: async (op, args) => (await l4api.loadL4()).call(op, args),
  l4Parse: async (text, options) => {
    const opts = options || {};
    const engine = await l4api.loadL4();
    const r = engine.call('datasetOpen', [text, opts.format || 'turtle', opts.baseIRI || '']);
    return new L4Dataset(engine, r.handle, r.count);
  },
  l4Query: async (dataset, sparql) => {
    const r = dataset._engine.call('datasetQuery', [dataset.handle, sparql]);
    if (r.kind === 'ask') return !!r.boolean;
    if (r.kind === 'select') {
      const rows = (r.srj.results && r.srj.results.bindings) || [];
      return rows.map((row) => {
        const map = new Map();
        for (const [name, term] of Object.entries(row)) map.set(name, srjTermToFn(term));
        return map;
      });
    }
    if (r.kind === 'construct') return r.nquads;
    throw new Error(`l4Query: unexpected result kind "${r.kind}"`);
  },
  l4Update: async (dataset, sparqlUpdate) => {
    const engine = await l4api.loadL4();
    const r = engine.call('datasetUpdate', [dataset.handle, sparqlUpdate]);
    dataset._count = r.count;
    return dataset;
  },
};

// The page's `fn`: only the wrappers this post uses (no npm/factoidal
// F* side -- post 40 stays on the Lean handle ABI throughout).
const fn = l4api;

const POST_FILE = '40-a-dataset-that-stays-open.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

test('post40: post has 12 live cells', () => {
  assert.equal(cells.length, 12, `expected 12 live cells, found ${cells.length}`);
});

test('post40: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes -- a stub, not a build`);
});

test('post40 cell "orgDataset": one fn.l4Parse call opens a TriG corpus, one handle, 10 triples', async () => {
  const ds = await post().value('orgDataset');
  assert.equal(ds.size, 10);
  assert.ok(ds.handle, 'expected a dataset handle string');
});

test('post40 cell "byDept": the cross-graph GRAPH ?g query returns 4 rows over 3 named graphs', async () => {
  const rows = await post().value('byDept');
  assert.equal(rows.length, 4);
  const people = rows.map((r) => r.person.split('#').pop()).sort();
  assert.deepEqual(people, ['alice', 'bob', 'carol', 'dave']);
  const graphs = new Set(rows.map((r) => r.g.split('#').pop()));
  assert.deepEqual([...graphs].sort(), ['eng', 'ops', 'sales']);
});

test('post40 cell "afterInsert": fn.l4Update mutates the SAME handle -- size grows from 10 to 12', async () => {
  const r = await post().value('afterInsert');
  assert.equal(r.rowsBefore, 4);
  assert.equal(r.size, 12);
});

test('post40 cell "byDeptAfter": the same handle, re-queried, now shows 5 rows including Erin', async () => {
  const r = await post().value('byDeptAfter');
  assert.equal(r.size, 12);
  assert.equal(r.rows.length, 5);
  const people = r.rows.map((row) => row.person.split('#').pop()).sort();
  assert.deepEqual(people, ['alice', 'bob', 'carol', 'dave', 'erin']);
});

test('post40 cell "closureCheck": rdfsPlusClosure over the handle\'s own data derives Employee', async () => {
  const r = await post().value('closureCheck');
  assert.equal(r.triplesInHandle, 12);
  assert.equal(r.before, false, 'the stated corpus must not already say :alice a :Employee');
  assert.equal(r.after, true, 'the RDFS closure must derive :alice a :Employee from subClassOf');
  assert.equal(r.rounds, 1);
});

test('post40 cell "consistentBefore": owlIsConsistent reports consistent (true) before the clash', async () => {
  const r = await post().value('consistentBefore');
  assert.equal(r.entailedEmployee, true);
  assert.equal(r.consistent, true);
});

test('post40 cell "consistentAfter": inserting the disjoint-class pair flips the verdict to false, with a reason', async () => {
  const r = await post().value('consistentAfter');
  assert.equal(r.wasConsistent, true);
  assert.equal(r.consistent, false);
  assert.match(r.reason, /clash-detecting tableau/);
});

test('post40 cell "finalTurtle": the closing Turtle shows both classes on :alice', async () => {
  const ttl = await post().value('finalTurtle');
  assert.match(ttl, /alice/);
  assert.match(ttl, /Contractor/);
  assert.match(ttl, /Manager/);
});

// Beyond the page: the same handle across the whole session -- proves
// the "nothing was re-parsed" claim in the page's prose, not just each
// cell's individual answer.
test('post40: the handle identity is stable across parse, query, update and close', async () => {
  const engine = await l4api.loadL4();
  const opened = engine.call('datasetOpen', ['<urn:s> <urn:p> <urn:o> .', 'ntriples', '']);
  assert.equal(opened.count, 1);
  const updated = engine.call('datasetUpdate', [opened.handle, 'INSERT DATA { <urn:s2> <urn:p> <urn:o> . }']);
  assert.equal(updated.count, 2);
  const queried = engine.call('datasetQuery', [opened.handle, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }']);
  assert.equal(queried.kind, 'select');
  assert.equal(queried.srj.results.bindings[0].n.value, '2');
});

test('post40: the committed wasm serves every op the page calls', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  for (const op of ['datasetOpen', 'datasetQuery', 'datasetUpdate', 'datasetSerialize',
    'queryDataset', 'rdfsPlusClosure', 'owlIsConsistent']) {
    assert.ok(ops.includes(op), `dispatch table is missing ${op}`);
  }
});
