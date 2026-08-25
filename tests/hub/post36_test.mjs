// Pins every live cell in docs/web/hub/36-lean-in-the-browser.md.
//
// What is different about this post's harness: the page runs TWO
// engines. `fn.parse` / `fn.query` are the F*-derived engine (the npm
// package, as in every other hub test), while `fn.loadL4` /
// `fn.l4Version` / `fn.l4Call` / `fn.l4Parse` / `fn.l4Query` are the
// Lean 4 engine compiled to wasm32. The Lean wrappers do not live in
// npm/factoidal, so this file builds them over the same on-disk loader
// the browser imports (docs/web/hub/assets/l4/l4factoidal.js) —
// exactly the browser-vs-test duality tests/hub/post35_test.mjs uses
// for the wikifn engine.
//
// The fn-surface parity pin (tests/hub/fn_surface_parity_test.mjs) is
// what proves l4Version/l4Call/l4Parse/l4Query ALSO exist in
// docs/_includes/hub.njk; this file cannot see that, because here `fn`
// is assembled locally.
//
// 2026-08-25 rework (issue #585, page-level half): the page used to
// call the raw dispatch, `fn.l4Call("parseToDatasetJson", …)` /
// `fn.l4Call("queryDataset", …)`, directly — owner feedback (2026-08-25):
// "WHY ARE WE PARSING TTL TO JSON NOT A GRAPH API??????". It now goes
// through `fn.l4Parse`/`fn.l4Query`, typed wrappers over the
// dataset-handle ABI (`Wasm/Ops/Handles.lean`) that read the same as
// the F* cells' `fn.parse`/`fn.query`. Post 38 still walks the raw
// dispatch surface directly, by design — that page's point is the ABI
// itself.
//
// Layer below: `lake build` in formal/lean4 (the #guard suite and the
// theorems), and formal/lean4/Wasm/Main.lean, a native driver over the
// same ABI so an ABI bug and a wasm bug cannot be confused.

import test from 'node:test';
import assert from 'node:assert/strict';
import { statSync } from 'node:fs';

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

const L4_LOADER = new URL('../../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const L4_WASM = new URL('../../docs/web/hub/assets/l4/l4factoidal.wasm', import.meta.url);

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const { loadL4 } = await import(L4_LOADER.href);

// SPARQL-Results-JSON term -> the same term-object shape npm/factoidal's
// srjTermToFn produces, so leanNameAge's post-processing (in the page
// cell) matches fstarNameAge's byte for byte. Duplicated from
// docs/_includes/hub.njk's srjTermToFn -- this file assembles `fn`
// locally (see file-top comment), so it cannot import the template.
function srjTermToFn(t) {
  if (t.type === 'uri') return { termType: 'NamedNode', value: t.value };
  if (t.type === 'bnode') return { termType: 'BlankNode', value: t.value };
  const language = t['xml:lang'] || '';
  const datatype = t.datatype
    || (language ? 'http://www.w3.org/1999/02/22-rdf-syntax-ns#langString'
                 : 'http://www.w3.org/2001/XMLSchema#string');
  return { termType: 'Literal', value: t.value, language, datatype: { termType: 'NamedNode', value: datatype } };
}

// Node twin of docs/_includes/hub.njk's L4Dataset class (issue #585's
// page-level half): holds the wasm engine handle datasetOpen returns,
// not the N-Quads text.
class L4Dataset {
  constructor(engine, handle, count) {
    this._engine = engine;
    this._handle = handle;
    this._count = count;
  }
  get size() { return this._count; }
  get handle() { return this._handle; }
  toNQuads() { return this._engine.call('datasetSerialize', [this._handle, 'nquads']).nquads; }
}

let l4Promise = null;
const l4api = {
  loadL4: () => (l4Promise ??= loadL4()),
  l4Version: async () => (await l4api.loadL4()).version(),
  l4Call: async (op, args) => (await l4api.loadL4()).call(op, args),
  // Node twins of hub.njk's fn.l4Parse/fn.l4Query -- same handle-based
  // ABI calls, same result shaping, so a page cell written against
  // either `fn` behaves identically.
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
};

// The page's `fn`: the npm package, with the Lean names layered on.
const fn = new Proxy(factoidal, {
  get(target, prop) {
    if (Object.hasOwn(l4api, prop)) return l4api[prop];
    const v = Reflect.get(target, prop);
    return typeof v === 'function' ? v.bind(target) : v;
  },
});

const POST_FILE = '36-lean-in-the-browser.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

test('post36: post has 13 live cells', () => {
  assert.equal(cells.length, 13, `expected 13 live cells, found ${cells.length}`);
});

test('post36: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes — a stub, not a build`);
});

test('post36 cell "loading": Lean identifies itself across the C boundary', async () => {
  const version = await post().value('leanVersion');
  assert.match(version, /^l4factoidal-wasm /,
    `expected the Lean ABI version string, got ${JSON.stringify(version)}`);
});

test('post36 cell "lean parses it": the Turtle parses to two triples per person', async () => {
  const ds = await post().value('leanDataset');
  assert.equal(ds.size, 4);
  assert.ok(ds.handle, 'leanDataset has no handle');
});

test('post36 cell "lean answers it": the join returns Alice and Bob', async () => {
  const rows = await post().value('leanNameAge');
  assert.deepEqual(
    rows.map((r) => `${r.s.split('/').pop()}/${r.n}/${r.a}`).sort(),
    ['alice/Alice/30', 'bob/Bob/24'],
  );
});

test('post36 cell "the F* engine": the same query, parsed from the same Turtle text', async () => {
  const rows = await post().value('fstarNameAge');
  assert.deepEqual(
    rows.map((r) => `${r.s.split('/').pop()}/${r.n}/${r.a}`).sort(),
    ['alice/Alice/30', 'bob/Bob/24'],
  );
});

test('post36 cell "do they agree": the two engines return the identical answer set', async () => {
  const result = await post().value('agreement');
  assert.equal(result.leanRows, 2);
  assert.equal(result.fstarRows, 2);
  assert.equal(result.agree, true,
    'the Lean and F* engines disagreed on a BGP — one of them has a bug');
});

test('post36 cell "one more question": both engines ASK true over the typed-literal FILTER', async () => {
  const result = await post().value('askAgreement');
  assert.equal(result.lean, true);
  assert.equal(result.fstar, true);
  assert.equal(result.agree, true,
    'the Lean and F* engines disagreed on ASK ?a > 25 — one of them has a bug');
});

// The display cells must actually PRODUCE a value, not `undefined` --
// this repo's cell compiler supplies an implicit `return` only for a
// NAMED cell's expression body, so an anonymous-block cell that forgets
// one silently renders `undefined`. Caught in the browser value check
// on 2026-08-22 for a different post's display cells; pinned here too.
test('post36: every named cell resolves to a defined value', async () => {
  const p = post();
  for (const name of [
    'leanVersion', 'EX', 'PEOPLE_TTL', 'NAME_AGE_QUERY',
    'leanDataset', 'leanNameAge', 'fstarDataset', 'fstarNameAge', 'agreement',
    'ASK_QUERY', 'leanAsk', 'fstarAsk', 'askAgreement',
  ]) {
    const value = await p.value(name);
    assert.notEqual(value, undefined, `${name} rendered undefined`);
  }
});

// Beyond the page: the decode-error path. This is pinned because it is
// the exact path that aborted the whole wasm module when the core
// library was built without -DNDEBUG (2026-08-22); the happy path was
// unaffected, so nothing else here would have caught it.
test('post36: a dispatch parse error comes back as an error, not as a module abort', async () => {
  const l4 = await l4api.loadL4();
  assert.throws(() => l4.call('parseToDatasetJson', ['this is not turtle {{{', 'turtle', '']),
    /l4factoidal:/);
  // The module must still be alive afterwards.
  assert.match(l4.version(), /^l4factoidal-wasm /);
});
