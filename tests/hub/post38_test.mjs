// Pins every live cell in docs/web/hub/38-one-triple-at-a-time.md.
//
// Post 38 is post 36's successor: where 36 stopped at BGP evaluation
// over term objects, 38 drives the DISPATCH ABI (formal/lean4/Wasm/
// Dispatch.lean) through the one generic wrapper fn.l4Call(op, args) —
// parse, ASK, SELECT, join, Turtle, UPDATE, CONSTRUCT, RDFS and OWL-RL
// closures, RDFC-1.0 canonicalization — and closes with the F* engine
// (fn.parse/fn.query, the npm package) answering the same join over the
// same N-Quads bytes.
//
// Harness shape follows tests/hub/post36_test.mjs: `fn` here is the
// node npm package with the Lean names layered on over the SAME on-disk
// loader the browser imports (docs/web/hub/assets/l4/l4factoidal.js).
// The fn-surface parity pin (tests/hub/fn_surface_parity_test.mjs) is
// what proves l4Call ALSO exists in docs/_includes/hub.njk; this file
// cannot see that, because here `fn` is assembled locally.

import test from 'node:test';
import assert from 'node:assert/strict';
import { statSync } from 'node:fs';

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

const L4_LOADER = new URL('../../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const L4_WASM = new URL('../../docs/web/hub/assets/l4/l4factoidal.wasm', import.meta.url);

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const { loadL4 } = await import(L4_LOADER.href);

// Node twin of docs/_includes/hub.njk's L4Dataset/srjTermToFn, needed
// for this post's closing "typed surface" cell (issue #585, page-level
// half) — see tests/hub/post36_test.mjs's copy of the same pair.
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
};

// The page's `fn`: the npm package, with the Lean dispatch layered on.
const fn = new Proxy(factoidal, {
  get(target, prop) {
    if (Object.hasOwn(l4api, prop)) return l4api[prop];
    const v = Reflect.get(target, prop);
    return typeof v === 'function' ? v.bind(target) : v;
  },
});

const POST_FILE = '38-one-triple-at-a-time.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

test('post38: post has 17 live cells', () => {
  assert.equal(cells.length, 17, `expected 17 live cells, found ${cells.length}`);
});

test('post38: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes — a stub, not a build`);
});

test('post38 cell "one triple": parse reports count 1 and the canonical echo', async () => {
  const env = await post().value('oneTriple');
  assert.equal(env.ok, true);
  assert.equal(env.count, 1);
  assert.equal(env.nquads, '<http://example.org/alice> <http://example.org/name> "Alice" .\n');
});

test('post38 cell "is anything there": ASK over one triple is true', async () => {
  assert.equal(await post().value('anythingThere'), true);
});

test('post38 cell "what is its name": SELECT one variable finds Alice', async () => {
  assert.deepEqual(await post().value('theName'), [{ name: 'Alice' }]);
});

test('post38 cell "two triples, one join": one row carries name and age together', async () => {
  const j = await post().value('firstJoin');
  assert.deepEqual(j.rows, [{ a: '30', n: 'Alice' }]);
  assert.equal(j.nquads.trim().split('\n').length, 2);
});

test('post38 cell "turtle in": same canonical bytes, same rows', async () => {
  assert.deepEqual(await post().value('turtleSame'), { sameNQuads: true, sameRows: true });
});

test('post38 cell "insert data": the dataset grows from 2 to 4 triples', async () => {
  const u = await post().value('afterInsert');
  assert.equal(u.triples, 4);
  assert.match(u.nquads, /<http:\/\/example\.org\/bob> <http:\/\/example\.org\/name> "Bob" \./);
});

test('post38 cell "query sees the new row": the join now returns Alice and Bob', async () => {
  const rows = await post().value('bothPeople');
  assert.deepEqual(
    rows.map((r) => `${r.s.split('/').pop()}/${r.n}/${r.a}`).sort(),
    ['alice/Alice/30', 'bob/Bob/24'],
  );
});

test('post38 cell "construct": new foaf:name triples, serialized as Turtle', async () => {
  const ttl = await post().value('constructed');
  assert.match(ttl, /@prefix foaf: <http:\/\/xmlns\.com\/foaf\/0\.1\/> \./);
  assert.match(ttl, /foaf:name "Alice"/);
  assert.match(ttl, /foaf:name "Bob"/);
});

test('post38 cell "rdfs closure": rex is an Animal after the closure, not before', async () => {
  assert.deepEqual(await post().value('inferred'),
    { statedTriples: 2, before: false, after: true });
});

test('post38 cell "owl-rl closure": sameAs propagates the name to superman', async () => {
  assert.deepEqual(await post().value('owlSame'), [{ n: 'Clark' }]);
});

test('post38 cell "same graph": two bnode labelings canonicalize identically', async () => {
  const s = await post().value('sameGraph');
  assert.equal(s.identical, true);
  assert.equal(s.canonicalA, s.canonicalB);
  assert.equal(s.canonicalA,
    '_:c14n0 <http://example.org/knows> _:c14n1 .\n_:c14n1 <http://example.org/knows> _:c14n0 .\n');
});

test('post38 cell "changed graph": one changed predicate breaks canonical equality', async () => {
  const c = await post().value('changedGraph');
  assert.equal(c.identicalToA, false);
  assert.match(c.canonicalC, /likes/);
});

test('post38 cell "typed surface": fn.l4Parse/fn.l4Query reproduce the earlier join', async () => {
  const rows = await post().value('typedJoin');
  assert.deepEqual(
    rows.map((r) => `${r.s.split('/').pop()}/${r.n}/${r.a}`).sort(),
    ['alice/Alice/30', 'bob/Bob/24'],
  );
});

test('post38 cell "the F* engine": the same join from the same bytes', async () => {
  const rows = await post().value('fstarRows');
  assert.deepEqual(
    rows.map((r) => `${r.s.split('/').pop()}/${r.n}/${r.a}`).sort(),
    ['alice/Alice/30', 'bob/Bob/24'],
  );
});

test('post38 cell "agreement": the two engines return the identical answer set', async () => {
  const result = await post().value('agreement');
  assert.equal(result.leanRows, 2);
  assert.equal(result.fstarRows, 2);
  assert.equal(result.identical, true,
    'the Lean and F* engines disagreed on a join — one of them has a bug');
});

// Beyond the page: the dispatch error path. A parse failure must come
// back as {"ok":false,...}, surfaced by the loader as a thrown Error —
// and the module must survive it (the 2026-08-22 -DNDEBUG abort class,
// pinned for the dispatch entry as post36 pins it for bgpQuery).
test('post38: a dispatch parse error throws and leaves the module alive', async () => {
  const l4 = await l4api.loadL4();
  assert.throws(() => l4.call('parseToDatasetJson', ['this is not turtle', 'turtle', '']),
    /l4factoidal:/);
  assert.throws(() => l4.call('noSuchOp', []), /unknown op/);
  assert.match(l4.version(), /^l4factoidal-wasm /);
});

test('post38: the committed wasm serves every op the page calls', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  for (const op of ['parseToDatasetJson', 'queryDataset', 'updateDataset',
    'serializeTurtle', 'owlClosure', 'canonicalizeToNQuads']) {
    assert.ok(ops.includes(op), `dispatch table is missing ${op}`);
  }
});
