// Pins every live cell in docs/web/hub/36-lean-in-the-browser.md.
//
// What is different about this post's harness: the page runs TWO
// engines. `fn.parse` / `fn.query` are the F*-derived engine (the npm
// package, as in every other hub test), while `fn.loadL4` /
// `fn.l4Version` / `fn.l4BgpQuery` are the Lean 4 engine compiled to
// wasm32. The Lean wrappers do not live in npm/factoidal, so this file
// builds them over the same on-disk loader the browser imports
// (docs/web/hub/assets/l4/l4factoidal.js) — exactly the browser-vs-test
// duality tests/hub/post35_test.mjs uses for the wikifn engine.
//
// The fn-surface parity pin (tests/hub/fn_surface_parity_test.mjs) is
// what proves the three l4* names ALSO exist in docs/_includes/hub.njk;
// this file cannot see that, because here `fn` is assembled locally.
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

let l4Promise = null;
const l4api = {
  loadL4: () => (l4Promise ??= loadL4()),
  l4Version: async () => (await l4api.loadL4()).version(),
  l4BgpQuery: async (data, bgp) => (await l4api.loadL4()).bgpQuery(data, bgp),
};

// The page's `fn`: the npm package, with the three Lean names layered on.
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

test('post36: post has 14 live cells', () => {
  assert.equal(cells.length, 14, `expected 14 live cells, found ${cells.length}`);
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

test('post36 cell "one pattern": Lean evaluates ?s :name ?n to Alice and Bob', async () => {
  const rows = await post().value('leanNames');
  assert.deepEqual(
    rows.map((r) => [r.s, r.n]).sort(),
    [['http://example.org/alice', 'Alice'], ['http://example.org/bob', 'Bob']],
  );
});

test('post36 cell "two patterns": Lean joins name and age on ?s', async () => {
  const rows = await post().value('leanNameAge');
  assert.deepEqual(
    rows.map((r) => `${r.s.split('/').pop()}/${r.n}/${r.a}`).sort(),
    ['alice/Alice/30', 'bob/Bob/24'],
  );
});

test('post36 cell "the F* engine": the same query, parsed from SPARQL text', async () => {
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
  assert.equal(result.identical, true,
    'the Lean and F* engines disagreed on a BGP — one of them has a bug');
});

// The display cells must actually PRODUCE a value. This repo's cell
// compiler supplies an implicit `return` only for a NAMED cell's
// expression body; an anonymous cell runs verbatim, so a bare
// `pretty(x)` renders `undefined`. Caught in the browser value check
// on 2026-08-22, when four display cells rendered nothing while every
// other gate was green — `node --test` alone would never have seen it,
// and neither would the pageerror-only browser sweep.
test('post36: the four display cells render tables, not undefined', async () => {
  const p = post();
  for (const name of ['leanNamesTable', 'leanNameAgeTable', 'fstarNameAgeTable']) {
    const table = await p.value(name);
    assert.equal(table.kind, 'table', `${name} did not render a table`);
    assert.ok(table.rows.length === 2, `${name} rendered ${table.rows.length} rows`);
  }
  const summary = await p.value('agreementTable');
  assert.ok(summary !== undefined, 'agreementTable rendered undefined');
});

// Beyond the page: the decode-error path. This is pinned because it is
// the exact path that aborted the whole wasm module when the core
// library was built without -DNDEBUG (2026-08-22); the happy path was
// unaffected, so nothing else here would have caught it.
test('post36: a decoding error comes back as an error, not as a module abort', async () => {
  const l4 = await l4api.loadL4();
  assert.throws(() => l4.bgpQuery('[', '[]'), /l4factoidal:/);
  // The module must still be alive afterwards.
  assert.match(l4.version(), /^l4factoidal-wasm /);
});

test('post36: an ill-formed IRI is rejected by the Lean well-formedness check', async () => {
  const l4 = await l4api.loadL4();
  const bad = [{
    subject: { type: 'uri', value: 'no-colon-here' },
    predicate: { type: 'uri', value: 'http://example.org/p' },
    object: { type: 'literal', value: 'x' },
  }];
  assert.throws(() => l4.bgpQuery(bad, '[]'), /well-formed IRI/);
});
