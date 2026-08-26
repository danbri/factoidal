// Pins every live cell in docs/web/hub/43-one-model-theory-under-all-of-it.md.
//
// Post 43 is the stage 7 account of the unified-semantics programme
// (https://github.com/danbri/factoidal/issues/598): LBase/IKL-style
// model theory in Lean 4, with the gate theorems shown as source
// EXCERPTS and only three live cells, each demonstrating something a
// theorem is about --
//
//   rhoDfAnswer  -- the rho-df closure answering a query, plus the
//                   executable fragment check that discharges one of
//                   the three hypotheses of unified_adequate_rhoDf_decided;
//   selfLoop     -- Finding C-1's separating pair (X subClassOf Y
//                   |= X subClassOf X): the rho-df schema refutes it,
//                   the full RDFS schema entails it, and the two engines
//                   agree with those two theorems;
//   owlRlAnswer  -- an OWL 2 RL row (prp-inv1) firing, the triple the
//                   T2 licensing chain plus unified_owlRl_sound covers.
//
// Every op called here is in the COMMITTED wasm dispatch table (see the
// last test): rhoDfClosure, rhoDfFragmentCheck, owlClosure, owlEntails,
// queryDataset. Harness shape follows tests/hub/post39_test.mjs: `fn`
// is the node npm package with the Lean dispatch layered on over the
// SAME on-disk loader the browser imports.

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
  l4Call: async (op, args) => (await l4api.loadL4()).call(op, args),
};

// The page's `fn`: the npm package, with the Lean dispatch layered on.
const fn = new Proxy(factoidal, {
  get(target, prop) {
    if (Object.hasOwn(l4api, prop)) return l4api[prop];
    const v = Reflect.get(target, prop);
    return typeof v === 'function' ? v.bind(target) : v;
  },
});

const POST_FILE = '43-one-model-theory-under-all-of-it.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

test('post43: post has 5 live cells', () => {
  assert.equal(cells.length, 5, `expected 5 live cells, found ${cells.length}`);
});

test('post43: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes — a stub, not a build`);
});

test('post43 cell "rhoDfAnswer": the closure derives the type, and the fragment check passes', async () => {
  const r = await post().value('rhoDfAnswer');
  assert.equal(r.statedTriples, 3);
  assert.equal(r.closureTriples, 5, 'rdfs7 then rdfs3 should add exactly two triples');
  assert.equal(r.rounds, 2);
  assert.equal(r.askOverStated, false, 'the stated graph does not contain the typing triple');
  assert.equal(r.askOverClosure, true, 'the rho-df closure must derive it');
  // RDFS.isRhoDfFrag on the CLOSURE is the executable sufficient check
  // behind RDF.rhoDfModelFrag_of_check, one of the three hypotheses of
  // unified_adequate_rhoDf_decided.
  assert.equal(r.fragmentCheckOnClosure, true);
});

test('post43 cell "selfLoop": Finding C-1 separates the two schemas, live', async () => {
  const r = await post().value('selfLoop');
  assert.equal(r.rhoDfSaysSelfLoop, false,
    'the six rho-df rules must NOT derive X rdfs:subClassOf X — this is the negative half of Finding C-1');
  assert.equal(r.rdfsSaysSelfLoop, true,
    'the full RDFS closure must derive it — the positive half, and why rdfsSchema is strictly stronger');
  assert.equal(r.rhoDfTriples, 1, 'the rho-df closure of a single subClassOf triple adds nothing');
  assert.ok(r.rdfsTriples > r.rhoDfTriples,
    'the full RDFS closure carries the axiomatic triples as well');
});

test('post43 cell "owlRlAnswer": prp-inv1 fires and owlEntails agrees via the closure', async () => {
  const r = await post().value('owlRlAnswer');
  assert.equal(r.askOverStated, false);
  assert.equal(r.askOverClosure, true, 'prp-inv1 must derive mary hasHusband john');
  assert.equal(r.entailed, true);
  assert.equal(r.via, 'closure');
  assert.ok(r.closureTriples > 2, 'the OWL-RL closure of the two stated triples grows');
});

// Beyond the page: every op the page calls must be in the COMMITTED
// dispatch table, and the module must survive a dispatch error (the
// 2026-08-22 -DNDEBUG abort class).
test('post43: the committed wasm serves every op the page calls', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  for (const op of ['queryDataset', 'rhoDfClosure', 'rhoDfFragmentCheck',
    'owlClosure', 'owlEntails']) {
    assert.ok(ops.includes(op), `dispatch table is missing ${op}`);
  }
});

test('post43: a dispatch parse error throws and leaves the module alive', async () => {
  const l4 = await l4api.loadL4();
  assert.throws(() => l4.call('rhoDfClosure', ['this is not n-triples']), /l4factoidal:/);
  assert.match(l4.version(), /^l4factoidal-wasm /);
});
