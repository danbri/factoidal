// Pins every live cell in docs/web/hub/39-propositions-as-first-class-citizens.md.
//
// Post 39 adds the Common Logic / IKL family (Wasm/Ops/CL.lean, issue
// 580) to the dispatch surface post 38 climbed: clParse, clToDataset,
// and the combination op queryWithIklService, all driven through the
// same fn.l4Call(op, args) wrapper.
//
// Harness shape follows tests/hub/post38_test.mjs: `fn` here is the
// node npm package with the Lean names layered on over the SAME
// on-disk loader the browser imports
// (docs/web/hub/assets/l4/l4factoidal.js).

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

const POST_FILE = '39-propositions-as-first-class-citizens.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

test('post39: post has 9 live cells', () => {
  assert.equal(cells.length, 9, `expected 9 live cells, found ${cells.length}`);
});

test('post39: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes — a stub, not a build`);
});

test('post39 cell "one CLIF sentence": pure CL, canonical form echoed back', async () => {
  const env = await post().value('plainParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, true);
  assert.equal(env.normalized, '(Dead OBL)');
});

test('post39 cell "what can IKL say": the (that S) term flips pureCL to false', async () => {
  const env = await post().value('believesParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized, '(believes Zeno (that (Dead OBL)))');
});

test('post39 cell "from proposition to graph": count/skipped and the named graph', async () => {
  const env = await post().value('believesDataset');
  assert.equal(env.ok, true);
  assert.equal(env.count, 2);
  assert.equal(env.skipped, 0);
  assert.match(env.nquads,
    /<urn:cl:Zeno> <urn:cl:believes> <urn:cl:that:%28Dead%20OBL%29> \.\n/);
  assert.match(env.nquads,
    /<urn:cl:OBL> <http:\/\/www\.w3\.org\/1999\/02\/22-rdf-syntax-ns#type> <urn:cl:Dead> <urn:cl:that:%28Dead%20OBL%29> \.\n/);
});

test('post39 cell "what is inside each proposition": GRAPH pattern enumerates it', async () => {
  const rows = await post().value('propositions');
  assert.deepEqual(rows, [{
    g: 'urn:cl:that:%28Dead%20OBL%29',
    s: 'urn:cl:OBL',
    p: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
    o: 'urn:cl:Dead',
  }]);
});

test('post39 cell "propositions joined against ordinary data": believer + label', async () => {
  const rows = await post().value('believerAndLabel');
  assert.deepEqual(rows, [{ believer: 'urn:cl:Zeno', label: 'Obadiah' }]);
});

// Beyond the page: the CLIF parse error path. A malformed sentence
// must come back as {"ok":false,...}, surfaced by the loader as a
// thrown Error — and the module must survive it (the same dispatch
// entry post38 pins for parseToDatasetJson).
test('post39: a dispatch clParse error throws and leaves the module alive', async () => {
  const l4 = await l4api.loadL4();
  assert.throws(() => l4.call('clParse', ['(P a']), /l4factoidal:.*unclosed/i);
  assert.match(l4.version(), /^l4factoidal-wasm /);
});

test('post39: the committed wasm serves every CL op the page calls', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  for (const op of ['clParse', 'clToDataset', 'queryWithIklService', 'queryDataset']) {
    assert.ok(ops.includes(op), `dispatch table is missing ${op}`);
  }
});
