// Pins every live cell in docs/web/hub/39-propositions-as-first-class-citizens.md.
//
// Post 39 is the Common Logic / IKL page (Wasm/Ops/CL.lean, issue 580)
// over the graph-decoration translation (issue 581): a top-level
// sentence becomes a named proposition graph, the default graph holds
// only decorations (asserts / link / rdf:reifies bridge), and the
// page's arc is a two-source disagreement found by a SPARQL join.
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

// The content-addressed graph names (issue 589):
// urn:cl:that:sha256:<sha256 of the alpha-normalized canonical CLIF>.
// echo -n '(Dead OBL)' | sha256sum ; echo -n '(Alive OBL)' | sha256sum
const DEADOBL_G =
  'urn:cl:that:sha256:627ab6c4ca999f2605c342e052ef3fe6ae4f8c9a5744df8a09ef4f66819eddd0';
const ALIVEOBL_G =
  'urn:cl:that:sha256:48bd3cc7b4cb344acaaa81bc2172ba453486f40132abc790b466ecc8dd1c0059';

const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';

test('post39: post has 14 live cells', () => {
  assert.equal(cells.length, 14, `expected 14 live cells, found ${cells.length}`);
});

test('post39: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes — a stub, not a build`);
});

test('post39 cell "flatStatus": the plain-triple merge asserts both classes as flat fact', async () => {
  const rows = await post().value('flatStatus');
  assert.deepEqual(rows, [{ status: 'urn:cl:Alive' }, { status: 'urn:cl:Dead' }]);
});

test('post39 cell "sourcesDataset": graphs + decorations, nothing flattened', async () => {
  const env = await post().value('sourcesDataset');
  assert.equal(env.ok, true);
  // count = graph-content triples (2) + decorations (2 says links + 2
  // rdf:reifies bridges) — sentence records are not counted.
  assert.equal(env.count, 6);
  assert.equal(env.skipped, 0);
  // The says links decorate the default graph.
  assert.ok(env.nquads.includes(
    `<urn:cl:MorningWire> <urn:cl:says> <${ALIVEOBL_G}> .\n`));
  assert.ok(env.nquads.includes(
    `<urn:cl:EveningPost> <urn:cl:says> <${DEADOBL_G}> .\n`));
  // Claim content lives in the NAMED graphs only: every type triple
  // carries a graph label (a default-graph line would end at the
  // object).
  assert.ok(env.nquads.includes(
    `<urn:cl:OBL> <${RDF_TYPE}> <urn:cl:Alive> <${ALIVEOBL_G}> .\n`));
  assert.ok(env.nquads.includes(
    `<urn:cl:OBL> <${RDF_TYPE}> <urn:cl:Dead> <${DEADOBL_G}> .\n`));
  assert.ok(!env.nquads.includes('<urn:cl:Alive> .\n'),
    'a claim atom leaked into the default graph');
  assert.ok(!env.nquads.includes('<urn:cl:Dead> .\n'),
    'a claim atom leaked into the default graph');
  // The sentence-record triples: canonical CLIF as data inside each graph.
  assert.ok(env.nquads.includes(
    `<${ALIVEOBL_G}> <urn:cl:def:sentence> "(Alive OBL)" <${ALIVEOBL_G}> .\n`));
  // The rdf:reifies bridge: graph name -> RDF 1.2 triple term, in the
  // default graph.
  assert.ok(env.nquads.includes(
    `<${DEADOBL_G}> <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> ` +
    `<<( <urn:cl:OBL> <${RDF_TYPE}> <urn:cl:Dead> )>> .\n`));
});

test('post39 cell "whoSaysWhat": sources paired with claim sentences, no hashes shown', async () => {
  const rows = await post().value('whoSaysWhat');
  assert.deepEqual(rows, [
    { source: 'urn:cl:EveningPost', claim: '(Dead OBL)' },
    { source: 'urn:cl:MorningWire', claim: '(Alive OBL)' },
  ]);
});

test('post39 cell "disagreement": the Alive/Dead join finds the conflicting pair', async () => {
  const rows = await post().value('disagreement');
  assert.deepEqual(rows, [{
    about: 'urn:cl:OBL',
    src1: 'urn:cl:MorningWire', claim1: '(Alive OBL)',
    src2: 'urn:cl:EveningPost', claim2: '(Dead OBL)',
  }]);
});

test('post39 cell "decorationRows": believes/ist/asserts decorate ONE graph', async () => {
  const rows = await post().value('decorationRows');
  assert.deepEqual(rows, [
    { who: 'urn:cl:Zeno', how: 'urn:cl:believes' },
    { who: 'urn:cl:kb', how: 'urn:cl:def:asserts' },
    { who: 'urn:cl:Day2006', how: 'urn:cl:ist' },
  ]);
});

test('post39 cell "disagreementNamed": the finale joins against reference labels', async () => {
  const rows = await post().value('disagreementNamed');
  assert.deepEqual(rows, [{
    person: 'Obadiah',
    name1: 'The Morning Wire', claim1: '(Alive OBL)',
    name2: 'The Evening Post', claim2: '(Dead OBL)',
  }]);
});

test('post39 cell "sourcesParse": two sentences, IKL not pure CL, canonical echo', async () => {
  const env = await post().value('sourcesParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 2);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized,
    '(says MorningWire (that (Alive OBL)))\n(says EveningPost (that (Dead OBL)))');
});

test('post39 cell "bridge": rdf:reifies triple terms render as <<( s p o )>>', async () => {
  const table = await post().value('bridge');
  assert.equal(table.kind, 'table');
  assert.deepEqual(table.columns, ['claim', 'fact']);
  assert.deepEqual(table.rows, [
    ['"(Alive OBL)"', `<<( urn:cl:OBL ${RDF_TYPE} urn:cl:Alive )>>`],
    ['"(Dead OBL)"', `<<( urn:cl:OBL ${RDF_TYPE} urn:cl:Dead )>>`],
  ]);
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
