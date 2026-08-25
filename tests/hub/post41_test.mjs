// Pins every live cell in
// docs/web/hub/41-a-walkthrough-of-the-ikl-guide.md.
//
// Post 41 is the tutorial post 39 promised to grow into: it parses and
// translates worked examples taken directly from Pat Hayes and Chris
// Menzel's IKL GUIDE (https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html)
// with the same clParse/clToDataset/queryWithIklService/queryDataset
// ops post 39 pins, run through the reactive cell runtime so cross-cell
// references (a later cell reading an earlier cell's resolved value,
// no `await` needed — the Observable runtime resolves promise-valued
// inputs before calling a dependent cell) are exercised exactly as the
// browser runs them.
//
// Harness shape follows tests/hub/post39_test.mjs: `fn` here is the
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

const POST_FILE = '41-a-walkthrough-of-the-ikl-guide.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

// Graph names pinned independently of the page (from CL/ToRdf.lean's
// own `#guard`s and CL/Examples.lean's alpha pin), so a page-level
// regression and an engine-level regression are told apart.
const LOVES_G =
  'urn:cl:that:sha256:98d23403b8111bf633e55edf9b546962a7ba5aadf08e68fe14fa563f21888b65';
const DEAD_OBL_TEMPORAL_G =
  'urn:cl:that:sha256:a81dac09284e8fff671dd81f16206ab9937b865b8399c4e624f0678911536cbf';
const COMMUTED_PQ_G =
  'urn:cl:that:sha256:d72c2c1f4950a265e438a9310c95c077ece6e084c5323eccb1abe61ce14d33a1';
const COMMUTED_QP_G =
  'urn:cl:that:sha256:6518ad058d39456fe81235b96230f40010117ef04eed1da1a8ca6a3071c7a14a';

test('post41: post has 36 live cells', () => {
  assert.equal(cells.length, 36, `expected 36 live cells, found ${cells.length}`);
});

test('post41: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes — a stub, not a build`);
});

test('post41: the committed wasm serves every CL/query op the page calls', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  for (const op of ['clParse', 'clToDataset', 'queryWithIklService', 'queryDataset']) {
    assert.ok(ops.includes(op), `dispatch table is missing ${op}`);
  }
});

// ---- "What the reader will not read" ----

test('post41 cell "moduleAttempt": cl:text is rejected with the issue-580 error, module stays alive', async () => {
  const env = await post().value('moduleAttempt');
  assert.equal(env.ok, false);
  assert.match(env.message, /l4factoidal:.*'cl:text' phrases are not covered by this reader \(issue 580\)/);
  const l4 = await l4api.loadL4();
  assert.match(l4.version(), /^l4factoidal-wasm /);
});

// ---- "Predication and names" ----

test('post41 cell "groundParse": two ground facts, pure CL, re-enclosed normal form', async () => {
  const env = await post().value('groundParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 2);
  assert.equal(env.pureCL, true);
  assert.equal(env.normalized,
    '(isHuman "Osama bin Laden")\n(childOf "Osama bin Laden" "Hamida al-Attas")');
});

// ---- "Quantifier forms" ----

test('post41 cell "restrictedParse": restricted forall/exists, pure CL', async () => {
  const env = await post().value('restrictedParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, true);
  assert.equal(env.normalized,
    '(forall ((x isHuman)) (exists ((y charseq)) (= y (nameOf x))))');
});

test('post41 cell "lovesXDs"/"lovesYDs": both translate, count 1 skipped 1, same graph name', async () => {
  const p = post();
  const dx = await p.value('lovesXDs');
  const dy = await p.value('lovesYDs');
  assert.equal(dx.ok, true);
  assert.equal(dx.count, 1);
  assert.equal(dx.skipped, 1);
  assert.ok(dx.nquads.includes(`<${LOVES_G}>`));
  assert.equal(dx.nquads, dy.nquads);
});

test('post41 cell "alphaPin": the alpha-variant pair names the SAME graph (issue 589)', async () => {
  const env = await post().value('alphaPin');
  assert.equal(env.graphOfX, LOVES_G);
  assert.equal(env.graphOfY, LOVES_G);
  assert.equal(env.sameGraph, true);
});

// ---- "Proposition names and (that S)" ----

test('post41 cell "cheikesParse": cancelling-parentheses assertion flips pureCL false', async () => {
  const env = await post().value('cheikesParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized, '((that (isHuman "Brant Cheikes")))');
});

test('post41 cell "harryBillDs": believes/that translates in full', async () => {
  const env = await post().value('harryBillDs');
  assert.equal(env.ok, true);
  // Graph-decoration translation (issue 581): link + content + the
  // rdf:reifies bridge a single-atom proposition earns.
  assert.equal(env.count, 3);
  assert.equal(env.skipped, 0);
  assert.ok(env.nquads.includes('<urn:cl:Harry> <urn:cl:Believes> <urn:cl:that:sha256:'));
  assert.ok(env.nquads.includes(
    '<urn:cl:Bill> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:cl:isLiar>'));
  assert.ok(env.nquads.includes(
    '<http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> ' +
    '<<( <urn:cl:Bill> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:cl:isLiar> )>>'));
});

// ---- "Quantifying-in" ----

test('post41 cell "loisParse": the GUIDE\'s quantifying-in sentence parses, pureCL false', async () => {
  const env = await post().value('loisParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
});

test('post41 cell "deDictoDs": simplified de dicto belief translates the link, skips the body', async () => {
  const env = await post().value('deDictoDs');
  assert.equal(env.ok, true);
  assert.equal(env.count, 1);
  assert.equal(env.skipped, 1);
  assert.ok(env.nquads.includes('<urn:cl:Bill_Andersen> <urn:cl:believes>'));
});

test('post41 cell "deDictoSentence": the alpha-normalized sentence text queried back out', async () => {
  const rows = await post().value('deDictoSentence');
  assert.deepEqual(rows, [
    { sentence: '(exists ((v1 Iranian)) (customer v1 "Bank Melli Iran"))' },
  ]);
});

// ---- "Contexts via ist" ----

test('post41 cell "xsdContextDs": the xsd:dateTime context name is a functional term, no link read', async () => {
  const env = await post().value('xsdContextDs');
  assert.equal(env.ok, true);
  // No context link (subj is a functional term); the sentence becomes
  // one asserted proposition graph holding only its record (count =
  // the assertion decoration), its content skipped and counted.
  assert.equal(env.count, 1);
  assert.equal(env.skipped, 1);
  assert.ok(env.nquads.includes('<urn:cl:kb> <urn:cl:def:asserts> <urn:cl:that:sha256:'));
  assert.ok(env.nquads.includes('<urn:cl:def:sentence>'));
  // Still no ist link and no content triple anywhere.
  assert.ok(!env.nquads.includes('<urn:cl:ist>'));
  assert.ok(!env.nquads.includes('<urn:cl:Dead>'));
});

test('post41 cell "simpleContextDs": simplified to a bare context name, translates in full', async () => {
  const env = await post().value('simpleContextDs');
  assert.equal(env.ok, true);
  // ist link + content triple + the single-atom rdf:reifies bridge.
  assert.equal(env.count, 3);
  assert.equal(env.skipped, 0);
  assert.ok(env.nquads.includes(`<${DEAD_OBL_TEMPORAL_G}>`));
});

test('post41 cell "contextQuery": GRAPH pattern reads inside the context\'s proposition', async () => {
  const rows = await post().value('contextQuery');
  assert.deepEqual(rows, [
    { g: DEAD_OBL_TEMPORAL_G, s: 'urn:cl:Osama-Bin-Laden' },
  ]);
});

// ---- "What identity does not include" ----

test('post41 cell "commutedNames": commuted conjunctions name DIFFERENT graphs today', async () => {
  const env = await post().value('commutedNames');
  assert.equal(env.graphOfPQ, COMMUTED_PQ_G);
  assert.equal(env.graphOfQP, COMMUTED_QP_G);
  assert.equal(env.sameGraph, false);
  assert.notEqual(env.graphOfPQ, env.graphOfQP);
});

// ---- Finale ----

test('post41 cell "orgJoined": the RDF label and the CL belief join to one row', async () => {
  const rows = await post().value('orgJoined');
  assert.deepEqual(rows, [{ employee: 'urn:cl:Alice', label: 'Acme Corp' }]);
});

// Headless-render sanity: pretty() must produce a renderable value (not
// undefined / [object Object]-shaped junk) for every named cell whose
// value is a plain object or an array of plain objects — the shapes
// this page's Table toggle renders.
test('post41: every JSON-envelope/table cell renders under pretty()', async () => {
  const p = post();
  const checked = [
    'moduleAttempt', 'groundParse', 'restrictedParse', 'lovesXDs', 'lovesYDs',
    'alphaPin', 'cheikesParse', 'harryBillDs', 'loisParse', 'deDictoDs',
    'deDictoSentence', 'xsdContextDs', 'simpleContextDs', 'contextQuery',
    'commutedDsPQ', 'commutedDsQP', 'commutedNames', 'orgJoined',
  ];
  for (const name of checked) {
    const value = await p.value(name);
    const rendered = pretty(value);
    const str = JSON.stringify(rendered);
    assert.ok(str !== undefined && str !== '{}' && !str.includes('"[object Object]"'),
      `cell "${name}" did not render sensibly under pretty(): ${str}`);
  }
});
