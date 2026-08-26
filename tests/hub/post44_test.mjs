// Pins every live cell in
// docs/web/hub/44-a-little-ikl-walkthrough.md.
//
// Post 44 tells one squirrel story twice -- once where Clud's report
// incriminates Jon, once where a retelling mix-up produced the same
// words -- in short question-and-answer steps. Every cell calls
// clParse and nothing else: the post projects no RDF (no
// clToDataset/queryWithIklService/queryDataset). Those ops and the
// projection behind them are DELETED from the engine
// (danbri/factoidal#626).
//
// The pins record the two facts the page argues from: `pureCL` reads
// true while the text quotes words and false from the first
// that-term onward, and a doubled that-term is rejected with a
// message naming the cancelling-parentheses form.
//
// Harness shape follows tests/hub/post41_test.mjs: `fn` here is the
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

const POST_FILE = '44-a-little-ikl-walkthrough.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

const TESTIMONY = "I saw Jon watching Foxworth by the nut tree";

test('post44: post has 20 live cells', () => {
  assert.equal(cells.length, 20, `expected 20 live cells, found ${cells.length}`);
});

test('post44: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes -- a stub, not a build`);
});

test('post44: the committed wasm serves the clParse op the page calls', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  assert.ok(ops.includes('clParse'), 'dispatch table is missing clParse');
});

// danbri/factoidal#627: the committed artifact used to be AHEAD of its
// source, still exporting two ops the projection purge
// (danbri/factoidal#626) had deleted. The rebuild closed that. This
// asserts the artifact's own reflection, so a stale wasm committed in
// future fails here rather than being found by a caller.
test('post44: the committed wasm no longer serves the deleted projection ops', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  for (const gone of ['clToDataset', 'queryWithIklService']) {
    assert.ok(!ops.includes(gone), `artifact still exports the deleted op ${gone}`);
  }
});

// The four ops the same rebuild ADDED (danbri/factoidal#623). Asserted
// against the artifact for the same reason as above.
test('post44: the committed wasm serves the four CL/IKL ops added by the rebuild', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  for (const op of ['clSerialize', 'clAlphaNorm', 'clNormalize', 'clFiniteSat']) {
    assert.ok(ops.includes(op), `dispatch table is missing ${op}`);
  }
});

// The page's hard constraint: clParse is the ONLY op it calls. The
// banned names below are the deleted projection ops
// (danbri/factoidal#626). The committed wasm no longer answers them --
// the rebuild of danbri/factoidal#627 landed -- and the test above
// asserts that directly; this check keeps a cell from reintroducing a
// call to either name.
test('post44: no cell calls any op other than clParse', () => {
  const source = cells.join('\n');
  for (const banned of ['clToDataset', 'queryWithIklService', 'queryDataset']) {
    assert.ok(!source.includes(banned), `cell source calls banned op ${banned}`);
  }
  const ops = [...source.matchAll(/l4Call\(\s*"([A-Za-z0-9_]+)"/g)].map((m) => m[1]);
  assert.deepEqual([...new Set(ops)], ['clParse'], `page calls ops beyond clParse: ${ops}`);
});

// ---- 1. The words ----

test('post44 cell "testimonyParse": quoted testimony is pure CL, unchanged in normal form', async () => {
  const env = await post().value('testimonyParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, true);
  assert.equal(env.normalized, `(uttered Bram '${TESTIMONY}')`);
});

// ---- 2. What Clud has ----

test('post44 cell "cludEvidenceParse": the first that-term flips pureCL false', async () => {
  const env = await post().value('cludEvidenceParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized, `(witnessed Clud (that (uttered Bram '${TESTIMONY}')))`);
});

// ---- 3. The rule that governs `that` ----

test('post44 cell "doubleThatAttempt": a that-term inside that is rejected, naming ((that S))', async () => {
  const env = await post().value('doubleThatAttempt');
  assert.equal(env.ok, false);
  assert.match(env.message,
    /l4factoidal: '\(that S\)' is a term; to assert the proposition write '\(\(that S\)\)' \(offset 21\)/);
  // The module survives the rejection -- every later cell runs on it.
  const l4 = await l4api.loadL4();
  assert.match(l4.version(), /^l4factoidal-wasm /);
});

// ---- 4. Scenario A ----

test('post44 cell "scenarioAParse": three-layer that-nesting through a predication parses', async () => {
  const env = await post().value('scenarioAParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized,
    "(witnessed Clud (that (saw Jon (that (cached Foxworth 'the beech hollow')))))");
});

// ---- 5. Factivity ----

test('post44 cell "factivityParse": cancelling parens over a variable stay pure CL', async () => {
  const env = await post().value('factivityParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, true);
  assert.equal(env.normalized, '(forall (a p) (if (witnessed a p) (p)))');
});

// ---- 6. Quantifying in ----

test('post44 cell "quantifyInParse": a variable bound outside that is used inside it', async () => {
  const env = await post().value('quantifyInParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized,
    '(exists (x) (and (squirrel x) (believes Clud (that (guilty x)))))');
});

// ---- 7. Transparency ----

test('post44 cell "transparencyParse": identity alongside a belief that-term parses', async () => {
  const env = await post().value('transparencyParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized,
    "(and (= Foxworth OldGrey) (believes Clud (that (cached Foxworth 'the beech hollow'))))");
});

// ---- 8. Scenario B ----

test('post44 cell "scenarioBParse": one string, two readAs readings, both parse', async () => {
  const env = await post().value('scenarioBParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized,
    `(and (uttered Bram '${TESTIMONY}')`
    + ` (readAs '${TESTIMONY}'`
    + ` (that (saw Jon (that (cached Foxworth 'the beech hollow')))))`
    + ` (readAs '${TESTIMONY}'`
    + ` (that (saw Bram (that (watched Jon Foxworth))))))`);
  // The incriminating reading and the clearing reading are anchored to
  // the SAME character sequence -- that is the page's claim.
  const occurrences = env.normalized.split(`'${TESTIMONY}'`).length - 1;
  assert.equal(occurrences, 3, 'the three readAs/uttered anchors must share one string');
});

// ---- 9. The mix-up ----

test('post44 cell "mixupParse": the retelling chain parses, Wren\'s words reading as another pair', async () => {
  const env = await post().value('mixupParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized,
    "(and (uttered Wren 'the grey one was watching the other by the nut tree')"
    + " (readAs 'the grey one was watching the other by the nut tree'"
    + " (that (watched Nib Quill)))"
    + " (heard Bram 'the grey one was watching the other by the nut tree')"
    + ` (retold Bram 'the grey one was watching the other by the nut tree' '${TESTIMONY}'))`);
});

// ---- 10. The declined axiom ----

test('post44 cell "readAsFunctionalParse": the string-determines-proposition axiom is pure CL', async () => {
  const env = await post().value('readAsFunctionalParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, true);
  assert.equal(env.normalized,
    '(forall (s p q) (if (and (readAs s p) (readAs s q)) (= p q)))');
});

// ---- The page's thesis, as one assertion ----

test('post44: pureCL is true exactly for the cells that quote words or quantify plainly', async () => {
  const p = post();
  const expected = {
    testimonyParse: true,
    factivityParse: true,
    readAsFunctionalParse: true,
    cludEvidenceParse: false,
    scenarioAParse: false,
    quantifyInParse: false,
    transparencyParse: false,
    scenarioBParse: false,
    mixupParse: false,
  };
  for (const [name, want] of Object.entries(expected)) {
    const env = await p.value(name);
    assert.equal(env.pureCL, want, `cell "${name}" reported pureCL ${env.pureCL}, expected ${want}`);
  }
});

// Headless-render sanity: pretty() must produce a renderable value (not
// undefined / [object Object]-shaped junk) for every named cell whose
// value is a plain object -- the shapes this page's Table toggle renders.
test('post44: every JSON-envelope cell renders under pretty()', async () => {
  const p = post();
  const checked = [
    'testimonyParse', 'cludEvidenceParse', 'doubleThatAttempt', 'scenarioAParse',
    'factivityParse', 'quantifyInParse', 'transparencyParse', 'scenarioBParse',
    'mixupParse', 'readAsFunctionalParse',
  ];
  for (const name of checked) {
    const value = await p.value(name);
    const rendered = pretty(value);
    const str = JSON.stringify(rendered);
    assert.ok(str !== undefined && str !== '{}' && !str.includes('"[object Object]"'),
      `cell "${name}" did not render sensibly under pretty(): ${str}`);
  }
});
