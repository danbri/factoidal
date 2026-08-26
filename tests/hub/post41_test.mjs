// Pins every live cell in
// docs/web/hub/41-a-walkthrough-of-the-ikl-guide.md.
//
// Post 41 parses and translates worked examples taken directly from Pat
// Hayes and Chris Menzel's IKL GUIDE
// (https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) with the
// clParse op, run through the reactive cell runtime so cross-cell
// references (a later cell reading an earlier cell's resolved value,
// no `await` needed — the Observable runtime resolves promise-valued
// inputs before calling a dependent cell) are exercised exactly as the
// browser runs them.
//
// This post projects no CL/IKL into RDF (no
// clToDataset/queryWithIklService/queryDataset cells). Those ops and
// the projection behind them are DELETED from the engine
// (danbri/factoidal#626); the post that carried the material was
// deleted with them. Every surviving cell here is clParse, which only
// reads CLIF and reports its structure.
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

const POST_FILE = '41-a-walkthrough-of-the-ikl-guide.md';
const cells = extractObservableCells(POST_FILE);

const post = () => runReactivePost(cells, { fn, pretty });

test('post41: post has 10 live cells', () => {
  assert.equal(cells.length, 10, `expected 10 live cells, found ${cells.length}`);
});

test('post41: the committed wasm artifact exists and is a real module', () => {
  const size = statSync(L4_WASM).size;
  assert.ok(size > 200_000, `l4factoidal.wasm is only ${size} bytes — a stub, not a build`);
});

test('post41: the committed wasm serves the clParse op the page calls', async () => {
  const ops = (await l4api.l4Call('ops', [])).ops;
  assert.ok(ops.includes('clParse'), 'dispatch table is missing clParse');
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

// ---- "Proposition names and (that S)" ----

test('post41 cell "cheikesParse": cancelling-parentheses assertion flips pureCL false', async () => {
  const env = await post().value('cheikesParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
  assert.equal(env.normalized, '((that (isHuman "Brant Cheikes")))');
});

// ---- "Quantifying-in" ----

test('post41 cell "loisParse": the GUIDE\'s quantifying-in sentence parses, pureCL false', async () => {
  const env = await post().value('loisParse');
  assert.equal(env.ok, true);
  assert.equal(env.sentences, 1);
  assert.equal(env.pureCL, false);
});

// Headless-render sanity: pretty() must produce a renderable value (not
// undefined / [object Object]-shaped junk) for every named cell whose
// value is a plain object or an array of plain objects — the shapes
// this page's Table toggle renders.
test('post41: every JSON-envelope/table cell renders under pretty()', async () => {
  const p = post();
  const checked = [
    'moduleAttempt', 'groundParse', 'restrictedParse', 'cheikesParse', 'loisParse',
  ];
  for (const name of checked) {
    const value = await p.value(name);
    const rendered = pretty(value);
    const str = JSON.stringify(rendered);
    assert.ok(str !== undefined && str !== '{}' && !str.includes('"[object Object]"'),
      `cell "${name}" did not render sensibly under pretty(): ${str}`);
  }
});
