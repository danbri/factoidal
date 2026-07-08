// Pins docs/web/hub/28-verified-math-rendered.md.
//
// Like post27, the cells reach mathmlEval/toanSummation/matrixDeterminant
// via Factoidal.loadNpmEntry() against the raw factoidalNpmEntry ABI, and
// reference each other ObservableHQ-style (`abi`, then `summationMathml`,
// then the Content->Presentation cell that reads it) -- exercised via
// runReactivePost(). `html` has no DOM in Node, so this file supplies a
// minimal tagged-template stub that mirrors @observablehq/stdlib's
// template() for plain-string interpolations (see
// third_party/observable/dist/stdlib.esm.js's `template()`: a
// non-Node/non-Array interpolated value is concatenated into the source
// string as-is, unescaped, before the browser parses it as markup) --
// so the test can assert on the exact markup the real `html` would also
// receive, without needing a DOM to build it.

import { createRequire } from 'node:module';
import {
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const POST_FILE = '28-verified-math-rendered.md';

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

const Factoidal = {
  async loadNpmEntry() {
    return abi;
  },
};

// Node-side stand-in for @observablehq/stdlib's `html` tagged template.
// Only string interpolations appear in this post's cells (no DOM Node
// or Array parts), so raw string concatenation matches template()'s
// real behavior for that case exactly -- see the file banner above.
function html(strings, ...values) {
  let out = strings[0];
  for (let i = 0; i < values.length; i++) out += String(values[i]) + strings[i + 1];
  return out;
}

const cells = extractObservableCells(POST_FILE);

test('post28: post ships eight live cells', () => {
  assert.equal(cells.length, 8, `expected 8 live cells, found ${cells.length}`);
});

test('post28: dependency inference names the cells in order', () => {
  const post = runReactivePost(cells, { Factoidal, pretty, html });
  // The one anonymous cell (`pretty(mathmlDemo)`, cell index 3) gets the
  // runtime's fallback name `cell0` -- the anon counter increments only
  // over anonymous cells, not the absolute cell index. See
  // tests/hub/_helpers.mjs's runReactivePost().
  assert.deepEqual(post.names, [
    'abi',
    'formatMathValue',
    'mathmlDemo',
    'cell0',
    'summationMathml',
    'summationPresentation',
    'determinantPlain',
    'determinantExact',
  ]);
});

test('post28: mathmlDemo evaluates 2+3 to an exact rational and 1/0 to undef', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty, html });
  const demo = await post.value('mathmlDemo');
  assert.deepEqual(demo, [
    { contentMathml: '<apply><plus/><cn>2</cn><cn>3</cn></apply>', value: '5/1' },
    { contentMathml: '<apply><divide/><cn>1</cn><cn>0</cn></apply>', value: 'undef (division-by-zero)' },
  ]);
});

test('post28: the pretty(mathmlDemo) cell renders a two-row table', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty, html });
  const table = await post.value('cell0');
  assert.equal(table.kind, 'table');
  assert.equal(table.rows.length, 2);
});

test('post28: summationMathml carries the verified Content MathML for the sum', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty, html });
  const mathml = await post.value('summationMathml');
  assert.equal(
    mathml,
    '<math xmlns="http://www.w3.org/1998/Math/MathML">' +
      '<apply><plus/>' +
      '<apply><times/><cn type="integer">10</cn><ci>y</ci></apply>' +
      '<apply><times/><cn type="integer">4</cn><ci>x</ci></apply>' +
      '</apply></math>'
  );
});

test('post28: summationPresentation converts to Presentation MathML for display', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty, html });
  const presentation = await post.value('summationPresentation');
  assert.equal(
    presentation,
    '<math display="block">' +
      '<mrow>' +
      '<mrow><mn>10</mn><mo>&#8290;</mo><mi>y</mi></mrow>' +
      '<mo>+</mo>' +
      '<mrow><mn>4</mn><mo>&#8290;</mo><mi>x</mi></mrow>' +
      '</mrow>' +
      '</math>'
  );
});

test('post28: determinantPlain is -2, determinantExact is the exact fraction 1/4', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty, html });
  assert.equal(await post.value('determinantPlain'), '-2');
  assert.equal(await post.value('determinantExact'), '1/4');
});
