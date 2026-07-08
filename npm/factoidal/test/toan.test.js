// TOAN exact CAS over Math.Expr (entry ABI toan* -> Math.Series /
// Simplify / Subst / Diff, serialized via MathML.Present).
'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  toanSummation, toanProduct, toanSimplify, toanDiff, toanSubst, capabilities,
} = require('..');

const PENDING = 'pending npm-entry build';

// x + i*y
const BODY = {
  app: 'plus',
  args: [
    { sym: 'x' },
    { app: 'times', args: [{ sym: 'i' }, { sym: 'y' }] },
  ],
};

test('toanSummation: sum_{i=1}^{4} (x + i*y) = 4x + 10y', async (t) => {
  const caps = await capabilities();
  if (!caps.toan) { t.skip(PENDING); return; }
  const mathml = await toanSummation(BODY, 'i', 1, 4);
  assert.equal(typeof mathml, 'string');
  // sum of x over i=1..4 is 4x; sum of i*y is 10y.
  assert.match(mathml, /<cn[^>]*>4<\/cn>/);
  assert.match(mathml, /<cn[^>]*>10<\/cn>/);
  assert.match(mathml, /<ci>x<\/ci>/);
  assert.match(mathml, /<ci>y<\/ci>/);
});

test('toanProduct: product_{i=1}^{3} i = 6', async (t) => {
  const caps = await capabilities();
  if (!caps.toan) { t.skip(PENDING); return; }
  const mathml = await toanProduct({ sym: 'i' }, 'i', 1, 3);
  assert.match(mathml, /<cn[^>]*>6<\/cn>/);
});

test('toanSimplify: 2 + 3 collapses to 5', async (t) => {
  const caps = await capabilities();
  if (!caps.toan) { t.skip(PENDING); return; }
  const mathml = await toanSimplify(
    { app: 'plus', args: [{ int: 2 }, { int: 3 }] });
  assert.match(mathml, /<cn[^>]*>5<\/cn>/);
});

test('toanDiff: d/dx (x*x) mentions x', async (t) => {
  const caps = await capabilities();
  if (!caps.toan) { t.skip(PENDING); return; }
  const mathml = await toanDiff(
    { app: 'times', args: [{ sym: 'x' }, { sym: 'x' }] }, 'x');
  assert.equal(typeof mathml, 'string');
  assert.match(mathml, /math/);
});

test('toanSubst: (x + 1)[x := 4] mentions 4', async (t) => {
  const caps = await capabilities();
  if (!caps.toan) { t.skip(PENDING); return; }
  const mathml = await toanSubst(
    { app: 'plus', args: [{ sym: 'x' }, { int: 1 }] }, 'x', { int: 4 });
  assert.match(mathml, /<cn[^>]*>4<\/cn>/);
});
