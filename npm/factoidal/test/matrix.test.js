// Exact matrix / vector algebra (entry ABI matrix* -> Math.Matrix).
'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  matrixDeterminant, matrixScalarProduct, matrixVectorProduct,
  matrixOuterProduct, capabilities,
} = require('..');

const PENDING = 'pending npm-entry build';

test('matrixDeterminant: 2x2 determinant is exact', async (t) => {
  const caps = await capabilities();
  if (!caps.matrix) { t.skip(PENDING); return; }
  const r = await matrixDeterminant([[1, 2], [3, 4]]);
  assert.equal(r.result, '-2'); // 1*4 - 2*3
});

test('matrixDeterminant: non-square is undefined', async (t) => {
  const caps = await capabilities();
  if (!caps.matrix) { t.skip(PENDING); return; }
  const r = await matrixDeterminant([[1, 2, 3], [4, 5, 6]]);
  assert.equal(r.result, 'undef');
  assert.match(r.reason, /square/);
});

test('matrixScalarProduct: dot product of two 3-vectors', async (t) => {
  const caps = await capabilities();
  if (!caps.matrix) { t.skip(PENDING); return; }
  const r = await matrixScalarProduct([1, 2, 3], [4, 5, 6]);
  assert.equal(r.result, '32'); // 4 + 10 + 18
});

test('matrixVectorProduct: cross product of unit vectors', async (t) => {
  const caps = await capabilities();
  if (!caps.matrix) { t.skip(PENDING); return; }
  // e_x x e_y = e_z
  const r = await matrixVectorProduct([1, 0, 0], [0, 1, 0]);
  assert.match(r.result, /0.*0.*1|\[?0.*1/);
});

test('matrixOuterProduct: outer product yields a matrix', async (t) => {
  const caps = await capabilities();
  if (!caps.matrix) { t.skip(PENDING); return; }
  const r = await matrixOuterProduct([1, 2], [3, 4]);
  assert.equal(typeof r.result, 'string');
  assert.ok(r.result.length > 0);
});

test('matrixDeterminant: exact rational entries', async (t) => {
  const caps = await capabilities();
  if (!caps.matrix) { t.skip(PENDING); return; }
  // [[1/2, 0],[0, 1/2]] determinant = 1/4
  const r = await matrixDeterminant([[[1, 2], 0], [0, [1, 2]]]);
  assert.equal(r.result, '1/4');
});
