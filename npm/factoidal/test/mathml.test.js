// Content MathML evaluation (entry ABI mathmlEval -> MathML.Content).
'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { mathmlEval, capabilities } = require('..');

const PENDING = 'pending npm-entry build';

const M = 'http://www.w3.org/1998/Math/MathML';

test('mathmlEval: 2 + 3 = 5/1 (exact rational)', async (t) => {
  const caps = await capabilities();
  if (!caps.mathml) { t.skip(PENDING); return; }
  const xml = `<math xmlns="${M}">
    <apply><plus/><cn>2</cn><cn>3</cn></apply>
  </math>`;
  const v = await mathmlEval(xml, {});
  assert.equal(v.kind, 'rat');
  assert.equal(v.num, 5);
  assert.equal(v.den, 1);
});

test('mathmlEval: division by zero is undef, not a bogus number', async (t) => {
  const caps = await capabilities();
  if (!caps.mathml) { t.skip(PENDING); return; }
  const xml = `<math xmlns="${M}">
    <apply><divide/><cn>1</cn><cn>0</cn></apply>
  </math>`;
  const v = await mathmlEval(xml, {});
  assert.equal(v.kind, 'undef');
  assert.equal(typeof v.reason, 'string');
});
