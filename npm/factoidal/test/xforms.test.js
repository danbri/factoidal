// XForms recalculate (entry ABI xformsRecalc -> XForms.Bind).
'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { xformsRecalc, capabilities } = require('..');

const PENDING = 'pending npm-entry build';

const INSTANCE = '<data><x>5</x><y>0</y></data>';

test('xformsRecalc: constant calculate writes the leaf', async (t) => {
  const caps = await capabilities();
  if (!caps.xforms) { t.skip(PENDING); return; }
  const r = await xformsRecalc(INSTANCE, [{ target: 'y', calculate: '7' }]);
  assert.equal(typeof r.instance, 'string');
  assert.ok(Array.isArray(r.validity));
  // the recalculated leaf y holds 7
  assert.match(r.instance, /<y>7<\/y>/);
  const yv = r.validity.find((v) => v.target === 'y');
  assert.ok(yv, 'expected a validity entry for y');
  assert.equal(yv.value, '7');
});

test('xformsRecalc: no binds leaves the instance well-formed', async (t) => {
  const caps = await capabilities();
  if (!caps.xforms) { t.skip(PENDING); return; }
  const r = await xformsRecalc(INSTANCE, []);
  assert.equal(typeof r.instance, 'string');
  assert.deepEqual(r.validity, []);
});
