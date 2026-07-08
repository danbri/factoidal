// JSON Schema draft-07 validation (entry ABI jsonSchemaValidate ->
// JSONSchema.Validate).
'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { jsonSchemaValidate, capabilities } = require('..');

const PENDING = 'pending npm-entry build';

test('jsonSchemaValidate: {type:"integer"} accepts an integer', async (t) => {
  const caps = await capabilities();
  if (!caps.jsonSchema) { t.skip(PENDING); return; }
  const r = await jsonSchemaValidate('{"type":"integer"}', '5');
  assert.equal(r.valid, true);
  assert.equal(r.result, 'pass');
  assert.deepEqual(r.errors, []);
});

test('jsonSchemaValidate: {type:"integer"} rejects a string', async (t) => {
  const caps = await capabilities();
  if (!caps.jsonSchema) { t.skip(PENDING); return; }
  const r = await jsonSchemaValidate('{"type":"integer"}', '"hello"');
  assert.equal(r.valid, false);
  assert.notEqual(r.result, 'pass');
  assert.ok(r.errors.length >= 1);
});
