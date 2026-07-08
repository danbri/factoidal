// Pins docs/web/hub/29-validating-data-json-schema-and-xforms.md.
//
// Like post27/post28, the cells call the typed `fn` methods now
// (jsonSchemaValidate/xformsRecalc) rather than reaching for the raw
// factoidalNpmEntry ABI, and reference each other ObservableHQ-style --
// exercised via runReactivePost(). `fn` here is the real npm/factoidal
// typed API. See tests/hub/_helpers.mjs.

import {
  NPM_FACTOIDAL_INDEX,
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const POST_FILE = '29-validating-data-json-schema-and-xforms.md';
const fn = (await import(NPM_FACTOIDAL_INDEX)).default;

const cells = extractObservableCells(POST_FILE);

test('post29: post ships five live cells', () => {
  assert.equal(cells.length, 5, `expected 5 live cells, found ${cells.length}`);
});

test('post29: dependency inference names the cells in order', () => {
  const post = runReactivePost(cells, { fn, pretty });
  assert.deepEqual(post.names, [
    'personSchema',
    'schemaAccept',
    'schemaReject',
    'xformsInstance',
    'xformsResult',
  ]);
});

test('post29: schemaAccept passes a well-formed instance', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const accept = await post.value('schemaAccept');
  assert.deepEqual(accept, { valid: true, result: 'pass', errors: [] });
});

test('post29: schemaReject fails an instance missing the required property', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const reject = await post.value('schemaReject');
  assert.equal(reject.valid, false);
  assert.equal(reject.result, 'fail');
  assert.ok(reject.errors.length > 0);
});

test('post29: xformsResult recalculates sum = a + b onto the sum leaf', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const result = await post.value('xformsResult');
  assert.equal(result.instance, '<data><a>2</a><b>3</b><sum>5</sum></data>');
  const sumValidity = result.validity.find((v) => v.target === 'sum');
  assert.ok(sumValidity, 'expected a validity entry for sum');
  assert.equal(sumValidity.value, '5');
  assert.equal(sumValidity.valid, true);
});
