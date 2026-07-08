// Pins docs/web/hub/29-validating-data-json-schema-and-xforms.md.
//
// Like post27/post28, the cells reach jsonSchemaValidate/xformsRecalc via
// Factoidal.loadNpmEntry() against the raw factoidalNpmEntry ABI, and
// reference each other ObservableHQ-style -- exercised via
// runReactivePost(). See tests/hub/_helpers.mjs.

import { createRequire } from 'node:module';
import {
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const POST_FILE = '29-validating-data-json-schema-and-xforms.md';

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

const cells = extractObservableCells(POST_FILE);

test('post29: post ships six live cells', () => {
  assert.equal(cells.length, 6, `expected 6 live cells, found ${cells.length}`);
});

test('post29: dependency inference names the cells in order', () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  assert.deepEqual(post.names, [
    'abi',
    'personSchema',
    'schemaAccept',
    'schemaReject',
    'xformsInstance',
    'xformsResult',
  ]);
});

test('post29: schemaAccept passes a well-formed instance', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  const accept = await post.value('schemaAccept');
  assert.deepEqual(accept, { ok: true, valid: true, result: 'pass', errors: [] });
});

test('post29: schemaReject fails an instance missing the required property', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  const reject = await post.value('schemaReject');
  assert.equal(reject.ok, true);
  assert.equal(reject.valid, false);
  assert.equal(reject.result, 'fail');
  assert.ok(reject.errors.length > 0);
});

test('post29: xformsResult recalculates sum = a + b onto the sum leaf', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  const result = await post.value('xformsResult');
  assert.equal(result.ok, true);
  assert.equal(result.instance, '<data><a>2</a><b>3</b><sum>5</sum></data>');
  const sumValidity = result.validity.find((v) => v.target === 'sum');
  assert.ok(sumValidity, 'expected a validity entry for sum');
  assert.equal(sumValidity.value, '5');
  assert.equal(sumValidity.valid, true);
});
