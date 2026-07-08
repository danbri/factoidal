// Pins docs/web/hub/27-transforming-and-checking-xml.md.
//
// The post's cells call Factoidal.loadNpmEntry() to reach the raw
// factoidalNpmEntry ABI directly (xsltTransform/schematronValidate
// aren't wrapped by docs/npm/foafos/browser.js yet, unlike
// xmlWellformed/xpathEval in post 25) and reference each other
// ObservableHQ-style (`abi = ...` in the first cell, read by every
// cell after it) -- so this exercises the reactive path via
// runReactivePost(), the same way post26/post28/post29 do. See
// tests/hub/_helpers.mjs.

import { createRequire } from 'node:module';
import {
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const POST_FILE = '27-transforming-and-checking-xml.md';

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

// Mirrors docs/npm/foafos/browser.js's loadNpmEntry(): resolves to the
// same ABI object every call, exactly as the browser's cached promise
// does after the first fetch.
const Factoidal = {
  async loadNpmEntry() {
    return abi;
  },
};

const cells = extractObservableCells(POST_FILE);

test('post27: post ships five live cells', () => {
  assert.equal(cells.length, 5, `expected 5 live cells, found ${cells.length}`);
});

test('post27: dependency inference names the cells in order', () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  assert.deepEqual(post.names, [
    'abi',
    'xsltResult',
    'schematronRules',
    'schematronBad',
    'schematronGood',
  ]);
});

test('post27: xsltResult builds the catalog via for-each/value-of', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  const xsltResult = await post.value('xsltResult');
  assert.equal(
    xsltResult,
    '<catalog><entry>SPARQL 1.1 by W3C</entry><entry>RDF Primer by W3C</entry></catalog>'
  );
});

test('post27: schematronBad reports one assert-fail finding as a table', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  const bad = await post.value('schematronBad');
  assert.equal(bad.kind, 'table');
  assert.deepEqual(bad.columns, ['type', 'context', 'test', 'message', 'path']);
  assert.deepEqual(bad.rows, [
    ['assert-fail', 'person', 'age', 'person must have an age', '/person'],
  ]);
});

test('post27: schematronGood clears the same rule', async () => {
  const post = runReactivePost(cells, { Factoidal, pretty });
  const good = await post.value('schematronGood');
  assert.deepEqual(good, []);
});
