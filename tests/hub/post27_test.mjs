// Pins docs/web/hub/27-transforming-and-checking-xml.md.
//
// The post's cells call `fn.xsltTransform`/`fn.schematronValidate` --
// typed methods now, the same shape `fn.xmlWellformed`/`fn.xpathEval`
// already had -- and reference each other ObservableHQ-style
// (`xsltResult`, `schematronRules`, `schematronBad`, `schematronGood`)
// -- so this exercises the reactive path via runReactivePost(), the
// same way post26/post28/post29 do. `fn` here is the real
// npm/factoidal typed API (NPM_FACTOIDAL_INDEX), which already has
// xsltTransform/schematronValidate. See tests/hub/_helpers.mjs.

import {
  NPM_FACTOIDAL_INDEX,
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const POST_FILE = '27-transforming-and-checking-xml.md';
const fn = (await import(NPM_FACTOIDAL_INDEX)).default;

const cells = extractObservableCells(POST_FILE);

test('post27: post ships four live cells', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

test('post27: dependency inference names the cells in order', () => {
  const post = runReactivePost(cells, { fn, pretty });
  assert.deepEqual(post.names, [
    'xsltResult',
    'schematronRules',
    'schematronBad',
    'schematronGood',
  ]);
});

test('post27: xsltResult builds the catalog via for-each/value-of', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const xsltResult = await post.value('xsltResult');
  assert.equal(
    xsltResult,
    '<catalog><entry>SPARQL 1.1 by W3C</entry><entry>RDF Primer by W3C</entry></catalog>'
  );
});

test('post27: schematronBad reports one assert-fail finding as a table', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const bad = await post.value('schematronBad');
  assert.equal(bad.kind, 'table');
  assert.deepEqual(bad.columns, ['type', 'context', 'test', 'message', 'path']);
  assert.deepEqual(bad.rows, [
    ['assert-fail', 'person', 'age', 'person must have an age', '/person'],
  ]);
});

test('post27: schematronGood clears the same rule', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const good = await post.value('schematronGood');
  assert.deepEqual(good, []);
});
