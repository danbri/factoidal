// Pins every live cell in docs/web/hub/34-extension-functions.md.
//
// node:test against the committed npm/factoidal typed API (the same
// external contract docs/_includes/hub.njk's `fn` adapter mirrors).
// The cell source under test is the literal string extracted from the
// shipped post. Layers below: tests/unit/extension_function_unit.ml
// (native F* dispatch) and npm/factoidal/test/extension-functions.test.js
// (async trampoline).

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '34-extension-functions.md';

const cells = extractObservableCells(POST_FILE);

function column(tableResult, name) {
  assert.equal(tableResult.kind, 'table');
  const idx = tableResult.columns.indexOf(name);
  assert.ok(idx >= 0, `expected a '${name}' column, got ${tableResult.columns}`);
  return tableResult.rows.map((r) => r[idx]);
}

test('post34: post has 7 live cells', () => {
  assert.equal(cells.length, 7, `expected 7 live cells, found ${cells.length}`);
});

test('post34 cell "the error is the specification": unbound in BIND, dropped in FILTER', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const counts = await post.value('cell0');
  assert.deepEqual(counts, {
    bindRowCount: 2,
    bindXBoundCount: 0,
    filterRowCount: 0,
  });
});

test('post34 cell "sync FILTER": fn:isAdult keeps only alice', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const table = await post.value('cell1');
  assert.deepEqual(column(table, 's'), ['http://example.org/alice']);
});

test('post34 cell "async BIND": fn:category labels adult/child through the trampoline', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const table = await post.value('cell2');
  assert.deepEqual(column(table, 'c'), ['"adult"', '"child"']);
});

test('post34 cell "wasm": fn:wasmAdd computes age+100 inside WebAssembly', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const table = await post.value('cell3');
  const values = column(table, 'plus100').map((v) => String(v).split('^^')[0]);
  assert.deepEqual(values, ['"130"', '"107"']);
});

test('post34 cell "F*-verified body": fn:sigmoid computes sigma(age/10) via Math.Sigmoid', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const table = await post.value('cell4');
  const scores = column(table, 'score').map((v) => String(v).split('^^')[0]);
  assert.equal(scores.length, 2);
  // sigma(3.0) ~ 0.9525..., sigma(0.7) ~ 0.668... — pin the leading
  // digits, not the full fixed-precision expansion.
  assert.ok(scores[0].startsWith('"0.95'), `alice score ${scores[0]}`);
  assert.ok(scores[1].startsWith('"0.6'), `bob score ${scores[1]}`);
});
