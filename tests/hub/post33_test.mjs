// Pins every live cell in
// docs/web/hub/33-correlated-federation-lateral-service.md.
//
// node:test against the committed npm/factoidal typed API (the same
// external contract docs/_includes/hub.njk's `fn` adapter mirrors).
// The cell source under test is the literal string extracted from the
// shipped post. Layer below: tests/unit/lateral_service_unit.ml pins
// the same semantics on the extracted F* functions directly.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '33-correlated-federation-lateral-service.md';

const cells = extractObservableCells(POST_FILE);

function column(tableResult, name) {
  assert.equal(tableResult.kind, 'table');
  const idx = tableResult.columns.indexOf(name);
  assert.ok(idx >= 0, `expected a '${name}' column, got ${tableResult.columns}`);
  return tableResult.rows.map((r) => r[idx]);
}

test('post33: post has 6 live cells', () => {
  assert.equal(cells.length, 6, `expected 6 live cells, found ${cells.length}`);
});

test('post33: dependency inference wires the endpoints cell into every query cell', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.deepEqual(post.names.slice(0, 3), ['LOCAL_TTL', 'dataset', 'endpoints']);
  for (const i of [3, 4, 5]) {
    assert.ok(post.infos[i].refs.includes('endpoints'),
      `cell ${i + 1} references endpoints (ordering dependency)`);
    assert.ok(post.infos[i].refs.includes('dataset'),
      `cell ${i + 1} references dataset`);
  }
});

test('post33 endpoints cell: registers both endpoints and returns their IRIs', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const iris = await post.value('endpoints');
  assert.deepEqual(iris, [
    'https://svc-a.example/sparql',
    'https://svc-b.example/sparql',
  ]);
});

test('post33 cell "remote lookup per row": both rows answer from endpoint A', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const table = await post.value('cell0');
  assert.deepEqual(column(table, 'label'), [
    '"Alice (endpoint A)"',
    '"Bob (endpoint A)"',
  ]);
});

test('post33 cell "SERVICE ?endpoint": each row dispatched to ITS OWN endpoint', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const table = await post.value('cell1');
  assert.deepEqual(column(table, 'label'), [
    '"Alice (endpoint A)"',
    '"Bob (endpoint B)"',
  ]);
});

test('post33 cell "SILENT vs not": silent keeps 2 unextended rows, loud keeps none', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const counts = await post.value('cell2');
  assert.deepEqual(counts, {
    silentRowCount: 2,
    silentLabelsBound: 0,
    loudRowCount: 0,
  });
});
