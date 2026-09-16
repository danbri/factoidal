import test from 'node:test';
import assert from 'node:assert/strict';

import {
  NPM_FACTOIDAL_INDEX,
  extractObservableCells,
  extractObservableCellsWithFlags,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const cells = extractObservableCells('47-writing-hub-notebooks.md');
const cellsWithFlags = extractObservableCellsWithFlags('47-writing-hub-notebooks.md');

test('post47: minimal notebook wires Turtle through a named dataset to a query', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.deepEqual(post.names, [
    'notebookTurtle',
    'notebookDataset',
    'rows',
    'cell0',
    'notebookRowCount',
    'notebookHelpers',
  ]);
  const result = await post.value('cell0');
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['name']);
  assert.deepEqual(result.rows, [['"Alice"']]);
});

test('post47: an earlier cell calling the closed library cell at the end resolves the forward reference', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const count = await post.value('notebookRowCount');
  assert.equal(count, 1);
});

test('post47: the last cell is the closed, titled library cell (fence flags)', () => {
  assert.equal(cellsWithFlags.length, 6);
  const last = cellsWithFlags[cellsWithFlags.length - 1];
  assert.deepEqual(last.flags, { closed: true, title: 'Library: notebook helpers' });
  assert.match(last.source, /notebookHelpers\s*=\s*\(\{/);
  // Every other cell in this post is unflagged.
  for (const cell of cellsWithFlags.slice(0, -1)) {
    assert.deepEqual(cell.flags, { closed: false, title: null });
  }
});
