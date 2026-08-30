import test from 'node:test';
import assert from 'node:assert/strict';

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const cells = extractObservableCells('47-writing-hub-notebooks.md');

test('post47: minimal notebook wires Turtle through a named dataset to a query', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.deepEqual(post.names, ['notebookTurtle', 'notebookDataset', 'cell0']);
  const result = await post.value('cell0');
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['name']);
  assert.deepEqual(result.rows, [['"Alice"']]);
});
