// Pins every live cell in docs/web/hub/19-correlated-joins-lateral.md.
//
// node:test against the committed npm/factoidal typed API (the same
// external contract docs/_includes/hub.njk's `fn` adapter mirrors), with
// the `pretty()` stub from _helpers.mjs standing in for the browser's
// DOM-returning renderer. The cell source under test is the literal
// string extracted from the shipped post -- not a hand-copied copy.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '19-correlated-joins-lateral.md';

const cells = extractObservableCells(POST_FILE);

// Pull the display column out of a pretty() table result: for a
// single-variable/-column projection, the values in that column.
function column(tableResult, name) {
  assert.equal(tableResult.kind, 'table');
  const idx = tableResult.columns.indexOf(name);
  assert.ok(idx >= 0, `expected a '${name}' column, got ${tableResult.columns}`);
  return tableResult.rows.map((r) => r[idx]);
}

test('post19: post has 6 live cells (LAT_TTL + dataset hoisted into named cells)', () => {
  assert.equal(cells.length, 6, `expected 6 live cells, found ${cells.length}`);
});

test('post19: dependency inference wires LAT_TTL -> dataset -> every query cell', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.deepEqual(post.names.slice(0, 2), ['LAT_TTL', 'dataset']);
  assert.ok(post.infos[1].refs.includes('LAT_TTL'), 'dataset cell references LAT_TTL');
  for (const i of [2, 3, 4, 5]) {
    assert.ok(post.infos[i].refs.includes('dataset'), `cell ${i + 1} references dataset`);
  }
});

test('post19 cell 1 (parse the dataset): 7 triples', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[2]);
  assert.equal(result, 7);
});

test('post19 cell 2 (plain correlated pattern): 4 rows, carol dropped', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[3]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['s', 'label']);
  assert.equal(result.rows.length, 4);
  assert.deepEqual(column(result, 'label'), ['"Alice A"', '"Alice B"', '"Bob A"', '"Bob B"']);
  // carol has no :label, so no carol row survives the LATERAL join.
  assert.ok(!column(result, 's').some((s) => s.includes('carol')));
});

test('post19 cell 3 (top-N per group): one label per person', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[4]);
  assert.equal(result.kind, 'table');
  assert.equal(result.rows.length, 2);
  assert.deepEqual(column(result, 's'), [
    'https://example.org/alice',
    'https://example.org/bob',
  ]);
  assert.deepEqual(column(result, 'label'), ['"Alice A"', '"Bob A"']);
});

test('post19 cell 4 (LATERAL vs plain join): 2 rows vs 1 row', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[5]);
  assert.equal(result.lateralRowCount, 2);
  assert.equal(result.plainJoinRowCount, 1);
  assert.deepEqual(result.lateralLabels, ['Alice A', 'Bob A']);
  assert.deepEqual(result.plainJoinLabels, ['Alice A']);
});

// ---------------------------------------------------------------------
// Direct API checks grounding the prose's claims about the feature.
// ---------------------------------------------------------------------

test('post19: SPARQL11.Algebra.fst really defines the GP_Lateral algebra node', async () => {
  const fs = await import('node:fs');
  const path = await import('node:path');
  const { fileURLToPath } = await import('node:url');
  const dir = path.dirname(fileURLToPath(import.meta.url));
  const algebra = fs.readFileSync(
    path.join(dir, '..', '..', 'formal', 'fstar', 'SPARQL11.Algebra.fst'), 'utf8');
  assert.match(algebra, /GP_Lateral\s*:/, 'expected a GP_Lateral constructor in the algebra');
  assert.match(algebra, /lateral_substitute/, 'expected the lateral_substitute machinery the post cites');
});
