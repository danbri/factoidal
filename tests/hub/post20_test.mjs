// Pins every live cell in docs/web/hub/20-fulltext-search-text-query.md.
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
const POST_FILE = '20-fulltext-search-text-query.md';

const cells = extractObservableCells(POST_FILE);

// The set of matched subject IRIs from a pretty() single-column ?s table.
function subjects(tableResult) {
  assert.equal(tableResult.kind, 'table');
  const idx = tableResult.columns.indexOf('s');
  assert.ok(idx >= 0, `expected an 's' column, got ${tableResult.columns}`);
  return tableResult.rows.map((r) => r[idx]).sort();
}

test('post20: post has 9 live cells (FT_TTL + dataset hoisted into named cells)', () => {
  assert.equal(cells.length, 9, `expected 9 live cells, found ${cells.length}`);
});

test('post20: dependency inference wires FT_TTL -> dataset -> every query cell', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.deepEqual(post.names.slice(0, 2), ['FT_TTL', 'dataset']);
  assert.ok(post.infos[1].refs.includes('FT_TTL'), 'dataset cell references FT_TTL');
  for (const i of [2, 3, 4, 5, 6, 7, 8]) {
    assert.ok(post.infos[i].refs.includes('dataset'), `cell ${i + 1} references dataset`);
  }
});

test('post20 cell 1 (parse the dataset): 15 triples', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[2]);
  assert.equal(result, 15);
});

test('post20 cell 2 (2-arity "panel"): 4 subjects across labels + a title', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[3]);
  assert.deepEqual(subjects(result), [
    'http://example.org/battery',
    'http://example.org/controlpanel',
    'http://example.org/panel1',
    'http://example.org/panel2',
  ]);
});

test('post20 cell 3 (AND-by-default "solar panel"): only the 2 with both tokens', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[4]);
  assert.deepEqual(subjects(result), [
    'http://example.org/panel1',
    'http://example.org/panel2',
  ]);
});

test('post20 cell 4 (list form, rdfs:label restriction): controlpanel dropped', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[5]);
  assert.deepEqual(subjects(result), [
    'http://example.org/battery',
    'http://example.org/panel1',
    'http://example.org/panel2',
  ]);
});

test('post20 cell 5 (list form + limit 2): capped count, no ranking claim', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[6]);
  assert.deepEqual(result, { matchCount: 2 });
});

test('post20 cell 6 (no-match): zero rows, no error', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[7]);
  assert.deepEqual(result, { matchCount: 0 });
});

test('post20 cell 7 (BGP composition): text:query joins ex:status, retired dropped', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[8]);
  assert.deepEqual(subjects(result), [
    'http://example.org/controlpanel',
    'http://example.org/panel1',
    'http://example.org/panel2',
  ]);
});

// ---------------------------------------------------------------------
// Direct checks grounding the prose's claims about the feature.
// ---------------------------------------------------------------------

test('post20: SPARQL.FullText.fst exists, uses the jena-text IRI, and is honest about no scoring', async () => {
  const fs = await import('node:fs');
  const path = await import('node:path');
  const { fileURLToPath } = await import('node:url');
  const dir = path.dirname(fileURLToPath(import.meta.url));
  const ft = fs.readFileSync(
    path.join(dir, '..', '..', 'formal', 'fstar', 'SPARQL.FullText.fst'), 'utf8');
  assert.match(ft, /jena\.apache\.org\/text/, 'expected the jena-text vocabulary IRI');
  assert.match(ft, /Slice 1/, 'expected the slice-1 scope banner the post cites');
  assert.doesNotMatch(ft, /let score_bm25\b/, 'slice 1 must not yet define scoring');
});
