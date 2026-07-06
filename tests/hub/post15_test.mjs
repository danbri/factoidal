// Pins the live cell in docs/web/hub/15-how-fast-the-performance-story.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed) — mirrors npm/factoidal/test's own harness style.
// This post's numbers (the tables) are cited prose, not executable
// claims -- there is nothing to pin about a historical benchmark run.
// The one thing this file DOES pin is that the live in-browser
// illustration cell actually parses/queries what it claims to.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '15-how-fast-the-performance-story.md';

const cells = extractObservableCells(POST_FILE);

test('post15: post has at least 1 live cell', () => {
  assert.ok(cells.length >= 1, `expected >= 1 live cell, found ${cells.length}`);
});

test('post15 cell 1 (in-browser timing illustration): 3000 generated triples round-trip and count correctly', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, pretty });
  assert.equal(result.kind, 'table');
  const asObject = Object.fromEntries(result.rows);
  assert.equal(asObject.triplesGenerated, 3000);
  assert.equal(asObject.countResult, 3000, 'the generated triples parsed and queried correctly');
  assert.equal(typeof asObject.parseAndQueryMs, 'number');
  assert.ok(asObject.parseAndQueryMs >= 0, 'timing is a non-negative number');
  assert.match(String(asObject.note), /not a benchmark/);
});
