// Pins every live cell in
// docs/web/hub/35-wikifunctions-extension-functions.md.
//
// node:test against the committed npm/factoidal typed API. The one
// browser-vs-test duality (post24's fn.queryHdt pattern): the page's
// `fn.loadWikifunctions()` wrapper script-injects the vendored
// wikifn-fstar engine (docs/web/hub/assets/wikifn/wikifn_engine.js);
// this test provides a Node-side twin that evaluates the SAME vendored
// file from disk — same artifact, same globals
// (wikifnCompiledCall / wikifnEngineCall), no network either way.

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const WIKIFN_ENGINE = path.join(
  __dirname, '..', '..', 'docs', 'web', 'hub', 'assets', 'wikifn', 'wikifn_engine.js');

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const fnBound = {
  ...factoidal,
  async loadWikifunctions() {
    if (typeof globalThis.wikifnCompiledCall === 'function') return true;
    (new Function(fs.readFileSync(WIKIFN_ENGINE, 'utf8')))();
    if (typeof globalThis.wikifnCompiledCall !== 'function') {
      throw new Error('vendored wikifn_engine.js did not export wikifnCompiledCall');
    }
    return true;
  },
};

const POST_FILE = '35-wikifunctions-extension-functions.md';
const cells = extractObservableCells(POST_FILE);

function column(tableResult, name) {
  assert.equal(tableResult.kind, 'table');
  const idx = tableResult.columns.indexOf(name);
  assert.ok(idx >= 0, `expected a '${name}' column, got ${tableResult.columns}`);
  return tableResult.rows.map((r) => r[idx]);
}

test('post35: post has 6 live cells', () => {
  assert.equal(cells.length, 6, `expected 6 live cells, found ${cells.length}`);
});

test('post35 wikifn cell: registers 4 ZIDs; exactly Z11040 answers via the interpreter', async () => {
  const post = runReactivePost(cells, { fn: fnBound, pretty });
  const setup = await post.value('wikifn');
  assert.deepEqual(setup, {
    registered: ['Z10052', 'Z10096', 'Z11040', 'Z10627'],
    interpreted: ['Z11040'],
  });
});

test('post35 cell "palindrome canals": 6 rows, four true (Mercer + three classics), controls false', async () => {
  const post = runReactivePost(cells, { fn: fnBound, pretty });
  const table = await post.value('cell0');
  const names = column(table, 'name');
  const pals = column(table, 'palindrome').map((v) => String(v).split('^^')[0]);
  assert.equal(names.length, 6);
  // ORDER BY DESC(?palindrome) ?name: the four true rows first, by name.
  assert.deepEqual(names.slice(0, 4), [
    '"Corinth Canal"', '"Grand Canal"', '"Kiel Canal"', '"Panama Canal"',
  ]);
  assert.deepEqual(pals, ['"true"', '"true"', '"true"', '"true"', '"false"', '"false"']);
  assert.deepEqual(names.slice(4).sort(), ['"Erie Canal"', '"Suez Canal"']);
});

test('post35 cell "filter to just those": the four palindromic canals survive', async () => {
  const post = runReactivePost(cells, { fn: fnBound, pretty });
  const table = await post.value('cell1');
  assert.deepEqual(column(table, 'name'), [
    '"Corinth Canal"', '"Grand Canal"', '"Kiel Canal"', '"Panama Canal"',
  ]);
  assert.deepEqual(column(table, 'country'), [
    '"Greece"', '"China"', '"Germany"', '"Panama"',
  ]);
});

test('post35 cell "any ZID": interpreter-backed length, compiled ROT13, ordered by letters', async () => {
  const post = runReactivePost(cells, { fn: fnBound, pretty });
  const table = await post.value('cell2');
  const letters = column(table, 'letters').map((v) => String(v).split('^^')[0]);
  const rot13 = column(table, 'rot13');
  const names = column(table, 'name');
  // Mercer's phrase has the most letters once spaces are stripped (21).
  assert.equal(names[0], '"Panama Canal"');
  assert.equal(letters[0], '"21"');
  assert.ok(rot13[0].startsWith('"Cnanzn Pnany"'), `rot13 of Panama Canal, got ${rot13[0]}`);
  // Every row got a length and a rot13 — both Wikifunctions ran per row.
  assert.equal(letters.length, 6);
  assert.ok(letters.every((l) => /^"\d+"$/.test(l)), `letters all numeric, got ${letters}`);
});
