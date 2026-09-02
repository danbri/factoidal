// Pins docs/web/hub/52-persisted-store-on-your-laptop.md: the recorded
// milestone numbers of 2026-09-02 and the claims the prose makes about
// what backs them. The page renders recorded numbers; nothing runs live,
// so this test checks the data cell, the rendering cell and the prose.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

import { extractObservableCells, runReactivePost } from './_helpers.mjs';

const POST_FILE = '52-persisted-store-on-your-laptop.md';
const POST_PATH = new URL(`../../docs/web/hub/${POST_FILE}`, import.meta.url);
const cells = extractObservableCells(POST_FILE);

test('post52: two cells, data then rendering', () => {
  assert.equal(cells.length, 2);
});

// Node stand-in for hub.njk's `html` tagged template: flattens strings and
// interpolated values (arrays joined) to one string, enough to check text.
const html = (strings, ...values) =>
  strings.reduce((out, s, i) => {
    const v = values[i];
    const text = v === undefined ? '' : Array.isArray(v) ? v.join('') : String(v);
    return out + s + text;
  }, '');

test('post52: the recorded milestone data matches the worknote', async () => {
  const post = runReactivePost(cells, { html });
  const m = await post.value('milestone');
  assert.equal(m.store.triples, 888949);
  assert.equal(m.store.blocks, 13);
  const byId = Object.fromEntries(m.rows.map((r) => [r.id, r]));
  assert.equal(byId.q3.evening, '0.12 s');
  assert.equal(byId.q6.evening, '0.86 s');
  assert.equal(byId.q6.rows, 25083);
  assert.equal(byId.q6.morning, '31.8 s');
  assert.equal(m.nextRung.triples, 1290077);
  assert.equal(m.nextRung.blocks, 52);
  // Every workload query except the whole-store count answers under a second.
  for (const r of m.rows) {
    if (r.id === 'q1' || r.id === 'q2') continue;
    assert.ok(parseFloat(r.evening) < 1, `${r.id} ${r.evening}`);
  }
  const table = String(await post.value('milestoneTable'));
  assert.match(table, /888,949 triples/);
  assert.match(table, /1,290,077 triples/);
  assert.match(table, /0\.86 s/);
});

test('post52: states what backs the numbers and what is not yet a theorem', () => {
  const source = readFileSync(POST_PATH, 'utf8');
  assert.match(source, /hashLeftJoin_eq_leftJoin/);
  assert.match(source, /encode\? = some bytes/);
  assert.match(source, /631 pass, 0 fail \(out of\s+631\)/);
  assert.match(source, /535 of 535/);
  assert.match(source, /Not yet a theorem/);
  assert.match(source, /specification gate 4/);
  assert.match(source, /shardborough-storage/);
});
