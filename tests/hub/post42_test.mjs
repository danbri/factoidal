// Pins every live cell in docs/web/hub/42-cottas-a-store-at-scale.md.
//
// `fn === factoidal`, the real npm/factoidal typed API (same shape the
// browser adapter in docs/_includes/hub.njk exposes: parse/query/
// toCottas/openCottas/queryCottas/closeCottas). The post's `fetch()`
// call for the committed fixture is stubbed to read
// docs/web/hub/assets/data/cottas-corpus.trig straight off disk (same
// pattern as tests/hub/post21_test.mjs / post24_test.mjs) -- the URL
// argument is only checked for the fixture's filename, since Node has
// no `location` to resolve a page-relative path against.
//
// Every expected value below comes from
// docs/web/hub/assets/data/gen-cottas-corpus.mjs's exported formulas,
// not hand-typed magic numbers -- if the fixture is regenerated with
// the same N_PEOPLE/N_ORGS/N_PROJECTS, these assertions keep passing
// without editing.
//
// The reactive module is built ONCE (module scope) and its cells'
// values read via run.value(name) from every test -- rebuilding it per
// test would re-run fetch+parse+toCottas (several seconds each) once
// per assertion for no benefit, since the Observable runtime caches a
// variable's computed value across repeated .value() calls on the same
// module instance.

import fs from 'node:fs';
import path from 'node:path';

import { NPM_FACTOIDAL_INDEX, HUB_POST_DIR, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';
import * as Corpus from '../../docs/web/hub/assets/data/gen-cottas-corpus.mjs';

import test, { after } from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '42-cottas-a-store-at-scale.md';
const FIXTURE_PATH = path.join(HUB_POST_DIR, 'assets', 'data', 'cottas-corpus.trig');

const cells = extractObservableCells(POST_FILE);

test('post42: post has exactly 8 live cells', () => {
  assert.equal(cells.length, 8, `expected 8 live cells, found ${cells.length}`);
});

// Stub fetch for the whole file: only this post's fixture cell calls
// it, and the runtime computes `fixture` (and everything downstream)
// at most once regardless of how many tests read a value below.
const previousFetch = globalThis.fetch;
globalThis.fetch = async (url) => {
  assert.match(String(url), /cottas-corpus\.trig$/);
  const text = fs.readFileSync(FIXTURE_PATH, 'utf8');
  return { ok: true, async text() { return text; } };
};
after(() => {
  if (previousFetch === undefined) delete globalThis.fetch; else globalThis.fetch = previousFetch;
});

const run = runReactivePost(cells, { fn: factoidal, pretty });

const TEST_PERSON = 375; // 1..N_PEOPLE=500
const EXPECTED_ORG = Corpus.orgIdForPerson(TEST_PERSON);
const EXPECTED_PROJECT = Corpus.projectIdForPerson(TEST_PERSON);

test('post42: fixture fetch cell reads the committed corpus text', async () => {
  const fixture = await run.value('fixture');
  assert.equal(typeof fixture.text, 'string');
  assert.ok(fixture.text.startsWith('@prefix ex:'));
  assert.equal(fixture.textBytes, fixture.text.length);
  assert.ok(fixture.fetchMs >= 0);
});

test('post42: parsed cell reports the labelled 4,000-triple count', async () => {
  const parsed = await run.value('parsed');
  assert.equal(parsed.tripleCount, Corpus.TOTAL_TRIPLES);
  assert.equal(Corpus.TOTAL_TRIPLES, 4000);
  assert.ok(parsed.parseMs >= 0);
});

test('post42: store cell (toCottas + openCottas) produces a non-empty store byte size and a handle', async () => {
  const store = await run.value('store');
  assert.ok(store.storeBytes > 0, 'toCottas() bytes should be non-empty');
  assert.ok(store.textBytes > 0);
  assert.equal(typeof store.handle, 'string');
  assert.ok(store.toCottasMs >= 0);
  assert.ok(store.openMs >= 0);
});

test('post42: storeTimings cell -- 3 queries, each run 3 times, rows match the fixture', async () => {
  const storeTimings = await run.value('storeTimings');
  assert.equal(storeTimings.length, 3);
  const byQuery = Object.fromEntries(storeTimings.map((r) => [r.query, r]));
  assert.equal(byQuery['point lookup'].rows, 1);
  assert.equal(byQuery['star join'].rows, 5);
  assert.equal(byQuery['cross-graph GRAPH join'].rows, 1);
  for (const r of storeTimings) {
    assert.equal(r.runs.length, 3, `${r.query}: expected 3 timed runs`);
    assert.ok(r.medianMs >= 0, `${r.query}: median should be non-negative`);
    for (const t of r.runs) assert.ok(t >= 0);
  }
});

test('post42: memoryTimings cell -- same 3 queries against the parsed dataset, same row counts', async () => {
  const memoryTimings = await run.value('memoryTimings');
  assert.equal(memoryTimings.length, 3);
  const byQuery = Object.fromEntries(memoryTimings.map((r) => [r.query, r]));
  assert.equal(byQuery['point lookup'].rows, 1);
  assert.equal(byQuery['star join'].rows, 5);
  assert.equal(byQuery['cross-graph GRAPH join'].rows, 1);
  for (const r of memoryTimings) assert.ok(r.ms >= 0, `${r.query}: timing should be non-negative`);
});

test('post42: comparisonTable cell -- array of plain row objects (Table-toggle shape), store and memory agree on every row', async () => {
  const comparisonTable = await run.value('comparisonTable');
  assert.equal(comparisonTable.length, 3);
  for (const row of comparisonTable) {
    assert.equal(typeof row, 'object');
    assert.equal(Array.isArray(row), false, 'each row must be a plain object, not an array/Map');
    assert.equal(row.answersMatch, true, `${row.query}: store and memory row counts should match`);
    assert.equal(row.storeRows, row.memoryRows);
  }
  // Table-toggle contract: pretty() must turn this into a table (not
  // fall through to the plain-object/scalar branches).
  const rendered = pretty(comparisonTable);
  assert.equal(rendered.kind, 'table');
  assert.deepEqual(rendered.columns, Object.keys(comparisonTable[0]));
});

test('post42: reopened cell -- openCottas() on the same bytes answers over the full corpus again', async () => {
  const reopened = await run.value('reopened');
  assert.equal(reopened.count, Corpus.TOTAL_TRIPLES);
  assert.ok(reopened.openMs >= 0);
});

test('post42: point lookup -- store and memory return the pinned name, not just a row count', async () => {
  const store = await run.value('store');
  const queries = await run.value('queries');
  const parsed = await run.value('parsed');

  const storeRows = await factoidal.queryCottas(store.handle, queries.point);
  const memoryRows = await factoidal.query(parsed.dataset, queries.point);

  assert.equal(storeRows.length, 1);
  assert.equal(memoryRows.length, 1);
  const expectedName = Corpus.personName(TEST_PERSON);
  assert.equal(storeRows[0].get('name').value, expectedName);
  assert.equal(memoryRows[0].get('name').value, expectedName);
});

test('post42: star join -- store and memory return the pinned 5-predicate set for one person, and agree with each other', async () => {
  const store = await run.value('store');
  const queries = await run.value('queries');
  const parsed = await run.value('parsed');

  const storeRows = await factoidal.queryCottas(store.handle, queries.star);
  const memoryRows = await factoidal.query(parsed.dataset, queries.star);
  assert.equal(storeRows.length, 5);
  assert.equal(memoryRows.length, 5);

  const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
  const FOAF = Corpus.FOAF;
  const EX = Corpus.EX;
  const expected = new Set([
    `${RDF_TYPE}|${FOAF}Person`,
    `${FOAF}name|${Corpus.personName(TEST_PERSON)}`,
    `${FOAF}age|${Corpus.personAge(TEST_PERSON)}`,
    `${FOAF}mbox|mailto:${Corpus.personMbox(TEST_PERSON)}`,
    `${EX}memberSince|${Corpus.personMemberSince(TEST_PERSON)}`,
  ]);

  function toSet(rows) {
    return new Set(rows.map((row) => `${row.get('p').value}|${row.get('o').value}`));
  }
  assert.deepEqual(toSet(storeRows), expected);
  assert.deepEqual(toSet(memoryRows), expected);
});

test('post42: cross-graph GRAPH join -- store and memory both resolve person -> org name across 3 named graphs', async () => {
  const store = await run.value('store');
  const queries = await run.value('queries');
  const parsed = await run.value('parsed');

  const storeRows = await factoidal.queryCottas(store.handle, queries.crossGraph);
  const memoryRows = await factoidal.query(parsed.dataset, queries.crossGraph);
  assert.equal(storeRows.length, 1);
  assert.equal(memoryRows.length, 1);

  const expectedPersonName = Corpus.personName(TEST_PERSON);
  const expectedOrgName = Corpus.orgName(EXPECTED_ORG);
  assert.equal(storeRows[0].get('personName').value, expectedPersonName);
  assert.equal(storeRows[0].get('orgName').value, expectedOrgName);
  assert.equal(memoryRows[0].get('personName').value, expectedPersonName);
  assert.equal(memoryRows[0].get('orgName').value, expectedOrgName);
});

test('post42: the fixture\'s affiliation link for the test person matches the generator formula independently', () => {
  // Sanity check on the formula itself (not the engine): the query
  // above trusts orgIdForPerson(375); confirm it lands inside 1..N_ORGS
  // and that a DIFFERENT person's org need not be the same one -- i.e.
  // the mapping is not degenerate.
  assert.ok(EXPECTED_ORG >= 1 && EXPECTED_ORG <= Corpus.N_ORGS);
  assert.ok(EXPECTED_PROJECT >= 1 && EXPECTED_PROJECT <= Corpus.N_PROJECTS);
  assert.notEqual(Corpus.orgIdForPerson(1), Corpus.orgIdForPerson(TEST_PERSON));
});
