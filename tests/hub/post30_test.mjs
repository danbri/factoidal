// Pins docs/web/hub/30-owl-reasoning-tableau.md.
//
// The cells call the typed `fn` methods (tableauMaterialise /
// tableauDlInconsistent / owlIsConsistent / owlEntails) and reference
// each other ObservableHQ-style, exercised via runReactivePost(). `fn`
// here is the real npm/factoidal typed API; the live page binds `fn` to
// the in-browser adapter in docs/_includes/hub.njk, which exposes the
// same methods over browser.js. See tests/hub/_helpers.mjs.

import {
  NPM_FACTOIDAL_INDEX,
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const POST_FILE = '30-owl-reasoning-tableau.md';
const fn = (await import(NPM_FACTOIDAL_INDEX)).default;

const cells = extractObservableCells(POST_FILE);

test('post30: post ships twenty-one live cells', () => {
  assert.equal(cells.length, 21, `expected 21 live cells, found ${cells.length}`);
});

test('post30: dependency inference names the cells in order', () => {
  const post = runReactivePost(cells, { fn, pretty });
  assert.deepEqual(post.names, [
    'someValuesOntology',
    'someValuesMaterialised',
    'parentOfDoctorMembers',
    'hasValueOntology',
    'hasValueMaterialised',
    'britishCitizens',
    'unsatisfiableOntology',
    'inconsistencyVerdict',
    'disjointClassesOntology',
    'disjointClassesVerdict',
    'cardinalityClashOntology',
    'cardinalityClashVerdict',
    'functionalClashOntology',
    'functionalClashVerdict',
    'satisfiableOntology',
    'satisfiableVerdict',
    'clashFamilySummary',
    'budgetOutVerdict',
    'entailmentPremise',
    'entailmentConclusion',
    'entailmentVerdict',
  ]);
});

test('post30: the tableau materialises at least one membership for the someValuesFrom ontology', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const m = await post.value('someValuesMaterialised');
  assert.ok(m.addedCount >= 1, `expected addedCount >= 1, got ${m.addedCount}`);
});

test('post30: Alice is classified as a member of ParentOfDoctor (someValuesFrom)', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const members = await post.value('parentOfDoctorMembers');
  assert.deepEqual(members, ['http://example.org/Alice']);
});

test('post30: Alice is classified as a BritishCitizen (hasValue)', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const members = await post.value('britishCitizens');
  assert.deepEqual(members, ['http://example.org/Alice']);
});

test('post30: the DL pipeline flags the unsatisfiable restriction that RL leaves consistent', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const verdict = await post.value('inconsistencyVerdict');
  assert.deepEqual(verdict, { inconsistent: true, rlAlone: false });
});

test('post30: owlIsConsistent refutes the disjoint-classes clash with a reason', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const v = await post.value('disjointClassesVerdict');
  assert.equal(v.consistent, false);
  assert.equal(typeof v.reason, 'string');
  assert.ok(v.reason.length > 0, 'expected a non-empty reason string');
});

test('post30: owlIsConsistent refutes the min/max cardinality clash', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const v = await post.value('cardinalityClashVerdict');
  assert.equal(v.consistent, false);
});

test('post30: owlIsConsistent refutes the functional-property clash', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const v = await post.value('functionalClashVerdict');
  assert.equal(v.consistent, false);
});

test('post30: owlIsConsistent leaves the satisfiable control graph consistent', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const v = await post.value('satisfiableVerdict');
  assert.equal(v.consistent, true);
  assert.equal(v.reason, undefined, 'a true verdict carries no reason');
});

test('post30: the clash-family summary is three refuted families plus one open control', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const rows = await post.value('clashFamilySummary');
  assert.equal(rows.length, 4);
  assert.deepEqual(rows.map((r) => r.consistent), [false, false, false, true]);
  // every refuted family names a reason; the open control does not.
  for (const r of rows.slice(0, 3)) assert.ok(r.reason.length > 0, `${r.family} has a reason`);
  assert.equal(rows[3].reason, '');
});

test('post30: a fuel:0 budget-out is reported as null, never a false', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const v = await post.value('budgetOutVerdict');
  assert.equal(v.consistent, null);
  assert.equal(typeof v.reason, 'string');
  assert.match(v.reason, /fuel 0/, 'the reason names the exhausted cap');
});

test('post30: owlEntails proves the someValuesFrom entailment by refutation', async () => {
  const post = runReactivePost(cells, { fn, pretty });
  const v = await post.value('entailmentVerdict');
  assert.deepEqual(v, { entailed: true, via: 'refutation' });
});
