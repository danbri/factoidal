// Pins docs/web/hub/30-owl-reasoning-tableau.md.
//
// The cells call the typed `fn` methods (tableauMaterialise /
// tableauDlInconsistent) and reference each other ObservableHQ-style,
// exercised via runReactivePost(). `fn` here is the real npm/factoidal
// typed API; the live page binds `fn` to the in-browser adapter in
// docs/_includes/hub.njk, which exposes the same two methods over
// browser.js. See tests/hub/_helpers.mjs.

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

test('post30: post ships eight live cells', () => {
  assert.equal(cells.length, 8, `expected 8 live cells, found ${cells.length}`);
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
