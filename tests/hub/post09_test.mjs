// Pins every code sample in docs/web/hub/09-mapping-tables-to-triples-rml.md.
//
// Fixtures are copied verbatim from the vendored W3C-community RML test
// suites: third_party/testing/rml-modules/rml-core/test-cases/RMLTC0002a-JSON/
// (JSON case, part of the rml-core 76/0/76 score) and
// third_party/testing/rml-modules/rml-io/test-cases/RMLSTC0007b/ (CSV case,
// a sibling module with its own separate score -- not part of the 76/0/76
// figure, per the post's own honesty note).

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '09-mapping-tables-to-triples-rml.md';

const cells = extractObservableCells(POST_FILE);

// The post's cells call the raw `Factoidal.rmlMap(mappingNQuads,
// sourceData, sourceKind)` contract (npm/factoidal/browser.js), not
// the typed `fn` adapter -- RML has no `fn.rmlMap` wrapper in
// docs/_includes/hub.njk today. This shim mirrors browser.js's return
// shape (`{ok, nquads}`) on top of the REAL npm/factoidal typed API's
// `rmlMap(mapping, sourceData, sourceKind, options) -> Promise<Dataset>`.
const FactoidalNode = {
  async rmlMap(mappingNQuads, sourceData, sourceKind) {
    const ds = await factoidal.rmlMap(mappingNQuads, sourceData, sourceKind, { format: 'nquads' });
    return { ok: true, nquads: ds.toNQuads() };
  },
};

test('post09: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post09 cell 1 (RMLTC0002a-JSON, rml-core): 3 triples for Venus', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, Factoidal: FactoidalNode });
  assert.equal(result.tripleCount, 3);
  const lines = result.nquads.trim().split('\n').sort();
  assert.deepEqual(lines, [
    '<http://example.com/10/Venus> <http://example.com/id> "10"^^<http://www.w3.org/2001/XMLSchema#integer> .',
    '<http://example.com/10/Venus> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> .',
    '<http://example.com/10/Venus> <http://xmlns.com/foaf/0.1/name> "Venus" .',
  ]);
});

test('post09 cell 2 (RMLSTC0007b, rml-io): 5 Friends rows, queried', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, [
    { name: 'Monica Geller', age: '33' },
    { name: 'Rachel Green', age: '34' },
    { name: 'Joey Tribbiani', age: '35' },
    { name: 'Chandler Bing', age: '36' },
    { name: 'Ross Geller', age: '37' },
  ]);
});

// ---------------------------------------------------------------------
// Direct API checks against the real vendored fixture files on disk,
// independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.join(__dirname, '..', '..');
const RML_CORE_CASE = path.join(
  REPO_ROOT, 'third_party', 'testing', 'rml-modules', 'rml-core', 'test-cases', 'RMLTC0002a-JSON');
const RML_IO_CASE = path.join(
  REPO_ROOT, 'third_party', 'testing', 'rml-modules', 'rml-io', 'test-cases', 'RMLSTC0007b');

test('post09: capabilities() reports RML support (grounds the "check first" cell pattern)', async () => {
  const caps = await factoidal.capabilities();
  assert.equal(caps.rml, true);
});

test('post09: the post\'s inlined JSON mapping/source match the real rml-core fixture files on disk', async () => {
  const mapping = fs.readFileSync(path.join(RML_CORE_CASE, 'mapping.ttl'), 'utf8');
  const source = fs.readFileSync(path.join(RML_CORE_CASE, 'student.json'), 'utf8');
  const expected = fs.readFileSync(path.join(RML_CORE_CASE, 'output.nq'), 'utf8');

  const ds = await factoidal.rmlMap(mapping, source, 'json');
  const expectedDs = await factoidal.parse(expected, { format: 'nquads' });
  assert.equal(ds.size, expectedDs.size);
  assert.equal(ds.size, 3);
});

test('post09: the post\'s inlined CSV mapping/source match the real rml-io fixture files on disk', async () => {
  const mapping = fs.readFileSync(path.join(RML_IO_CASE, 'mapping.ttl'), 'utf8');
  const source = fs.readFileSync(path.join(RML_IO_CASE, 'Friends.csv'), 'utf8');
  const expected = fs.readFileSync(path.join(RML_IO_CASE, 'default.nq'), 'utf8');

  const ds = await factoidal.rmlMap(mapping, source, 'csv');
  const expectedDs = await factoidal.parse(expected, { format: 'nquads' });
  assert.equal(ds.size, expectedDs.size);
  assert.equal(ds.size, 10);
});
