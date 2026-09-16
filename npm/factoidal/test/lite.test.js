// factoidal/lite (issue #684) -- the 'lite' profile entry point.
// Exercises the core surface end to end against the real lite npm-
// entry bundle, and pins the boundary: no SHACL (etc.), and an
// RDF/XML parse routes to a clear error naming the full bundle
// instead of silently misbehaving.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const lite = require('../lite.js');

async function entryAvailable() {
  try {
    return !!(await lite.capabilities()).entry;
  } catch (_) {
    return false;
  }
}

const TTL = '@prefix ex: <http://example.org/> .\n' +
  'ex:alice ex:name "Alice" ; ex:knows ex:bob .\n' +
  'ex:bob ex:name "Bob" .\n';

test('lite: parses, queries, updates, serialises, opens a handle', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('lite npm-entry bundle not present');
    return;
  }

  const ds = await lite.parse(TTL, { format: 'turtle' });
  assert.equal(ds.size, 3);
  assert.deepEqual(ds.prefixes, { ex: 'http://example.org/' });

  const rows = await lite.query(ds,
    'PREFIX ex: <http://example.org/> SELECT ?s ?n WHERE { ?s ex:name ?n }');
  assert.equal(rows.length, 2);

  const updated = await lite.update(ds,
    'PREFIX ex: <http://example.org/> INSERT DATA { ex:carol ex:name "Carol" }');
  assert.equal(updated.size, 4);

  const nq = await lite.serialize(updated, { format: 'nquads' });
  assert.match(nq, /carol/i);
  const ttl = await lite.serialize(updated, { format: 'turtle' });
  assert.match(ttl, /@prefix/);

  const handle = await lite.openDataset(TTL, { format: 'turtle' });
  assert.equal(handle.size, 3);
  const handleRows = await handle.query(
    'PREFIX ex: <http://example.org/> SELECT ?s WHERE { ?s ex:name ?n }');
  assert.equal(handleRows.length, 2);
  await handle.close();
});

test('lite: capabilities().profile === "lite"', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('lite npm-entry bundle not present');
    return;
  }
  const caps = await lite.capabilities();
  assert.equal(caps.profile, 'lite');
  assert.equal(caps.datasetHandles, true);
});

test('lite: shaclValidate is absent from the export list', () => {
  assert.equal('shaclValidate' in lite, false);
  assert.equal('shexValidate' in lite, false);
  assert.equal('owlClosure' in lite, false);
  assert.equal('jsonldToRdf' in lite, false);
  assert.equal('csvwToRdf' in lite, false);
  assert.equal('rmlMap' in lite, false);
  assert.equal('rifEval' in lite, false);
  assert.equal('queryHdt' in lite, false);
});

test('lite: parsing "rdfxml" rejects with the routing error naming the full bundle', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('lite npm-entry bundle not present');
    return;
  }
  await assert.rejects(
    lite.parse('<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"/>',
      { format: 'rdfxml' }),
    /lite bundle|factoidal-npm-entry\.js/i);
});

test('lite: entailment regimes reject -- no CLI bundle in the lite profile', async () => {
  await assert.rejects(
    lite.query(TTL, 'SELECT * WHERE { ?s ?p ?o }', { format: 'turtle', entail: 'RDFS' }),
    /lite/i);
});

test('lite: engine is "js-lite"', () => {
  assert.equal(lite.engine, 'js-lite');
});

test('lite: exports the core surface (ParseError, DatasetHandle, Dataset)', () => {
  assert.equal(typeof lite.ParseError, 'function');
  assert.equal(typeof lite.DatasetHandle, 'function');
  assert.equal(typeof lite.Dataset, 'function');
  assert.equal(typeof lite.dataFactory, 'object');
  assert.equal(typeof lite.version, 'string');
});
