// Unit tests for queryHdt (lib/api.js) -- a SPARQL 1.1 query over a
// read-only HDT (Header-Dictionary-Triples) artifact's raw bytes,
// driven through the CLI's `--data-hdt` backend. No npm-entry ABI
// bundle needed: this is a CLI-only capability, exercised through
// index.js's typed wrapper (fn.js re-exports it unchanged -- see
// fn.js's "Typed engine functions" section).
//
// Fixture and expected count (343) are the same ones
// docs/web/hub/24-hdt-header-dictionary-triples.md's live cells and
// tests/hub/post24_test.mjs pin.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const engine = require('..'); // index.js

const FIXTURE_HDT = path.resolve(
  __dirname, '..', '..', '..', 'third_party', 'testing', 'hdt', 'rml-core-ontology.hdt');

const haveFixture = fs.existsSync(FIXTURE_HDT);

test('queryHdt: SELECT COUNT(*) over the RML-Core HDT fixture is 343', { skip: !haveFixture && 'HDT fixture not found' }, async () => {
  const bytes = fs.readFileSync(FIXTURE_HDT);
  const rows = await engine.queryHdt(bytes, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
  assert.equal(rows.length, 1);
  assert.equal(rows[0].get('n').value, '343');
});

test('queryHdt: ASK over the same fixture is true', { skip: !haveFixture && 'HDT fixture not found' }, async () => {
  const bytes = fs.readFileSync(FIXTURE_HDT);
  const result = await engine.queryHdt(bytes, 'ASK { ?s ?p ?o }');
  assert.equal(result, true);
});

test('queryHdt: SELECT bindings carry real RDF/JS terms (owl:Class labels)', { skip: !haveFixture && 'HDT fixture not found' }, async () => {
  const bytes = fs.readFileSync(FIXTURE_HDT);
  const query = `PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?class ?label WHERE {
  ?class a owl:Class ; rdfs:label ?label .
} ORDER BY ?label`;
  const rows = await engine.queryHdt(bytes, query);
  assert.ok(rows.length >= 20, `expected >= 20 class rows, got ${rows.length}`);
  const labels = rows.map((r) => r.get('label').value);
  for (const expected of ['Triples Map', 'Subject Map', 'Object Map']) {
    assert.ok(labels.includes(expected), `missing class label ${expected}`);
  }
  assert.equal(rows[0].get('class').termType, 'NamedNode');
});

test('queryHdt: accepts an ArrayBuffer, not just a Buffer/Uint8Array', { skip: !haveFixture && 'HDT fixture not found' }, async () => {
  const buf = fs.readFileSync(FIXTURE_HDT);
  const ab = buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength);
  const rows = await engine.queryHdt(ab, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
  assert.equal(rows[0].get('n').value, '343');
});

test('queryHdt: CONSTRUCT rejects (SELECT/ASK only over --data-hdt)', { skip: !haveFixture && 'HDT fixture not found' }, async () => {
  const bytes = fs.readFileSync(FIXTURE_HDT);
  await assert.rejects(
    () => engine.queryHdt(bytes, 'CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }'),
    /SELECT\/ASK only/);
});

test('queryHdt: fn.js re-exports the same function', { skip: !haveFixture && 'HDT fixture not found' }, async () => {
  const fn = require('../fn.js');
  assert.equal(typeof fn.queryHdt, 'function');
  const bytes = fs.readFileSync(FIXTURE_HDT);
  const rows = await fn.queryHdt(bytes, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
  assert.equal(rows[0].get('n').value, '343');
});
