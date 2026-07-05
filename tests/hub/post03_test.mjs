// Pins every code sample in
// docs/web/hub-drafts/03-schemas-that-infer-rdfs-owl.md.

import { NPM_FACTOIDAL_INDEX } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

const RDFS_TTL = `
  @prefix schema: <https://schema.org/> .
  @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix ex:     <http://example.org/> .

  schema:Person rdfs:subClassOf schema:Thing .
  ex:alice a schema:Person .
`;

const Q = `SELECT ?type WHERE { <http://example.org/alice> a ?type }`;

test('post03: no entailment sees only the asserted type', async () => {
  const dataset = await factoidal.parse(RDFS_TTL);
  const rows = await factoidal.query(dataset, Q);
  const types = rows.map((r) => r.get('type').value);
  assert.deepEqual(types, ['https://schema.org/Person']);
});

test('post03: RDFS entailment adds schema:Thing via subClassOf', async () => {
  const dataset = await factoidal.parse(RDFS_TTL);
  const rows = await factoidal.query(dataset, Q, { entail: 'RDFS' });
  const types = rows.map((r) => r.get('type').value).sort();
  assert.deepEqual(types, ['https://schema.org/Person', 'https://schema.org/Thing']);
});

const OWL_TTL = `
  @prefix schema: <https://schema.org/> .
  @prefix foaf:   <http://xmlns.com/foaf/0.1/> .
  @prefix owl:    <http://www.w3.org/2002/07/owl#> .
  @prefix ex:     <http://example.org/> .

  schema:Person owl:equivalentClass foaf:Person .
  ex:alice a schema:Person .
`;

test('post03: RDFS entailment does not know owl:equivalentClass', async () => {
  const dataset2 = await factoidal.parse(OWL_TTL);
  const rows = await factoidal.query(dataset2, Q, { entail: 'RDFS' });
  const types = rows.map((r) => r.get('type').value);
  assert.deepEqual(types, ['https://schema.org/Person']);
});

test('post03: OWL-RL entailment derives foaf:Person and owl:Thing via equivalentClass', async () => {
  const dataset2 = await factoidal.parse(OWL_TTL);
  const rows = await factoidal.query(dataset2, Q, { entail: 'OWL-RL' });
  const types = rows.map((r) => r.get('type').value).sort();
  assert.deepEqual(types, [
    'http://www.w3.org/2002/07/owl#Thing',
    'http://xmlns.com/foaf/0.1/Person',
    'https://schema.org/Person',
  ]);
});
