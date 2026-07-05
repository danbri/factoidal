// Pins every code sample in
// docs/web/hub-drafts/02-asking-questions-sparql.md.

import { NPM_FACTOIDAL_INDEX } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

const TTL = `
  @prefix wd:   <http://www.wikidata.org/entity/> .
  @prefix wdt:  <http://www.wikidata.org/prop/direct/> .
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

  wd:Q42 rdfs:label "Douglas Adams" ;
    wdt:P31  wd:Q5 ;
    wdt:P106 wd:Q36180 .

  wd:Q5     rdfs:label "human" .
  wd:Q36180 rdfs:label "writer" .
`;

test('post02: dataset has 5 triples', async () => {
  const dataset = await factoidal.parse(TTL);
  assert.equal(dataset.size, 5);
});

test('post02: SELECT with OPTIONAL returns 3 rows (one per Q42 edge)', async () => {
  const dataset = await factoidal.parse(TTL);
  const rows = await factoidal.query(dataset, `
    PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    SELECT ?label WHERE {
      <http://www.wikidata.org/entity/Q42> ?p ?o .
      OPTIONAL { ?o rdfs:label ?label }
    }
  `);
  assert.equal(rows.length, 3);
});

test('post02: ASK confirms Douglas Adams occupation is writer', async () => {
  const dataset = await factoidal.parse(TTL);
  const ask = await factoidal.query(dataset, `
    PREFIX wdt: <http://www.wikidata.org/prop/direct/>
    ASK { <http://www.wikidata.org/entity/Q42> wdt:P106 <http://www.wikidata.org/entity/Q36180> }
  `);
  assert.equal(ask, true);
});

test('post02: property-path alternation (wdt:P31|wdt:P106) returns both targets', async () => {
  const dataset = await factoidal.parse(TTL);
  const types = await factoidal.query(dataset, `
    PREFIX wd:  <http://www.wikidata.org/entity/>
    PREFIX wdt: <http://www.wikidata.org/prop/direct/>
    SELECT ?type WHERE { wd:Q42 (wdt:P31|wdt:P106) ?type }
  `);
  const values = types.map((r) => r.get('type').value).sort();
  assert.deepEqual(values, [
    'http://www.wikidata.org/entity/Q36180',
    'http://www.wikidata.org/entity/Q5',
  ]);
});

test('post02: CONSTRUCT derives a one-triple occupation-label graph', async () => {
  const dataset = await factoidal.parse(TTL);
  const caps = await factoidal.capabilities();
  if (!caps.construct) {
    // Falls back to documenting the CLI-bundle limitation rather than
    // failing outright, mirroring npm/factoidal/test's own capability
    // gating style (see test/fn.test.js).
    return;
  }
  const derived = await factoidal.query(dataset, `
    PREFIX wdt:  <http://www.wikidata.org/prop/direct/>
    PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    CONSTRUCT { ?person <http://example.org/hasOccupationLabel> ?label }
    WHERE { ?person wdt:P106 ?occ . ?occ rdfs:label ?label }
  `);
  assert.equal(derived.size, 1);
  assert.equal(
    derived.toNQuads(),
    '<http://www.wikidata.org/entity/Q42> <http://example.org/hasOccupationLabel> "writer" .\n'
  );
});
