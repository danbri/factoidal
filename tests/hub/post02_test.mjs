// Pins every code sample in
// docs/web/hub/02-asking-questions-sparql.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '02-asking-questions-sparql.md';

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

// ---------------------------------------------------------------------
// Cell-pinning tests: extract the exact ```observable-js source shipped
// on the page and execute it via the same new Function(...) construction
// docs/_includes/hub.njk's mountCell() uses, against the real
// npm/factoidal typed API (fn === factoidal here; the live page instead
// binds `fn` to the in-browser adapter — see docs/web/hub/README.md).
// ---------------------------------------------------------------------

const cells = extractObservableCells(POST_FILE);

test('post02: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post02 cell 1 (SELECT with OPTIONAL): 3 rows', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.equal(result, '3 row(s)');
});

test('post02 cell 2 (ASK): true', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal });
  assert.equal(result, true);
});

test('post02 cell 3 (property-path alternation): both targets', async () => {
  const result = await runObservableCell(cells[2], { fn: factoidal });
  assert.deepEqual([...result].sort(), [
    'http://www.wikidata.org/entity/Q36180',
    'http://www.wikidata.org/entity/Q5',
  ]);
});

test('post02 cell 4 (CONSTRUCT): one-triple occupation-label graph', async () => {
  const caps = await factoidal.capabilities();
  if (!caps.construct) return;
  const result = await runObservableCell(cells[3], { fn: factoidal });
  assert.equal(result.size, 1);
  assert.equal(
    result.nquads,
    '<http://www.wikidata.org/entity/Q42> <http://example.org/hasOccupationLabel> "writer" .\n'
  );
});
