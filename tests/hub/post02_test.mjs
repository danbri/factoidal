// Pins every code sample in
// docs/web/hub/02-asking-questions-sparql.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, runReactivePost, pretty } from './_helpers.mjs';

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

test('post02: post has 9 live cells (including the music property-path notebook)', () => {
  assert.equal(cells.length, 9, `expected 9 live cells, found ${cells.length}`);
});

test('post02: dependency inference wires ttl -> dataset -> every query cell', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.deepEqual(post.names.slice(0, 2), ['ttl', 'dataset']);
  assert.ok(post.infos[1].refs.includes('ttl'), 'dataset cell references ttl');
  for (const i of [2, 3, 4, 8]) {
    assert.ok(post.infos[i].refs.includes('dataset'), `cell ${i + 1} references dataset`);
  }
});

test('post02 cell 3 (pretty(SELECT bindings) -> table): 3 rows, one "label" column', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[2]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['label']);
  assert.equal(result.rows.length, 3);
  // One of the three edges (rdf:type/instance-of/occupation OPTIONAL
  // match) has no rdfs:label -- OPTIONAL leaves that binding unset,
  // which the table renders as an empty cell rather than dropping the
  // row.
  const unbound = result.rows.filter((r) => r[0] === '');
  assert.equal(unbound.length, 1, 'exactly one row has no OPTIONAL label binding');
});

test('post02 cell 4 (ASK): true', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[3]);
  assert.equal(result, true);
});

test('post02 cell 5 (property-path alternation): both targets', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[4]);
  assert.deepEqual([...result].sort(), [
    'http://www.wikidata.org/entity/Q36180',
    'http://www.wikidata.org/entity/Q5',
  ]);
});

test('post02 cell 6 (CONSTRUCT): one-triple occupation-label graph', async () => {
  const caps = await factoidal.capabilities();
  if (!caps.construct) return;
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[8]);
  assert.equal(result.size, 1);
  assert.equal(
    result.nquads,
    '<http://www.wikidata.org/entity/Q42> <http://example.org/hasOccupationLabel> "writer" .\n'
  );
});

test('post02: music notebook retains the album-to-band-to-musician property path', () => {
  assert.match(cells[5], /fstar-extracted\/samples\/music\.ttl/);
  assert.match(cells[7], /ex:by\/ex:member/);
});
