// Pins every code sample in docs/web/hub/04-concept-schemes-skos.md.
//
// Fixtures mirror skills/skos-integrity/sample-vocab.ttl and
// sample-vocab-broken.ttl (and a trimmed skos-shapes.ttl excerpt) --
// see that skill's SKILL.md for the full six-condition writeup this
// post reuses.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '04-concept-schemes-skos.md';

const cells = extractObservableCells(POST_FILE);

test('post04: post has at least 4 live cells', () => {
  assert.ok(cells.length >= 4, `expected >= 4 live cells, found ${cells.length}`);
});

test('post04 cell 1 (parse the concept scheme): 28 triples, four English concept labels', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.equal(result.tripleCount, 28);
  assert.deepEqual(result.concepts, ['Animal', 'Cat', 'Dog', 'Mammal']);
});

test('post04 cell 2 (skos:broader+ property path): Dog\'s ancestors are Mammal then Animal', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal });
  assert.deepEqual(result, [
    'http://example.org/skos-integrity/animals#Mammal',
    'http://example.org/skos-integrity/animals#Animal',
  ]);
});

test('post04 cell 3 (six SPARQL integrity checks): valid scheme clean, broken scheme catches exactly its planted defect', async () => {
  const result = await runObservableCell(cells[2], { fn: factoidal });
  assert.deepEqual(result, {
    S9: { valid: false, broken: true },
    S13: { valid: 0, broken: 1 },
    S14: { valid: 0, broken: 1 },
    S27: { valid: false, broken: true },
    S37: { valid: false, broken: true },
    S46: { valid: 0, broken: 1 },
  });
});

test('post04 cell 4 (SHACL integrity check): valid conforms, broken reports 5 SHACL-checkable violations', async () => {
  const result = await runObservableCell(cells[3], { fn: factoidal });
  assert.deepEqual(result, {
    valid: { available: true, conforms: true, violations: 0 },
    broken: { available: true, conforms: false, violations: 5 },
  });
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above
// -- confirms the underlying claims in the post's prose (triple count,
// six-condition scores) against the real npm/factoidal typed API.
// ---------------------------------------------------------------------

const SKOS_VALID_TTL = `
  @prefix skos: <http://www.w3.org/2004/02/skos/core#> .
  @prefix ex:   <http://example.org/skos-integrity/animals#> .
  @prefix ext:  <http://example.org/skos-integrity/external#> .

  ex:scheme a skos:ConceptScheme ;
      skos:prefLabel "Animals"@en ;
      skos:hasTopConcept ex:Animal .

  ex:Animal a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:topConceptOf ex:scheme ;
      skos:prefLabel "Animal"@en ;
      skos:prefLabel "Animal"@en-GB .

  ex:Mammal a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Mammal"@en ;
      skos:broader ex:Animal .

  ex:Cat a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Cat"@en ;
      skos:altLabel "Feline"@en ;
      skos:hiddenLabel "Kat"@en ;
      skos:broader ex:Mammal ;
      skos:exactMatch ext:Cat .

  ex:Dog a skos:Concept ;
      skos:inScheme ex:scheme ;
      skos:prefLabel "Dog"@en ;
      skos:broader ex:Mammal ;
      skos:related ex:Cat .

  ex:PetsCollection a skos:Collection ;
      skos:prefLabel "Pets"@en ;
      skos:member ex:Cat ;
      skos:member ex:Dog .
`;

test('post04: skos:broader+ from Dog reaches Mammal and Animal, direct API', async () => {
  const dataset = await factoidal.parse(SKOS_VALID_TTL);
  const rows = await factoidal.query(dataset, `
    PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
    PREFIX ex:   <http://example.org/skos-integrity/animals#>
    SELECT ?ancestor WHERE { ex:Dog skos:broader+ ?ancestor }
  `);
  assert.deepEqual(rows.map((r) => r.get('ancestor').value).sort(), [
    'http://example.org/skos-integrity/animals#Animal',
    'http://example.org/skos-integrity/animals#Mammal',
  ]);
});

test('post04: S9 (ConceptScheme/Concept disjoint) is clean on the valid scheme', async () => {
  const dataset = await factoidal.parse(SKOS_VALID_TTL);
  const holds = await factoidal.query(dataset,
    'PREFIX skos: <http://www.w3.org/2004/02/skos/core#> ASK { ?x a skos:ConceptScheme , skos:Concept . }');
  assert.equal(holds, false);
});
