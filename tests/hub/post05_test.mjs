// Pins every code sample in docs/web/hub/05-shapes-that-validate-shacl.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '05-shapes-that-validate-shacl.md';

const cells = extractObservableCells(POST_FILE);

test('post05: post has at least 3 live cells', () => {
  assert.ok(cells.length >= 3, `expected >= 3 live cells, found ${cells.length}`);
});

test('post05 cell 1 (conforming data): Alice and Bob satisfy the PersonShape', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.deepEqual(result, { conforms: true, reportSize: 2 });
});

test('post05 cell 2 (broken data): missing foaf:name on Bob is one minCount violation', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal });
  assert.equal(result.conforms, false);
  assert.deepEqual(result.violations, [
    {
      focusNode: 'http://example.org/bob',
      path: 'http://xmlns.com/foaf/0.1/name',
      message: 'foaf:Person needs at least one foaf:name',
    },
  ]);
});

test('post05 cell 3 (three distinct constraints): minCount/datatype/class each fire independently', async () => {
  const result = await runObservableCell(cells[2], { fn: factoidal });
  assert.deepEqual(result, {
    minCount: { conforms: false, component: 'MinCountConstraintComponent' },
    datatype: { conforms: false, component: 'DatatypeConstraintComponent' },
    class: { conforms: false, component: 'ClassConstraintComponent' },
  });
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

const PERSON_SHAPE_TTL = `
  @prefix sh:   <http://www.w3.org/ns/shacl#> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
  @prefix ex:   <http://example.org/shapes/> .

  ex:PersonShape
      a sh:NodeShape ;
      sh:targetClass foaf:Person ;
      sh:property [
          sh:path foaf:name ;
          sh:minCount 1 ;
          sh:message "foaf:Person needs at least one foaf:name" ;
      ] ;
      sh:property [
          sh:path foaf:name ;
          sh:datatype xsd:string ;
          sh:message "foaf:name must be a plain xsd:string" ;
      ] ;
      sh:property [
          sh:path foaf:knows ;
          sh:class foaf:Person ;
          sh:message "foaf:knows must point to another foaf:Person" ;
      ] .
`;

test('post05: shaclValidate accepts raw Turtle text for both data and shapes', async () => {
  const ttl = `
    @prefix foaf: <http://xmlns.com/foaf/0.1/> .
    @prefix ex:   <http://example.org/> .
    ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
    ex:bob a foaf:Person ; foaf:name "Bob" .
  `;
  const result = await factoidal.shaclValidate(ttl, PERSON_SHAPE_TTL);
  assert.equal(result.conforms, true);
});

test('post05: capabilities() reports SHACL support (grounds the "check first" cell pattern)', async () => {
  const caps = await factoidal.capabilities();
  assert.equal(caps.shacl, true);
});
