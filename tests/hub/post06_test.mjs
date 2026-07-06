// Pins every code sample in docs/web/hub/06-shapes-the-other-dialect-shex.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '06-shapes-the-other-dialect-shex.md';

const cells = extractObservableCells(POST_FILE);

// The post's cells call the raw `Factoidal.shexValidate(dataNQuads,
// schemaJson, focus, shapeLabel)` contract (npm/factoidal/browser.js),
// not the typed `fn` adapter -- ShEx has no `fn.shexValidate` wrapper
// in docs/_includes/hub.njk today (only shaclValidate got one). This
// tiny shim mirrors browser.js's raw signature/return shape
// ({ok, verdict, deferred}, N-Quads text in) on top of the REAL
// npm/factoidal typed API's `shexValidate(data, schemaJson, focus,
// shape, options) -> Promise<boolean|null>`, since browser.js itself
// needs a DOM/fetch environment this node:test run doesn't have. The
// cell source under test is identical either way -- only this harness
// binding differs from what a real browser page wires up.
const FactoidalNode = {
  async shexValidate(dataNQuads, schemaJson, focus, shapeLabel) {
    const verdict = await factoidal.shexValidate(
      dataNQuads, schemaJson, focus, shapeLabel || null, { format: 'nquads' });
    return { ok: true, verdict, deferred: verdict === null };
  },
};

test('post06: post has at least 5 live cells', () => {
  assert.ok(cells.length >= 5, `expected >= 5 live cells, found ${cells.length}`);
});

test('post06 cell 1 (parse the Wikidata-shaped dataset): 3 triples', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.equal(result, 3);
});

test('post06 cell 2 (conforming node, ShExJ schema): Q42 matches HumanShape', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, { available: true, verdict: true, deferred: false });
});

test('post06 cell 3 (non-conforming node, ShExJ schema): Q5 does not match HumanShape', async () => {
  const result = await runObservableCell(cells[2], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, { available: true, verdict: false, deferred: false });
});

test('post06 cell 4 (conforming node, ShExC schema text): Q42 matches HumanShape', async () => {
  const result = await runObservableCell(cells[3], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, { available: true, verdict: true, deferred: false });
});

test('post06 cell 5 (non-conforming node, ShExC schema text): Q5 does not match HumanShape', async () => {
  const result = await runObservableCell(cells[4], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, { available: true, verdict: false, deferred: false });
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post06: capabilities() reports ShEx support (grounds the "check first" cell pattern)', async () => {
  const caps = await factoidal.capabilities();
  assert.equal(caps.shex, true);
});

test('post06: shexValidate accepts RDF/JS terms for focus/shape too', async () => {
  const ttl = `
    @prefix foaf: <http://xmlns.com/foaf/0.1/> .
    @prefix ex:   <http://example.org/> .
    ex:alice a foaf:Person ; foaf:name "Alice" .
  `;
  const dataset = await factoidal.parse(ttl);
  const schema = JSON.stringify({
    type: 'Schema',
    shapes: [{
      type: 'ShapeDecl', id: 'http://example.org/PersonShape',
      shapeExpr: {
        type: 'Shape',
        expression: {
          type: 'TripleConstraint',
          predicate: 'http://xmlns.com/foaf/0.1/name',
          valueExpr: { type: 'NodeConstraint', nodeKind: 'literal' },
        },
      },
    }],
  });
  const verdict = await factoidal.shexValidate(
    dataset, schema, 'http://example.org/alice', 'http://example.org/PersonShape');
  assert.equal(verdict, true);
});

test('post06: shexValidate dispatches ShExC text (no leading "{") straight to Parser.ShExC.fst', async () => {
  const ttl = `
    @prefix foaf: <http://xmlns.com/foaf/0.1/> .
    @prefix ex:   <http://example.org/> .
    ex:alice a foaf:Person ; foaf:name "Alice" .
  `;
  const dataset = await factoidal.parse(ttl);
  const shexc = `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    PREFIX ex:   <http://example.org/>

    <http://example.org/PersonShape> {
      foaf:name LITERAL
    }
  `;
  const verdict = await factoidal.shexValidate(
    dataset, shexc, 'http://example.org/alice', 'http://example.org/PersonShape');
  assert.equal(verdict, true);
});
