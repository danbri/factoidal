// Pins every code sample in docs/web/hub/06-shapes-the-other-dialect-shex.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost } from './_helpers.mjs';

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

test('post06: post has 10 live cells (WD_TTL/dataset/HUMAN_SHAPE_SCHEMA/tryShexValidate/HUMAN_SHAPE_SHEXC hoisted into named cells)', () => {
  assert.equal(cells.length, 10, `expected 10 live cells, found ${cells.length}`);
});

test('post06: dependency inference wires the shared cells to every consumer', () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(post.names.slice(0, 2), ['WD_TTL', 'dataset']);
  assert.ok(post.infos[1].refs.includes('WD_TTL'), 'dataset cell references WD_TTL');
  // cell index 2: `return dataset.size;`
  assert.ok(post.infos[2].refs.includes('dataset'), 'triple-count cell references dataset');
  assert.equal(post.names[3], 'HUMAN_SHAPE_SCHEMA');
  assert.equal(post.names[4], 'tryShexValidate');
  // tryShexValidate takes the schema text as a parameter (schemaText),
  // so it does NOT reference HUMAN_SHAPE_SCHEMA itself -- that's what
  // lets the same wrapper serve both the ShExJ cells below and the
  // ShExC cells further down the page.
  assert.ok(!post.infos[4].refs.includes('HUMAN_SHAPE_SCHEMA'), 'tryShexValidate does not reference HUMAN_SHAPE_SCHEMA directly');
  // cells 5, 6: conforming/non-conforming ShExJ checks reference the
  // shared dataset, the shared tryShexValidate wrapper, AND the ShExJ
  // schema (passed explicitly as tryShexValidate's second argument).
  for (const i of [5, 6]) {
    assert.ok(post.infos[i].refs.includes('dataset'), `cell ${i + 1} references dataset`);
    assert.ok(post.infos[i].refs.includes('tryShexValidate'), `cell ${i + 1} references tryShexValidate`);
    assert.ok(post.infos[i].refs.includes('HUMAN_SHAPE_SCHEMA'), `cell ${i + 1} references HUMAN_SHAPE_SCHEMA`);
  }
  assert.equal(post.names[7], 'HUMAN_SHAPE_SHEXC');
  // cells 8, 9: conforming/non-conforming ShExC checks reference dataset,
  // tryShexValidate, AND the ShExC schema text (passed explicitly too).
  for (const i of [8, 9]) {
    assert.ok(post.infos[i].refs.includes('dataset'), `cell ${i + 1} references dataset`);
    assert.ok(post.infos[i].refs.includes('tryShexValidate'), `cell ${i + 1} references tryShexValidate`);
    assert.ok(post.infos[i].refs.includes('HUMAN_SHAPE_SHEXC'), `cell ${i + 1} references HUMAN_SHAPE_SHEXC`);
  }
});

test('post06 cell 3 (parse the Wikidata-shaped dataset): 3 triples', async () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  const result = await post.value(post.names[2]);
  assert.equal(result, 3);
});

test('post06 cell 6 (conforming node, ShExJ schema): Q42 matches HumanShape', async () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  const result = await post.value(post.names[5]);
  assert.deepEqual(result, { available: true, verdict: true, deferred: false });
});

test('post06 cell 7 (non-conforming node, ShExJ schema): Q5 does not match HumanShape', async () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  const result = await post.value(post.names[6]);
  assert.deepEqual(result, { available: true, verdict: false, deferred: false });
});

test('post06 cell 9 (conforming node, ShExC schema text): Q42 matches HumanShape', async () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  const result = await post.value(post.names[8]);
  assert.deepEqual(result, { available: true, verdict: true, deferred: false });
});

test('post06 cell 10 (non-conforming node, ShExC schema text): Q5 does not match HumanShape', async () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  const result = await post.value(post.names[9]);
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
