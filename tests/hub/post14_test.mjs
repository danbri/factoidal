// Pins every code sample in docs/web/hub/14-the-rdfjs-api.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed) — mirrors npm/factoidal/test's own harness style.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '14-the-rdfjs-api.md';

// ---------------------------------------------------------------------
// Direct API checks: the RDF/JS data model rdfjs.js exposes, and how
// npm/factoidal/index.js's typed parse()/query() are built on it.
// ---------------------------------------------------------------------

test('post14: real npm/factoidal query() bindings carry genuine RDF/JS term instances', async () => {
  const dataset = await factoidal.parse(
    '<http://example.org/a> <http://example.org/p> "hi" .', { format: 'ntriples' });
  const rows = await factoidal.query(dataset, 'SELECT ?o WHERE { ?s ?p ?o }');
  const term = rows[0].get('o');
  assert.equal(term.termType, 'Literal');
  assert.equal(typeof term.equals, 'function', 'a real npm/factoidal term has .equals()');
  assert.ok(Object.isFrozen(term), 'rdfjs.js terms are frozen at construction');
  assert.ok(term.equals(factoidal.dataFactory.literal('hi')), '.equals() is value-based');
});

test('post14: dataFactory-built quads round-trip through N-Quads text', async () => {
  const df = factoidal.dataFactory;
  const q = df.quad(
    df.namedNode('http://example.org/alice'),
    df.namedNode('http://xmlns.com/foaf/0.1/name'),
    df.literal('Alice'));
  const ds = new factoidal.Dataset([q]);
  const back = factoidal.Dataset.fromNQuads(ds.toNQuads());
  assert.equal(back.size, 1);
  assert.ok([...back][0].equals(q));
});

// ---------------------------------------------------------------------
// Cell-pinning tests: extract the exact ```observable-js source shipped
// on the page and execute it via the same new Function(...) construction
// docs/_includes/hub.njk's mountCell() uses, against the real
// npm/factoidal typed API (fn === factoidal here; the live page instead
// binds `fn` to the in-browser adapter — see docs/web/hub/README.md).
// ---------------------------------------------------------------------

const cells = extractObservableCells(POST_FILE);

test('post14: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post14 cell 1 (dataFactory-built quads, parsed and queried): SELECT returns Alice then Bob', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, pretty });
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['name']);
  assert.deepEqual(result.rows, [['"Alice"'], ['"Bob"']]);
});

test('post14 cell 2 (.equals() vs ===): identity differs, value-equality agrees, and a real query term has .equals()', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal, pretty });
  assert.equal(result.kind, 'table');
  const asObject = Object.fromEntries(result.rows);
  assert.equal(asObject.sameReferenceAB, false, 'two NamedNodes built separately are distinct objects');
  assert.equal(asObject.sameByEqualsAB, true, 'but equal by value per the RDF/JS spec');
  assert.equal(asObject.sameReferenceAC, false);
  assert.equal(asObject.sameByEqualsAC, false, 'different IRIs are never .equals()');
  // Pinned against the real npm/factoidal package: a query result term
  // IS a genuine rdfjs.js instance here. The live page's browser
  // adapter reports false for this same field — the post's prose says
  // so explicitly; this assertion is about what the real package does.
  assert.equal(asObject.queriedTermHasEquals, true,
    'the real npm/factoidal package always gives query result terms a working .equals()');
});
