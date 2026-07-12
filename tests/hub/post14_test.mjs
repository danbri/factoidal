// Pins every code sample in docs/web/hub/14-the-rdfjs-api.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed) — mirrors npm/factoidal/test's own harness style.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

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

test('post14: post has 3 live cells (namedNode hoisted into its own named cell)', () => {
  assert.equal(cells.length, 3, `expected 3 live cells, found ${cells.length}`);
});

test('post14: dependency inference wires both consuming cells to the named namedNode cell', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.equal(post.names[0], 'namedNode');
  for (const i of [1, 2]) {
    assert.ok(post.infos[i].refs.includes('namedNode'), `cell ${i + 1} references namedNode`);
  }
});

test('post14 cell 2 (dataFactory-built quads, parsed and queried): SELECT returns Alice then Bob', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[1]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['name']);
  assert.deepEqual(result.rows, [['"Alice"'], ['"Bob"']]);
});

test('post14 cell 3 (.equals() vs ===): identity differs, value-equality agrees, and a real query term has .equals()', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[2]);
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
