// Pins every code sample in
// docs/web/hub/01-triples-rdf-from-first-principles.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed) — mirrors npm/factoidal/test's own harness style.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '01-triples-rdf-from-first-principles.md';

test('post01: foaf:knows Turtle parses to 5 triples', async () => {
  const turtle = `
    @prefix foaf: <http://xmlns.com/foaf/0.1/> .
    @prefix ex:   <http://example.org/> .

    ex:alice a foaf:Person ;
      foaf:name  "Alice" ;
      foaf:knows ex:bob .

    ex:bob a foaf:Person ;
      foaf:name "Bob" .
  `;
  const dataset = await factoidal.parse(turtle);
  assert.equal(dataset.size, 5);
});

test('post01: iterating quads shows subject/predicate/object term kinds', async () => {
  const turtle = `
    @prefix foaf: <http://xmlns.com/foaf/0.1/> .
    @prefix ex:   <http://example.org/> .

    ex:alice a foaf:Person ;
      foaf:name  "Alice" ;
      foaf:knows ex:bob .

    ex:bob a foaf:Person ;
      foaf:name "Bob" .
  `;
  const dataset = await factoidal.parse(turtle);
  const lines = [...dataset].map(
    (q) => `${q.subject.value} -- ${q.predicate.value} --> ${q.object.value} (${q.object.termType})`
  );
  assert.equal(lines.length, 5);

  const nameLines = lines.filter((l) => l.endsWith('(Literal)'));
  assert.equal(nameLines.length, 2, 'foaf:name objects are Literals');

  const typeAndKnowsLines = lines.filter((l) => l.endsWith('(NamedNode)'));
  assert.equal(typeAndKnowsLines.length, 3, 'rdf:type and foaf:knows objects are NamedNodes');

  for (const q of dataset) {
    assert.equal(q.subject.termType, 'NamedNode', 'every subject here is a NamedNode');
  }
});

test('post01: blank-node subject is a genuine BlankNode term', async () => {
  const bnodeTurtle =
    '@prefix foaf: <http://xmlns.com/foaf/0.1/> . ' +
    '[] a foaf:Person ; foaf:name "Anonymous Friend" .';
  const ds2 = await factoidal.parse(bnodeTurtle);
  assert.equal(ds2.size, 2);
  const [first] = [...ds2];
  assert.equal(first.subject.termType, 'BlankNode');
  // Both triples share the same blank-node subject.
  for (const q of ds2) {
    assert.equal(q.subject.value, first.subject.value);
  }
});

// ---------------------------------------------------------------------
// Cell-pinning tests: extract the exact ```observable-js source shipped
// on the page and execute it via the same new Function(...) construction
// docs/_includes/hub.njk's mountCell() uses, against the real
// npm/factoidal typed API (fn === factoidal here; the live page instead
// binds `fn` to the in-browser adapter — see docs/web/hub/README.md).
// ---------------------------------------------------------------------

const cells = extractObservableCells(POST_FILE);

test('post01: post has 4 live cells (turtle hoisted into its own named cell)', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

// Cells 2 and 3 (index 1 and 2) both reference the named `turtle` cell
// (index 0) instead of redeclaring the Turtle text -- exercise the REAL
// reactive wiring (the same compiler docs/_includes/hub.njk uses) to
// prove the cross-cell reference actually resolves, not just that each
// cell happens to run standalone.
test('post01: dependency inference wires cells 2 and 3 to the named turtle cell', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.equal(post.names[0], 'turtle');
  assert.ok(post.infos[1].refs.includes('turtle'), 'cell 2 references turtle');
  assert.ok(post.infos[2].refs.includes('turtle'), 'cell 3 references turtle');
});

test('post01 cell 1 (named turtle cell): the Turtle text itself', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const turtle = await post.value(post.names[0]);
  assert.equal(typeof turtle, 'string');
  assert.ok(turtle.includes('foaf:knows'), 'turtle cell carries the foaf:knows Turtle');
});

test('post01 cell 2 (parse + size): returns 5', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[1]);
  assert.equal(result, 5);
});

test('post01 cell 3 (pretty(dataset) -> triples table): 5 rows, 2 quoted literals, 3 IRIs', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[2]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['s', 'p', 'o']);
  assert.equal(result.rows.length, 5);

  const literalObjects = result.rows.filter((r) => String(r[2]).startsWith('"'));
  assert.equal(literalObjects.length, 2, 'foaf:name objects render as quoted literals');

  const iriObjects = result.rows.filter((r) => !String(r[2]).startsWith('"'));
  assert.equal(iriObjects.length, 3, 'rdf:type and foaf:knows objects render as bare IRIs');

  for (const row of result.rows) {
    assert.ok(row[0].startsWith('http://'), 'every subject here is an IRI');
  }
});

test('post01 cell 4 (blank node): size 2, BlankNode subject, shared across both triples', async () => {
  const result = await runObservableCell(cells[3], { fn: factoidal });
  assert.deepEqual(result, {
    size: 2,
    subjectTermType: 'BlankNode',
    sameSubjectOnBothTriples: true,
  });
});
