// Pins every code sample in
// docs/web/hub-drafts/01-triples-rdf-from-first-principles.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed) — mirrors npm/factoidal/test's own harness style.

import { NPM_FACTOIDAL_INDEX } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

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
