---
title: "Triples: RDF from first principles"
description: "What an RDF triple actually is, read straight out of the F* term algebra, then parsed live from a foaf:knows example."
series: docs-hub
series_order: 1
vocab: foaf
status: draft
tests: tests/hub/post01_test.mjs
---

RDF describes the world as a set of **triples**: subject, predicate,
object. Nothing else. No rows, no columns, no nesting — every fact is
one small statement, and a graph is just a set of them. This post
builds that idea up from the actual specification this project
verifies, then parses a real example live.

## Three kinds of term

Every triple is built from **terms**, and RDF 1.1 recognizes exactly
three disjoint kinds of term. This project's F\* specification says so
directly — [`RDF.Term.fsti`](https://github.com/danbri/factoidal/blob/main/formal/fstar/RDF.Term.fsti)
is written to be read by a human who knows RDF but not F\*, one
concept per block:

```fstar
noeq type rdf_term =
  | T_IRI     : wf_iri -> rdf_term
  | T_BNode   : bnode_id -> rdf_term
  | T_Literal : wf_literal -> rdf_term
```

- **IRI** (`T_IRI`) — a global name for something, e.g.
  `http://xmlns.com/foaf/0.1/knows`. `RDF.Term.fsti`'s `wf_iri` type
  refines a plain string down to "non-empty and contains a colon" —
  the cheap structural check every term constructor runs; full RFC
  3987 grammar conformance is a separate module's job
  (`RDF.IRI.fst`).
- **Blank node** (`T_BNode`) — a locally-scoped identifier for
  "something exists here, I'm just not naming it." Disjoint from IRIs
  and literals.
- **Literal** (`T_Literal`) — a value: a lexical form, a datatype IRI,
  and — only when the datatype is `rdf:langString` — a language tag.
  `RDF.Term.fsti`'s `literal_wf` predicate encodes that "iff" directly:
  a literal has a language tag exactly when its datatype is
  `rdf:langString`, never otherwise.

A **triple** is subject–predicate–object, where the subject is
restricted to an IRI or a blank node (never a literal — RDF 1.1
Concepts §3.1), the predicate is always an IRI, and the object can be
any of the three term kinds. A **graph** is a set of triples.

## Parsing one, live

Here's a small foaf graph: Alice knows Bob.

```turtle
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex:   <http://example.org/> .

ex:alice a foaf:Person ;
  foaf:name  "Alice" ;
  foaf:knows ex:bob .

ex:bob a foaf:Person ;
  foaf:name "Bob" .
```

That's four statements about Alice (type, name, knows-Bob... plus the
implicit `a` triple) and two about Bob — five triples in total. Parse
it with the same F\*-extracted Turtle parser the W3C conformance suite
runs against (`Parser.Turtle.fst`, 313 pass, 0 fail on the rdf-turtle
suite — see the plan doc for the full RDF 1.1 scorecard), via the
published npm package:

```js
import factoidal from "@danbri/foafos";

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
dataset.size;
// => 5
```

Five triples, exactly as counted above. Each one is an RDF/JS `Quad`
— walk them and print subject/predicate/object:

```js
for (const q of dataset) {
  console.log(`${q.subject.value} -- ${q.predicate.value} --> ${q.object.value} (${q.object.termType})`);
}
// http://example.org/alice -- ...#type --> http://xmlns.com/foaf/0.1/Person (NamedNode)
// http://example.org/alice -- .../knows --> http://example.org/bob (NamedNode)
// http://example.org/alice -- .../name --> Alice (Literal)
// http://example.org/bob -- ...#type --> http://xmlns.com/foaf/0.1/Person (NamedNode)
// http://example.org/bob -- .../name --> Bob (Literal)
```

The object of the last two is a `Literal`, everything else is a
`NamedNode` (the RDF/JS spelling for an IRI term). That's `T_IRI` vs
`T_Literal` from `RDF.Term.fsti`, made concrete.

## The third kind: blank nodes

Turtle's `[]` syntax introduces a blank node — "some person, unnamed":

```turtle
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
[] a foaf:Person ; foaf:name "Anonymous Friend" .
```

```js
const ds2 = await factoidal.parse(
  '@prefix foaf: <http://xmlns.com/foaf/0.1/> . ' +
  '[] a foaf:Person ; foaf:name "Anonymous Friend" .'
);
ds2.size;                       // => 2
[...ds2][0].subject.termType;   // => 'BlankNode'
```

Two triples, both with the same blank-node subject — `T_BNode` in the
F\* term algebra, `BlankNode` in RDF/JS. That's all three term kinds
now seen live: `NamedNode`/`T_IRI`, `BlankNode`/`T_BNode`,
`Literal`/`T_Literal`.

## What's next

The next post in this series asks questions of a graph instead of just
reading it — [SPARQL SELECT, ASK, CONSTRUCT, and property paths](./02-asking-questions-sparql.md)
over a small Wikidata-shaped dataset. After that, [RDFS and OWL 2 RL](./03-schemas-that-infer-rdfs-owl.md)
show how a graph can imply triples nobody asserted.

Every code sample above is pinned in
[`tests/hub/post01_test.mjs`](../../../tests/hub/post01_test.mjs).
