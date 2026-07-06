---
title: "Triples: RDF from first principles"
description: "What an RDF triple actually is, read straight out of the F* term algebra, then parsed live from a foaf:knows example."
layout: hub.njk
series: docs-hub
series_order: 1
vocab: foaf
status: published
tests: tests/hub/post01_test.mjs
---

RDF describes the world as a set of **triples**: subject, predicate,
object. Nothing else. No rows, no columns, no nesting — every fact is
one small statement, and a graph is just a set of them. This post
builds that idea up from the actual specification this project
verifies, then parses a real example live, in your browser, against
the F\*-extracted engine.

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

That's three statements about Alice (type, name, knows-Bob) and two
about Bob — five triples in total. The `a` keyword is Turtle (and
SPARQL) shorthand for the `rdf:type` predicate, so `ex:alice a
foaf:Person` *is* the type triple, not an extra one. Parse
it with the same F\*-extracted Turtle parser the W3C conformance suite
runs against (`Parser.Turtle.fst`, 313 pass, 0 fail on the rdf-turtle
suite — see the plan doc for the full RDF 1.1 scorecard). The cell
below runs that parse right now, in this page, using the `fn` typed
API (see [`README.md`](./README.md) for the full cell-authoring
contract):

```observable-js
const turtle = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .

  ex:alice a foaf:Person ;
    foaf:name  "Alice" ;
    foaf:knows ex:bob .

  ex:bob a foaf:Person ;
    foaf:name "Bob" .
`;

const dataset = await fn.parse(turtle);
return dataset.size;
```

Five triples, exactly as counted above. Each one is a `{subject,
predicate, object}` term triple — walk them and print each part:

```observable-js
const turtle = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .

  ex:alice a foaf:Person ;
    foaf:name  "Alice" ;
    foaf:knows ex:bob .

  ex:bob a foaf:Person ;
    foaf:name "Bob" .
`;

const dataset = await fn.parse(turtle);
const lines = [...dataset].map(
  (q) => `${q.subject.value} -- ${q.predicate.value} --> ${q.object.value} (${q.object.termType})`
);
return lines.join("\n");
```

The object of the `foaf:name` triples is a `Literal`, everything else
is a `NamedNode` (the RDF/JS spelling for an IRI term). That's
`T_IRI` vs `T_Literal` from `RDF.Term.fsti`, made concrete.

## The third kind: blank nodes

Turtle's `[]` syntax introduces a blank node — "some person, unnamed":

```turtle
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
[] a foaf:Person ; foaf:name "Anonymous Friend" .
```

```observable-js
const bnodeTurtle =
  '@prefix foaf: <http://xmlns.com/foaf/0.1/> . ' +
  '[] a foaf:Person ; foaf:name "Anonymous Friend" .';
const ds2 = await fn.parse(bnodeTurtle);
const quads = [...ds2];
return {
  size: ds2.size,
  subjectTermType: quads[0].subject.termType,
  sameSubjectOnBothTriples: quads[0].subject.value === quads[1].subject.value,
};
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

Every live cell above is pinned in
[`tests/hub/post01_test.mjs`](../../../tests/hub/post01_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn` adapter.
