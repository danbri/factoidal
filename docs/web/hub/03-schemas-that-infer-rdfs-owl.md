---
title: "Schemas that infer: RDFS and OWL 2 RL"
description: "Types nobody asserted, derived live from an rdfs:subClassOf axiom and an owl:equivalentClass mapping over schema.org data."
layout: hub.njk
series: docs-hub
series_order: 3
vocab: schema.org
status: published
tests: tests/hub/post03_test.mjs
---

[The previous post](./02-asking-questions-sparql.md) queried exactly
what was asserted. This post asks a graph what it *implies*. RDFS and
OWL 2 RL are both entailment regimes: given a set of asserted triples
plus some schema-level axioms (subclass relationships, equivalences),
a *closure* computation derives additional triples that were never
written down. Factoidal's SPARQL evaluator can materialize either
closure on demand via the `entail` option — the two cells below run
that closure live, side by side with the plain (no-entailment) result.

## RDFS: subClassOf

```turtle
@prefix schema: <https://schema.org/> .
@prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
@prefix ex:     <http://example.org/> .

schema:Person rdfs:subClassOf schema:Thing .
ex:alice a schema:Person .
```

One instance (`ex:alice`, a `schema:Person`), one subclass axiom. Ask
what type `ex:alice` has, twice — with and without RDFS entailment:

```observable-js
const ttl = `
  @prefix schema: <https://schema.org/> .
  @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix ex:     <http://example.org/> .

  schema:Person rdfs:subClassOf schema:Thing .
  ex:alice a schema:Person .
`;
const dataset = await fn.parse(ttl);
const q = `SELECT ?type WHERE { <http://example.org/alice> a ?type }`;

const plain = await fn.query(dataset, q);
const withRdfs = await fn.query(dataset, q, { entail: "RDFS" });

return {
  withoutEntailment: plain.map((r) => r.get("type").value),
  withRDFS: withRdfs.map((r) => r.get("type").value).sort(),
};
```

Plain SELECT sees exactly what's written: `ex:alice a schema:Person`.
With `entail: 'RDFS'`, the closure applies `rdfs:subClassOf`
transitively (`RDF.Graph.Executable.fst`'s `rdfs_closure`, the same
rule set rdf-mt's 14 RDFS-closure tests exercise) and `schema:Thing`
appears as a second type — derived, not asserted.

## OWL 2 RL: equivalentClass

RDFS's subclass rule doesn't know about *equivalence* between two
classes from different vocabularies — that's an OWL construct. Map
`schema:Person` onto `foaf:Person`:

```turtle
@prefix schema: <https://schema.org/> .
@prefix foaf:   <http://xmlns.com/foaf/0.1/> .
@prefix owl:    <http://www.w3.org/2002/07/owl#> .
@prefix ex:     <http://example.org/> .

schema:Person owl:equivalentClass foaf:Person .
ex:alice a schema:Person .
```

```observable-js
const ttl2 = `
  @prefix schema: <https://schema.org/> .
  @prefix foaf:   <http://xmlns.com/foaf/0.1/> .
  @prefix owl:    <http://www.w3.org/2002/07/owl#> .
  @prefix ex:     <http://example.org/> .

  schema:Person owl:equivalentClass foaf:Person .
  ex:alice a schema:Person .
`;
const dataset2 = await fn.parse(ttl2);
const q = `SELECT ?type WHERE { <http://example.org/alice> a ?type }`;

const withRdfs = await fn.query(dataset2, q, { entail: "RDFS" });
const withOwlRl = await fn.query(dataset2, q, { entail: "OWL-RL" });

return {
  withRDFS: withRdfs.map((r) => r.get("type").value),
  withOWLRL: withOwlRl.map((r) => r.get("type").value).sort(),
};
```

`entail: 'RDFS'` leaves the result unchanged — `owl:equivalentClass`
isn't an RDFS-vocabulary construct, so the RDFS closure has nothing to
do with it. `entail: 'OWL-RL'` derives two more types: `foaf:Person`
(via the equivalence, both directions) and `owl:Thing` (every OWL
individual belongs to it). Same input graph, same query — the only
thing that changed is which closure ran first.

This is measured against the real W3C OWL 2 RL test catalog, not
asserted: positive entailment 28 pass, 2 fail (of 30 — the two fails
are a documented-impossible comprehension pair, not a silent gap),
negative entailment 6 pass 0 fail, consistency 76 pass 0 fail,
inconsistency 14 pass 0 fail.

## Why this matters beyond the toy example

Real-world graphs mix vocabularies constantly — the same "person" idea
gets asserted as `schema:Person` on one site, `foaf:Person` on
another, and a Wikidata query might expect neither directly. Whichever
of those three vocabularies your query is written against, an
`owl:equivalentClass` bridge plus `entail: 'OWL-RL'` means you don't
have to rewrite the query for every source's vocabulary choice — the
closure does the translation once, over the data, before the query
ever runs.

## What's next

[Concept schemes: SKOS](./04-concept-schemes-skos.md) is next, followed
by [Shapes that validate: SHACL](./05-shapes-that-validate-shacl.md).
The other RDF serializations (N-Triples, N-Quads, TriG, RDF/XML),
SPARQL Update and the HTTP protocol, and ShEx are still planned — see
the [series plan](../../designissues/2026-07-05-docs-hub-plan.md) for
the full map.

Every live cell above is pinned in
[`tests/hub/post03_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post03_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn` adapter.
