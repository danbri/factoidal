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

One instance (`ex:alice`, a `schema:Person`), one subclass axiom. The
query itself — "what type does `ex:alice` have" — is the same across
every cell in this post, so it's named once and referenced everywhere
below:

```observable-js
q = `# What type or types does ex:alice have.
SELECT ?type WHERE { <http://example.org/alice> a ?type }`
```

Ask it twice — with and without RDFS entailment:

```observable-js
const ttl = `
  @prefix schema: <https://schema.org/> .
  @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix ex:     <http://example.org/> .

  schema:Person rdfs:subClassOf schema:Thing .
  ex:alice a schema:Person .
`;
const dataset = await fn.parse(ttl);

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
appears as a second type — derived, not asserted. Since the 2026-07-31
rule-completeness work the closure also derives `rdfs:Resource` for
every subject (rules rdfs4a/rdfs4b — in RDFS, everything is a
resource), so entailed type lists carry it alongside the
vocabulary-specific types below.

## OWL 2 RL: equivalentClass

To map two classes from different vocabularies onto each other, OWL
gives you a single, self-documenting triple. Map `schema:Person` onto
`foaf:Person`:

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

Plain RDFS *can* express the same equivalence, though — assert
`rdfs:subClassOf` in **both directions** and the subclass rule fires
both ways. (That is exactly how OWL defines `EquivalentClasses`: a
subclass axiom in each direction.) What `owl:equivalentClass` buys is
the single self-documenting triple rather than a pair:

```observable-js
const bothWays = `
  @prefix schema: <https://schema.org/> .
  @prefix foaf:   <http://xmlns.com/foaf/0.1/> .
  @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix ex:     <http://example.org/> .

  schema:Person rdfs:subClassOf foaf:Person .
  foaf:Person   rdfs:subClassOf schema:Person .
  ex:alice a schema:Person .
`;
const ds3 = await fn.parse(bothWays);
const rows = await fn.query(ds3, q, { entail: "RDFS" });
return rows.map((r) => r.get("type").value).sort();
```

Both types, pure RDFS, no OWL vocabulary in sight.

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
Other posts in the series cover the RDF serializations (N-Triples,
N-Quads, TriG, RDF/XML), SPARQL Update and the HTTP protocol, and ShEx
— see the [series plan](../../designissues/2026-07-05-docs-hub-plan.md)
for the full map.

Every live cell above is pinned in
[`tests/hub/post03_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post03_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn` adapter.
