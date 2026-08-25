---
title: "Propositions as first-class citizens"
description: "The Lean 4 engine reads IKL's (that S) proposition term, turns it into a named graph, and joins it against ordinary RDF data through a SPARQL SERVICE clause."
layout: hub.njk
series: docs-hub
series_order: 39
vocab: none
status: published
tests: tests/hub/post39_test.mjs
---

[Post 38](../38-one-triple-at-a-time/) climbed the Lean 4 engine's
dispatch surface from a single triple to a join between two engines.
This page adds a reader for a different input entirely: [Common Logic
(CL)](https://www.iso.org/standard/66249.html), ISO/IEC 24707, and
[IKL](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html), Pat
Hayes and Chris Menzel's extension of it that lets a sentence be
turned into a term and reasoned about as a value. The engine turns an
IKL proposition into an RDF named graph, so SPARQL can query it the
same way it queries any other named graph.

## One CLIF sentence. What does the parser see?

[CLIF](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) —
Common Logic Interchange Format — is the text syntax both CL and IKL
use. A single sentence, in the shape ISO/IEC 24707 Annex A gives for
predication: a name applied to arguments.

```observable-js
deadObl = "(Dead OBL)"
```

`clParse` reads the text, counts its sentences, re-serialises each to
canonical form, and reports whether the text uses any IKL construct.
This sentence does not, so `pureCL` comes back `true`.

```observable-js
plainParse = fn.l4Call("clParse", [deadObl])
```

## What can IKL say that plain CL cannot?

IKL adds one term-forming construct: `(that S)` turns a sentence `S`
into a term denoting the proposition `S` expresses. That term can then
appear as an ordinary argument — here, the argument of `believes`,
so the sentence states that Zeno believes a proposition, not that
Zeno stands in some relation to a sentence of text.

```observable-js
believesText = "(believes Zeno (that (Dead OBL)))"
```

Parsing it again with `clParse` flips `pureCL` to `false`: the text is
still well-formed CLIF, but it is IKL, not ISO/IEC 24707 CL proper.

```observable-js
believesParse = fn.l4Call("clParse", [believesText])
```

## From proposition to graph

`clToDataset` translates a CLIF text into an RDF dataset (RDF 1.1
Concepts §4). Every `(pred subj (that S))` sentence becomes two
things: a triple `subj pred <propIri>` in the default graph, linking
the believer to the proposition, and a NAMED GRAPH at `<propIri>`
holding `S`'s own content — here, one triple, `OBL rdf:type Dead`.

```observable-js
believesDataset = fn.l4Call("clToDataset", [believesText, "urn:cl:"])
```

`count` is 2 — the link triple plus the one triple inside the
proposition — and `skipped` is 0: nothing in this sentence fell
outside the translatable fragment. The graph name in the N-Quads is
`urn:cl:that:sha256:` followed by 64 hex characters: the SHA-256 of
the proposition's canonical CLIF text, computed after renaming bound
variables to a canonical scheme. One sentence states the naming rule:
a proposition's graph name is the content address (SHA-256) of the
alpha-normalized canonical CLIF form of its sentence, so two
that-terms name the same graph exactly when their sentences differ at
most by bound-variable renaming — the individuation minimum of the
[IKL GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html)'s
Appendix B, where `(that (exists (x)(loves Jim x)))` and `(that
(exists (y)(loves Jim y)))` are one proposition. The sentence itself
is not packed into the IRI; it travels inside the graph, as the next
section shows.

## What is inside each proposition?

The dataset `clToDataset` returned is already N-Quads text, so
`queryDataset` reads it directly — no separate parse step. A
[`GRAPH` pattern](https://www.w3.org/TR/sparql11-query/#queryDataset)
(SPARQL 1.1 §13.3) quantifies over every named graph in the dataset,
which here means every proposition the translation produced.

```observable-js
rows = (r) => r.srj.results.bindings.map(
  (b) => Object.fromEntries(Object.entries(b).map(([k, t]) => [k, t.value])))
```

```observable-js
propositions = {
  const r = await fn.l4Call("queryDataset", [believesDataset.nquads,
    "SELECT ?g ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }"]);
  return rows(r);
}
```

Two rows from one named graph: the content triple `urn:cl:OBL
rdf:type urn:cl:Dead` — exactly the content of `(Dead OBL)` — and a
sentence-record triple, whose object is the canonical CLIF text of
the proposition's sentence as a literal.

## The sentence is in the graph, not in the URL

The graph name is only a hash; the proposition's sentence lives
INSIDE the named graph as data, under the predicate
`urn:cl:def:sentence`. That keeps the parts of a sentence the
translator cannot turn into triples — quantifiers, negation,
disjunction — queryable instead of lost (they are still counted in
`skipped`). Asking the dataset for each proposition's own sentence is
an ordinary `GRAPH` query:

```observable-js
sentenceBack = {
  const r = await fn.l4Call("queryDataset", [believesDataset.nquads,
    "SELECT ?sentence WHERE { GRAPH ?g { ?g <urn:cl:def:sentence> ?sentence } }"]);
  return rows(r);
}
```

One row, and its value is `(Dead OBL)` — the canonical CLIF text,
recovered from the data rather than decoded out of an IRI.

## Propositions joined against ordinary data

`queryWithIklService` combines the two things this page has built:
the SPARQL query runs against a caller-supplied RDF dataset while a
CLIF text is bound to the [SERVICE endpoint
IRI](https://www.w3.org/TR/sparql11-federated-query/#defn_service)
`urn:ikl:kb`, and that same translation's named graphs are merged into
the query's dataset, so a `GRAPH` pattern in the same query can read
inside a proposition the SERVICE clause only pointed at. The RDF data
below never mentions belief; the CLIF text never mentions labels. The
join needs both.

```observable-js
oblLabel = `<urn:cl:OBL> <http://www.w3.org/2000/01/rdf-schema#label> "Obadiah" .`
```

```observable-js
believerAndLabel = {
  const r = await fn.l4Call("queryWithIklService", [oblLabel, believesText, `
    PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    SELECT ?believer ?label WHERE {
      ?obl rdfs:label ?label .
      SERVICE <urn:ikl:kb> { ?believer <urn:cl:believes> ?g }
      GRAPH ?g { ?obl a <urn:cl:Dead> }
    }`]);
  return rows(r);
}
```

The default-graph pattern `?obl rdfs:label ?label` reads the caller's
RDF data. The `SERVICE` pattern reads the CLIF translation's link
triple to find who believes which proposition. The `GRAPH` pattern
reads inside that proposition to confirm it is about `?obl`. One row
comes back: Zeno, believer of a proposition about `OBL`, joined
against the label `"Obadiah"` that only the RDF side knows.

## Closing

Nothing above required a bespoke reasoner for belief or context: `(that
S)` makes a proposition a term, `clToDataset` makes a term with
content a named graph, and SPARQL's existing `GRAPH` and `SERVICE`
forms do the rest. The fragment this page exercises is documented in
[`CL/ToRdf.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/CL/ToRdf.lean):
binary and unary atomic predication, and the `(that S)` clause,
translated and counted; a quantified sentence, or a non-name subject,
is skipped and counted rather than silently dropped, and every
proposition's canonical sentence rides along inside its named graph.
The wider CL/IKL port — quantifiers, equations, `cl:module`
structure, the guide's numeric quantifiers — is tracked at
[issue 580](https://github.com/danbri/factoidal/issues/580);
proposition individuation (the alpha-normalized content-address
naming above, and the guide's stronger `=p` relation as a follow-up)
at [issue 589](https://github.com/danbri/factoidal/issues/589); the
sentence forms above follow the [IKL
GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html)
(Hayes and Menzel).
