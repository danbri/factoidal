---
title: "Propositions as first-class citizens"
description: "Two sources disagree; flattening their reports to bare triples asserts the contradiction and loses who said what. The Lean 4 engine turns each IKL proposition into a named graph, decorated with who says it, and SPARQL finds the disagreement from declared disjointness."
layout: hub.njk
series: docs-hub
series_order: 39
vocab: none
status: published
tests: tests/hub/post39_test.mjs
---

Two news sources report on the same person. One says he is alive; the
other says he is dead. Both reports are real data — you want to keep
both, know who said what, and query where they disagree. Write the
claims down as plain RDF triples and the trouble starts at the merge:

```observable-js
plainFacts = `<urn:cl:OBL> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:cl:Alive> .
<urn:cl:OBL> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:cl:Dead> .
`
```

```observable-js
rows = (r) => r.srj.results.bindings.map(
  (b) => Object.fromEntries(Object.entries(b).map(([k, t]) => [k, t.value])))
```

```observable-js
flatStatus = {
  const r = await fn.l4Call("queryDataset", [plainFacts,
    "SELECT ?status WHERE { <urn:cl:OBL> a ?status } ORDER BY ?status"]);
  return rows(r);
}
```

The merged graph asserts BOTH rows as flat fact: OBL is Alive, and OBL
is Dead. RDF can attach a source to a statement — RDF reification,
named graphs, and RDF 1.2 reifiers all exist for exactly that — but
this data used none of them: flattening the two reports to bare
triples UNIONED their contents, so the graph itself now makes the
contradictory claim and no triple records who said what. What each
source produced was a claim; to keep the claims apart, the claims
themselves must become addressable objects, rather than their contents
merged into one graph.

## Hold the claims, not the contradiction

[IKL](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) — Pat
Hayes and Chris Menzel's extension of [Common Logic (ISO/IEC
24707)](https://www.iso.org/standard/66249.html) — adds one
term-forming construct to the CLIF syntax: `(that S)` turns a sentence
`S` into a term denoting the proposition `S` expresses. A source can
then stand in a relation to a claim without the claim being asserted:

```observable-js
sourcesText = `(says MorningWire (that (Alive OBL)))
(says EveningPost (that (Dead OBL)))`
```

`clToDataset` translates a CLIF text into an RDF dataset (RDF 1.1
Concepts §4). Each proposition becomes a NAMED GRAPH holding the
claim's content; the default graph holds only DECORATIONS of those
graphs — here, one `says` link per source, pointing at the graph of
the claim it made. Neither `(Alive OBL)` nor `(Dead OBL)` lands in
the default graph, so the dataset asserts no contradiction — it
asserts who said what.

```observable-js
sourcesDataset = fn.l4Call("clToDataset", [sourcesText, "urn:cl:"])
```

One naming rule does all the individuation on this page:
alpha-equivalent canonical CLIF sentences receive the same
content-address IRI — that, and nothing wider. IKL's referential
transparency (if Bill = William, a proposition about Bill IS the
proposition about William) cannot be implemented by any syntactic
naming rule; the guide places it in the defined relation `=p`, tracked
in [issue 589](https://github.com/danbri/factoidal/issues/589).

## Who says what

`queryWithIklService` runs a SPARQL query with the CLIF translation
bound to the [SERVICE endpoint
IRI](https://www.w3.org/TR/sparql11-federated-query/#defn_service)
`urn:ikl:kb`, and the translation's named graphs visible to [`GRAPH`
patterns](https://www.w3.org/TR/sparql11-query/#queryDataset) (SPARQL
1.1 §13.3). The SERVICE pattern reads the decorations; the GRAPH
pattern reads inside a claim. Each proposition graph records its own
sentence as data (under `urn:cl:def:sentence`), so the answer shows
the claim itself, not an identifier:

```observable-js
whoSaysWhat = {
  const r = await fn.l4Call("queryWithIklService", ["", sourcesText, `
    SELECT ?source ?claim WHERE {
      SERVICE <urn:ikl:kb> { ?source <urn:cl:says> ?g }
      GRAPH ?g { ?g <urn:cl:def:sentence> ?claim }
    } ORDER BY ?source`]);
  return rows(r);
}
```

Two rows: each source paired with the CLIF text of the claim it made,
read back out of the claim's own graph. The same variable `?g` is
used here both as the proposition's identifier (in the `says` link)
and as the name of the graph holding its content (in the `GRAPH`
pattern). RDF semantics does not identify a graph name with the graph
it names; reading the one IRI both ways is a deliberate extra
semantic commitment of Factoidal's `x-ikl-*` encoding, not an RDF
entailment.

## Where do the sources disagree?

`Alive` and `Dead` are disjoint — no one is both — and the data can
SAY so, with an ordinary OWL vocabulary triple:

```observable-js
disjointness = `<urn:cl:Alive> <http://www.w3.org/2002/07/owl#disjointWith> <urn:cl:Dead> .
`
```

A disagreement is then two propositions, from two sources, whose
contents put the same individual into two classes DECLARED disjoint.
The query below discovers the conflicting class pair from the
`owl:disjointWith` declaration — no class IRI is hardcoded — and
joins it against the classifications inside the two proposition
graphs:

```observable-js
disagreement = {
  const r = await fn.l4Call("queryWithIklService", [disjointness, sourcesText, `
    SELECT ?about ?src1 ?claim1 ?src2 ?claim2 WHERE {
      ?c1 <http://www.w3.org/2002/07/owl#disjointWith> ?c2 .
      SERVICE <urn:ikl:kb> { ?src1 <urn:cl:says> ?g1 . ?src2 <urn:cl:says> ?g2 }
      GRAPH ?g1 { ?about a ?c1 . ?g1 <urn:cl:def:sentence> ?claim1 }
      GRAPH ?g2 { ?about a ?c2 . ?g2 <urn:cl:def:sentence> ?claim2 }
    }`]);
  return rows(r);
}
```

One row: the individual both claims are about, and the two
source/claim pairs that conflict. The dataset never asserted the
contradiction; the query FOUND it, with its provenance attached. Be
precise about what this query does and does not do: it finds
classifications the data declares incompatible via `owl:disjointWith`.
It is not general contradiction detection — nothing here notices
`(P a)` against `(not (P a))`, or conflicts that follow only through
longer inference chains. The `x-ikl-*` regimes ([issue
581](https://github.com/danbri/factoidal/issues/581)) are the
continuation where entailment machinery returns.

## Assertion, belief, and context: one link pattern

`says` above is not special — any predication about a proposition
becomes a default-graph link to the proposition's graph. IKL's stock
examples use `believes` (an agent's belief) and `ist` (truth in a
context), and CLIF's "cancelling parentheses" form `((that S))`
asserts the proposition outright — which the translation records as a
`urn:cl:def:asserts` decoration from the knowledge base itself. Three
sentences about ONE proposition:

```observable-js
threeDecorations = `(believes Zeno (that (Dead OBL)))
(ist Day2006 (that (Dead OBL)))
((that (Dead OBL)))`
```

```observable-js
decorationRows = {
  const r = await fn.l4Call("queryWithIklService", ["", threeDecorations, `
    SELECT ?who ?how WHERE {
      SERVICE <urn:ikl:kb> { ?who ?how ?g }
      GRAPH ?g { ?g <urn:cl:def:sentence> "(Dead OBL)" }
    } ORDER BY ?how`]);
  return rows(r);
}
```

Three rows, one graph: Zeno believes it, it holds in Day2006, and the
knowledge base asserts it. Assertion, belief and context use one
uniform proposition-link pattern — the same STRUCTURE, with different
semantics and axioms: `believes` relates an agent to a proposition,
`ist` a context, and `asserts` commits the knowledge base to it; only
the last makes the proposition's content hold under the `x-ikl-*`
regime rule. (The three links land on ONE graph because a
proposition's graph is named by its sentence's content, not by which
input sentence mentioned it — the encoding section below says how.)

## The payoff: disagreement joined against reference data

The sources and the person also exist in ordinary RDF — say, a
reference dataset with human-readable labels, which is also where the
disjointness declaration belongs. `queryWithIklService`'s first
argument is that RDF data; the query below is the disagreement query
again — still discovering the conflicting classes from
`owl:disjointWith` — joined against the labels, so the answer arrives
in words:

```observable-js
refData = `<urn:cl:OBL> <http://www.w3.org/2000/01/rdf-schema#label> "Obadiah" .
<urn:cl:MorningWire> <http://www.w3.org/2000/01/rdf-schema#label> "The Morning Wire" .
<urn:cl:EveningPost> <http://www.w3.org/2000/01/rdf-schema#label> "The Evening Post" .
<urn:cl:Alive> <http://www.w3.org/2002/07/owl#disjointWith> <urn:cl:Dead> .
`
```

```observable-js
disagreementNamed = {
  const r = await fn.l4Call("queryWithIklService", [refData, sourcesText, `
    PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    SELECT ?person ?name1 ?claim1 ?name2 ?claim2 WHERE {
      ?about rdfs:label ?person .
      ?c1 <http://www.w3.org/2002/07/owl#disjointWith> ?c2 .
      SERVICE <urn:ikl:kb> { ?src1 <urn:cl:says> ?g1 . ?src2 <urn:cl:says> ?g2 }
      GRAPH ?g1 { ?about a ?c1 . ?g1 <urn:cl:def:sentence> ?claim1 }
      GRAPH ?g2 { ?about a ?c2 . ?g2 <urn:cl:def:sentence> ?claim2 }
      ?src1 rdfs:label ?name1 . ?src2 rdfs:label ?name2 .
    }`]);
  return rows(r);
}
```

"The Morning Wire says `(Alive OBL)`; The Evening Post says `(Dead
OBL)`; both are about Obadiah." The claims stayed first-class, the
provenance stayed attached, and the contradiction stayed un-asserted
— found by an ordinary SPARQL join, no bespoke belief reasoner
anywhere.

## How it is encoded

The machinery under the story, briefly. `clParse` reads a CLIF text,
counts sentences, canonicalises each, and reports whether the text is
pure ISO/IEC 24707 CL — the `(that S)` term makes ours IKL, so
`pureCL` is `false`:

```observable-js
sourcesParse = fn.l4Call("clParse", [sourcesText])
```

The translation rules
([`CL/ToRdf.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/CL/ToRdf.lean)):
every top-level sentence maps to a named graph holding its
translatable atoms plus its own canonical sentence as data — one
top-level sentence, one proposition, uniformly: a top-level
`(and A B)` is ONE asserted proposition whose conjuncts are graph
content, exactly as if it had been written `((that (and A B)))`. The
default graph receives only decorations — an assertion triple per
top-level asserted sentence, a link triple per predication about a
proposition, and the `cl:rdfProjection` decoration below. Sentence parts
outside the translatable fragment (quantifiers, negation,
disjunction) are counted in `skipped`, and the sentence record keeps
their text queryable. `count` in the `clToDataset` envelope above is
graph-content triples plus decorations. A proposition's graph is
named by a SHA-256 content address of its alpha-normalized canonical
CLIF sentence — the one place a raw hash shows: `(Dead OBL)`'s graph
is `urn:cl:that:sha256:627ab6…` in every dataset on this page, which
is exactly why three input sentences decorated one graph above.

One more decoration ties the smallest propositions to RDF 1.2. When a
proposition's sentence translates to exactly one triple, the default
graph links the proposition to that triple's [triple
term](https://www.w3.org/TR/rdf12-concepts/#section-triple-terms)
under the predicate `urn:cl:def:rdfProjection` — the proposition's
RDF-native rendering as a `<<( … )>>` value, queryable without
entering the graph. The predicate is deliberately NOT `rdf:reifies`:
in RDF 1.2 the triple term itself denotes the proposition, while a
reifier is an occurrence token — many reifiers may share one triple
term. The proposition IRI names the proposition, not an occurrence of
it, so `rdf:reifies` is reserved for the report layer in the closing
section.

```observable-js
asMaps = (r) => r.srj.results.bindings.map((b) => {
  const t = (v) => v.type === "uri" ? { termType: "NamedNode", value: v.value }
    : v.type === "bnode" ? { termType: "BlankNode", value: v.value }
    : v.type === "triple" ? { termType: "Quad", value: "",
        subject: t(v.value.subject), predicate: t(v.value.predicate),
        object: t(v.value.object) }
    : { termType: "Literal", value: v.value, language: v["xml:lang"] || "",
        datatype: { termType: "NamedNode",
                    value: v.datatype || "http://www.w3.org/2001/XMLSchema#string" } };
  return new Map(Object.entries(b).map(([k, v]) => [k, t(v)]));
})
```

```observable-js
bridge = {
  const r = await fn.l4Call("queryWithIklService", ["", sourcesText, `
    SELECT ?claim ?fact WHERE {
      SERVICE <urn:ikl:kb> {
        ?g <urn:cl:def:rdfProjection> ?fact .
      }
      GRAPH ?g { ?g <urn:cl:def:sentence> ?claim }
    } ORDER BY ?claim`]);
  return pretty(asMaps(r));
}
```

Each single-atom claim appears twice over: as its sentence text, and
as the RDF 1.2 triple term it translates to — rendered by the table
as `<<( subject predicate object )>>`.

## Closing: the three-layer model

The architecture this page has been building, stated as three layers:

1. **Proposition** — content-addressed: alpha-equivalent canonical
   CLIF sentences receive one IRI (`urn:cl:that:sha256:…`); anything
   wider than alpha-equivalence lives under `=p`, [issue
   589](https://github.com/danbri/factoidal/issues/589).
2. **RDF projection** — the proposition's RDF-native rendering: its
   named graph, and, when the sentence translates to exactly one
   triple, the `cl:rdfProjection` triple term.
3. **Assertion-report occurrences** — the next implementation step,
   NOT implemented on this page: `rdf:reifies`-based report tokens,
   one per report event, never content-deduplicated — two Morning
   Wire reports of one proposition stay two reports, each open to its
   own date, page and retraction metadata. This is what `rdf:reifies`
   is reserved for.

IKL gives us first-class proposition terms. Factoidal gives those
terms stable, queryable RDF identities and RDF projections, while
keeping assertion/context metadata outside the proposition content.

The fragment this page exercises is documented in
[`CL/ToRdf.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/CL/ToRdf.lean):
atomic predication and the `(that S)` clause, translated into
proposition graphs and decorations; everything outside the fragment
is skipped, counted, and preserved as sentence text. The wider CL/IKL
port — quantifiers, equations, `cl:module` structure — is tracked at
[issue 580](https://github.com/danbri/factoidal/issues/580); the
`x-ikl-*` entailment-regime family, whose provisional rule makes
exactly the ASSERTED propositions' content hold in the default graph,
at [issue 581](https://github.com/danbri/factoidal/issues/581). The
sentence forms follow the [IKL
GUIDE](https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) (Hayes
and Menzel).
