---
title: "Lean 4 in the browser: a second engine on the page"
description: "The Lean 4 port, compiled Lean → C → WebAssembly, parsing the same Turtle and answering the same SPARQL as the F*-derived engine, in the same page."
layout: hub.njk
series: docs-hub
series_order: 36
vocab: none
status: published
tests: tests/hub/post36_test.mjs
---

Every other page in this series runs one engine: the F\* specification,
extracted to OCaml, compiled to JavaScript. This page runs **two**. The
second is the [Lean 4 port](https://github.com/danbri/factoidal/issues/466)
— separate source, separate proof assistant, separate compiler —
compiled Lean → C → wasm32, with Lean's runtime and core library
rebuilt for wasm32
([`skills/lean4-wasm-export`](https://github.com/danbri/factoidal/blob/claude/main/skills/lean4-wasm-export/SKILL.md)).
Both engines below parse the same Turtle text and answer the same
SPARQL text, through typed wrappers with the same shape on each side:
`fn.l4Parse`/`fn.l4Query` for Lean, `fn.parse`/`fn.query` for F\*.
The Lean wrappers hold the parsed data as a HANDLE inside the wasm
module rather than as N-Quads text passed back and forth
([issue #585](https://github.com/danbri/factoidal/issues/585)) —
`fn.l4Parse` calls `datasetOpen` once in
[`Wasm/Ops/Handles.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/Wasm/Ops/Handles.lean)
and every later `fn.l4Query` call carries only that handle. When the
two engines return the same rows, the specification is doing the
work; when they disagree, one of them has a bug, and it shows here
rather than in a conformance report.

## Loading the Lean engine

`fn.loadL4()` instantiates the module (once per page) and
`fn.l4Version()` asks the Lean code to identify itself. The string comes
out of Lean's `String` type, across the C boundary, into JavaScript.

```observable-js
leanVersion = fn.l4Version()
```

## The data and the query, as text

Four triples about two people, and a SPARQL query that joins `?s :name
?n` with `?s :age ?a` — the same subject variable in both patterns, so
an answer row must satisfy them together.

```observable-js
EX = "http://example.org/"
```

```observable-js
PEOPLE_TTL = `
  @prefix : <${EX}> .
  :alice :name "Alice" ; :age 30 .
  :bob   :name "Bob"   ; :age 24 .
`
```

```observable-js
NAME_AGE_QUERY = `
  # People with both a name and an age, joined on the shared subject.
  SELECT ?s ?n ?a WHERE {
    ?s <${EX}name> ?n .
    ?s <${EX}age> ?a .
  }
`
```

## Lean parses it and answers it

`fn.l4Parse` parses the Turtle into a dataset handle; `fn.l4Query` runs
the SPARQL SELECT against that handle. Same two-step shape as the F\*
cells below — parse once into a dataset, query the dataset.

```observable-js
leanDataset = fn.l4Parse(PEOPLE_TTL)
```

```observable-js
leanNameAge = {
  const rows = await fn.l4Query(leanDataset, NAME_AGE_QUERY);
  return rows.map((m) => Object.fromEntries([...m].map(([k, t]) => [k, t.value])));
}
```

## The F\* engine, same text in

`fn.parse` and `fn.query` are the F\*-derived engine every other page
in this series runs — the same wrapper the F\* cells on
[post 38](../38-one-triple-at-a-time/) use.

```observable-js
fstarDataset = fn.parse(PEOPLE_TTL)
```

```observable-js
fstarNameAge = {
  const res = await fn.query(fstarDataset, NAME_AGE_QUERY);
  return res.map((m) => Object.fromEntries([...m].map(([k, t]) => [k, t.value])));
}
```

## Do they agree?

A BGP's answer is a set: the comparison sorts each row's own keys, then
sorts the row list, so neither key order nor row order can produce a
false disagreement.

```observable-js
agreement = {
  const key = (r) => Object.keys(r).sort().map((k) => `${k}=${r[k]}`).join("|");
  const lean = leanNameAge.map(key).sort();
  const fstar = fstarNameAge.map(key).sort();
  return {
    agree: JSON.stringify(lean) === JSON.stringify(fstar),
    leanRows: lean.length,
    fstarRows: fstar.length,
  };
}
```

## One more question, over a typed literal

`?a` above is an `xsd:integer`, not a string — [SPARQL 1.1 §17.3](https://www.w3.org/TR/sparql11-query/#OperatorMapping)
defines `>` over numeric operands, not over their lexical form. Both
engines run the identical ASK against the identical data.

```observable-js
ASK_QUERY = `
# Is there anyone older than 25? FILTER keeps only ?a values that
# satisfy the numeric comparison.
ASK { ?s <${EX}age> ?a . FILTER(?a > 25) }`
```

```observable-js
leanAsk = fn.l4Query(leanDataset, ASK_QUERY)
```

```observable-js
fstarAsk = fn.query(fstarDataset, ASK_QUERY)
```

```observable-js
askAgreement = ({ agree: leanAsk === fstarAsk, lean: leanAsk, fstar: fstarAsk })
```

That agreement is not proof of anything on its own — both engines could
misread the same clause of the SPARQL Query Language recommendation in
the same way. What it does buy is independence: the Lean evaluator was
written from the specification text, not from the F\* source, so a
shared bug now needs the same misreading to have happened twice. Where
the F\* tree carries theorems about its evaluator, the Lean tree
carries its own
([`Invariants.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/SPARQL/Invariants.lean)
proves BGP monotonicity and the merge/lookup characterisation, with
`#print axioms` in the build log to show nothing was assumed).

## Status

The Lean engine parses N-Triples/N-Quads, Turtle, TriG and RDF/XML,
parses and evaluates SPARQL query and update, runs the RDFS and OWL 2
RL closures, and canonicalizes with RDFC-1.0 — all through the wasm
module's dispatch entry, reached above through the typed
`fn.l4Parse`/`fn.l4Query` wrappers over `datasetOpen`/`datasetQuery`.
[Post 38](../38-one-triple-at-a-time/) drives the same dispatch
surface directly, one call at a time through `fn.l4Call`, ending in
its own cross-engine agreement check.
