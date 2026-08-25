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
SPARQL text, through `fn.l4Call(op, args)` — the generic dispatch
wrapper into
[`Wasm/Dispatch.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/Wasm/Dispatch.lean).
When the two engines return the same rows, the specification is doing
the work; when they disagree, one of them has a bug, and it shows here
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
  SELECT ?s ?n ?a WHERE {
    ?s <${EX}name> ?n .
    ?s <${EX}age> ?a .
  }
`
```

## Lean parses it and answers it

`parseToDatasetJson` parses the Turtle; `queryDataset` runs the SPARQL
SELECT over the parsed dataset. Both are dispatch ops on the same wasm
module `leanVersion` came from.

```observable-js
leanParsed = fn.l4Call("parseToDatasetJson", [PEOPLE_TTL, "turtle", ""])
```

```observable-js
leanNameAge = {
  const r = await fn.l4Call("queryDataset", [leanParsed.nquads, NAME_AGE_QUERY]);
  return r.srj.results.bindings.map((b) =>
    Object.fromEntries(Object.entries(b).map(([k, t]) => [k, t.value])));
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
ASK_QUERY = `ASK { ?s <${EX}age> ?a . FILTER(?a > 25) }`
```

```observable-js
leanAsk = {
  const r = await fn.l4Call("queryDataset", [leanParsed.nquads, ASK_QUERY]);
  return r.boolean;
}
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
module's generic dispatch entry, `fn.l4Call`, exercised above.
[Post 38](../38-one-triple-at-a-time/) walks that surface one call at
a time, ending in its own cross-engine agreement check.
