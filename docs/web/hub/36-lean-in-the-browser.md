---
title: "Lean 4 in the browser: a second engine on the page"
description: "The Lean 4 port, compiled Lean → C → WebAssembly, answering the same query as the F*-derived engine in the same page."
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
When the two engines return the same rows, the specification is doing
the work; when they disagree, one of them has a bug, and it shows here
rather than in a conformance report.

The Lean function on this page is
[`L4Factoidal.SPARQL.evalBgp`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/SPARQL/Algebra.lean)
— [SPARQL 1.1 §18.3](https://www.w3.org/TR/sparql11-query/#BasicGraphPatterns)
Basic Graph Pattern matching, written with no `sorry`, no `axiom`, no
`partial` and no `native_decide`. The cells keep the narrow phase-1
surface they were written against: patterns and data arrive as term
tables, because this page predates the Lean parsers. That gap has
closed — the same wasm module now parses RDF text and full SPARQL, and
[post 38](../38-one-triple-at-a-time/) runs that wider surface from
text on both sides.

## Loading the Lean engine

`fn.loadL4()` instantiates the module (once per page) and
`fn.l4Version()` asks the Lean code to identify itself. The string comes
out of Lean's `String` type, across the C boundary, into JavaScript.

```observable-js
leanVersion = fn.l4Version()
```

## The data, as both engines want it

Four triples about two people. The Lean side takes them as term objects
in the [SPARQL Query Results
JSON](https://www.w3.org/TR/sparql11-results-json/) shape; the F\* side
takes the same four triples as Turtle text.

```observable-js
EX = "http://example.org/"
```

```observable-js
term = ({
  iri: (v) => ({ type: "uri", value: v }),
  lit: (v, datatype) => (datatype ? { type: "literal", value: v, datatype } : { type: "literal", value: v }),
  v: (name) => ({ type: "var", value: name }),
})
```

```observable-js
PEOPLE = {
  const XSD_INT = "http://www.w3.org/2001/XMLSchema#integer";
  const t = (s, p, o) => ({ subject: term.iri(EX + s), predicate: term.iri(EX + p), object: o });
  return [
    t("alice", "name", term.lit("Alice")),
    t("alice", "age", term.lit("30", XSD_INT)),
    t("bob", "name", term.lit("Bob")),
    t("bob", "age", term.lit("24", XSD_INT)),
  ];
}
```

```observable-js
PEOPLE_TTL = `
  @prefix : <${EX}> .
  :alice :name "Alice" ; :age 30 .
  :bob   :name "Bob"   ; :age 24 .
`
```

## One pattern, evaluated by Lean

`?s :name ?n` — a one-triple BGP. Lean scans the graph and returns the
solution sequence as a results-JSON document; the cell flattens it to a
table.

```observable-js
rowsOf = (doc) =>
  doc.results.bindings.map((b) =>
    Object.fromEntries(Object.entries(b).map(([k, t]) => [k, t.value])))
```

```observable-js
leanNames = {
  const doc = await fn.l4BgpQuery(PEOPLE, [
    { subject: term.v("s"), predicate: term.iri(EX + "name"), object: term.v("n") },
  ]);
  return rowsOf(doc);
}
```

```observable-js
leanNamesTable = pretty(leanNames)
```

## Two patterns, correlated on `?s`

The same query [`Demo.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/Demo.lean)
runs at the command line: two triple patterns sharing a subject
variable, so each answer row must agree on `?s` in both. This is where a
BGP stops being a filter and starts being a join.

```observable-js
leanNameAge = {
  const doc = await fn.l4BgpQuery(PEOPLE, [
    { subject: term.v("s"), predicate: term.iri(EX + "name"), object: term.v("n") },
    { subject: term.v("s"), predicate: term.iri(EX + "age"), object: term.v("a") },
  ]);
  return rowsOf(doc);
}
```

```observable-js
leanNameAgeTable = pretty(leanNameAge)
```

## The same question, asked of the F\* engine

Here the query is a *string*, because this engine has a parser. Same
four triples, same intended answer.

```observable-js
fstarNameAge = {
  const dataset = await fn.parse(PEOPLE_TTL);
  const rows = await fn.query(dataset, `
    SELECT ?s ?n ?a WHERE {
      ?s <${EX}name> ?n .
      ?s <${EX}age> ?a .
    }`);
  return rows.map((m) => Object.fromEntries([...m].map(([k, t]) => [k, t.value])));
}
```

```observable-js
fstarNameAgeTable = pretty(fstarNameAge)
```

## Do they agree?

The interesting cell. Both engines produced rows for `?s`, `?n`, `?a`
over the same graph; a BGP's answer is a *set*, so the comparison sorts
before comparing and does not care about row order.

```observable-js
agreement = {
  const norm = (rows) => rows.map((r) => `${r.s}|${r.n}|${r.a}`).sort();
  const lean = norm(leanNameAge);
  const fstar = norm(fstarNameAge);
  return {
    leanRows: lean.length,
    fstarRows: fstar.length,
    identical: JSON.stringify(lean) === JSON.stringify(fstar),
  };
}
```

```observable-js
agreementTable = pretty(agreement)
```

Two proof assistants, two compilers, two runtimes, one answer.

That agreement is not proof of anything on its own — both engines could
misread the same clause of §18.3 in the same way. What it does buy is
independence: the Lean evaluator was written from the specification
text, not from the F\* source, so a shared bug now needs the same
misreading to have happened twice. Where the F\* tree carries theorems
about its evaluator, the Lean tree carries its own
([`Invariants.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/SPARQL/Invariants.lean)
proves BGP monotonicity and the merge/lookup characterisation, with
`#print axioms` in the build log to show nothing was assumed).

## Status

**Update (2026-08-25):** the phase-1 gaps have closed. The Lean engine
now parses N-Triples/N-Quads, Turtle, TriG and RDF/XML, parses and
evaluates SPARQL query and update, runs the RDFS and OWL 2 RL
closures, and canonicalizes with RDFC-1.0 — all through the same wasm
module's generic dispatch entry (`fn.l4Call`).
[Post 38](../38-one-triple-at-a-time/) walks that surface one call at
a time, ending in a cross-engine agreement check.
