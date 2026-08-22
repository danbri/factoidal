---
title: "Lean 4 in the browser: a second engine on the page"
description: "The Lean 4 port compiled Lean → C → WebAssembly and run next to the F*-derived engine, on the same data, in the same page — with an exact account of what the Lean side can and cannot do yet."
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
— separate source, separate proof assistant, separate compiler — reaching
your browser by a completely different road: Lean to C, C to
WebAssembly.

Two independently written implementations of the same W3C specification,
answering the same query in the same page, is a much stronger signal than
either one answering it alone. When they agree, the specification is
doing the work. When they disagree, one of them has a bug — and you can
see it here rather than in a conformance report.

## What is actually running

The Lean side is not a re-implementation of the JavaScript engine, and
it is not a wrapper around it. It is
[`L4Factoidal.SPARQL.evalBgp`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/SPARQL/Algebra.lean)
— the Basic Graph Pattern evaluator of [SPARQL 1.1
§18.3](https://www.w3.org/TR/sparql11-query/#BasicGraphPatterns), written
in Lean with no `sorry`, no `axiom`, no `partial` and no
`native_decide` — compiled by the Lean compiler to C, and that C
compiled to wasm32 together with Lean's own runtime.

Getting there needed one piece nobody ships: Lean's runtime and its
compiled core library exist as native binaries only, so both were
rebuilt for wasm32 (the recipe is in
[`skills/lean4-wasm-export`](https://github.com/danbri/factoidal/blob/claude/main/skills/lean4-wasm-export/SKILL.md)).
The result is a single 1.5 MB `.wasm` that the browser, Node and Deno all
load — no GMP, no threads, no server.

## Be clear about what this is not

This is phase 1, and the gap is worth stating plainly rather than
discovering mid-page:

- **The Lean side parses no SPARQL.** There is no query parser in the
  Lean port yet, so a Basic Graph Pattern arrives as a *table of
  patterns*, not as a query string. The F\* engine below gets the same
  query as ordinary SPARQL text, because it has a parser.
- **The Lean side parses no Turtle or N-Triples.** Data arrives as a
  table of term objects. The N-Triples/N-Quads reader and a JSON module
  are in flight on separate branches; when they land, the JSON shim in
  [`Wasm/Abi.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/Wasm/Abi.lean)
  gets deleted and these cells start from text on both sides.
- **Only BGP evaluation is exported.** No `OPTIONAL`, `UNION`,
  `FILTER`, projection or `ORDER BY` across the wasm boundary yet,
  though `Algebra.lean` implements the §18.5 operators natively.

So the comparison below is narrow on purpose: the part both engines
implement today.

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
pretty(leanNames)
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
pretty(leanNameAge)
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
pretty(fstarNameAge)
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
pretty(agreement)
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

## What lands next

In dependency order: the [N-Triples/N-Quads
reader](https://github.com/danbri/factoidal/issues/466) and a JSON
module, which let both sides start from RDF text; then a SPARQL parser
on the Lean side, which turns the pattern table above into an actual
query string; then the §18.5 operators across the wasm boundary, which
`Algebra.lean` already implements. At that point this page can run the
W3C test suite twice on one screen.
