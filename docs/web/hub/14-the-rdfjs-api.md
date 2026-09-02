---
title: "The RDF/JS API"
description: "The W3C RDF/JS Data Model spec, factoidal's own adapter (npm/factoidal/rdfjs.js), and how it relates to fn.parse's Dataset — the data-model interop story, distinct from post 12's function tour."
layout: hub.njk
series: docs-hub
series_order: 14
vocab: foaf
status: published
tests: tests/hub/post14_test.mjs
---

[Post 12](./12-the-api-tour.md) walked `npm/factoidal`'s whole function
surface — one row per capability. This post is narrower and lower-level:
not *what functions exist*, but *what a term and a dataset actually are*
once a call returns one, and how that shape relates to the rest of the
JavaScript RDF ecosystem.

## The spec this is built on

[RDF/JS: Data model specification](https://rdf.js.org/data-model-spec/)
is the community standard a JavaScript RDF library is expected to
implement: a `DataFactory` that constructs `NamedNode`/`BlankNode`/
`Literal`/`Variable`/`DefaultGraph`/`Quad` terms, each with a fixed
`termType` string, a `value`, and a value-based `.equals()` method — the
shape N3.js, rdflib.js, Comunica, and every other JS RDF tool
inter-operate through. A library that speaks this shape can hand a
`Dataset` to any of them without a translation layer.

`npm/factoidal` implements it directly in
[`rdfjs.js`](https://github.com/danbri/factoidal/blob/claude/main/npm/factoidal/rdfjs.js):
a `dataFactory` (`namedNode`/`blankNode`/`literal`/`variable`/
`defaultGraph`/`quad`/`fromTerm`/`fromQuad`), the five term classes plus
`Quad` (each frozen at construction, each with a spec-correct
`.equals()`), and a minimal `Dataset` — `size`, `add`/`delete`/`has`,
`match(s, p, o, g)`, iteration, `toNQuads()`/`Dataset.fromNQuads()`. It
is genuinely small: no parsing logic lives here (RDF parsing is F\*'s
job, per Iron Rule #4) — `rdfjs.js` only builds/compares/tokenizes terms
that some other layer already produced.

`npm/factoidal/index.js`'s typed `parse()`/`query()` are built directly
on top of this module — `lib/api.js` imports `Dataset`, `dataFactory`,
and `termFromSrj` from it and uses them to shape every `Dataset` and
every `Map<string, Term>` binding row the package returns. So in Node,
"the RDF/JS API" and "the data shape the rest of this series has been
using all along" are the same thing.

## How this page's own `fn` relates

This page's `fn.parse()` — the binding every other post's live cells
call — does **not** go through `rdfjs.js` directly. `rdfjs.js` is
CommonJS with `node:fs`/`node:crypto` dependencies elsewhere in
`npm/factoidal`, so it can't load in this page's `<script type="module">`
context; `docs/_includes/hub.njk` instead defines a small
browser-local adapter (`FnDataset`, plain `{termType, value, ...}`
term objects) that mimics the same *shape* by hand — see
[`README.md`](../README/)'s "Why `fn` is an adapter, not an import" for
the full reasoning. The practical difference: a term this page's `fn`
hands back is duck-typed to look like a Term (same fields a real one
has) but is **not** an instance of the classes above, and has no
`.equals()` method. A term Node's real `npm/factoidal` hands back
(what this post's pinning test actually runs against) **is** a genuine
frozen `rdfjs.js` instance, `.equals()` included. Both shapes carry
`termType`/`value`/`language`/`datatype` identically — a cell written
against either one runs unchanged — but only the real package's terms
support `.equals()` directly. The second cell below measures this gap
rather than asserting past it.

## Building quads by hand, and querying them

`dataFactory` lets a caller build a graph term-by-term instead of
writing Turtle text — useful when the data is already structured in
JS (rows from a database query, results from another API) rather than
a string. This page's `fn`/`Factoidal` bindings don't expose
`dataFactory` directly (see above), so the cells below define the same
minimal factory shape locally — three tiny constructors, matching
`rdfjs.js`'s `NamedNode`/`Literal`/`Quad` contract (frozen-shaped
objects, a `termType`, a value-based `.equals()`) — then hand the
constructed quads to the real engine the only way any RDF/JS-shaped
data reaches it: serialized to N-Quads text, parsed by `fn.parse()`.
`namedNode` is used by both cells below, so it's declared once as a
shared, named cell:

```observable-js
namedNode = (value) => ({
  termType: "NamedNode",
  value,
  equals(o) { return !!o && o.termType === "NamedNode" && o.value === value; },
})
```

```observable-js
function literal(value, language) {
  return {
    termType: "Literal",
    value,
    language: language || "",
    equals(o) {
      return !!o && o.termType === "Literal" && o.value === value &&
        (o.language || "") === (language || "");
    },
  };
}
function quad(subject, predicate, object) {
  return {
    subject, predicate, object,
    equals(o) {
      return !!o && subject.equals(o.subject) && predicate.equals(o.predicate) &&
        object.equals(o.object);
    },
  };
}
function quadToNQuads(q) {
  const term = (t) => t.termType === "NamedNode"
    ? `<${t.value}>`
    : (t.language ? `"${t.value}"@${t.language}` : `"${t.value}"`);
  return `${term(q.subject)} ${term(q.predicate)} ${term(q.object)} .\n`;
}

const ex = (s) => namedNode("http://example.org/" + s);
const foaf = (s) => namedNode("http://xmlns.com/foaf/0.1/" + s);

const quads = [
  quad(ex("alice"), foaf("name"), literal("Alice")),
  quad(ex("alice"), foaf("knows"), ex("bob")),
  quad(ex("bob"), foaf("name"), literal("Bob")),
];

const nquads = quads.map(quadToNQuads).join("");
const dataset = await fn.parse(nquads, { format: "nquads" });
const rows = await fn.query(
  dataset,
  `# Every foaf:name in the graph, in alphabetical order.
PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name`
);
return pretty(rows);
```

Three quads built as terms, never as hand-escaped strings, serialized
once, parsed by the F\*-extracted N-Quads parser, then queried by the
same F\*-extracted SPARQL evaluator every other post in this series
uses — `["Alice", "Bob"]` in a `pretty()` table. The factory is the
front door; the engine underneath doesn't know or care whether its
input text was hand-written or assembled from term objects.

## `.equals()` vs `===`

Two `NamedNode`s built from the same IRI are two different JavaScript
objects — `===` compares object identity, so it's `false` even though
both terms denote the same resource. The RDF/JS spec's answer is
`.equals()`: value equality, per the spec's own contract for each term
kind (same `termType` and `value`, and for `Literal` also the same
`language`/`datatype`). This is the check that matters for RDF —
`===` almost never is:

```observable-js
const a = namedNode("http://example.org/alice");
const b = namedNode("http://example.org/alice");
const c = namedNode("http://example.org/bob");

const nquads = "<http://example.org/alice> <http://example.org/knows> <http://example.org/bob> .\n";
const dataset = await fn.parse(nquads, { format: "nquads" });
const rows = await fn.query(dataset, `# The object of every triple, to get one term back from the engine.
SELECT ?o WHERE { ?s ?p ?o }`);
const queriedTerm = rows[0].get("o");

return pretty({
  sameReferenceAB: a === b,
  sameByEqualsAB: a.equals(b),
  sameReferenceAC: a === c,
  sameByEqualsAC: a.equals(c),
  queriedTermHasEquals: typeof queriedTerm.equals === "function",
});
```

The first four fields are environment-independent: `a === b` is
`false` (distinct objects), `a.equals(b)` is `true` (same IRI), and the
`...AC` pair (different IRIs) is `false` both ways. `queriedTermHasEquals`
is the one field that is *not* the same everywhere, and that's the
point of this post's second section: this exact cell, pinned in
[`tests/hub/post14_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post14_test.mjs)
and executed there against the real `npm/factoidal` package, reports
`true` — a query result term from the real package is a genuine
`rdfjs.js` instance. Loaded on *this* page, against this page's
lightweight browser adapter, the same field reports `false` — a
demonstration, not a defect, of the gap the section above described.
If you're writing code against the shipped `npm/factoidal` package
rather than this demo page, `.equals()` on a query result term is
always safe to call.

## What's next

[The next post](./15-how-fast-the-performance-story.md) turns from data
model to data volume — the performance story, with numbers that carry
their own dates and commits rather than being asserted.

Every live cell above is pinned in
[`tests/hub/post14_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post14_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API, which is where `queriedTermHasEquals` above reads `true` rather
than the `false` this live page reports.
