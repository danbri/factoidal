---
title: "One graph, five syntaxes"
description: "The same foaf graph parsed from Turtle, N-Triples, RDF/XML, N-Quads, and TriG — the bytes converge every time."
layout: hub.njk
series: docs-hub
series_order: 11
vocab: foaf
status: published
tests: tests/hub/post11_test.mjs
---

[Post 1](./01-triples-rdf-from-first-principles.md) parsed Alice and
Bob out of Turtle. Turtle is one concrete syntax for RDF among several
this project implements — the abstract graph (a set of
subject-predicate-object triples) doesn't care which syntax it was
written in. This post proves that concretely: the same graph, written
by hand five different ways, parsed with five different parsers, comes
out as the identical set of triples every time.

## The five syntaxes

- **Turtle** — the human-writable syntax every earlier post has used.
- **N-Triples** — Turtle stripped to its simplest possible form: one
  full triple per line, no prefixes, no shorthand.
- **N-Quads** — N-Triples plus an optional fourth term, the named
  graph.
- **TriG** — Turtle plus `graphname { ... }` blocks for named graphs
  (Turtle is to N-Triples as TriG is to N-Quads).
- **RDF/XML** — the original 1999-era RDF syntax, an XML tree read
  back into the same triples.

Combined, RDF 1.1 parsing (all five syntaxes plus the RDF model-theory
suite) scores **1031 pass, 0 fail (of 1031)**:
rdf-turtle 313 pass, 0 fail; rdf-xml 166 pass, 0 fail; rdf-n-triples 70
pass, 0 fail; rdf-n-quads 87 pass, 0 fail; rdf-trig 356 pass, 0 fail —
see [the test-results dashboard]({{ '/test-results/' | url }}) for the
current run of each suite individually.

## Same triples, two syntaxes, one parse each

Turtle and RDF/XML describing the identical Alice/Bob graph from
post 1. Parse both with `fn.parse()` (each with its own `format`) and
compare the resulting N-Quads text byte for byte — `Dataset.toNQuads()`
dumps triples in a fixed sorted order (`RDF.Canonical`'s
`canonical_nquads`), so two parses of an equivalent graph, regardless
of which syntax or triple order the source used, produce the exact
same string:

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

const rdfxml = `<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:foaf="http://xmlns.com/foaf/0.1/">
  <foaf:Person rdf:about="http://example.org/alice">
    <foaf:name>Alice</foaf:name>
    <foaf:knows rdf:resource="http://example.org/bob"/>
  </foaf:Person>
  <foaf:Person rdf:about="http://example.org/bob">
    <foaf:name>Bob</foaf:name>
  </foaf:Person>
</rdf:RDF>`;

const dsTurtle = await fn.parse(turtle, { format: "turtle" });
const dsXml = await fn.parse(rdfxml, { format: "rdfxml" });

return {
  turtleSize: dsTurtle.size,
  xmlSize: dsXml.size,
  identicalBytes: dsTurtle.toNQuads() === dsXml.toNQuads(),
};
```

Five triples each way, and `identicalBytes: true` — RDF/XML's verbose
tree and Turtle's terse prefixed form describe the same graph, and
both parsers agree down to the byte.

## N-Triples and N-Quads: the simplest two

N-Triples is what Turtle looks like with every shorthand removed —
full IRIs, one triple per line, a `.` terminator. N-Quads is
N-Triples plus a graph term. Parsed straight, they should match the
Turtle version above too:

```observable-js
const turtle = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob a foaf:Person ; foaf:name "Bob" .
`;

const ntriples = `
<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> .
<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> "Alice" .
<http://example.org/alice> <http://xmlns.com/foaf/0.1/knows> <http://example.org/bob> .
<http://example.org/bob> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> .
<http://example.org/bob> <http://xmlns.com/foaf/0.1/name> "Bob" .
`;

const dsTurtle = await fn.parse(turtle, { format: "turtle" });
const dsNTriples = await fn.parse(ntriples, { format: "ntriples" });

return {
  identicalBytes: dsTurtle.toNQuads() === dsNTriples.toNQuads(),
  sampleLine: dsNTriples.toNQuads().split("\n")[0],
};
```

## TriG and N-Quads: adding a named graph

TriG and N-Quads are the only two of the five that carry a **named
graph** — a fourth term saying which graph a triple belongs to, not
just the default one. Put Alice and Bob inside a named graph
`ex:g` in TriG, and the same triples plus the same graph name in
N-Quads, and the two should still converge:

```observable-js
const trig = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:g {
    ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
    ex:bob a foaf:Person ; foaf:name "Bob" .
  }
`;

const nquads = `
<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> <http://example.org/g> .
<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> "Alice" <http://example.org/g> .
<http://example.org/alice> <http://xmlns.com/foaf/0.1/knows> <http://example.org/bob> <http://example.org/g> .
<http://example.org/bob> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> <http://example.org/g> .
<http://example.org/bob> <http://xmlns.com/foaf/0.1/name> "Bob" <http://example.org/g> .
`;

const dsTrig = await fn.parse(trig, { format: "trig" });
const dsNQuads = await fn.parse(nquads, { format: "nquads" });

return {
  identicalBytes: dsTrig.toNQuads() === dsNQuads.toNQuads(),
  size: dsTrig.size,
};
```

Same result: `identicalBytes: true`. TriG's `{ }` block and N-Quads'
fourth term are two spellings of the same fact — "this triple is in
graph `ex:g`."

## The newest parser strata

Two more W3C-conformance surfaces landed recently, underneath the
syntaxes above rather than alongside them: full **XML 1.0
well-formedness** (`Parser.XML.fst`, needed by RDF/XML parsing itself)
scores 1442 pass, 0 fail on well-formedness of 2585 total in the W3C
XML Conformance Suite — the remaining 1143 are DTD-validation buckets
this project doesn't implement (well-formedness only, not the DOCTYPE
validation layer), skipped rather than force-passed. **XPath 1.0**
(`Parser.XPath.fst`/`XPath.Eval.fst`, 8 of 13 axes and all 22 core
functions) scores 69 pass, 0 fail on its 69 spec-cited unit tests. Both
are documented in
[the test-results dashboard]({{ '/test-results/' | url }}); neither
has a live cell of its own here since neither is a top-level RDF
concrete syntax, but both sit underneath RDF/XML parsing and (XPath)
RML's XML source support.

## What's next

[The previous post](./10-rules-rif-core.md) forward-chained RIF
rules over a fact base. [The next post](./12-the-api-tour.md) is the
one door to everything this series has shown so far — the npm
package's whole surface, one function per capability.

Every live cell above is pinned in
[`tests/hub/post11_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post11_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn` adapter.
