---
title: "HDT: querying a compressed binary RDF file"
description: "HDT (Header-Dictionary-Triples) packs a whole RDF graph into one compact binary file with its terms dictionary-encoded and its triples bitmap-indexed. Factoidal's parser is pure F*, so a SPARQL query runs straight over the .hdt bytes with no prior decompression to Turtle."
layout: hub.njk
series: docs-hub
series_order: 24
vocab: hdt
status: published
tests: tests/hub/post24_test.mjs
---

Every earlier post fed the engine text — Turtle, N-Quads, JSON-LD. Text
is readable but bulky: each IRI is spelled out in full on every triple
it appears in, and a real ontology repeats the same few hundred IRIs
thousands of times. **HDT** (Header-Dictionary-Triples) is a binary RDF
serialization built to remove that redundancy. It splits a graph into
three parts: a **Header** of metadata, a **Dictionary** that assigns
each distinct term one integer id, and a **Triples** section that stores
the graph as id-triples in a bitmap-indexed structure. The result is a
single file that is both smaller than the equivalent Turtle and directly
queryable without expanding it back to text first.

That "queryable without expanding" is the part that matters here. HDT is
not a compression wrapper you unzip before use — the dictionary and the
bitmap-triples together *are* an index, so a triple-pattern lookup is
answered against the binary structure. Factoidal's HDT reader is written
in F*
([`HDT.Triples.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/HDT.Triples.fst)
and the parser modules around it) and extracted like everything else, so
the same `--data-hdt` path runs natively, and — as below — in your
browser.

## A real ontology in one binary file

The file this post queries is the
[RML-Core ontology](http://w3id.org/rml/core/spec) shipped as HDT at
[`third_party/testing/hdt/rml-core-ontology.hdt`](https://github.com/danbri/factoidal/blob/claude/main/third_party/testing/hdt/rml-core-ontology.hdt)
— under 9 KB of binary holding the whole vocabulary. The fetch is named
once, below, and every cell that queries the file references `buf`
instead of re-fetching it:

```observable-js
buf = fetch("../rml-core-ontology.hdt").then((r) => r.arrayBuffer())
```

This first cell hands those bytes to the CLI under a virtual path, and
asks the one question every store should be able to answer about itself:
how many triples are in here?

```observable-js
const rows = await fn.queryHdt(buf, `# How many triples the HDT file holds: count every solution of the
# open triple pattern ?s ?p ?o.
SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }`);
return Number(rows[0].get("n").value);
```

343 triples. `fn.queryHdt` hides the argv+files primitive the [COTTAS
on-disk demo](../../../fstar-extracted/demo-cottas.html) uses for
`--data-cottas`: the fetched bytes are registered under a virtual path
(js_of_ocaml's in-memory filesystem) inside `fn.queryHdt` itself, and
the CLI's HDT reader opens that path exactly as the native binary opens
a real file. No `fetch` reaches back out once the bytes are in hand;
the SPARQL runs entirely against the in-memory HDT structure.

## The classes it defines

Because the query layer sees ordinary triples — the dictionary decode is
invisible above the reader — the vocabulary's classes come back from a
plain `owl:Class` + `rdfs:label` query. Flip the cell's `Output` toggle
to `Table` to read the id-to-label decode the dictionary made possible:

```observable-js
const query = `# Every class the ontology defines, with its label.
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?class ?label WHERE {
  ?class a owl:Class ; rdfs:label ?label .
} ORDER BY ?label`;
const bindings = await fn.queryHdt(buf, query);
const rows = bindings.map((row) => ({
  class: row.get("class").value.replace(/^.*[#/]/, ""),
  label: row.get("label").value,
}));
return pretty(rows);
```

Every row is a class in the RML mapping vocabulary — `Triples Map`,
`Subject Map`, `Object Map`, `Reference Formulation`, and the rest — the
same terms the [RML post](../09-mapping-tables-to-triples-rml/) used to
turn tables into triples, here read back out of their binary-packed
definitions.

## Predicate shape as a bar chart

A store's predicate histogram is a quick read on what kind of graph it
is. This cell groups by predicate and draws the top few with Observable
Plot — a schema-heavy ontology leans on `rdf:type`, `rdfs:comment`,
`rdfs:label`, `rdfs:domain`/`rdfs:range`, which is exactly the profile
that shows up:

```observable-js
const query = `# Triple count per predicate, most frequent first.
SELECT ?p (COUNT(*) AS ?n) WHERE { ?s ?p ?o } GROUP BY ?p ORDER BY DESC(?n)`;
const bindings = await fn.queryHdt(buf, query);
const data = bindings.slice(0, 8).map((row) => ({
  predicate: row.get("p").value.replace(/^.*[#/]/, ""),
  count: Number(row.get("n").value),
}));

return Plot.plot({
  width: 640,
  height: 320,
  marginLeft: 130,
  x: { label: "triples" },
  y: { label: null, domain: data.map((d) => d.predicate) },
  marks: [
    Plot.barX(data, { x: "count", y: "predicate", fill: "currentColor" }),
    Plot.text(data, { x: "count", y: "predicate", text: "count", dx: 12, fontWeight: "bold" }),
    Plot.ruleX([0]),
  ],
});
```

The tallest bar is `rdf:type` at 84 — one per named term the ontology
declares — followed by the three `rdfs:` documentation predicates at 53
each. Nothing here parsed any text: the counts are tallied over the
id-triples, and only the eight winning predicate ids were decoded back
to IRIs for the labels.

## Scope and the parity floor

Factoidal's HDT support is a read path — it opens and queries an
existing `.hdt`; it does not yet *write* one (that is the HDT generator,
follow-on work). The reader is checked against a ground-truth parity
script,
[`tests/local/hdt_stage4_parity.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/local/hdt_stage4_parity.sh),
which loads this same RML-Core fixture through the HDT path and through
the ground-truth N-Triples and asserts the two agree: **6 pass, 0 fail**
at the current stage. The queries above are the same reader that floor
covers, driven from the browser instead of the shell.

## What's next

HDT is one of several binary/columnar shapes RDF lands in; the
[on-disk COTTAS format](https://github.com/danbri/factoidal/blob/claude/main/skills/disk-storage-format/SKILL.md) — a
Parquet-based RDF store from the external `pycottas` project, which
factoidal reads and now also writes natively — has the same "query the
bytes, do not expand first" property. Neither format is ours; the
verified part is the reader (and, for COTTAS, the writer). The
[performance hub](../../perf/) measures how the four extraction targets
compare on these read paths.

Every live cell above is pinned in
[`tests/hub/post24_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post24_test.mjs) —
the exact same source, driven through a `fn.queryHdt` built on the same
`--data-hdt` argv contract against the native binary instead of the
in-browser js bundle.
