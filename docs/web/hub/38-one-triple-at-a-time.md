---
title: "One triple at a time"
description: "The Lean 4 engine's full dispatch surface, climbed step by step: parse, ask, select, join, update, construct, infer, canonicalize — ending with the F* engine computing the same answer from the same bytes."
layout: hub.njk
series: docs-hub
series_order: 38
vocab: none
status: published
tests: tests/hub/post38_test.mjs
---

[Post 36](../36-lean-in-the-browser/) put the [Lean 4
port](https://github.com/danbri/factoidal/issues/466) on this page as a
second engine and stopped at Basic Graph Pattern evaluation over
term objects — no parsers, no update, no inference. The port has moved
since. This page climbs the surface it now exports, one call at a
time, starting from a single triple of text.

Each step below asks the engine one question, one idea bigger than the
last, and shows the computed answer before the next question uses it.
The mechanism is one wrapper, `fn.l4Call(op, args)`: `op` is a method
name from
[`Wasm/Dispatch.lean`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/Wasm/Dispatch.lean),
`args` an array of string arguments, and the result is the same JSON
envelope the F\*-derived npm entry returns for the same op — so the
answers on this page come out of Lean source compiled Lean → C →
wasm32, running in your browser.

## One triple. What does the parser see?

A single line of [N-Triples](https://www.w3.org/TR/n-triples/). The
`parseToDatasetJson` op parses it, counts it, and echoes it back in
canonical N-Quads form. The `nquads` string in the envelope is the
dataset handle every later op takes.

```observable-js
EX = "http://example.org/"
```

```observable-js
oneTriple = fn.l4Call("parseToDatasetJson", [
  `<${EX}alice> <${EX}name> "Alice" .`, "ntriples", "",
])
```

The envelope reports `count: 1` — the parser saw exactly the one triple.

## Is anything there?

The smallest SPARQL query form: [ASK](https://www.w3.org/TR/sparql11-query/#ask)
returns a boolean and nothing else. This is the Lean SPARQL *parser* at
work — post 36 had none, so its queries arrived as pattern tables.
Here the query is a string.

```observable-js
anythingThere = {
  const r = await fn.l4Call("queryDataset", [oneTriple.nquads, `# True if the graph holds at least one triple.
ASK { ?s ?p ?o }`]);
  return r.boolean;
}
```

## What is its name?

SELECT with one variable. The answer comes back as a [SPARQL 1.1 Query
Results JSON](https://www.w3.org/TR/sparql11-results-json/) document in
the envelope's `srj` field; this helper flattens it to plain rows, and
every later query cell reuses it.

```observable-js
rows = (r) => r.srj.results.bindings.map(
  (b) => Object.fromEntries(Object.entries(b).map(([k, t]) => [k, t.value])))
```

```observable-js
theName = {
  const r = await fn.l4Call("queryDataset", [oneTriple.nquads,
    `# What name does Alice's subject have?
    SELECT ?name WHERE { ?s <${EX}name> ?name }`]);
  return rows(r);
}
```

## Two triples. Can it join?

Add an age. Two triple patterns sharing `?s` force the evaluator to
correlate them: an answer row must satisfy both patterns with the same
subject. One row comes back, carrying Alice's name and age together.

```observable-js
firstJoin = {
  const parsed = await fn.l4Call("parseToDatasetJson", [
    [
      `<${EX}alice> <${EX}name> "Alice" .`,
      `<${EX}alice> <${EX}age> "30"^^<http://www.w3.org/2001/XMLSchema#integer> .`,
    ].join("\n"), "ntriples", "",
  ]);
  const r = await fn.l4Call("queryDataset", [parsed.nquads,
    `# Join name and age for the same subject.
    SELECT ?n ?a WHERE { ?s <${EX}name> ?n . ?s <${EX}age> ?a }`]);
  return { nquads: parsed.nquads, rows: rows(r) };
}
```

## Does Turtle change the answer?

The same two triples, written as [Turtle](https://www.w3.org/TR/turtle/)
this time — prefixed names, a predicate list, and the bare `30` that
Turtle defines as an `xsd:integer` literal. Both comparisons are
computed live: the parse produces byte-identical canonical N-Quads, and
the query produces the identical rows.

```observable-js
turtleSame = {
  const parsed = await fn.l4Call("parseToDatasetJson", [`
    @prefix : <${EX}> .
    :alice :name "Alice" ; :age 30 .
  `, "turtle", ""]);
  const r = await fn.l4Call("queryDataset", [parsed.nquads,
    `# Same join as before, now over Turtle-parsed data.
    SELECT ?n ?a WHERE { ?s <${EX}name> ?n . ?s <${EX}age> ?a }`]);
  return {
    sameNQuads: parsed.nquads === firstJoin.nquads,
    sameRows: JSON.stringify(rows(r)) === JSON.stringify(firstJoin.rows),
  };
}
```

## Can the data change?

[SPARQL 1.1 Update](https://www.w3.org/TR/sparql11-update/), parsed and
applied by the Lean engine: `INSERT DATA` adds Bob. The op returns the
updated dataset, and `triples` counts its lines, so the growth from 2
to 4 is computed by the cell.

```observable-js
afterInsert = {
  const r = await fn.l4Call("updateDataset", [firstJoin.nquads, `
    # Add Bob as a new subject, with a name and an age.
    PREFIX : <${EX}>
    INSERT DATA { :bob :name "Bob" . :bob :age 24 . }
  `]);
  return { triples: r.nquads.trim().split("\n").length, nquads: r.nquads };
}
```

The join query from before now sees the new subject: two rows.

```observable-js
bothPeople = {
  const r = await fn.l4Call("queryDataset", [afterInsert.nquads,
    `# Join name and age again, now that Bob is in the dataset too.
    SELECT ?s ?n ?a WHERE { ?s <${EX}name> ?n . ?s <${EX}age> ?a }`]);
  return rows(r);
}
```

## Can it build new triples from old ones?

[CONSTRUCT](https://www.w3.org/TR/sparql11-query/#construct) turns each
answer row into a new triple — here, restating each `:name` as
`foaf:name`. The result is a graph, and `serializeTurtle` prints it as
prefix-compacted Turtle.

```observable-js
constructed = {
  const r = await fn.l4Call("queryDataset", [afterInsert.nquads, `
    # Restate each :name triple as a foaf:name triple.
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    CONSTRUCT { ?s foaf:name ?n } WHERE { ?s <${EX}name> ?n }
  `]);
  const t = await fn.l4Call("serializeTurtle", [r.nquads]);
  return t.turtle;
}
```

## What follows from what was said?

Two stated triples: `:Dog rdfs:subClassOf :Animal`, and `:rex a :Dog`.
Nobody typed `:rex a :Animal`, but the stated graph RDFS-entails it
([RDF 1.1 Semantics §9.2](https://www.w3.org/TR/rdf11-mt/#rdfs-entailment),
entailment pattern rdfs9), and the `owlClosure` op's `RDFS` mode
derives it. The cell asks the same ASK twice: over the stated graph,
then over its closure.

```observable-js
inferred = {
  const stated = await fn.l4Call("parseToDatasetJson", [`
    @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
    <${EX}Dog> rdfs:subClassOf <${EX}Animal> .
    <${EX}rex> a <${EX}Dog> .
  `, "turtle", ""]);
  const q = `# Is rex an Animal? Not stated directly -- entailed via rdfs:subClassOf.
  ASK { <${EX}rex> a <${EX}Animal> }`;
  const before = await fn.l4Call("queryDataset", [stated.nquads, q]);
  const closure = await fn.l4Call("owlClosure", [stated.nquads, "RDFS"]);
  const after = await fn.l4Call("queryDataset", [closure.nquads, q]);
  return { statedTriples: stated.count, before: before.boolean, after: after.boolean };
}
```

## And with heavier vocabulary?

The same op, `OWL-RL` mode: the [OWL 2 RL
rules](https://www.w3.org/TR/owl2-profiles/#OWL_2_RL). The data states
a name for `:clark` and `owl:sameAs` between `:clark` and `:superman`;
the closure propagates the name to `:superman`, and the query reads it
off a subject the input never gave a name to.

```observable-js
owlSame = {
  const stated = await fn.l4Call("parseToDatasetJson", [`
    @prefix owl: <http://www.w3.org/2002/07/owl#> .
    <${EX}clark> owl:sameAs <${EX}superman> .
    <${EX}clark> <${EX}name> "Clark" .
  `, "turtle", ""]);
  const closure = await fn.l4Call("owlClosure", [stated.nquads, "OWL-RL"]);
  const r = await fn.l4Call("queryDataset", [closure.nquads,
    `# Read the name off superman, propagated there via owl:sameAs.
    SELECT ?n WHERE { <${EX}superman> <${EX}name> ?n }`]);
  return rows(r);
}
```

## Are these two graphs the same graph?

Two graphs, each two triples over two blank nodes, with different
labels: `_:a`/`_:b` in one, `_:x`/`_:y` in the other. Blank node labels
carry no meaning ([RDF 1.1 Concepts
§3.4](https://www.w3.org/TR/rdf11-concepts/#section-blank-nodes)), so
comparing the two documents as strings reports a difference that is not
a difference between the graphs.
[RDFC-1.0](https://www.w3.org/TR/rdf-canon/) canonicalization assigns
each blank node a label computed from the graph's structure, so two
datasets receive the same canonical form exactly when they are
isomorphic. Both graphs here canonicalize to the same text.

```observable-js
sameGraph = {
  const a = await fn.l4Call("canonicalizeToNQuads", [
    `_:a <${EX}knows> _:b .\n_:b <${EX}knows> _:a .`]);
  const b = await fn.l4Call("canonicalizeToNQuads", [
    `_:x <${EX}knows> _:y .\n_:y <${EX}knows> _:x .`]);
  return { canonicalA: a.nquads, canonicalB: b.nquads, identical: a.nquads === b.nquads };
}
```

## And when one triple changes?

A third graph, same shape, one predicate changed from `:knows` to
`:likes`. The two graphs are not isomorphic, so their canonical texts
differ.

```observable-js
changedGraph = {
  const c = await fn.l4Call("canonicalizeToNQuads", [
    `_:x <${EX}knows> _:y .\n_:y <${EX}likes> _:x .`]);
  return { canonicalC: c.nquads, identicalToA: c.nquads === sameGraph.canonicalA };
}
```

## Does the F\* engine agree?

The final question goes to the *other* engine — the F\* specification
extracted to OCaml and compiled to JavaScript, the one every other page
in this series runs. It receives the exact `afterInsert.nquads` bytes
the Lean engine produced above, and the same join query.

```observable-js
fstarRows = {
  const dataset = await fn.parse(afterInsert.nquads, { format: "nquads" });
  const res = await fn.query(dataset,
    `# The same join, computed by the F* engine over the Lean engine's bytes.
    SELECT ?s ?n ?a WHERE { ?s <${EX}name> ?n . ?s <${EX}age> ?a }`);
  return res.map((m) => Object.fromEntries([...m].map(([k, t]) => [k, t.value])));
}
```

A BGP's answer is a set, so the comparison sorts the rows on both sides
before comparing.

```observable-js
agreement = {
  const norm = (rs) => rs.map((r) => `${r.s}|${r.n}|${r.a}`).sort();
  const lean = norm(bothPeople);
  const fstar = norm(fstarRows);
  return {
    leanRows: lean.length,
    fstarRows: fstar.length,
    identical: JSON.stringify(lean) === JSON.stringify(fstar),
  };
}
```

## A typed surface over the same dispatch

Every call above went through `fn.l4Call(op, args)` — the raw dispatch,
walked deliberately one op at a time so this page shows the ABI itself.
A typed layer sits over the same dispatch: `fn.l4Parse`/`fn.l4Query`,
the wrappers [post 36](../36-lean-in-the-browser/) uses, backed by the
same dataset-handle ABI (`Wasm/Ops/Handles.lean`,
[issue #585](https://github.com/danbri/factoidal/issues/585)) instead
of the stateless `parseToDatasetJson`/`queryDataset` ops. It reproduces
`bothPeople`'s join from the exact same bytes.

```observable-js
typedJoin = {
  const ds = await fn.l4Parse(afterInsert.nquads, { format: "nquads" });
  const rows = await fn.l4Query(ds,
    `# Same join again, through the typed l4Parse/l4Query wrappers.
    SELECT ?s ?n ?a WHERE { ?s <${EX}name> ?n . ?s <${EX}age> ?a }`);
  return rows.map((m) => Object.fromEntries([...m].map(([k, t]) => [k, t.value])));
}
```

## What the agreement means

Every answer above the last cell was computed by one engine; the last
cell shows a second engine, written in a different proof assistant from
different source, producing the identical answer over the identical
bytes. The two formalizations of the W3C specifications are
independent: the F\* tree is the shipping engine, and the Lean tree
([issue 466](https://github.com/danbri/factoidal/issues/466)) was
written from the specification text, with its own kernel-checked
theorems in place of F\*'s SMT-backed lemmas. For the operations this
page exercises, a defect that keeps the two answers equal needs the
same misreading of the specification made twice, independently.

The Lean side's standing against the real W3C files is recorded in
[`formal/lean4/PORT_NOTES.md`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/PORT_NOTES.md):
`lake exe l4w3c` over the four RDF 1.1 syntax manifests plus rdf-canon
reports TOTAL: 912 pass, 0 fail (out of 912), and `l4rdfc-probe` over
the RDFC-1.0 corpus reports 86 pass, 0 fail (out of 86) — the same
score the F\* tree reports on the same corpus. The dispatch surface
this page climbed is the same code those runners exercise, compiled to
one wasm module.
