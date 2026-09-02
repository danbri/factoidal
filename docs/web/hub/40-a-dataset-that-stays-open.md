---
title: "A dataset that stays open"
description: "The Lean 4 engine's dataset-handle graph API, worked as one session: parse a multi-graph corpus once, query it, mutate it in place, close it, and check its consistency — all against the same handle."
layout: hub.njk
series: docs-hub
series_order: 40
vocab: none
status: published
tests: tests/hub/post40_test.mjs
---

[Post 38](../38-one-triple-at-a-time/) closed on `fn.l4Parse`/`fn.l4Query`:
typed wrappers over the [dataset-handle
ABI](https://github.com/danbri/factoidal/issues/585) (`Wasm/Ops/Handles.lean`)
instead of the stateless ops that ship the whole dataset as text on
every call. That page reproduced one join. This page is the session the
handle was built for: parse once, hold several named graphs open in the
engine, query across them, change one of them, close a proof over the
result, and check consistency — one dataset, open for the length of the
page.

## One corpus, three departments, one handle

[TriG](https://www.w3.org/TR/trig/) can state several named graphs in
one document. Below: a schema fact and one class assertion in the
default graph, then three named graphs — `:eng`, `:sales`, `:ops` — each
holding one department's people. `fn.l4Parse` reads the whole document
once and returns a dataset handle, not a JSON tree; every triple the
parser saw is now held inside the wasm module's own store.

```observable-js
EX = "http://example.org/org#"
```

```observable-js
corpus = `
    @prefix : <${EX}> .
    @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
    @prefix owl: <http://www.w3.org/2002/07/owl#> .

    :Manager rdfs:subClassOf :Employee .
    :Manager owl:disjointWith :Contractor .
    :alice a :Manager .

    GRAPH :eng {
      :alice :dept "Engineering" .
      :bob a :Manager ; :dept "Engineering" .
    }
    GRAPH :sales {
      :carol a :Manager ; :dept "Sales" .
    }
    GRAPH :ops {
      :dave a :Manager ; :dept "Ops" .
    }
`
```

```observable-js
orgDataset = fn.l4Parse(corpus, { format: "trig" })
```

`orgDataset.size` reads 10 immediately after this cell runs: two
default-graph facts, one default-graph class assertion, and seven
triples across the three named graphs. This cell holds a live
reference to the handle, and every later cell on this page reuses that
same reference — including the ones that change what the handle holds.
Redrawing this cell's own box later (the Table toggle does that) shows
the handle's CURRENT count, not a count frozen at 10.

## Querying across the open graphs

A [`GRAPH` pattern](https://www.w3.org/TR/sparql11-query/#queryDataset)
with an unbound graph variable quantifies over every named graph the
handle holds, joining `?person`'s name to `?dept` inside whichever graph
it came from.

```observable-js
rowsOf = (maps) => maps.map((m) => Object.fromEntries([...m].map(([k, t]) => [k, t.value])))
```

```observable-js
crossGraphQuery = `
# Every person's department, in whichever named graph holds them.
PREFIX : <${EX}>
# ?g is unbound, so GRAPH quantifies over every named graph the
# handle holds, not one graph in particular.
SELECT ?g ?person ?dept WHERE { GRAPH ?g { ?person :dept ?dept } }`
```

```observable-js
byDept = {
  const maps = await fn.l4Query(orgDataset, crossGraphQuery);
  return rowsOf(maps);
}
```

Four rows: Alice and Bob from `:eng`, Carol from `:sales`, Dave from
`:ops` — one query, reading three named graphs through one handle.

## Changing one graph, in place

[`INSERT DATA`](https://www.w3.org/TR/sparql11-update/#insertData) adds
a fourth engineer, Erin, to the `:eng` graph. `fn.l4Update` applies the
update to the SAME handle: `orgDataset` is not replaced, it is mutated.

```observable-js
afterInsert = {
  await fn.l4Update(orgDataset, `
    # Add a fourth engineer, Erin, to the :eng graph.
    PREFIX : <${EX}>
    INSERT DATA { GRAPH :eng { :erin a :Manager ; :dept "Engineering" . } }`);
  return { rowsBefore: byDept.length, size: orgDataset.size };
}
```

```observable-js
byDeptAfter = {
  const maps = await fn.l4Query(orgDataset, crossGraphQuery);
  return { size: afterInsert.size, rows: rowsOf(maps) };
}
```

Five rows now, and `orgDataset.size` reads 12. The cell above sent one
SPARQL Update string and got back a count; the cell after it sent the
same SELECT text as before and read Erin off the same handle. The
dataset stayed parsed in the engine between these two cells — nothing
was re-parsed. Contrast that with the stateless ops post 38 climbed
(`parseToDatasetJson`/`queryDataset`), where every call sends the whole
dataset as text again.

## A closure over the handle's own data

[`rdfsPlusClosure`](https://www.w3.org/TR/rdf11-mt/) needs the
dataset as N-Quads text, not a handle, so the next cell serialises the
handle once with `fn.l4Call`'s `datasetSerialize` op — the same bytes
`orgDataset.toNQuads()` would give — then closes it and asks the same
question before and after.

```observable-js
closureCheck = {
  const ser = await fn.l4Call("datasetSerialize", [orgDataset.handle, "nquads"]);
  const ask = `
# Does Alice have rdf:type Employee -- asked once before the RDFS
# closure runs, once after.
PREFIX : <${EX}> ASK { :alice a :Employee }`;
  const before = await fn.l4Call("queryDataset", [ser.nquads, ask]);
  const closed = await fn.l4Call("rdfsPlusClosure", [ser.nquads]);
  const after = await fn.l4Call("queryDataset", [closed.ntriples, ask]);
  return { triplesInHandle: byDeptAfter.size, before: before.boolean, after: after.boolean, rounds: closed.rounds };
}
```

`before` is `false`: the corpus states `:alice a :Manager`, never
`:alice a :Employee`. `after` is `true`: the closure applies
`:Manager rdfs:subClassOf :Employee` and derives it in one round.

## Is the corpus consistent?

[`owlIsConsistent`](https://www.w3.org/TR/owl2-profiles/#OWL_2_RL) runs
the OWL-RL closure and a clash-detecting tableau over the same
default-graph data, and answers one of three values: consistent,
inconsistent, or indeterminate (a budget ran out before every branch
closed). The corpus states `:Manager owl:disjointWith :Contractor`
and `:alice a :Manager` — nothing contradictory yet.

```observable-js
consistentBefore = {
  const ser = await fn.l4Call("datasetSerialize", [orgDataset.handle, "nquads"]);
  const verdict = await fn.l4Call("owlIsConsistent", [ser.nquads, ""]);
  return { entailedEmployee: closureCheck.after, consistent: verdict.consistent };
}
```

Now the contradiction: another `INSERT DATA`, this time into the
default graph, states `:alice a :Contractor` — the same individual in
two classes the corpus already declared disjoint.

```observable-js
consistentAfter = {
  await fn.l4Update(orgDataset, `
    # State the contradiction: :alice is now both a :Manager and a
    # :Contractor, classes the corpus already declared disjoint.
    PREFIX : <${EX}>
    INSERT DATA { :alice a :Contractor . }`);
  const ser = await fn.l4Call("datasetSerialize", [orgDataset.handle, "nquads"]);
  const verdict = await fn.l4Call("owlIsConsistent", [ser.nquads, ""]);
  return { wasConsistent: consistentBefore.consistent, consistent: verdict.consistent, reason: verdict.reason };
}
```

The verdict flips from `true` to `false`, with a reason: the tableau
derived a contradiction on every branch of the OWL-RL closure. Nothing
about the query or the closure op changed between the two checks — only
the data the handle holds did.

## Closing state

One `.toTurtle()` call reads the handle's current content: the three
departments, Erin's insert, and the class clash all in one document.

```observable-js
finalTurtle = {
  // consistentAfter's INSERT is the last write to the handle; reference
  // it so this cell reads the handle only after that write lands.
  void consistentAfter;
  return orgDataset.toTurtle();
}
```

`:alice` now carries both `a ns1:Contractor` and `a ns1:Manager` in the
printed Turtle — the same clash `owlIsConsistent` reported, visible
directly in the serialised graph.

Nothing above sent the corpus text more than once. Every query, every
update, and every closure after the first cell addressed the same
handle, the [dataset-handle ABI](https://github.com/danbri/factoidal/issues/585)
this page exercises end to end. Holding a parsed dataset in the engine
for the length of a page, mutating it, and reading it back is a smaller
version of what a longer-lived store needs to do across many requests —
the direction [issue 595](https://github.com/danbri/factoidal/issues/595)
tracks for persistence beyond one page's lifetime.
