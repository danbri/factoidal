# Named-graph query scale: the reported `GRAPH ?g` crash on the full skosall store

Date: 2026-09-08. Branch `wt/named-graph-scale`.

## Summary

Two defects were reported against the full skosall generation (662 named
graphs, 219M quads, a 36,106-entry / 25.5 MB manifest), queried over HTTP
against the live R2 store through a committed wasm module labelled
`6201b6c4`:

1. `SELECT ?c WHERE { GRAPH ?g { ?c a skos:Concept } } LIMIT 1` was refused
   with `[object WebAssembly.Exception]` — an engine crash.
2. Default-graph queries (`{ ?s ?p ?o }`, `{ ?c a skos:Concept }`) returned
   zero rows.

This note records what each is, measured on the current branch tip against
the same real 25.5 MB manifest.

## Defect 2 is correct SPARQL, not a bug

The skosall generation was built by the `graphed` step, which puts every
triple into a named graph (one per scheme). Its default graph is empty.

SPARQL 1.1 §13 (RDF Dataset) and §18.6 (the `GRAPH` form): a basic graph
pattern that is NOT inside a `GRAPH` clause is evaluated against the ACTIVE
graph, which outside any `GRAPH` clause is the default graph. With no `FROM`
clause the default graph is the dataset's own default graph. A store whose
data is only in named graphs therefore answers `{ ?s ?p ?o }` and
`{ ?c a skos:Concept }` with zero rows. This is the specified answer, not a
reader fault.

The consequence is a PACKING choice, not an engine choice: a user who wants
to read across the graphs must use `GRAPH ?g { … }`, a `FROM`/`FROM NAMED`
dataset clause, or a union-default-graph packing. The `graphed` step is the
reason the default graph is empty; if reading the union without a `GRAPH`
clause is wanted, that is where to change it (a union-default-graph option in
the pack step), and it is a product decision rather than a correctness fix.

## Defect 1 — the crash does not reproduce on the current tip

The store-over-HTTP host answers a query in two engine calls: `storeQueryPlan`
(which artifacts to fetch — no block is read) and then `storeQuery` /
`storeOpen` over the fetched blocks. The crash was attributed to the
named-graph collector inside `storeQueryPlan`. Measured on the current tip
against the real manifest (`l4wasm-cli call storeQueryPlan`, hexadecimal of
the 25.5 MB manifest, default stack):

| query | result | shards | wall |
|---|---|---|---|
| `GRAPH ?g { ?c a skos:Concept } LIMIT 1` | `ok:true` | 1529 | 5.7 s |
| `GRAPH ?g { ?s ?p ?o } LIMIT 1` | `ok:true` | 36106 | 7.7 s |

The same two queries through the committed wasm module in Node (default
stack; and under `node --stack-size=500`, i.e. a browser-tab-sized V8 call
stack) both return `ok:true` with the same shard counts and no exception. The
36,106-key plan serialises to a 2.8 MB JSON envelope without crashing.

So `storeQueryPlan` does not fault on 662 graphs / 36,106 entries on this tip.
The reasons are already in the code, and the labels of the modules involved
say why an earlier module crashed:

- `L4Factoidal/SPARQL/StoreDataset.lean` carries a dedicated
  `evalPatternBackend` arm for `GRAPH (.var v)` that walks each named backend
  directly (`flatMap` over `dsb.named`). Its own comment records that WITHOUT
  this arm the shape fell through to the materialise-and-delegate case, which
  rebuilt the whole dataset as lists for every such query and overflowed the
  wasm stack on a 45,806-row block
  (<https://github.com/danbri/factoidal/issues/653>).
- `L4Factoidal/Storage/QuadDataset.lean`'s `datasetOfQuads` groups quads into
  named graphs through a `Std.HashMap` with `HashMap.modify` (not lookup-then-
  insert), which its comment ties to the measured named-graph scaling failure
  in the N-Quads accumulator (<https://github.com/danbri/factoidal/issues/650>).
- `StoreDataset.limitGraphVarAcc` is the LIMIT push-down for a single triple
  pattern under `GRAPH ?v`: it is a tail-recursive accumulator that stops at
  the limit and reads each graph with `backendSearchLimited (limit - acc)`, so
  a `LIMIT 1` does not materialise every scheme's concepts first. It carries a
  bound theorem `limitGraphVarAcc_bounded`.
- The plan collectors `queryGraphNames?`, `queryQuadConstantPredicates?` and
  the zone collectors in `L4Factoidal/Storage/ShardManifest.lean` end in a
  `List.filter` over `manifest.entries`; Lean compiles `List.filter` to a
  tail-recursive loop. For `GRAPH ?g` the graph collector returns `none` (a
  variable graph establishes no restriction), so no per-entry
  `graphSet × wanted` membership scan runs at all for the reported query.

The `6201b6c4` module predates one or more of the issue-650/653 fixes; the
crash was a wasm shadow-stack overflow in the materialise-and-delegate
fallback that the `GRAPH (.var v)` arm removed. On the current tip that arm is
present and the query plans and evaluates without a fallback.

## The one surface not exercised here

`storeQueryPlan` for the 1529-shard concept query selects 1529 artifacts,
which is over the stateless `storeQuery` cap of 64 (`maxStoreArtifacts`), so
the HTTP host answers it through the HANDLE path (`Wasm/Ops/StoreHandles.lean`,
<https://github.com/danbri/factoidal/issues/657>), whose bound is retained
BYTES rather than a per-call artifact count. Driving that path end to end
needs the block artifacts from R2, which this investigation did not fetch. The
dataset-assembly and evaluation functions it calls are the same
`datasetOfQuads` / `evalPatternBackend` shown above to scale; the handle
wrapper's own accumulation was not measured here and is the residual risk.

## Tests added with this note

- `formal/lean4/Wasm/Ops/NamedGraphQueryTests.lean` — a `#guard` battery over
  the real query ABI (`queryDataset`: N-Quads in, SPARQL, SPARQL-Results-JSON
  out), pinning the exact answers of the five named-graph scenarios on a
  hand-built store with a subject present in two graphs and an empty default
  graph. These pin CORRECTNESS. On the current tip they PASS; they did not
  drive a fix because the defect above does not reproduce on this tip.
- `tests/stack/` gains a synthesised 662-graph / 40,000-entry manifest case
  and a `GRAPH ?g` plan over it, run under the portable `node --stack-size`
  canary, asserting the engine does not crash. This pins SCALE.

## Notebook queries

The hub notebook's `GRAPH ?g` queries over skosall will return rows on this
tip. Each store-over-HTTP query re-decodes the 25.5 MB manifest (measured 5.7
s for the concept plan alone), so every query is slow until the
decode-once-behind-a-handle work of
<https://github.com/danbri/factoidal/issues/670> lands.
