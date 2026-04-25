# Second On-Disk Backend Options: Oxigraph vs QLever

**Date:** 2026-04-25
**Context:** `factoidal --data-cottas` currently spends most of its time in
artifact loading, not SPARQL evaluation, on the UK Parliament corpus.

## Why this note exists

The current COTTAS/Parquet path is useful as a first verified native path, but
it is not a good fit for the way the runtime currently consumes it.

The current load path:

- opens a `data.cottas` file,
- reconstructs all rows eagerly,
- converts every row back into RDF terms,
- then reshapes all quads into the in-memory dataset used by the current
  SPARQL engine.

On the UK Parliament corpus, profiling showed that this time is spent in
`load_cottas_dataset` / `load_cache`, not in algebra evaluation:

- [formal/fstar/experimental_ocaml_glue/cottas_runtime.sh](/Users/danbri/working/factoidal/formal/fstar/experimental_ocaml_glue/cottas_runtime.sh:248)
- [formal/fstar/Parquet.Footer.fst](/Users/danbri/working/factoidal/formal/fstar/Parquet.Footer.fst:1449)
- [formal/fstar/ocaml-output/factoidal_cli.ml](/Users/danbri/working/factoidal/formal/fstar/ocaml-output/factoidal_cli.ml:195)

This is a backend shape problem, not only a micro-optimization problem.

## Current diagnosis

The present COTTAS runtime uses Parquet as if it were a random-access string
store. That loses most of the benefit of Parquet:

- columnar layout is not exploited as a columnar scan,
- values are fetched per cell instead of per page / per column,
- all quads are materialized before query evaluation,
- the current CLI then flattens the loaded quads into the existing
  list-of-triples dataset representation.

That makes even selective queries pay a bulk-load cost up front.

## What Oxigraph suggests

Official Oxigraph architecture documentation says that the on-disk store is
based on RocksDB, with:

- one `id2str` table,
- three permutations for default-graph triples: `spo`, `pos`, `osp`,
- six permutations for named-graph quads: `spog`, `posg`, `ospg`, `gspo`,
  `gpos`, `gosp`,
- big-endian encoded keys for efficient range scans.

Sources:

- Oxigraph architecture wiki:
  `https://github.com/oxigraph/oxigraph/wiki/Architecture`
- Oxigraph repository README:
  `https://github.com/oxigraph/oxigraph`

What is attractive for Factoidal:

- immutable sorted key ranges are easy to scan,
- dictionary-encoded terms + permutation indices match RDF/SPARQL access
  patterns,
- the separation between dictionary and index keys is verification-friendly,
- prefix/range scans over sorted keys are a natural fit for bound triple
  patterns.

What is unattractive for Factoidal:

- RocksDB is an LSM KV engine with nontrivial runtime semantics,
- binary compatibility with RocksDB SST internals is not a sensible verified
  target,
- mixed read/write transaction semantics are much more machinery than we need
  for the current read-mostly query engine,
- proving correctness over RocksDB-specific compaction / snapshots would push
  us away from the core SPARQL problem.

Conclusion on Oxigraph:

- **Good logical model**
- **Bad binary/runtime target**

We should copy the logical ideas, not target RocksDB compatibility.

## What QLever suggests

QLever’s documented index design is closer to the kind of backend that a
verified query engine can exploit directly:

- immutable RDF index built offline,
- sorted permutations over dictionary IDs,
- optimized scans for triple patterns with one or two variables,
- query execution over sorted postings / relations rather than reconstructing
  full RDF terms eagerly.

Public QLever material states:

- the engine is built around offline index construction and fast query-time
  access,
- the classic design uses permutations of `S`, `P`, and `O`,
- in practice, QLever often relies on two primary permutations (`PSO`, `POS`),
  while the full six permutations can also be built.

Sources:

- QLever docs: `https://docs.qlever.dev/`
- QLever repository: `https://github.com/ad-freiburg/qlever`
- CIKM paper snippet surfaced via publication search:
  `https://ad-publications.cs.uni-freiburg.de/CIKM_qlever_BB_2017.pdf`

What is attractive for Factoidal:

- immutable offline-built index is exactly the right operating mode,
- sorted integer IDs + merge joins are verification-friendly,
- the backend can answer many triple-pattern scans without decoding lexical RDF
  terms until projection/output,
- there is no need to model a mutable KV engine.

What is unattractive for Factoidal:

- QLever has a lot of engine-specific machinery beyond the core index,
- binary compatibility with QLever index files would likely be brittle,
- the full QLever feature set includes text, autocompletion, and optimizer
  machinery that we do not need for a first verified backend.

Conclusion on QLever:

- **Good logical model**
- **Much closer to the right backend shape for Factoidal than RocksDB**

## Recommendation

If we build a second verified on-disk backend, it should be **QLever-like in
shape, Oxigraph-like in permutation coverage, and Factoidal-native in file
format**.

That means:

1. **Do not target binary compatibility** with either Oxigraph or QLever.
2. **Do target a common logical representation**:
   - dictionary-encoded terms,
   - immutable sorted permutations,
   - range-scan-friendly byte encoding,
   - late decoding of lexical strings.
3. **Keep the current SPARQL evaluator**, but add a second dataset backend that
   answers quad-pattern scans from sorted on-disk relations instead of first
   rebuilding a full in-memory RDF dataset.

## Proposed common logical representation

The common representation should be simple enough to verify and simple enough
to generate from Python/Rust tooling:

- `terms.dict`
  - `term_id -> encoded RDF term`
- `graphs.dict`
  - `graph_id -> graph IRI`
- `spo.idx`
- `pos.idx`
- `osp.idx`
- optionally named-graph variants:
  - `spog.idx`
  - `posg.idx`
  - `ospg.idx`
  - `gspo.idx`
  - `gpos.idx`
  - `gosp.idx`

Each index file should be:

- immutable,
- sorted lexicographically on packed integer IDs,
- block-addressable,
- independent of any external database runtime.

This gets the good parts of both designs:

- Oxigraph’s permutation coverage,
- QLever’s offline immutable scan model.

## Why this is better than iterating Parquet strings

With a dictionary + permutation backend, a query like:

```sparql
SELECT * WHERE {
  ?Procedure a :Procedure ;
             :name ?ProcedureName .
  FILTER (?Procedure IN (id:iCdMN1MW))
}
```

can be executed roughly as:

1. dictionary-encode `rdf:type`, `:Procedure`, `:name`, and `id:iCdMN1MW`
2. range-scan the relevant permutation(s)
3. join on integer IDs
4. decode only the projected output IDs

That avoids:

- parsing millions of lexical RDF terms up front,
- reconstructing all quads eagerly,
- decoding strings for rows that will never survive the joins.

## Why not just make Parquet faster?

We still should improve the current COTTAS loader, because it is already wired
up and useful.

But even with better caching, Parquet remains a less natural backend for the
current engine than sorted ID permutations:

- Parquet is great for analytic column scans,
- SPARQL basic graph patterns want selective relation access and joins,
- our current engine already thinks in terms of triples/quads and bindings,
  not vectorized column batches.

So:

- **Short term:** fix COTTAS load-path waste.
- **Medium term:** add a second immutable permutation backend.

## Suggested implementation plan

### Phase 1: make the current diagnosis visible

- Add timing breakdown around:
  - `cottas_open_dataset_store`
  - `load_cache`
  - CLI reshaping in `load_cottas_dataset`
  - actual query evaluation

### Phase 2: define a Factoidal-native immutable backend format

- dictionary file format
- permutation file format
- exact byte ordering and block framing
- default-graph and named-graph handling

### Phase 3: write an external index builder

Prefer Python or Rust for the builder, not F*:

- read N-Quads / TriG,
- assign stable term IDs,
- emit sorted permutation files.

This keeps the file production path pragmatic while reserving the verified work
for the reader/scanner/query path.

### Phase 4: verified reader + scan API

In F*:

- open dictionary and index files,
- seek to scan ranges by bound prefixes,
- return row streams of integer IDs,
- decode terms only when necessary.

### Phase 5: backend bridge into the existing evaluator

Add a dataset backend interface that can satisfy quad-pattern access without
first materializing a full `rdf_dataset` as lists.

## Concrete recommendation

For the next serious on-disk backend:

- **Choose QLever-like immutable sorted permutations as the target shape.**
- **Borrow Oxigraph’s default/named-graph permutation split where useful.**
- **Do not try to verify RocksDB or adopt QLever’s binary index format.**
- **Use a Factoidal-native file format with simple sorted integer tuples.**

That gives the clearest path to a backend that is:

- fast enough to matter,
- simple enough to verify,
- close enough to existing high-performance RDF engines to be credible.

## Open questions

- Do we want 3 permutations first, or 6/9 from day one?
- Should named graphs be first-class in the index or layered separately?
- Is late lexical decoding sufficient for current SPARQL result formatting?
- Do we want the first builder to emit only immutable snapshots, or also
  support append/merge later?

## Bottom line

If the goal is a bearably fast verified on-disk backend for the current SPARQL
engine, the strongest next move is **not** “more clever Parquet probing”.

It is:

- keep COTTAS as an import/interchange format,
- add a second Factoidal-native immutable permutation backend,
- make that backend logically comparable to Oxigraph/QLever,
- and wire the current evaluator to scan it directly.
