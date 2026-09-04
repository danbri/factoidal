# Several IBK4 blocks per predicate

2026-09-04. Issue: <https://github.com/danbri/factoidal/issues/650>.

Owner, 2026-09-04, verbatim: "scale the DB to handle all of skosdex, fast
query/search with fulltext and geo and query extension properties."

This document decides the first half: make a store of the whole corpus
possible and queryable. It follows
[`2026-09-04-ibk4-named-graph-packing-scale.md`](2026-09-04-ibk4-named-graph-packing-scale.md),
which repaired the packer and left this piece open.

## The defect

An IBK4 block holds ONE PREDICATE across EVERY graph of the source. On a
60 MB subset of skosdex the `skos:prefLabel` block is already 5,571,302 bytes
and 45,806 rows — 66 per cent of the 8,388,608-byte read cap and 46 per cent
of the 100,000-row read cap of `Wasm/Ops/Store.lean`. The whole corpus is
about twenty times that subset, so its `prefLabel` block would be far over
both caps and `storeQuery` would refuse it.

The refusal is correct. The block is the wrong shape.

## The wire decision: NO new manifest version

SBM7 already admits several entries for one predicate.
`ShardManifest.valid` applies `uniquePredicates` only when
`manifest.version < 2`; SBM2 introduced several bounded blocks per predicate
for the IBK3 path and every later version inherited it. The SBM7 decoder
therefore already accepts the manifests this change writes, and no manifest
byte, field, or framing rule changes.

Specification section 10 says a byte change is a new wire version and that
encoder admission must equal decoder admission. Neither is violated: the
encoded manifest form is identical, and the decoder's admitted set already
contains the new encoder's output. What changes is the emitted BLOCK SET for
a source large enough to split, which the specification does not fix.

Every read path was already written over a LIST of entries rather than one:

| path | how it selects |
|---|---|
| `ShardManifest.selectAll` | `filter`, not `find?` |
| `ShardManifest.scanBound` / `estimateBound` | `filter` then `flatMap` / `foldl` |
| `ShardManifest.quadEntriesForQuery` | `filter` over `manifest.entries` |
| `Harness/QuadQuery.readEntries` | folds over the selected entry list |
| `Harness/ShardActivate.verifyQuadEntries` | per entry |
| `Wasm/Ops/Store.storeQuery` | per entry, with the three caps over the set |

`ShardManifest.select?` uses `find?` and returns the FIRST entry for a
predicate. It is used only by `Harness/ShardMerklePread.lean` and
`Harness/ShardMerkleScan.lean`, which are IBK2 range-read demonstrations over
SBM0/SBM1 generations. They are untouched and stay correct for the
generations they read.

## The split policy

A block is closed when any of three conditions holds.

1. **The graph changes.** Always. A block holds rows of one predicate in ONE
   graph.
2. **16,384 rows.**
3. **2,097,152 bytes of estimated wire size.**

### Why the graph boundary

`quadsOfDataset` flattens a dataset graph-major: the default graph first,
then each named graph in order. Restricting that list to one predicate
therefore already yields the graph runs in order, so splitting a predicate's
rows at graph changes is a partition of the EXISTING row order into
consecutive runs. Nothing is reordered, and the concatenation of the new
blocks' rows equals the old single block's rows exactly. That is
`PredicateQuadBlocksTheorems.chunkQuadRows_flatten`.

The consequence for `GRAPH ?g` and `GRAPH <iri>`:

* Every entry's `graphSet` now has exactly ONE member. The graph filter in
  `quadEntriesForQuery` — which was conservative, keeping any entry whose
  graph set INTERSECTED the wanted set — becomes exact. A
  `GRAPH <iri> { ?s ?p ?o }` over a constant predicate reads exactly the
  blocks of that one graph and that one predicate. On the full corpus that
  is the difference between reading 1.1 GB and reading a few hundred
  kilobytes.
* `GRAPH ?g` is unchanged: `graphsReadFrom` returns `none` for a variable
  graph, every entry survives, and the whole generation is read. Splitting
  neither helps nor hurts it. Making it selective needs a graph-name index,
  which is not this piece of work.
* The manifest grows: a graph-set summary that listed 142 graph IRIs on one
  entry is now 142 entries with one IRI each. The total summary text is the
  same; the entry overhead (key, digest, chunk commitment) is what is added.

### Why those two numbers

The read caps in `Wasm/Ops/Store.lean` are TOTALS over the entries one
`storeQuery` selects, not per-block limits: 64 artifacts, 8,388,608 bytes,
100,000 rows. A per-block target must therefore leave room for SEVERAL
blocks in one query, not just one.

* 2,097,152 bytes is 8,388,608 / 4 — four blocks of the target size can be
  co-selected by one query and stay inside the byte cap.
* 16,384 rows is 100,000 / 6 rounded down to a power of two — six such blocks
  stay inside the row cap.

The byte figure is checked against a conservative UPPER BOUND of the encoded
block, computed while the rows are grouped and without encoding anything:
20 bytes for the row, 4 bytes for a graph-summary entry, and the exact
`DeltaLog.serializeTerm` length of the subject, predicate, object and graph
term. The bound ignores dictionary de-duplication, which only removes bytes,
so a chunk that passes it encodes to under 2,097,152 bytes plus the 21-byte
frame. One quad whose own bound exceeds the budget still forms a block of its
own; nothing is ever dropped or truncated (anti-pattern 25).

## The price: dictionary duplication

Each block carries its own PTD1 dictionary, so a term used by two blocks is
stored twice. Two separate cases:

* **Across the graph boundary.** Nearly free for this corpus. Two
  vocabularies share almost no term: their concept IRIs and their labels are
  disjoint. What repeats is the graph name, the predicate IRI and the handful
  of shared datatype and class IRIs — a few dozen terms per block.
* **Across a row-count or byte split inside one graph.** A term used by rows
  on both sides of the cut is stored twice. Subjects mostly appear once per
  predicate, so this is bounded by the terms straddling a cut.

Measured on the corpus below, the generation grew from 268,435,456 bytes to
the figure recorded in the results section. That number is the price and is
reported to the owner rather than argued away.

## Old generations

Nothing in the decoder changes, so every committed generation reads exactly
as before. `factoidal-skoscross` and `factoidal-skosgraphs` are checked by
comparing ROWS, not counts (anti-pattern 34). This is additive: the packer
emits a different block set for a large source, the reader admits both.

## What this does NOT do

Peak packer memory is still proportional to the source. The blocks are
partitioned at construction and published at the end of the pass, so the
whole dataset and the whole encoded generation are still live at once. The
next step is to publish a graph's blocks when the graph closes, which bounds
peak memory by the LARGEST GRAPH instead of the corpus. That needs the
streaming ingest to carry a publication state beside its `FastDataset`
accumulator, and the `NQuadsFold.streamConsume11_eq_batch` instantiation to
be restated over the new accumulator. It is deliberately separate from this
change so that the block-set decision lands on its own.

A per-block literal token index is a separate sidecar being added in
[`2026-09-04-literal-token-index.md`](2026-09-04-literal-token-index.md). The
two compose because the manifest ENTRY stays the unit: one entry per block,
each with its own sidecars. This change alters how many entries there are and
alters no entry field and no sidecar name.
