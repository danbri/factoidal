# The packer publishes every batch

2026-09-05. The IBK4 quad packer held every row of every predicate until the
end of the source, so its peak memory grew with the source. It now publishes
blocks DURING the ingest pass. No artifact byte format changes; the BLOCK SET
does.

This implements section 5 of
[`2026-09-05-wire-version-10-scale.md`](2026-09-05-wire-version-10-scale.md)
(tracking issue <https://github.com/danbri/factoidal/issues/658>). It follows
[`2026-09-05-shard-pack-profile-and-memory.md`](2026-09-05-shard-pack-profile-and-memory.md),
which measured the slope that forced it, and
[`2026-09-04-blocks-per-predicate.md`](2026-09-04-blocks-per-predicate.md),
which decided the per-block cut rule this reuses.

## 1. Why

The packer's peak memory was LINEAR in the source: 3.76 bytes of peak
footprint per source byte, plus about 145 MB. YAGO 4.5 is 142 GB of Turtle,
so it needed about 534 GB. The machine has 16 GB.

The cost was not the parse. The N-Quads and Turtle grammars already stream in
65,536-byte chunks. The cost was the PUBLICATION POINT: every row of every
predicate was held in `PredicateQuadBlocks.Buckets` until the end of the
source, then cut into blocks, then encoded — so the rows, the blocks and
their encoded bytes were all live together at the end.

## 2. The policy

Deterministic in the input and two operator numbers.

**Amended 2026-09-05:** a bucket is keyed by the PAIR (predicate, graph),
not by the predicate alone, and rule 2 has no graph clause. See
[`2026-09-05-wire-version-10-scale.md`](2026-09-05-wire-version-10-scale.md)
section 5 and its subsection "The repair, measured 2026-09-05".

| Rule | What | Constant |
|---|---|---|
| 1 | quads accumulate into per-(predicate, graph) OPEN RUNS | — |
| 2 | a run the per-block cut rule closes is published at once, its rows released | `maxBlockRows` 16,384, `maxBlockWireBytes` 2,097,152 |
| 3 | at each batch of source, every run of at least `minBatchRows` rows is published; smaller runs carry over | `batchSourceBytes` 268,435,456 (`--batch-bytes`), `minBatchRows` 4,096 |
| 4 | when the carried rows pass the bound, every run is published | `maxCarriedRows` 1,048,576 |
| 5 | at end of source every run is published | — |

Rule 3 keeps a rare bucket from producing one tiny block per batch. Rule 4
bounds what rule 3 retains, for a source with hundreds of thousands of
buckets.

What rule 3 costs, measured on a 3,999,912-byte skosdex N-Quads prefix over
three graphs, 19,320 quads: at the default batch it runs in one batch and
writes 39 blocks; at `--batch-bytes 262144` it runs in 16 batches and writes
40. One extra block for fifteen extra batch ends, because `minBatchRows`
carries every run below 4,096 rows across the boundary.

`Buckets` held every row of every bucket. `Pub` holds, per bucket key, only
the open run — the rows of the block being built — with the cut state
`chunkGo` carries in its arguments. So the per-bucket memory is bounded by
the per-block targets, and the whole is bounded by `maxCarriedRows` plus one
batch of parser state.

The WebAssembly default is 67,108,864 source bytes per batch, half the native
default, because the module has a 32-bit address space and the queued
generation shares it with the packer's state. It is `packBegin`'s fourth
argument. `maxPackSourceBytes` (134,217,728) now binds TriG alone, which has
no chunk fold.

## 3. What changes for a reader

Two things, both of which every manifest since SBM2 admits — "a reader MUST
take the union of the entries for a predicate", specification section 6.1.1.

1. **More blocks.** A predicate whose rows straddle a batch boundary gets a
   block ending at that boundary. An interleaved N-Quads source (g1, g2, g1,
   …) also produces more blocks than the buffered route, which grouped a
   graph's rows before cutting: each block still holds ONE graph, and there
   may now be several blocks per (predicate, graph) below the size targets.
2. **A different block ORDER.** Blocks publish in completion order rather
   than predicate-major order, so the ordinals — and therefore the artifact
   names — differ.

Byte identity between the streamed and the buffered route holds only for a
source below one batch whose predicates never straddle a graph change in a
different place. Above that, rows are compared, as gate 2 below does.

## 4. What is proved

`L4Factoidal/Storage/PackStreamTheorems.lean`, stated PER BUCKET KEY — a
(predicate, graph) pair since 2026-09-05 — over an
event list — one read of the source: each quad the grammar completed, in
order, with a `flush` wherever a publication rule fired.

| Theorem | Statement |
|---|---|
| `pubRun_rows` | `rowsFor k published ++ heldFor k state = fedFor k quads`, for every key and every prefix of a pass |
| `pubRun_published_eq_fed` | after rule 5 (`flush 0`), `rowsFor k published = fedFor k quads` |
| `streamed_eq_buffered` | that equals `(chunkQuadRows ((addQuads {} quads).rows.getD k []).reverse).flatten`, the buffered route's rows for `k` |
| `mem_graphTriples_of_perm` | a permutation of the rows keeps every graph's triples |
| `bucket_one_graph` | every row of a bucket's block has the bucket's predicate and the bucket's graph (`PredicateQuadBlocksTheorems`) |

`#print axioms` on all five: `[propext, Classical.choice, Quot.sound]`.

`pubRun_published_eq_fed` rests on `PubOrdered` — every key holding an
open run is named by `orderRev`, which `pubFlush` walks — proved preserved by
`pubAddRun`, `pubAdd`, `pubFlush` and a whole pass. `streamed_eq_buffered`
adds `addQuad_rows` and `addQuads_rows` to the landed
`chunkQuadRows_flatten`.

Together: the streamed route publishes the same rows for the same bucket key
in the same order as the buffered route. The block boundaries and the block
order differ.

**What is NOT proved**, and is measured by gate 2 instead:

* the assembly of the per-key statements into ONE permutation over all
  keys, which needs `orderRev` to have no duplicate entry;
* that a `QuadBlock` built by `IndexedBlockWireV4.fromQuads` denotes its rows
  — `IndexedBlockWireV4Theorems` has no such theorem today, only
  `denotes_decode_encode?`, which is about the wire round trip;
* the connection from the N-Quads chunk fold to the event list.
  `NQuadsFold.streamConsume11_eq_batch` is stated for EVERY consumer and
  `PackStream.addQuadPub` has exactly its consumer signature, so the
  instantiation is available; it is not written.

### 4.1 The duplicate rows, and where the set is made

One behaviour changed that the theorems do not cover, and it is the one thing
this landing found in the reader. The buffered route built a
`Syntax.FastDataset`, whose `FastGraph.add` has SET semantics, so a quad
repeated in one graph was dropped before any block was written. The streamed
route has no whole-graph index — that is the whole point — and cannot see that
a row repeats one it wrote to an earlier block, so it writes both.

skosdex does repeat quads: in the 209,715,187-byte prefix, 603 distinct quads
repeat, for 1,067 repeated rows. The two packers report `quads=941802` and
`quads=942869` for that input.

`Storage/QuadDataset.lean`'s `datasetOfQuads` appended every row, so the extra
row became an extra triple in the graph and the evaluator answered a repeated
solution. That was already wrong against RDF 1.1 Concepts section 3 — an RDF
graph is a SET — and `RDF/Core.lean`'s `Graph.add` states it; the buffered
packer had been hiding it. The reader is where the set belongs, so
`datasetOfQuads` now builds each graph with a bucketed membership test, keyed
by `(subject, predicate, object joinKey)` and compared with `Triple.eqb`, in
first-occurrence row order. `Wasm/Ops/Store.lean` reads the same function, so
the WebAssembly store answers the same dataset.

A generation therefore holds a MULTISET of rows and denotes a SET of triples
per graph. Compaction may drop the repeats later; nothing depends on it.

## 5. The memory ladder

skosdex N-Quads prefixes cut at a line boundary, `/usr/bin/time -l`, native
`l4block-shard-pack IN OUT ibk4` at the 268,435,456-byte default. The "before"
column is the same ladder from
[`2026-09-05-shard-pack-profile-and-memory.md`](2026-09-05-shard-pack-profile-and-memory.md).

| source bytes | quads | blocks | batches | wall s | user s | instructions retired | max RSS bytes | peak footprint bytes | peak BEFORE |
|---|---|---|---|---|---|---|---|---|---|
| 52,428,626 | 260,286 | 1,018 | 1 | 16.40 | 15.85 | 188,482,637,589 | 225,312,768 | 222,955,392 | 390,318,656 |
| 104,857,577 | 477,360 | 1,135 | 1 | 39.05 | 37.95 | 459,232,093,082 | 330,530,816 | 328,272,128 | 599,870,336 |
| 209,715,187 | 942,869 | 1,252 | 1 | 67.13 | 65.54 | 753,736,669,227 | 333,807,616 | 331,581,824 | 933,809,856 |
| 1,543,478,120 | 7,316,318 | 3,306 | 6 | 526.05 | 514.97 | 4,719,520,405,344 | 472,907,776 | 472,746,624 | 5,951,730,560 |

Generation sizes: 65,436 KiB, 111,516 KiB, 167,488 KiB and 1,059,984 KiB. Each
was deleted after it was measured.

Read it as follows.

* **Peak memory is no longer linear in the source.** Over a 29.4x range of
  source it moves by 2.12x, from 222,955,392 to 472,746,624 bytes. Before, the
  same range moved it 15.25x. The full corpus needs 472,746,624 bytes rather
  than 5,951,730,560: 12.6 times less.
* **It is not FLAT either, and the residue is named.** The rise from
  331,581,824 (210 MB, one batch) to 472,746,624 (1,543 MB, six batches) is
  141,164,800 bytes. What grows with the source and is not released is the
  manifest: one `Entry` and one TSV line per block, 1,252 blocks against
  3,306. That is bounded by the BLOCK count, not the row count, so it grows
  with the source divided by the block size; the next step for it is a
  manifest written incrementally rather than at the end.
* **Time is linear.** 7.35x the source between the last two rungs took 7.84x
  the wall clock and 6.26x the instructions. The instruction ratio is below
  the byte ratio because the 210 MB rung pays a larger fixed share.
* The first three rungs all run in ONE batch — the default is 256 MiB — so
  rules 2 and 5 alone already hold the 210 MB rung at 331 MB. Rule 3 first
  fires on the full corpus.
* **The block set grows sublinearly with the source**, because most blocks
  are full at the size targets: 1,018 blocks for 52 MB and 3,306 for 1,543 MB,
  a 3.25x block count for a 29.4x source.

## 6. Gate 2 — the same input, the old packer against the new

This repeats gate 2 of
[`2026-09-04-blocks-per-predicate.md`](2026-09-04-blocks-per-predicate.md).
The 209,715,187-byte skosdex N-Quads prefix was packed by the packer at
`claude/main` and by this one, both generations were activated, and ten
queries were run against each with ONE binary.

**The pack.**

| | `claude/main` | this branch |
|---|---|---|
| wall clock | 104.18 s | 66.66 s |
| peak memory footprint | 932,269,632 bytes | 330,418,496 bytes |
| rows written | 941,802 | 942,869 |
| blocks | 1,252 | 1,252 |
| predicates | 100 | 100 |

**The block set.** The per-predicate block counts are IDENTICAL, predicate by
predicate, over all 100 predicates: 163 blocks for `skos:prefLabel`, 159 for
`rdf:type`, 153 for `skos:inScheme`, 147 for `skos:hasTopConcept`, 84 for
`skos:definition`, then a long tail. That is expected for this source and does
not generalise: skosdex N-Quads is grouped by graph, the graph-change rule
already cuts a predicate at every graph, and 209,715,187 bytes is below the
268,435,456-byte batch, so rule 3 never fires. What DOES differ is the block
ORDER, and therefore the ordinals and the artifact names: the buffered route
emits all of a predicate's blocks together, the streamed route emits each
block when its run closes.

The row difference is the 1,067 repeated quads of section 4.1.

**The queries.** Ten shapes: four `GRAPH <iri>` SELECTs, one `GRAPH ?g`
SELECT, two ASKs, a `GRAPH ?g` SELECT with `FILTER NOT EXISTS`, a two-triple
BGP join inside a `GRAPH <iri>`, and a subject-bound SELECT. The harness
prints `rows=N` and a TEN-ROW preview rather than every row, so every broad
query carries an `ORDER BY`, which makes the preview a canonical sample
independent of the block layout, and the subject-bound query answers fewer
than ten rows, where the preview IS every row. The shard-count header line,
which necessarily differs, was stripped.

Answers: 17,648 rows, 338, 4,994, 2,651, 8,905, `true`, `false`, 18, 17,629
and 0. **The two outputs are identical over 281 lines.** GATE 2 PASSES.

The FIRST run of this gate did NOT pass: query 2 answered 17,648 rows against
the old generation and 17,649 against the new. That was the duplicate row of
section 4.1, and it is what sent the set semantics to the reader. The result
above is with `datasetOfQuads` building a set.

Query 10 answers 0 rows against both generations. The subject it names is in
the source, in a named graph, and the query has no `GRAPH` clause, so it asks
the default graph, which this corpus does not fill. It is a valid comparison
and a weak one; it is reported as it ran rather than tuned afterwards.

One query shape was replaced during the run and the replacement is stated
here rather than hidden: a `GRAPH ?g` SELECT on `skos:narrower` with
`FILTER NOT EXISTS { ?s skos:prefLabel ?l }` was killed after four minutes on
the first store. It selects every block of both predicates and evaluates the
sub-pattern per solution, which is a planner cost unrelated to this change.
It was replaced by the same shape inside one small `GRAPH <iri>`, which
answers 18 rows.

### 6.1 Gate 2 re-run for the (predicate, graph) buckets, 2026-09-05

The same 209,715,187-byte prefix, packed at `ibk5` by the packer at
`claude/main` and by the bucket change, both activated, the ten shapes run
with ONE binary, header line stripped.

| | `claude/main` | (predicate, graph) buckets |
|---|---|---|
| quads | 942,869 | 942,869 |
| blocks | 1,252 | 1,252 |
| graphs | 153 | 153 |
| pack wall clock | 80.86 s | 89.28 s |
| pack peak footprint | 241,270,784 bytes | 408,158,208 bytes |
| activation | 58.80 s | 55.45 s |
| verified logical bytes | 97,578,312 | 97,578,312 |

The BLOCK SET is byte-identical, not merely equal in count: the multiset of
(predicate, rows, SHA-256, graph set) over the 1,252 manifest entries agrees
exactly, and so does the per-predicate block count over all 100 predicates.
Only the ORDER differs, and with it the ordinals and the artifact names —
`claude/main` emits a predicate's blocks together, the bucket change emits
each block when its run closes.

Answers: 17,648 rows, 0, 2,634, 1,392, 4,887, `true`, `false`, 0, 17,426 and
1. **The two outputs are identical over 186 lines. GATE 2 PASSES.**

The pack costs more memory: 408,158,208 bytes against 241,270,784. There are
more open runs, one per (predicate, graph) pair instead of one per predicate,
and this source has 153 graphs. The peak is still bounded by `maxCarriedRows`
and one batch, not by the source, so the ladder of section 5 keeps its shape;
the constant is larger. The wall clock rose from 80.86 s to 89.28 s on the
same machine, both runs measured here rather than quoted from section 6.

## 7. Where the code is

| Piece | File |
|---|---|
| the policy as pure functions | `L4Factoidal/Storage/PredicateQuadBlocks.lean` (`Run`, `Pub`, `freshRun`, `flushStep`, `pubFlush`, `pubAddRun`, `pubAdd`, the four constants, `runsOfBuckets`) |
| the fold accumulator and the pass | `L4Factoidal/Storage/PackStream.lean` (`QuadPub`, `addQuadPub`, `quadPubStep`, `QuadStream`, `quadStreamDrain`, `quadStreamFinish`, `QuadIngestState`, `quadIngestFeed`, `quadIngestFinish`) |
| the theorems | `L4Factoidal/Storage/PackStreamTheorems.lean` |
| the native host | `Harness/PredicateShardPack.lean` (`--batch-bytes`, `batches=` in the summary, artifacts written per feed) |
| the WebAssembly ops | `Wasm/Ops/Pack.lean` (`packBegin`'s fourth argument, `defaultPackBatchBytes`), `Wasm/Dispatch.lean` |
| the JavaScript host | `npm/factoidal/bin/pack.mjs`, `pack-host.mjs`, `factoidal.mjs` (`--batch-bytes`) |

## 8. What this does NOT do

* **The manifest is still written at the end**, and its entries are held in
  memory until then. That is the 141 MB residue of section 5.
* **TriG still buffers its whole source.** It has no chunk fold.
* **The W3C TriG suite was not run in this worktree.** A git worktree
  inherits no test submodule, so `tools/blockengine-ibk4-w3c-trig-smoke.sh`
  reports 0 pass, 0 fail (out of 0) here rather than its 241. Run it in the
  main checkout before this branch is trusted against TriG.
* **The wasm module is not rebuilt here.** The evidence for the wasm ops is
  `formal/lean4/Wasm/native-smoke.sh`, which runs them natively: 85 pass,
  0 fail (out of 85), including the `diff -r` byte comparison of the CLI and
  the ops on an N-Quads fixture. The committed module still runs the old
  packer until the next rebuild.
* **Nothing here touches the term codec, the dictionary, the block wire
  version or the manifest version.** Those are the other two thirds of wire
  version 10.
