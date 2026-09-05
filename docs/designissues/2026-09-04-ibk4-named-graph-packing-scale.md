# Why named graphs did not scale, and what changed

2026-09-04. Issue: <https://github.com/danbri/factoidal/issues/650>.

Owner, 2026-09-04, verbatim: "We need the graphs stuff to scale!!!"

Two independent defects made the IBK4 (quad) packer far more expensive than
the IBK3 (triple) packer. One was a quadratic term that only named graphs
paid. The other was a character list about twenty-four times the size of the
source. Both are repaired. Both repairs keep every committed byte the same.

A third cost remains, is NOT repaired, and needs an owner decision. It is
stated at the end.

## Measured before

`l4block-shard-pack INPUT OUT ibk4`, synthetic N-Quads, 20 predicates,
`/usr/bin/time -l` peak memory footprint on macOS 15.6.

| Input bytes | Graphs | Wall clock | Peak memory |
|---|---|---|---|
| 20,077,780 | 1 | 17.01 s | 948,813,824 |
| 25,837,780 | 50 | 22.28 s | 957,546,496 |
| 104,017,780 | 50 | 268.73 s | 2,075,672,576 |
| 104,017,780 | 1 | 84.53 s | 2,709,291,008 |

Reported in the issue from real corpora: 410,280,495 bytes over one graph
packed in 182 s with a peak of 15,984,296,064 bytes; 553,021,327 bytes over
194 named graphs ran 1 h 57 min and was killed by the operating system with
an empty output directory.

Read the 50-graph rows against the 1-graph rows: four times the input cost
five times the time in one graph and twelve times the time over fifty
graphs. That excess is the first defect.

## Defect 1 — a quadratic term in the named-graph accumulator

`L4Factoidal/Syntax/NQuadsFast.lean`, `addQuadFast`. The named-graph case was:

```lean
match ds.named[name]? with
| some g => { ds with named := ds.named.insert name (g.add t) }
```

`ds.named[name]?` hands out a second reference to the graph while `ds.named`
still holds the first. `FastGraph.add` then calls `Std.HashMap.insert` on
`g.buckets`, which cannot update in place under a shared reference and copies
the whole bucket map of that graph. The copy is proportional to the size of
the graph, so the whole pass cost O(quads x graph size).

The default-graph case never paid it: `{ ds with default := ds.default.add t }`
consumes the field, so the update was in place. That is exactly the shape of
the complaint — triples scaled and named graphs did not.

The repair uses `Std.HashMap.modify`, whose map argument is consumed:

```lean
if ds.named.contains name then
  { ds with named := ds.named.modify name (FastGraph.add t) }
else
  ...
```

`contains` returns a `Bool` and keeps no reference to the value.

The two proofs over `addQuadFast` in `Syntax/NQuadsFastTheorems.lean`
(`FastDataset.add_inv`, `addQuadFast_toDataset`) were restated through
`Std.HashMap.getElem?_modify` and `Std.HashMap.getD_modify`, which carry the
same `if k == k'` shape as the `insert` lemmas they replace. No proof was
weakened and no axiom was added.

Measured effect alone, 104,017,780 bytes over 50 graphs: 268.73 s -> 103.12 s,
generation byte-identical.

## Defect 2 — a whole-file character list

`quadArtifacts` took the whole source as a `String` and `parseNQuadsFast`
began with `s.toList`. A `List Char` cons cell is three machine words, so that
one list is about twenty-four bytes per source byte, and it is live at the
same time as the dataset built from it. That is the whole 15,984,296,064-byte
figure for a 410 MB source, not the dataset.

The repair is `PackStream.quadIngestInit` / `quadIngestFeed` /
`quadIngestFinish`, driven by `Harness/PredicateShardPack.lean`'s
`quadIngestFile` in 65,536-byte chunks. It is byte-identical BY THEOREM, not
by test alone: `Syntax/NQuadsFold.lean` proves `streamConsume11_eq_batch` —
for every consumer, the chunked fold and the whole-document fold reach the
same accumulator — and this instantiates it at `FastDataset`, the accumulator
`parseNQuadsFast` itself uses. The dataset a chunked run builds IS the dataset
the buffered run builds.

The streaming route also checks the second-pass source digest against the
pre-pass commitment, which the IBK3 path always did and the buffered IBK4
native route did not.

Only the N-Quads grammar streams. TriG has no chunk fold. Turtle has one
(`TurtleChunkFold`) but no agreement theorem against `parseTurtle` for the
IBK4 dataset shape, so it stays buffered until that theorem lands.

**Superseded 2026-09-05 for Turtle and N-Triples.** See the section below.

## Turtle streams too (2026-09-05)

What stopped Turtle was not the parser. `Syntax/TurtleChunkFold.lean` has
streamed Turtle since the IBK3 packer landed. The quad path did not call it
because the IBK4 route needs a `Dataset` and the fold hands back statements;
nobody had written the twenty lines that turn one into the other.

`PackStream.QuadIngestState.stream` is now a `QuadStream` with two
alternatives — the N-Quads `StreamStateC` and the Turtle chunk fold with the
packer's own `ingestStep` — and `quadStreamDataset` closes either one. A
Turtle source has no named graph, so its triples are the default graph in
source order. `quadStreams` is true for `turtle`, `ntriples` and `nquads`.

### What is proved and what is measured

The N-Quads route is byte-identical BY THEOREM, as above. The Turtle route
is HALF proved:

- PROVED. `Syntax.parseStatements_eq_fold` and `Syntax.parseTurtle_eq_fold`
  state that folding statements with `Syntax.prependReverse` and reversing
  once gives exactly the `Graph` `parseTurtle` returns.
  `PackStream.ingestStep_eq_prependReverse` ties the packer's step to that
  accumulator. This is the counterpart of instantiating
  `streamConsume11_eq_batch` at the accumulator the batch parser uses.
- NOT PROVED. That the chunk fold reaches the same accumulator whatever the
  chunking. It rests on `TurtleStatementScan` never offering a candidate
  that `readStatement` would read past — a lexical property of the scanner
  that no theorem states. The IBK3 packer has always rested on it too.

So Turtle byte identity is MEASURED, not proved. Do not describe it as
proved.

### Measured 2026-09-05

Byte identity, `diff -r` of the previous binary's generation against the new
one: 261 identical, 0 differed (out of 262 inputs; 1 rejected by both). The
inputs were the W3C RDF 1.1 Turtle suite files, 40 rdf-canon N-Quads files,
the heterogeneous Turtle fixture, the 4-named-graph TriG fixture, and a
104,179,872-byte Turtle source (six copies of the lifesci-kgx `gene.ttl`,
5,333,694 quads, 407 blocks).

Peak memory on that 104,179,872-byte Turtle source, `/usr/bin/time -l`
maximum resident set size, shared machine at load average 10 (before) and 21
(after):

| | Peak RSS | Bytes per source byte |
|---|---|---|
| buffered | 2,788,786,176 | 26.8 |
| streaming | 1,253,408,768 | 12.0 |

Ratio 0.45 after over before; 2.23 before over after. The generation was
byte-identical.

Throughput, RECORDED NOT FIXED, for whoever profiles the packer: user CPU
went from 139.88 s to 164.43 s on that input, about 17 per cent more work.
Wall clock went from 175.75 s to 401.47 s, but the load average doubled
between the two runs, so the wall figure is not a measurement of the change.

TriG still buffers. It has no chunk fold at all, so there is nothing to
stream it with; writing one is a separate piece of work.

## Measured after

| Input bytes | Graphs | Wall clock | Peak memory | Peak / input |
|---|---|---|---|---|
| 20,077,780 | 1 | 24.80 s | 228,245,504 | 11.4 |
| 25,837,780 | 50 | 29.77 s | 261,308,416 | 10.1 |
| 104,017,780 | 50 | 140.11 s | 1,127,907,328 | 10.8 |
| 316,816,934 | 194 | 750.67 s | 2,344,140,800 | 7.4 |

The last row is the shape that used to fail: 194 named graphs, 2,400,000
quads, about 60 per cent of the 553,021,327-byte corpus that was killed by
the operating system. It completes.

Byte identity, verified with `diff -r` against generations from the previous
binary, for the 1-graph and the 50-graph inputs: identical.

Peak memory per input byte falls from 37 (small) and 20 (large) to between
7.4 and 11.4, and the named-graph time penalty is gone. It is still LINEAR in the
input, which is the remaining cost below.

## The cost that remains, and the decision it needs

An IBK4 block holds one predicate across ALL graphs of the source. Every row
of a predicate must therefore be in memory when its block is encoded, and
every encoded block is in memory when the manifest commits. Peak memory is
proportional to the data, and no amount of streaming in the reader changes
that.

A memory footprint independent of the input needs SEVERAL blocks per
predicate — publish a batch, start a new block for the same predicate, and
let the manifest carry the union of the graph sets, which is what the IBK3
path already does under SBM2. That changes the emitted block set for any
source larger than one publication batch. Specification section 10: a byte
change is a new wire version, and encoder admission equals decoder admission.
It is therefore not a refactor and was not landed here. It needs an owner
decision on:

* a new manifest version alongside SBM7, or SBM7 widened to admit several
  IBK4 entries per predicate;
* what a planner does when `GRAPH <iri>` must now consider several blocks per
  predicate rather than one;
* the loss of dictionary sharing across a predicate's blocks, which makes the
  generation larger.

Until then the practical ceiling for an IBK4 pack is about ten times the
source size in memory. On a 16 GB host that is roughly 1.5 GB of N-Quads, up
from the 553 MB that failed.

## The WebAssembly module

`Wasm/Ops/Pack.lean` buffered the whole IBK4 source and capped it at
`maxPackSourceBytes` = 134,217,728 bytes. The N-Quads grammar now streams
there too, through the same `quadIngestFeed`, so no source is buffered and
that cap no longer applies to it. `maxPackSourceBytes` now bounds only IBK4
over TriG, Turtle and N-Triples. The ceiling for an IBK4 N-Quads pack in the
module is `maxPackQueuedBytes` (134,217,728 bytes of generation waiting for
`packNext`) plus the module's 32-bit address space.

`Wasm/native-smoke.sh` gains one check for this: it packs the same N-Quads
file through the CLI and through the pack ops and compares the two
generations with `diff -r`. A routing change that made only one surface
stream would pass every other check in that script. The suite is now 80 pass,
0 fail (out of 80).
