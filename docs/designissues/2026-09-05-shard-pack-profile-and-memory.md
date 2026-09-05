# The shard packer: where its time goes, and how its memory grows

2026-09-05. Method, measurements and conclusions from profiling
`l4block-shard-pack` on the IBK4 N-Quads path, taken to decide whether
YAGO 4.5 (132 million facts, 142 GB of Turtle) can be imported.

The two repairs this profile produced are commits `c5ae37b82` (the
source-identity digest walks with HACL* C) and `e675b8054` (the literal gram
windows slide). Both are byte-identical: 6,110 artifact files, same SHA-256.

## 1. Method, and what it cannot see

`/usr/bin/sample <pid> 20 1 -file out.txt` against a running packer. It
samples the call stack of every thread 20 times a second and gives a call
tree with per-leaf totals.

What it CANNOT see, stated next to the result as anti-pattern 28 requires:

* **It is a time profile of one window, not of the run.** The first sample
  taken here held 21,918 of 21,918 samples inside `prepassFile`, which says
  the pre-pass was running for the whole window — not what fraction of the
  run the pre-pass is. Phase shares need several windows at known offsets,
  which is why the runs below sample at 10 s, 70 s, 130 s and 190 s.
* **It attributes to the symbol on the stack, not to the cause.** A leaf of
  `List.drop` names the walk, not the caller who asked for a quadratic
  number of them. Every attribution here was read UP the call tree to a
  Factoidal function before it was believed.
* **It cannot see work that is fast per call and frequent**, because such a
  frame is rarely on the stack when the timer fires. Allocation volume and
  retain/release traffic are visible only as `mi_malloc`/`lean_dec_ref`
  totals, which name no caller.
* **It says nothing about memory.** Section 3 uses `/usr/bin/time -l`.

Wall-clock time on this laptop is not a measurement: it is shared, and load
average ran from 5 to 82 during this work. Every timing below carries its
load average, and **instructions retired** (from `/usr/bin/time -l`) is the
number to compare, because it does not move with contention.

## 2. What dominated, and what dominates now

Both findings were accidental costs, not intrinsic ones. That is now five
in a row in this tree, after `Crypto.processBlocks256`,
`LiteralGramIndexWire.encodeBody`, `TermLocalIndex.entriesGo`,
`NQuadsFast.addQuadFast` and `Refute.collectAxioms`.

**Finding 1 — the source digest, 65% of the pre-pass.** The packer streams
the SHA-256 of every input byte twice: the pre-pass commits the source
identity, and the ingest pass recomputes it to check the file did not change
between the two. Both ran the pure Lean compression fold at about 5 MB/s
while HACL* C was already linked into the same binary for the block digests.
Of the pre-pass's 21,806 leaf samples, 14,162 were inside
`Sha256Stream.update`.

Repaired by making the compression walk an injected operation
(`Crypto.BlockFold256`), the way `Storage.BlockMerkle.Hasher` already is.
The pure walk stays the specification and stays what every `#guard`, every
theorem and every WebAssembly operation evaluates; only the native packer
passes `Harness.nativeBlockFold256`.

**Finding 2 — the literal gram windows, 36% of the publication phase.**
`LiteralGramIndex.gramsOf` built the windows of a literal as
`(List.range k).map (fun i => (cs.drop i).take n)`. `List.drop i` walks `i`
cons cells, so a literal of `L` characters cost about `L^2 / 2` cell steps,
for every literal of every block. In a 20-second window of the publication
phase, `List.drop` under `pairsOf` held 5,318 of 14,904 main-thread samples.
Repaired by a sliding walk (`gramsGo`), with `gramsOf_eq_windows` proving it
equals the map form.

**After both: no dominator, and no third accidental quadratic.** The
profile is flat. The largest remaining leaf is
`NQuadsStreaming.feedChunkC`'s two `List.length` calls at 15%: it computes
`complete.length` once for `foldFrom`'s totality fuel and once for the
error-position counter, so every chunk's character list is walked about
three times instead of once. That is a CONSTANT FACTOR on linear work, not a
quadratic. Fusing the length into `splitCompleteLines`, which already walks
the same list, is the next candidate and is worth roughly 10%.

## 3. The curve: time is linear, memory is not

skosdex prefixes, all cut from the same file at a line boundary, packed with
the repaired binary at load average 5 to 10.

| source bytes | quads | CPU s | quads/s | instructions | peak memory | peak / source |
|---|---|---|---|---|---|---|
| 52,428,626 | 259,219 | 52.52 | 4,936 | 192.0 G | 390,318,656 | 7.45x |
| 104,857,577 | 476,293 | 113.02 | 4,214 | 466.5 G | 599,870,336 | 5.72x |
| 209,715,187 | 941,802 | 214.58 | 4,389 | 775.3 G | 933,809,856 | 4.45x |

Instructions per source byte are 3,662, 4,449 and 3,697 — not monotone, so
the variation is corpus shape (the later part of the file has longer
literals), not superlinearity. **Time is linear in the source.**

Against the same inputs before the repairs: 243.4 G at 52 MB and 582.2 G at
105 MB, so instructions fell 21.1% and 19.9%. The two figures agreeing at
two sizes is what says the win is a constant factor and not a slope change.

**Memory is SUBLINEAR in the source over the measured range.** Peak
footprint grows about as `n^0.63`: fitting the 52 MB and 210 MB points and
extrapolating to the full 1,543,478,120-byte corpus predicts 3.21 GB against
the 3,192,258,560 bytes measured — a 30-fold extrapolation landing within
1%. The ratio to the source therefore FALLS with size: 7.45x, 5.72x, 4.45x,
and 2.07x at 1.54 GB.

**The mechanism of that sublinearity is NOT identified**, and the obvious
explanation is wrong: distinct subjects per quad are 0.113, 0.135 and 0.121
across the three prefixes, so the term vocabulary is not saturating. Until
the mechanism is named, the exponent is a description of skosdex and not a
property of the packer, and it must not be carried to another corpus. See
section 4.

**What stays live to the end** is certain, whatever the exponent. An IBK4
block holds one predicate across all graphs and commits its graph-set
summary in its header, so a batch boundary would either split a predicate
with partial graph sets or need a further pass. The publication point is
therefore the END of the source, and at that moment all three of these are
live at once: the `FastDataset` of every quad, the `QuadBlock`s built from
it, and the encoded bytes of every artifact of the whole generation.
`PackStream.quadIngestFinish` builds the complete artifact list before the
host writes any of it.

## 4. What this does and does not say about YAGO 4.5

At 4,400 quads per second, 132 million facts is about 8.3 hours on one core.
That is a schedule, not a blocker.

Memory is the blocker, and the honest position is that WE DO NOT KNOW. The
`n^0.63` fit is measured on prefixes of ONE thesaurus, whose vocabulary
repeats. YAGO has 49 million entities and adds new terms all the way
through, so its dictionary grows where skosdex's may not. Reading 55 GB off
that fit would be an extrapolation 92 times past the largest measurement, on
a corpus of a different shape, with no mechanism behind it.

What is needed before the import is attempted, in order:

1. The same curve on a YAGO PREFIX ladder (1, 2, 4, 8 GB), which is the only
   measurement that speaks about YAGO's shape.
2. The mechanism behind the sublinearity, so the fit means something.
3. If the answer is still too large, the flat-memory redesign: move the
   publication point to the graph boundary. That changes the emitted block
   set, which is a wire-format decision
   (`docs/designissues/2026-09-04-blocks-per-predicate.md`), so it is a new
   wire version and a separate decision, not a tuning change.
