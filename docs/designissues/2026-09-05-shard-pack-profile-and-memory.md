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

## 3. The curve: time is linear, and so is memory

skosdex prefixes, all cut from the same file at a line boundary, plus the
whole file. Packed with the repaired binary at load average 4 to 10.

| source bytes | quads | CPU s | quads/s | instructions | peak memory | peak / source |
|---|---|---|---|---|---|---|
| 52,428,626 | 259,219 | 52.52 | 4,936 | 192.0 G | 390,318,656 | 7.44x |
| 104,857,577 | 476,293 | 113.02 | 4,214 | 466.5 G | 599,870,336 | 5.72x |
| 209,715,187 | 941,802 | 214.58 | 4,389 | 775.3 G | 933,809,856 | 4.45x |
| 1,543,478,120 | 7,315,251 | 1,777.47 | 4,116 | 5,057.4 G | 5,951,730,560 | 3.86x |

**Time is linear in the source.** Instructions per source byte are 3,662,
4,449, 3,697 and 3,277 — not monotone, so the variation is corpus shape (the
later part of the file has longer literals), not a slope.

Against the same inputs before the repairs: 243.4 G at 52 MB and 582.2 G at
105 MB, so instructions fell 21.1% and 19.9%. The two figures agreeing at
two sizes is what says the win is a constant factor and not a slope change.

**Memory is LINEAR in the source: 3.76 bytes of peak footprint per source
byte, plus a constant of about 145 MB.** Those two numbers are fitted to the
210 MB and 1,543 MB points and they reproduce the 105 MB point to 10% and
the 52 MB point to 14%.

The ratio to the source FALLS with size — 7.44x, 5.72x, 4.45x, 3.86x — and
that fall is the 145 MB constant amortising, nothing more. **Reading a trend
out of the ratio is how this measurement was got wrong once already.** On
the first three points alone the ratio fits a sublinear power law with
exponent 0.63, and a draft of this document reported memory as sublinear on
that basis. The fourth point, ten times larger, gives exponent 0.93 between
the top two and settles it: the curve is a straight line through an offset,
and a three-point fit spanning only 4x could not tell the two apart. Do not
fit a memory curve without a point at least an order of magnitude above the
others.

**A number in the task that set this work off did not reproduce.** It gave
3,192,258,560 bytes of peak footprint for the full 1,543,478,120-byte
corpus, a ratio of 2.07x. Measured here: 5,951,730,560 bytes, 3.86x, with
maximum resident set size 5,585,649,664. The repairs in this landing are
byte-identical and reduce allocation, so they cannot account for it; the
earlier figure must come from a different binary, corpus or metric. It is
recorded as unreproduced rather than averaged in.

**What stays live to the end**, which is why the slope is what it is: an
IBK4 block holds one predicate across all graphs and commits its graph-set
summary in its header, so a batch boundary would either split a predicate
with partial graph sets or need a further pass. The publication point is
therefore the END of the source, and at that moment all three of these are
live at once: the `FastDataset` of every quad, the `QuadBlock`s built from
it, and the encoded bytes of every artifact of the whole generation.
`PackStream.quadIngestFinish` builds the complete artifact list before the
host writes any of it. Nothing the pass builds is released before the end,
so peak memory is a fixed multiple of the data — the measured 3.76.

## 4. What this says about YAGO 4.5

**Time is not the problem.** At 4,116 quads per second measured on 7.3
million quads, YAGO's 132 million facts is about 8.9 hours on one core.

**Memory is the problem, and it is decisive.** At 3.76 bytes per source
byte, 142 GB of source needs about **534 GB** of peak footprint. This is
worse than the 294 GB the task estimated from the 2.07x ratio, because the
ratio was low and because a ratio is the wrong shape to extrapolate: the
slope is what extrapolates, and it is 3.76.

No amount of tuning closes a 534 GB gap on a laptop. The import needs the
publication point moved to the graph boundary, so that a block's bytes are
written and released as soon as its graph ends and peak memory stops
tracking the source at all. That changes the emitted block set, which is a
wire-format decision (`docs/designissues/2026-09-04-blocks-per-predicate.md`,
specification section 10), so it is a new wire version and a separate
decision — not a tuning change, and deliberately not attempted here.

One measurement should precede that work: the same ladder on a YAGO PREFIX
(1, 2, 4, 8 GB). The slope of 3.76 is skosdex's; YAGO has 49 million
entities against skosdex's 113,680 distinct subjects at 210 MB, so its
dictionary is a larger share of what stays live and its slope will be its
own.
