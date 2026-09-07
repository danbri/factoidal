# The WebAssembly packer's memory: what grows, and what does not

2026-09-07. https://github.com/danbri/factoidal/issues/658.

The native packer completes a 700 MB AGROVOC prefix with 257 MB of peak
resident set. The same bytes through the WebAssembly module stop with
`INTERNAL PANIC: out of memory` 436 MB into the ingest pass, at 1.99 GB.
This record holds the measurements that localise the difference, the
one-variable results, and what is still open.

## 1. Method, and what it cannot see

Two instruments.

* **Linear memory per feed.** `pack.mjs` writes
  `Module.HEAPU8.byteLength` with the ingest offset after every
  `packFeed` and after every drain, to the file named by
  `L4_PACK_MEM`. The worker thread's `process.stderr` does NOT flush
  while the pack loop runs, so the trace is written with
  `appendFileSync`; a first attempt through `stderr` delivered ONE line
  for a run of 3,000 feeds and looked like a stalled process.
* **Process memory.** `/usr/bin/time -l` around each run; the figures
  quoted are `peak memory footprint` for the native runs and
  `maximum resident set size` for the Node runs.

What they cannot see:

* **Linear memory is an upper bound on demand, not a measure of it.**
  Emscripten grows the heap in steps of about 1.2x, so a curve reports
  the growth EVENTS, not the bytes asked for. Every step below is a
  request the current heap could not satisfy; the true demand lies
  between two steps.
* **Neither instrument separates bytes in use from bytes the allocator
  holds free.** That distinction is what decides whether the packer
  retains data or the allocator retains pages, and nothing measured
  here answers it. A module export that reports mimalloc's own view is
  the next instrument, not a conclusion of this one.
* The Node runs also carry the JavaScript heap, which holds one
  artifact name per artifact written. That is thousands of short
  strings, not hundreds of megabytes, but it is inside every RSS figure
  quoted for a Node run.

Input: a 100 MB line-aligned prefix of `prefix700.nq` (AGROVOC),
587,430 lines, IBK5 layout, N-Quads grammar. Every route reads it in
65,536-byte chunks — `FEED_BYTES` in `npm/factoidal/bin/pack.mjs` is
65,536, the same figure the native packer reads.

## 2. The same operations, natively, cost what the native packer costs

`lake exe l4wasm-cli pack` drives `packBegin`, `packFeed`,
`packEndPass`, `packNext`, `packFinish`, `packClose` — the operations in
`Wasm/Ops/Pack.lean` — in the same order, with the same chunk size, in a
native process.

| route | peak memory footprint | max RSS |
|---|---|---|
| `l4block-shard-pack` (native packer) | 207,521,856 | — |
| `l4wasm-cli pack` (the wasm operations, natively) | 195,201,216 | 202,817,536 |
| `l4wasm-cli pack`, `MIMALLOC_PURGE_DELAY=-1` | 195,742,016 | 183,713,792 |
| `factoidal pack` (the wasm module, Node) | 586,235,904 | 597,098,496 |

**The handle table is not the cause.** The pack handle sits in a
process-global `Std.HashMap` for the whole pass, so every
`quadIngestFeed` runs against a state the table also references; that
makes each feed's first update to a shared `Array` or `Std.HashMap`
copy rather than update in place. It was the leading suspect. It costs
nothing measurable: the same code natively is within 6% of the native
packer, and BELOW it.

Disabling mimalloc's purge natively changes nothing either, so the
native figure is not low because the allocator returned pages to the
operating system.

## 3. The curve, and the one-variable results

Linear memory against ingest offset, 100 MB source, IBK5, batch 64 MiB:

| pass | ingest offset (bytes) | linear memory (bytes) |
|---|---|---|
| prepass | 65,536 … 99,680,256 | 55,443,456 throughout |
| ingest | 8,847,360 | 83,886,080 |
| ingest | 8,978,432 | 181,207,040 |
| ingest | 28,508,160 | 217,448,448 |
| ingest | 37,027,840 | 260,964,352 |
| ingest | 45,350,912 | 313,196,544 |
| ingest | 63,438,848 | 381,747,200 |
| ingest | 81,330,176 | 458,096,640 |
| ingest | 97,058,816 | 549,715,968 |

**The pre-pass is flat.** It digests all 100 MB and does not grow the
heap by one page. Whatever grows is in the parse-and-publish pass.

One variable at a time:

| variable | value | end of ingest, linear memory |
|---|---|---|
| publication batch | 67,108,864 (64 MiB) | 549,715,968 |
| publication batch | 4,194,304 (4 MiB) | 549,715,968 |

**Batch size does not move it, at all.** A 4 MiB batch publishes and
releases open runs sixteen times more often and produces a much larger
block set; the curve is byte-for-byte the same. So the growth is not
the open runs, not the carried rows, and not the publication point.

## 4. Repeating one unit of work inside one module instance

This is the measurement that says where to look next. Each row is one
module instance; the work is repeated on the same input.

| repeated unit | linear memory after each repetition (bytes) |
|---|---|
| `_malloc(50 MB)` + `_free` from JavaScript, ten times | 98,697,216 unchanged |
| 5,000 calls of the `ops` operation | 98,697,216 unchanged |
| `parseToDatasetJson` of 5 MB, six times | 692,125,696 · 1,348,993,024 · 1,348,993,024 · 1,348,993,024 · 1,348,993,024 · 1,348,993,024 |
| `datasetOpen` + `datasetClose` of 5 MB, six times | 340,852,736 · 409,075,712 · 490,930,176 · 589,168,640 · 707,002,368 · 826,343,424 |
| pack of 1 MB, twenty times | 55,443,456 → 83,886,080 (third) → 117,440,512 (thirteenth) → unchanged |
| pack of 20 MB, five times | 181,207,040 · 260,964,352 · 375,848,960 · 541,261,824 · 649,527,296 |

Read together:

1. **The host does not leak.** Ten 50 MB regions allocated and freed
   from JavaScript, and five thousand small operations, leave the heap
   where they found it.
2. **Freed memory is broadly reusable.** A pure operation repeated on
   the same input converges after two repetitions and then never grows
   again.
3. **A pack does not converge.** The same pack of the same 20 MB file
   raises the heap on every repetition, and the increment grows.
4. **The per-repetition growth rises faster than the input.** Twenty
   packs of 1 MB add 62 MB in total; one pack of 20 MB adds about 100
   MB by itself.
5. `datasetOpen` + `datasetClose` also fails to converge, so whatever
   this is, it is not confined to the packer.

## 5. What section 4 was read to mean, and why that reading was wrong

The first reading of the table above was that the packer's allocation
pattern meets the module's allocator badly: Lean built with
`LEAN_MIMALLOC`, mimalloc 2.2.7 on Emscripten, whose operating-system
layer is emmalloc and whose `_mi_prim_decommit` is a no-op. That
reading was recorded here as the remaining candidate. **It is wrong,
and the measurement in section 6 replaces it.** The error is worth
naming, because the same shape can recur: linear memory is an upper
bound, and every figure available at the time was an upper bound, so
"the allocator holds it" was the only hypothesis the instruments could
not refute. Nothing said it was true.

## 6. Bytes in use, measured

Three instruments were added to the module and run (a measuring build,
`L4_WASM_MIMALLOC_CFLAGS=-DMI_STAT=2`, in its own work dir):

* `l4_mem_stats_c` returns mimalloc's own statistics as text. Its
  `total:` row is bytes allocated and not yet freed; its `reserved:`
  row is memory mimalloc holds from emmalloc. Together they split the
  linear-memory curve into bytes in use and bytes held free.
* `l4_heap_tags_c` visits every live mimalloc block and reads its
  eighth byte, which is the `m_tag` field of `lean_object`'s header. It
  answers WHAT the live bytes are.
* `l4_mi_option_set` sets one mimalloc option at run time, so an
  allocator experiment needs no rebuild (the module has no environment,
  so `MIMALLOC_*` variables cannot reach it).

The input for section 6 is a 100 MB line-aligned prefix of
`prefix700t.nq` (617,158 lines) and a 20 MB prefix of the same file
(109,804 rows). Section 3's prefix has 587,430 lines, so the two sets of
figures are not directly comparable line for line; every comparison
below is within section 6.

`l4_mem_report_c` and `l4_collect`, added in the previous landing, were
also run. `l4_collect(1)` does not move the heap by one byte, in any
configuration; `l4_mem_report_c`'s `commit` figure is not a measure of
live bytes, because `_mi_prim_decommit` is a no-op and the counter
drifts (it reported 83 MiB while 385 MiB was allocated). Read `total:`,
not `commit`.

### 6.1 In use is flat within a pass and rises across passes

100 MB AGROVOC prefix, IBK5, N-Quads, 64 KiB feeds, per-feed trace:

| ingest offset | in use (`total:` current) | mimalloc reserved | linear memory |
|---|---|---|---|
| 65,536 | 9.8 MiB | 32.0 MiB | 55,443,456 |
| 10,551,296 | 82.8 MiB | 138.0 MiB | 191,365,120 |
| 26,279,936 | 82.8 MiB | 138.0 MiB | 191,365,120 |
| 47,251,456 | 82.8 MiB | 224.0 MiB | 330,694,656 |
| 68,222,976 | 82.8 MiB | 320.0 MiB | 396,886,016 |
| 99,680,256 | 82.8 MiB | 448.0 MiB | 571,604,992 |

The `committed` figure in that trace is flat at 82.8 MiB, and taking it
for "bytes in use" is what made the allocator look guilty. The `total:`
row over the whole pack says otherwise: **peak in use 449.3 MiB,
385.0 MiB still in use after `packClose`**, against 512.0 MiB reserved.
The allocator's overhead over live bytes is 1.33x. It is not the cause.

### 6.2 The same pack repeated raises the LIVE bytes every time

20 MB prefix, one module instance, the same file each repetition:

| repetition | in use, after `packClose` | reserved | linear memory |
|---|---|---|---|
| 1 | 70.1 MiB | 160.0 MiB | 229,638,144 |
| 2 | 134.9 MiB | 224.0 MiB | 330,694,656 |
| 3 | 199.8 MiB | 320.0 MiB | 476,315,648 |
| 4 | 264.6 MiB | 394.0 MiB | 571,604,992 |
| 5 | 329.5 MiB | 458.0 MiB | 675,348,480 |

64.8 MiB of live bytes per pack of the same 20 MB file, after the pack
handle is closed and erased from the table. Reserved tracks it at about
1.4x. This is retention, not fragmentation.

### 6.3 What is retained: `mpz`, 15.6 objects per quad

`l4_heap_tags_c` after each of three repeated 20 MB packs:

| repetition | tag 250 (`mpz`) | tag 0, 8-byte blocks | everything else |
|---|---|---|---|
| start | 2,522 / 0.1 MiB | 5,348 / 0.1 MiB | 5.1 MiB |
| 1 | 1,709,007 / 52.2 MiB | 1,649,313 / 12.6 MiB | 5.3 MiB |
| 2 | 3,415,492 / 104.2 MiB | 3,293,286 / 25.2 MiB | 5.3 MiB |
| 3 | 5,121,977 / 156.3 MiB | 4,937,258 / 37.7 MiB | 5.3 MiB |

Every other tag is constant. The retained bytes are arbitrary-precision
integers and one small block each, 1,709,007 of them per 109,804-row
pack — 15.6 per quad — growing by exactly that count per repetition.

This is a wasm32-only object. The module is GMP-free and 32-bit, so a
Lean `Nat` at or above 2^30 is a heap `mpz`; on a 64-bit build the same
value is an unboxed scalar and no object exists. That is why the native
route through the same operations (`lake exe l4wasm-cli pack`, 195 MB
peak) does not show it.

### 6.4 Where it is, and where it is not

| route, repeated in one module instance | live bytes |
|---|---|
| `parseToDatasetJson`, 3 MB, four times | 5.3 MiB, unchanged |
| `datasetOpen` + `datasetClose`, 3 MB, four times | 5.3 MiB, unchanged |
| the pack's PRE-PASS alone, 20 MB | 5.2 MiB, unchanged |
| the pack's ingest pass, 20 MB | 5.2 -> 70.7 MiB |
| `packFinish`, then `packClose` | 70.8 -> 70.1 MiB |

So the retention is in the parse-and-publish pass, and only there. The
pre-pass digests the same bytes with the same SHA-256 block fold and
retains nothing, which excludes the digest. `packClose` releases
0.7 MiB of the 65 MiB, which excludes the pack handle and its state:
whatever holds these objects is not in `packTable`. Publication timing
is irrelevant — a batch of 999,999,999,999 bytes, which publishes
nothing until the end, and a batch of 4 MiB give the identical count of
1,709,007 — which excludes the open runs and the artifact queue.

`datasetOpen` + `datasetClose` still raises the heap on every
repetition (236 -> 409 -> 490 -> 589 MB) while its live bytes stay at
5.3 MiB. THAT one is fragmentation, and it is a different problem from
the packer's.

### 6.5 The allocator options, one at a time

Each is one module instance, five repeated 20 MB packs, set through
`l4_mi_option_set` before the first pack (`mi_option_t` ordinals from
mimalloc 2.2.7's `include/mimalloc.h`):

| option | linear memory after 5 repetitions | verdict |
|---|---|---|
| (default) | 675,348,480 | — |
| `arena_reserve` = 512 MiB | 599,851,008 after 1 | no better |
| `arena_reserve` = 1 GiB | 591,462,400 (flat from the 4th) | 12% better |
| `arena_reserve` = 2 GiB | 688,586,752 (flat from the 1st) | worse |
| `arena_reserve` = 4 GiB | 4 GiB ceiling by the 3rd | fails |
| `arena_reserve` = 0 | 4 GiB ceiling by the 3rd | fails |
| `disallow_arena_alloc` = 1 | 4 GiB ceiling by the 3rd | fails |
| `purge_delay` = 0 | 675,348,480 | no change |
| `l4_collect(1)` after each | 675,348,480 | no change |

Two readings. Turning the arena layer OFF is much worse, not better:
without it every 4 MiB mimalloc segment is an `emmalloc_memalign` call
and the fragmentation is catastrophic, so the arena layer is carrying
this build rather than harming it. And purging cannot help, because
`_mi_prim_decommit` is a no-op by construction. **No allocator option
is a fix, and none is shipped.**

## 7. The 700 MB reproduction does not reproduce

Section 1 records that the module stops with `INTERNAL PANIC: out of
memory` 436 MB into the ingest pass, at 1.99 GB. Re-run on 2026-09-07
against `SCRATCH/oom/prefix700t.nq` (734,003,186 bytes), IBK5, 64 MiB
batch, through `npm/factoidal/bin/factoidal.mjs pack`, it does not:

| module | verdict | peak RSS | wall clock |
|---|---|---|---|
| the module committed before this landing | completes | 1,099,366,400 | 576 s |
| the module this landing commits | completes | 1,062,567,936 | 517 s |

Both write 4,016 artifacts, 518,790,565 bytes, 4,282,588 rows — the
same generation. The 3% difference between them is build-to-build; this
landing makes no behaviour change and does not claim it.

So the reported panic is not a property of the committed module on this
input. Either the input differed (section 1 names `prefix700.nq`, and
only `prefix700t.nq` is now on disk), or the invocation did, or the
module measured was not the committed one. **A reproduction that no
longer reproduces is a fact about the record, not about the engine**:
until the failing invocation is recovered, the panic is unconfirmed and
the working figure for a 700 MB pack is 1.06 GB of peak resident set,
against the native packer's 257 MB.

That leaves the retention in section 6 measured and real, and its
consequence smaller than assumed: the packer costs 4.1x the native
packer on this input rather than failing on it. The live bytes are also
sublinear in the source over the whole file — 385 MiB after 100 MB
would project to 2.7 GB at 700 MB, and the run peaks at 1.06 GB — so
the per-quad figure in section 6.3 is a rate at the head of the file,
not a constant.

## 8. What is open

The cause is localised and not closed. What is known: 15.6 `mpz`
objects per quad, allocated in the pack's parse-and-publish pass, are
never freed; they are not reachable from the pack handle, since closing
it releases 1% of them; and the standalone N-Quads parse
(`parseToDatasetJson`, a different, non-streaming parser) does not
produce them. What is not known is which allocation site they come from
and what holds them. The next measurement is a bisect inside the ingest
pass — the streaming N-Quads fold
(`L4Factoidal.Syntax.NQuadsStreaming.feedChunkC`) against the run
accumulation and block encoding — with `l4_heap_tags_c` after each,
which the shipping module exports.

The gate stands at 1.06 GB of peak resident set for the 700 MB prefix,
against a target of 514 MB (twice the native packer) and a floor of
1 GB. It is missed by 6% and follows the repair in section 6, not an
allocator setting.

`-sMAXIMUM_MEMORY` moves the panic and touches no line of this record.
