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

## 5. Where this leaves the cause

Not the host, not `Pack.lean`'s operation sequence, not the handle
table, not the publication batch, and not a general inability of the
module to reuse freed memory. What remains is the interaction between
the packer's allocation pattern and the module's allocator — Lean's
runtime built with `LEAN_MIMALLOC`, mimalloc 2.2.7 on Emscripten, whose
operating-system layer is emmalloc and whose `_mi_prim_decommit` is a
no-op — and the measurements above cannot separate bytes in use from
bytes held free.

**The cause is not closed.** The next instrument is in the tree and is
not yet measured: `l4_mem_report_c` and `l4_collect` in
`formal/lean4/Wasm/l4_shim.c`, exported by `build-wasm.sh`. The first
answers mimalloc's own committed and in-use totals, which splits the
curve into bytes in use and bytes held free; the second asks mimalloc
to release what it holds free, which is the candidate repair if the
split says the allocator holds it. Both compile for wasm32 and both
symbols are present in the mimalloc object; NEITHER HAS BEEN RUN, because
the module was not relinked in this landing.

Two conditions on that measurement:

* mimalloc's commit counters are maintained only when it is compiled
  with `MI_STAT` above zero. `build-wasm.sh` does not set it — the cost
  of setting it is not measured — so a measuring build must add
  `-DMI_STAT=2` to the mimalloc compile line and must not ship.
* The probe drives one pack repeatedly in ONE module instance and
  reports the heap, the mimalloc totals, and the totals again after
  `l4_collect(1)`. The repeat table in section 4 is what it extends.

Raising `-sMAXIMUM_MEMORY` moves the panic and does not touch any line
of this record.
