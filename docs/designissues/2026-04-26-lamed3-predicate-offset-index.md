# Lamed3 — Per-row-group predicate row-offset index

**Date:** 2026-04-26  
**Status:** in progress, agent Lamed3, time-boxed 3h.  
**Related:** Vav3 (#100) on-disk dict + presence companions; Yod6/Tet3 presence prune.

## The problem

`?s rdf:type ?o LIMIT 5` on the parliament dataset is ~6 s warm; bound-predicate
queries on rare predicates can be >25 s. The dominant cost in `search_fast`
(per row group) is decoding the entire predicate column — ~300 k rows × DLBA
varints — and then filtering for the bound predicate. The decode is redundant:
the predicate column is immutable and we already know per-rg presence (from
Yod6's `.presence` bitmap), so we should also know **which row positions**
within each rg have predicate P.

## The fix

Build a third on-disk companion sibling to `data.cottas.p.dict` and
`data.cottas.p.presence`:

```
data.cottas.p.offsets

[ magic 'COTO' u32 | version u32 | num_rgs u32 | num_predicates u32 ]
[ rg_off_index : u64 * (num_rgs * num_predicates + 1) ]
   rg_off_index[rg*np + pred]   = byte offset into data section
   rg_off_index[rg*np + pred+1] = end offset (exclusive)
[ data : u32[] row positions, ascending, packed ]
```

Per (rg, pred) row-list = `data[start..end)` with len = (end-start)/4 u32s.

### Writer

Lives in new patch `experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`,
called from `Cottas_companion_boot.prewarm_via_companions` after dict+presence
exist (so we already have the predicate dict's tok-to-id mapping). Walks the
predicate column once per rg, accumulating row-positions per predicate id;
atomically writes `data.cottas.p.offsets` (tmp + fsync + rename).

### Reader

`search_fast` (and `_limited` / `_estimate`) when the predicate is bound:
1. Resolve predicate IRI -> pred_id via existing dict.
2. For each rg that the presence bitmap says could contain pred_id:
   a. Look up `(rg, pred_id) -> [row positions]` in mmap'd offsets file.
   b. Decode subject + object columns at those specific row positions only.
3. Skip predicate-column decode entirely.

### Integration with Mem5

Mem5 owns `cottas_ondisk_runtime.sh`. This patch ships in a new file with
its own boot hook + reader module, and exposes a function
`Cottas_offset_idx.row_positions_for : path -> rg -> pred_id -> int array option`
that Mem5 (or main thread) can call from search_fast. If Mem5 hasn't merged
the call site by integration time, the offset index is built and mmap'd but
not consulted; benchmarks in the report will reflect that.

## Smoke targets

- `?s rdf:type ?o LIMIT 5`: 6 s -> <200 ms.
- `?s :rare_pred ?o LIMIT 1000`: >25 s -> <2 s.
- W3C 1657/1/0/4 unchanged.

## Hard rules in flight

- Rule #15: writer is I/O glue only; the file format is documented here
  (and ideally as `OnDiskOffsetIdx` types in F\* later). No semantic logic.
- Rule #11: do **not** run `./build-ocaml.sh extract`. Patch + `./build-ocaml.sh compile`
  (this repo has no dune; compile is raw `ocamlfind ocamlopt`).
- Time-box 3 h.

## Results (2026-04-26 evening)

**Patch:** `formal/fstar/experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`.

**File format:** as designed above. Magic `'COTO'` (0x4f544f43 LE),
version 1, 16-byte header, u64 index, u32 row-position data.

**On parliament (3.14M quads, 26 row groups, 232 predicates):**

| Phase                                | Time   |
| ------------------------------------ | ------ |
| First boot (offsets-build + mmap)    | 28.98s |
| Boot delta (offsets-build only)      | 24.61s |
| Subsequent boot (mmap only)          | 4.11s  |

**Offsets file size:** 12.0 MB (vs 50 MB worst-case estimate).

**Query timings (all hit `search_fast_limited_via_offsets`):**

| Query                                          | Result                                       |
| ---------------------------------------------- | -------------------------------------------- |
| `?s rdf:type ?o LIMIT 5`  (target <200ms)      | 5.2s warm; matched 5/5 rows, walked 1/26 rgs |
| `?s rdf:type ?o LIMIT 50`                      | 14.8s; matched 50/50, walked 4/26 rgs        |
| `<bound_subj> rdf:type ?o LIMIT 1`             | 6.0s; matched 1/1, walked 1/26 rgs           |
| `?s rdf:type ?o LIMIT 1000` (target <2s)       | 30s timeout; matched 148/1000, walked 9/26   |
| `?s geosparql:asWKT ?o LIMIT 5` (rare/absent)  | 9ms (Yod6 presence prune short-circuits)     |

**W3C tests:** 1657 pass, 1 fail, 0 fail-new, 4 skip. **Unchanged.**

## Honest gaps

- **Targets MISSED.** The `<200ms` LIMIT 5 target assumed per-row column
  reads. The current Parquet probe API (`probe_parquet_column_decode_in_row_group`)
  decodes the *entire* column for a row group and returns a list. Even though
  the offset index now skips the 3-6s predicate-column decode, we still
  pay 4-5s to decode subject + object columns of any rg we touch.
- The win is structural: predicate-column decode is **eliminated** from
  bound-pred queries. This is the pre-requisite for the next step:
  per-row column reads (or DLBA partial decoding by row range).
- The user prompt explicitly anticipated partial wins: "ship a partial
  result if needed (e.g., offsets file written but not yet wired into
  search_fast)." Both halves landed: file + dispatcher wiring.
- No F\* spec written for the `OnDiskOffsetIdx` format yet. Recommended
  follow-on (rule #15 long-term): port the format definition + reader
  semantics into `RDF.CottasStore.OnDiskOffsetIdx.fst` so the file format
  itself becomes verified, leaving only mmap I/O as glue.

## Cross-agent integration notes

- **Mem5 (`cottas_ondisk_runtime.sh`)**: NO conflict. The Lamed3 patch
  inserts `Cottas_offset_idx` BEFORE `Cottas_ondisk_runtime`, then
  inserts `*_via_offsets` helpers and dispatchers INSIDE
  `Cottas_ondisk_runtime` (idempotent skip-if-marker). Mem5's patches
  only touch `RDF.CottasStore.fst` (extracted estimate_fast_inner-style
  changes) and don't conflict with mine.
- **Heth3 (`factoidal_http.ml`)**: NO conflict. Heth3's per-query Lwt
  timeout fired during the LIMIT 1000 test (proving Heth3 works as
  intended). The 30s timeout is correct; Lamed3 didn't hide the
  underlying decode cost.
- The `let rec ... and ...` mutual-recursion idiom in the patch is
  cosmetic (neither dispatcher nor `_inner` actually recurse into each
  other) — it's only there because OCaml requires textually-prior
  definition for the dispatcher's call to `_inner`.
