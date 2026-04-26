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
- Rule #11: do **not** run `./build-ocaml.sh extract`. Patch + dune.
- Time-box 3 h.
