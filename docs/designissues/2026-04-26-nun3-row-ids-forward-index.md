# Nun3 — flat row_ids forward index for the on-disk COTTAS backend

Issue #100, 2026-04-26.

## Problem

23 of 24 modern parliament demo queries hit the Heth3 30s wall-clock cap
because `search_fast`/`estimate_fast` still **decode subject + object
DLBA columns per-rg-per-query** (~3-6 s/rg per column × multiple
candidate rgs × multiple BGP patterns = 30 s+).

Lamed3 closed the predicate-decode hot path by recording, per (rg,
predicate-id), the row-positions where that predicate occurs. But the
final subject/object decode is still per-rg full column.

## Plan

A flat **per-row tuple of column-IDs** `(s_id, p_id, o_id, g_id)` =
4 × u32 = 16 bytes, mmap'd at boot. The hot loop becomes:

```
for each candidate rg (after Yod6/Tet3 prune):
  for each row in rg:
    read 16-byte tuple from mmap
    compare bound IDs (u32 equality)
    if match, record position
decode subjects/objects only for the LIMIT-many output rows.
```

## Companion file format

`data.cottas.row_ids`:

```
[ magic 'COTR' u32 (LE) | version u32 | num_rgs u32 | reserved u32 ]
[ total_rows u64 ]
[ rg_offsets : u64 array, length num_rgs+1 ]
   rg_offsets[i] = byte offset where rg i's row-tuples start
   rg_offsets[num_rgs] = end (exclusive)
[ rows : per rg, rows_in_rg × 16 bytes (s_id, p_id, o_id, g_id) as u32 LE ]
```

Sizing on parliament: 3.14M rows × 16 = **50 MB**. Tiny.

## Work breakdown

1. Extend `RDF.CottasStore.OnDiskIndex.fst` with `row_ids_header`,
   `read_row_ids_header`, and `row_ids_lookup_tuple` (F*-pure, refinement
   typed, only `assume val` for byte-range I/O — already inherited).
2. New OCaml-glue patch `cottas_ondisk_zzzzzzzz_nun3_row_ids.sh`:
   - Writer: walks 26 rgs once, encoding tokens via Vav3's mmap'd dict
     (binary-search in the .dict), atomically writes `.row_ids`.
   - Reader: mmap'd via Vav3_mmap.try_open_mmap.
   - Dispatcher: `search_fast` / `search_fast_limited` / `estimate_fast`
     try a `*_via_row_ids` path before falling through to Lamed3 →
     full column walk.
3. Boot: `ensure_row_ids_built` runs in `prewarm_via_companions` after
   Lamed3.

## Acceptance

- First-boot: `.row_ids` (50 MB) built; <90 s extra.
- Second-boot: <2 s ready.
- 12+/24 modern queries < 30 s (vs 1/24 today).
- Q01 `?s rdf:type ?o LIMIT 5` < 500 ms (was 6 s).
- W3C: 1657 / 1 / 0 / 4 unchanged.
- F\* module verifies clean.

## Rule #15 / #100

Writer + reader are I/O glue + memory layout. Row positions are
byte-identical to "concatenated rows in rg order; each row is its
column-id tuple". No new RDF/SPARQL semantics. The format itself is
documented in F\* (Step 1).
