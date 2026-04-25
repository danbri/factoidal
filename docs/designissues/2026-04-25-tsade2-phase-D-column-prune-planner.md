# Tsade2 — issue #100 Phase D: Column-prune query planner (scratch)

Date: 2026-04-25
Branch: claude/main
Status: in-flight

## Background

Mim2 (`87e9dda`) shipped Phases B+C: lazy walker + page cache + byte cache.
Honest disclosure: cottas-info still 110s, daemon dies on
`SELECT (COUNT(*)) WHERE { ?s ?p ?o }`. Bottleneck is DLBA + RLE_DICTIONARY
decoder over 26 row groups × 4 columns per query.

Phase D unlocks usable perf: for predicate-bound query
`?s wdt:P31 :Human`, decode only the predicate column of row groups whose
predicate dictionary contains `wdt:P31`, skip others.

## Constraint conflict resolution

Brief asked for **eager per-rg dicts at handle open time** by extending
the OCaml glue (`cottas_ondisk_runtime.sh`). Brief ALSO says **do NOT
touch `cottas_ondisk_runtime.sh`** because Pe4 owns it.

**Resolution:** populate per-rg dicts **lazily in F\*** on first query, via
a new pure F\* helper `probe_parquet_column_dictionary_in_row_group` in
`Parquet.Footer.fst`. No OCaml-glue changes. Caching via the existing
`page_cache` module — keyed under a synthetic `col_index` offset
(or a dedicated dict cache slot).

Cost: <10s on first predicate-bound query (one-shot per rg, dict pages
are tiny — <50KB total across 26 rgs based on parliament's 231 distinct
predicates). Subsequent queries are free.

## Plan

### Step A — F\* helper: dict-only decode

`Parquet.Footer.probe_parquet_column_dictionary_in_row_group :
   path -> rg -> col -> option (list string)`

Reuses existing primitives:
- `probe_parquet_column_dictionary_page_offset_in_row_group`
- `parquet_decompressed_page_at`
- `parquet_dictionary_page_num_values_at`
- `decode_plain_dictionary`

Pure F\*. Decodes the dict page only — NOT the data page. Small + fast.

### Step B — Per-rg dict cache

Add `pcache_dict_cache` to `RDF.CottasStore.PageCache` keyed by
`(rg_index, col_index) -> list string`. Or piggy-back the existing
`page_cache` by storing dict entries with `col_index = base + 100`
sentinel (cleaner: separate field).

Decision: **separate field `pc_dicts : list (pcache_key & list string)`**
on `page_cache`. Avoids semantic confusion with decoded data pages.

### Step C — Pruned search

```fstar
val cottas_ondisk_search_pruned :
  handle -> bound -> cache -> Tot (list cottas_qp_row & page_cache)
```

1. If `bound.cbqp_p = Some pred_id`:
   - resolve `pred_iri = list_nth handle.coh_predicates_raw pred_id`
   - compute candidate rgs: rgs where `pred_iri ∈ rg's predicate dict`
   - walk only those candidates
2. Same for `cbqp_s` (subject_dict) and `cbqp_o` (object_dict) IF
   those bounds are present (compose: candidate_rgs = intersection).
3. Within each candidate rg, decode predicate column first, filter
   matched rows (stored as row-indices), then decode s/o/g columns
   (existing logic re-uses entire decoded list — simpler).

Compromise on the "decode only matched indices" optimization: F\*'s
RLE/DLBA decoders return whole-column lists, not by-index. Refactoring
to per-index decode is a Phase E project. For Phase D the win is
**row-group skipping**, which alone should turn 26-rg walk into
~3-rg walk for selective predicates.

### Step D — Wire up `cottas_ondisk_search`

Dispatch:
- Any of s/p/o bound → `cottas_ondisk_search_pruned`
- All unbound → existing `walk_row_groups_search`

### Acceptance gates

1. F\* `make verify` clean.
2. cottas-info reports 3,143,406 quads, open <120s.
3. Predicate-bound smoke `signatureCount` LIMIT 10 < 5s wall-clock.
4. Unbound `COUNT(*)` uses unpruned path (Pe4's bug separate).
5. W3C 1657/1/0 unchanged.

## Notes

- `cottas_ondisk_search` signature changes from `Tot (list cottas_qp_row)`
  to internally use a cache; public signature must stay the same (no
  caller changes), so we plumb a fresh empty cache inside.
- For Phase D the page_cache is reset per query — fine, the dict cache
  hit-rate within a single query is what matters (1 dict probe per rg
  per column; reused across the per-rg walk).
- A **module-level dict cache** would survive across queries but
  requires mutable state. Punting to Phase E — for now, per-query
  cache is sufficient since dict probes are <50KB total.

Actually — let's escalate dict cache to **handle-attached** so it
survives across queries. Implementation: thread page_cache through
`cottas_ondisk_search` callsite (the daemon already calls it once per
query). If unable to thread without breaking callers, accept per-query
cost (1 dict probe × 26 rgs × 1 col = 26 small reads; <1s).

Decision: per-query for now (no caller signature changes). Document
hand-off opportunity for next phase.
