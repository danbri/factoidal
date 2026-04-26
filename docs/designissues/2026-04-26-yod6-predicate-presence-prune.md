# Yod6 — Per-Row-Group Predicate Presence Pruning (issue #100)

**Date:** 2026-04-26
**Branch:** `claude/main`
**Status:** in progress

## Problem

Predicate-bound SPARQL queries on the on-disk COTTAS backend currently walk
**all 26 row groups** even when the bound predicate appears in only a handful.

Root cause (in `formal/fstar/RDF.CottasStore.fst`):

- `populate_dict_cache_for_column` calls
  `probe_parquet_column_dictionary_in_row_group`.
- COTTAS-style data has DLBA-encoded predicate column with NO dictionary page
  per row group, so the probe returns `None` for every rg.
- `compute_candidate_rgs_loop` sees an empty `dict_cache` and falls back to
  "include all rgs" (the safe-fallback `| None -> rg_index :: acc_rev`).

Aleph6 explicitly de-scoped this; it's the deferred prune-via-DLBA-distinct-
extraction.

## Critical re-evaluation: F\* path is bypassed

After reading `cottas_ondisk_runtime.sh` lines 885+ I confirmed:

```
search_old = "let cottas_ondisk_search ... =\n  Cottas_ondisk_runtime.search_fast ds.cods_handle bound"
estimate_old = "let cottas_ondisk_estimate ... =\n  Z.of_int (Cottas_ondisk_runtime.estimate_fast ...)"
```

The F\*-extracted `cottas_ondisk_search` (with its `plan_candidate_rgs` and
dict-cache prune) is **replaced by a direct call to OCaml `search_fast`**.
That OCaml shim does an unconditional `for rg = 0 to rg_count - 1` walk
with no prune.

So Shape B (extending the F\* `cottas_ondisk_handle` with a presence
field) won't actually affect the running query path — the F\* code is
extracted but bypassed.

Shape A is the only one that closes the bug. The F\* spec already has the
prune logic via `plan_candidate_rgs`; the OCaml fast-path failed to mirror
it. Adding the prune to `search_fast` / `estimate_fast` / `search_fast_limited`
is mirroring the F\* semantics, not adding new ones — rule #15 conformance
is preserved (the SEMANTIC decision "skip rgs not containing the bound
predicate" already lives in F\* in `compute_candidate_rgs_loop`; the OCaml
shim merely propagates the same optimisation).

## Approach: Shape A (mirror F\* prune in OCaml shims)

1. In `cottas_ondisk_z_lazy_open.sh`, extend `ensure_predicates_loaded`
   to walk the predicate column per-row-group (instead of the current
   batched `collect_distinct h.coh_path 1`) and record per-rg distinct
   predicate-token sets in a path-keyed mutable Hashtbl
   `pred_presence_by_path : (string, (int, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t`.

2. In `cottas_ondisk_runtime.sh` (or as a follow-up patch), modify
   `search_fast`, `estimate_fast`, and `search_fast_limited` to consult
   the presence table when `bound_p = Some tok`:
   - if rg N is recorded as not containing `tok`, skip rg N entirely
     (don't decode any column).
   - if rg N has no presence entry yet, fall back to walking it (safe).

3. Log per-query rg-skip counts as `[yod6-trace] skipped N/26 rg(s) for
   predicate=...`.

The semantic decision (skip rgs not containing the bound predicate) is
already in F\* in `compute_candidate_rgs_loop` (rg-skip via
`list_string_mem dict bound_token`). The OCaml shim just mirrors it.

## Files to touch

- `formal/fstar/RDF.CottasStore.fst` — add field, plumb prune.
- `formal/fstar/experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh` —
  populate the field during `ensure_predicates_loaded`.
- Subsidiary: places that construct a `cottas_ondisk_handle` need the
  new field (default `[]`).

## Acceptance

- The geosparql-wktLiteral query (3.14M result crash) returns `[]` in <30 s.
- Daemon stays alive after the crash query.
- Predicate-bound LIMIT queries stay fast.
- W3C 1657/1/0/4 unchanged.
- F\* verifies clean — no `--lax`.

## Time-box

3 hours wall-clock.
