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

## Approach: Shape B (F\*-pure prune logic)

1. Extend `cottas_ondisk_handle` with a new field
   `coh_pred_presence : list (nat & list string)` mapping rg_index to the
   list of distinct predicate column-tokens present in that rg.

2. In `populate_dict_cache_for_column`, when col_index = 1 (predicate),
   prefer the handle-resident presence map over re-probing the parquet dict
   page. Specifically: if `coh_pred_presence` is non-empty, use it to
   construct a synthetic per-rg dict; else fall back to the existing
   parquet dictionary probe.

3. Populate `coh_pred_presence` in OCaml glue's `ensure_predicates_loaded`
   (in `cottas_ondisk_z_lazy_open.sh`) by walking the predicate column
   per-rg via `probe_parquet_column_decode_in_row_group` and recording
   each rg's distinct token set. Same total work as `collect_distinct`,
   so no extra cost on cold-boot.

4. The synthetic-dict construction lives in F\* (rule #15 conformance:
   the prune logic is pure F\*; only the populate-from-disk is glue).

## Why Shape B over Shape A

Shape A (OCaml-side prune in `search_fast` / `estimate_fast`) is faster
to ship but adds prune logic to perf shims. Per rule #15 / `feedback_fstar_first_always.md`,
the prune decision should live in F\*. Shape B keeps it there.

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
