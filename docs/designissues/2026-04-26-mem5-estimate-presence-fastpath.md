# Mem5: estimate_fast presence-bitmap fast path

**Date:** 2026-04-26
**Agent:** Mem5 (subagent)
**Branch:** claude/main

## Problem

`cottas_ondisk_estimate` (extracted as `estimate_fast` in OCaml glue) currently
calls into the per-row-group scan path for every triple pattern in a BGP. For
a 26-row-group corpus (UK Parliament), each pattern costs
26 × ~3 s of column-decode work just to size up cardinality. A 3–6 pattern
modern query therefore eats minutes before the join planner even chooses an
order.

## Approach

Use Yod6 / Tet3 per-rg presence bitmaps already populated by
`ensure_predicates_loaded` / subj-obj equivalents:

- For a triple pattern with at least one bound non-graph term, AND the
  presence bitmaps of the bound terms across all row groups. Cardinality
  estimate = `count_present_rgs * avg_rows_per_rg` (avg from footer).
- Empty AND => return 0 immediately (zero-rg short-circuit).
- Fully unbound `?s ?p ?o` => use footer total (Aleph6 path).

Cost drops from O(num_rgs × column_decode) ≈ seconds to
O(num_rgs × bound_terms) ≈ microseconds. Off-by-2× error is acceptable
(estimate only drives join order; correctness is unaffected).

## Implementation choice

Add an OCaml helper `estimate_fast_via_presence` co-located in
`cottas_ondisk_runtime.sh` and invoked from the existing `estimate_fast`
patched body. F\* signature for `cottas_ondisk_estimate` stays the same;
the OCaml glue inspects its arguments and short-circuits using the
in-memory presence dictionaries that Yod6/Tet3 already maintain. No new
F\* `assume val` is required for v1.

## Smoke target

`tools/sample-queries/ukparliament/main/procedures_main_01_modern.rq`
3-pattern modern query: currently > 25 s, target < 5 s.

## Risk

- If presence bitmaps are missing for a term (cold cache), fall back to the
  existing slow path. Don't pollute the hot path with eager loads.
- avg_rows_per_rg is footer-only; no decode cost.
