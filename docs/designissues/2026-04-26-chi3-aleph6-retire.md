# Chi3 — Phase 2.4 Aleph6 retire — verification plan and result

**Date:** 2026-04-26
**Subagent:** Chi3
**Phase:** docs/designissues/fstar-purity-unwind.md Phase 2.4
**Status:** GAP identified — patch must NOT be deleted yet

## Plan

1. Inventory `experimental_ocaml_glue/cottas_ondisk_zz_aleph6_count_limit.sh`'s edits.
2. For each edit, confirm whether the F\* source already provides the same
   semantics, and whether the F\*-extracted output is the actual runtime path.
3. If any item is not redundant in the current build, document the gap and
   leave the patch in place.

## Inventory of Aleph6's edits

The patch applies after `cottas_ondisk_runtime.sh` (which replaces
`cottas_ondisk_search` / `_estimate` bodies with calls to the OCaml-side
`Cottas_ondisk_runtime` module) and after `cottas_ondisk_z_lazy_open.sh`
(Bet7, which leaves `coh_subjects_raw` etc. empty and populates a separate
in-memory `Cottas_ondisk_lazy` table set instead). It does three things:

A. Replaces `cottas_ondisk_estimate`'s body again, this time with an
   "all-None bound -> `Parquet_Footer.probe_parquet_num_rows`" fast path
   that bypasses `estimate_fast`. Bound branch falls through to
   `Cottas_ondisk_runtime.estimate_fast`.

B. Defines a new function `Cottas_ondisk_runtime.search_fast_limited`
   (~80 lines of OCaml). Mirrors `search_fast`'s row-group walker but
   stops once `limit` matches accumulate. Uses Bet7's
   `Cottas_ondisk_lazy.ensure_subjects_loaded` /
   `ensure_objects_loaded` to populate the OCaml-side hashtables, then
   uses `Hashtbl.find_opt` for token->id revmap lookups.

C. Replaces F\*-extracted `cottas_ondisk_search_limited`'s body with
   `Cottas_ondisk_runtime.search_fast_limited ds.cods_handle bound (Z.to_int limit)`.

## F\* equivalents

A. `cottas_ondisk_estimate` (RDF.CottasStore.fst:821). The all-None branch
   already calls `probe_parquet_num_rows` (line 841). Confirmed at
   commit `86c7251` and still present in HEAD. **Semantically equivalent.**

B./C. The streaming-COUNT(\*) detector and LIMIT-pushdown machinery in F\*:

- `SPARQL11.Store.fst:416` `detect_streaming_count_star`
- `SPARQL11.Store.fst:435` `count_star_solution`
- `SPARQL11.Store.fst:446` `detect_limit_single_tp`
- `SPARQL11.Store.fst:468` `eval_limit_single_tp` → `backend_search_limited`
- `RDF.CottasStore.fst:711` `filter_zipped_rows_limited`
- `RDF.CottasStore.fst:736` `walk_row_groups_search_limited`
- `RDF.CottasStore.fst:763` `walk_candidate_rgs_search_limited`
- `RDF.CottasStore.fst:794` `cottas_ondisk_search_limited`

All five F\* functions exist with full bodies.

## Why the patch is NOT redundant in the current build

Two reasons:

### 1. cottas\_ondisk\_runtime.sh shadow is still live

The F\* `cottas_ondisk_estimate` body's all-None footer fast path is correct
(line 841: `match probe_parquet_num_rows h.coh_path with | Some n -> n`).
However the wholesale shadow installed by `cottas_ondisk_runtime.sh`
(extracted .ml line 2755..., before this patch applies) replaces that
body with `Cottas_ondisk_runtime.estimate_fast` unconditionally — the F\*
fast-path never runs. Aleph6's edit re-introduces the all-None footer
fast path on top of the runtime.sh shim.

This is fixable only after Phase 2.5 retires `cottas_ondisk_runtime.sh`.
Until then, deleting Aleph6 means COUNT(\*) on parliament's 3.14M-row
corpus regresses from <1s to 100s+ (per the patch header notes).

### 2. F\* `cottas_ondisk_search_limited` calls `id_to_raw_token` on `coh_*_raw`, which Bet7 leaves empty

The F\* body (RDF.CottasStore.fst:794):
```fstar
let bound_s = id_to_raw_token h.coh_subjects_raw   bound.cbqp_s in
...
```

Bet7's lazy-open patch (`cottas_ondisk_z_lazy_open.sh`) populates a
separate `Cottas_ondisk_lazy.ft_id_to_subj_tok` hashtable on demand and
leaves the F\* `coh_subjects_raw` / `coh_objects_raw` lists empty. So if
the F\* `cottas_ondisk_search_limited` body runs, `id_to_raw_token`
returns None for every bound, and the matching/build_qp_row path
returns rows whose s/p/o/g revmap lookups all fail — the result is
**empty** for any query that has bound terms.

The Aleph6 patch's own header says this explicitly (lines 24-27):

> Without this, the F\* implementation walks the parquet using the empty
> `coh_subjects_raw`/`coh_objects_raw` that Bet7's lazy-open leaves
> behind — so build_qp_row's revmap lookups fail for every row and the
> result is empty.

So Aleph6's `search_fast_limited` is not a perf shim; it is also a
correctness workaround for Bet7's invariant violation. It cannot be
deleted until either Phase 2.7 (Bet7 retire) lands, or the F\* code is
modified to consult `Cottas_ondisk_lazy`'s tables instead of
`coh_*_raw`, or Bet7 populates `coh_*_raw` itself.

### 3. Yod6 and Tet3 mutate Aleph6's `search_fast_limited`

`cottas_ondisk_zzz_yod6_pred_presence_prune.sh:91` requires the marker
`'aleph6: search_fast_limited installed'` to be present, and
`cottas_ondisk_zzzz_tet3_subj_obj_prune.sh` similarly extends the same
function. If Aleph6 were deleted, both Yod6 and Tet3 would error and
abort, leaving their pruning logic uninstalled. Phase 2.6 retires
Yod6/Tet3, but until then their dependency on Aleph6's symbol blocks
the deletion.

## Result

**GAP — Aleph6 stays in place.** The F\* implementations exist and match
the OCaml-side semantics, but the patch has three real responsibilities
in the current build:

1. Workaround for `cottas_ondisk_runtime.sh`'s wholesale `_estimate`
   shadow that hides the F\* footer fast-path.
2. Workaround for Bet7's empty `coh_*_raw` invariant violation.
3. Symbol provider for Yod6/Tet3's per-rg prune extensions.

All three are blocked by other unfinished phases (2.5, 2.7, 2.6
respectively). Phase 2.4 cannot land in isolation.

## Recommendation for the planning doc

Phase 2.4 should be re-sequenced to follow Phases 2.5 + 2.6 + 2.7. After
those land, Aleph6's three responsibilities all evaporate and the patch
becomes a true no-op that can be deleted. Alternatively, the F\*
implementation of `cottas_ondisk_search_limited` could be modified to
consult Bet7's hashtables rather than `coh_*_raw`, but that is a Phase
2.7-shaped change.

## What I did NOT do

- Did not delete the patch.
- Did not run extract+compile (no point — the gap is structural, not
  test-discoverable).
- Did not run W3C (no change to runtime path).

LoC retired this phase: 0.
