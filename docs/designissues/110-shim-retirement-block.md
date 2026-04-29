# Issue #110 retirement — diagnosed block

Branch: `claude/110-retire-dead-cottas-ocaml-shims`
Base: `0da371e Restore 9 dead-on-public-path glue patches + ci-push robustness`

## What was done

1. Deleted the 11 patch files specified in the agent prompt:

   The 9 listed in section A:
   - `cottas_ondisk_zzz_yod6_pred_presence_prune.sh`
   - `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh`
   - `cottas_ondisk_zzzzzzz_mem5_estimate_presence.sh`
   - `cottas_ondisk_zzzzzzzzzz_tet3_fstar_redirect_estimate.sh`
   - `cottas_ondisk_zzzzzzzzzzz_tet3_fstar_redirect_search.sh`
   - `cottas_ondisk_zzzzzzzzzzzz_tet3_fstar_redirect_search_limited.sh`
   - `cottas_ondisk_zzzzzzzzzzzzzz_compound_po_redirect_estimate.sh`
   - `cottas_ondisk_zzzzzzzzzzzzzzz_compound_po_redirect_search.sh`
   - `cottas_ondisk_zzzzzzzzzzzzzzzz_pagecache_hot_path.sh`

   Plus the two re-evaluated as retire-eligible per the prompt:
   - `cottas_ondisk_zz_aleph6_count_limit.sh` — its public-API
     replacement (`cottas_ondisk_estimate` -> `Cottas_ondisk_runtime.
     estimate_fast`) no longer matches because F* `cottas_ondisk_estimate`
     already has the all-None footer fast path inlined; its
     `search_fast_limited` definition is dead with the rest of the
     shim chain.
   - `cottas_ondisk_zzzzz_z_rename_inner_pivot.sh` — only purpose was
     to rename `search_fast`/`estimate_fast`/`search_fast_limited` to
     `*_inner` so the (now-deleted) Mem5 / Tet3-redirect / Lamed3
     patches could anchor on `_inner`. With those patches gone, the
     rename has no consumer.

2. In `experimental_ocaml_glue/cottas_ondisk_runtime.sh`, deleted the
   bodies of the OCaml shim functions and their helpers:
   - `pe4_rss_mb`, `pe4_fd_count`, `pe4_gc_mb`
   - `bound_id_to_token`, `cell_match_str`
   - `search_fast` (entire definition + `walk_rg` / `arr_of_col` /
     `cell_of` inner helpers)
   - `estimate_fast` (entire definition + its inner walk)

   Kept (rule-#11 allowed): `cottas_ondisk_handle` type, `handles`
   Hashtbl, `fast_table_cache`, `tables_for`, `load_handle`,
   `build_handle_and_tables`, `parse_*` token helpers (used by
   `build_handle_and_tables`), `collect_distinct[_graph]`, all the
   `encode_*_fast` / `decode_*_fast` / `predicate_present_fast`
   functions (still referenced by the shim_replacements section that
   substitutes the F* `cottas_ondisk_encode_*` / `cottas_ondisk_decode_*`
   bodies — that retrofit is itself rule-#11 allowed perf glue).

   Updated trailing comment to record the deletion under issue #110.

## Block: Vav3 ondisk-index reader needs Hashtbls defined by deleted patches

The kept patch `cottas_ondisk_zzzzz_ondisk_index.sh` (Vav3 companion
writer + bulk-load reader) references three accessors on
`Cottas_ondisk_lazy`:

```
| 0 -> Cottas_ondisk_lazy.subj_presence_for_path
| 1 -> Cottas_ondisk_lazy.presence_for_path
| 2 -> Cottas_ondisk_lazy.obj_presence_for_path
```

These were defined inside the now-deleted patches:

- `subj_presence_for_path` + `obj_presence_for_path` + the matching
  `*_by_path` Hashtbls — defined in
  `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh` (deleted).
- `presence_for_path` (the predicate-presence variant) +
  `pred_presence_by_path` — defined in
  `cottas_ondisk_zzz_yod6_pred_presence_prune.sh` (deleted).

Build error after extraction + `build-ocaml.sh`:

```
File "RDF_CottasStore.ml", line 3230, characters 15-56:
3230 |         | 0 -> Cottas_ondisk_lazy.subj_presence_for_path
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Unbound value Cottas_ondisk_lazy.subj_presence_for_path
```

(Same unbound-value error would surface for `presence_for_path` and
`obj_presence_for_path` once the first is satisfied.)

These accessors are NOT semantic logic — they are per-path,
per-row-group `(string, unit) Hashtbl.t` presence bitmaps, used by
Vav3's `bulk_load_column_into_tables` to populate them once from the
on-disk `.presence` companion file. The READ side of Vav3 (which is
in F* via `RDF.CottasStore.PresenceBitmap`) is the verified path; the
WRITE/bulk-load side stays in OCaml.

## Why I stopped instead of bridging

Per agent prompt:

> If the build still fails after the obvious deletions, do NOT add
> bridging glue to make it pass. Stop and write the diagnosis to
> `docs/designissues/110-shim-retirement-block.md` and commit + push
> that file alone, leaving the branch in a "diagnosed but not fixed"
> state for main thread to inspect.

Adding the three Hashtbl definitions (`*_presence_by_path` +
`*_presence_for_path`) into `Cottas_ondisk_lazy` inside
`cottas_ondisk_runtime.sh` (or into a new keeper patch) would be the
mechanical fix — they're pure storage cells (rule #11 allowance b /
realisation of an `assume val`-shaped boundary). But it requires a
judgment call about WHERE they live (runtime.sh vs. ondisk_index.sh
vs. lazy_open.sh) and the prompt explicitly forbids that on this
single-commit task.

## Recommended path forward (for main thread)

Option A (smallest delta): move the three accessor + storage
Hashtbl definitions from the deleted yod6/tet3 patches into the head
of `cottas_ondisk_zzzzz_ondisk_index.sh` (Vav3) — the only surviving
consumer — guarded by an idempotency marker. They become Vav3's
private state (read+written by Vav3's bulk-load only).

Option B (cleaner): move them into `cottas_ondisk_z_lazy_open.sh`'s
existing `Cottas_ondisk_lazy` module definition — that module already
owns the per-path "is column N populated yet" flags, so the
per-rg presence bitmaps fit alongside. Same rule-#11(b) status.

Option C (purest): lift the per-rg presence storage to F* and let
Vav3's bulk-load path call into an `assume val` realised by a tiny
companion patch. This is the 2.6 unwind direction, but bigger than
issue #110's scope.

I recommend Option B for the smallest correct delta on this branch.
