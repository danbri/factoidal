# Tet3 — Subject + Object Presence Pruning (2026-04-26)

## Scope

Mirror Yod6's predicate-presence prune for **subjects** and **objects** in
the on-disk COTTAS backend. Yod6 added a per-rg predicate-token presence
table (`pred_presence_by_path`) populated during `ensure_predicates_loaded`,
and consulted via `pred_rg_could_contain` from `search_fast` /
`estimate_fast` / `search_fast_limited`. With it, queries with absent or
rare bound predicates short-circuit instead of walking all 26 rgs.

For parliament's 908 k distinct subjects + 956 k distinct objects, a bound
subject/object is typically present in only 1-3 of 26 rgs — yet today we
still walk all 26. Tet3 closes that gap.

## Approach

New patch file `cottas_ondisk_zzzz_tet3_subj_obj_prune.sh` (extra `z`
sorts after Yod6). It:

1. Adds `subj_presence_by_path` and `obj_presence_by_path` Hashtbls in
   `Cottas_ondisk_lazy`, each `(path, (rg_index, token_set)) Hashtbl`.
2. Replaces `ensure_subjects_loaded` and `ensure_objects_loaded` to walk
   each rg's column and populate the per-rg presence sets alongside the
   existing global tok_to_id / id_to_subject (object) tables. Same total
   work as the previous batched walk.
3. Adds `subj_rg_could_contain` and `obj_rg_could_contain` helpers.
4. Extends the existing `pred_rg_could_contain` gate in `search_fast` /
   `estimate_fast` / `search_fast_limited` with a conjunctive check on
   subj + obj presence as well.

## Soundness

A rg is skipped only if we definitively know the bound subject (or object,
or predicate) is absent from that rg. Presence sets are built by
enumerating every value in the rg's column at populate time. No new
RDF/SPARQL semantics; this mirrors `compute_candidate_rgs_loop` in F\*.

## Cost

- Boot time +10–20 s (already-walking-the-column work, just records sets).
- RSS +50–100 MB (26 rgs × ~35 k subjs/rg + ~37 k objs/rg).

## Demo expectation

- Bound subject in 1 rg: walks 1 rg instead of 26. `<1 s` instead of ~10 s.
- Bound object absent: short-circuit to `[]` in <50 ms.

## Watchdog

Tet3 scratch checkpoint. Hard timebox 2.5 h.
