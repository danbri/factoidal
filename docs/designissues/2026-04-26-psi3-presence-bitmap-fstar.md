# Psi3 — `RDF.CottasStore.PresenceBitmap.fst` (Phase 2.6 first step)

**Date:** 2026-04-26
**Agent:** Psi3
**Phase:** Unwind 2.6 (per `docs/designissues/fstar-purity-unwind.md`)

## Goal

Establish an F\*-source-of-truth read API for the per-row-group presence
bitmaps that today are consulted only by Yod6 (predicate) and Tet3
(subject/object) OCaml glue patches. Yod6/Tet3 currently mirror, in OCaml
`Hashtbl.t` form, what Vav3 already wrote to disk as `.presence` companion
files (format `COTP`, see `RDF.CottasStore.OnDiskIndex.fst:44-52`). The
Phase 2.6 plan retires the OCaml mirroring; the runtime must consult the
mmap'd bitmap via F\*-pure code.

## What this commit ships

A new module `formal/fstar/RDF.CottasStore.PresenceBitmap.fst` that:

- Re-exports `presence_header` and the existing `presence_test_bit`
  primitives from `RDF.CottasStore.OnDiskIndex` under a focused name
  (`rg_contains_token`).
- Adds typed convenience wrappers — `bitmap_handle`, `open_bitmap`,
  `close_bitmap` — composing Vav3's mmap I/O `assume val`s into a
  one-call API for Yod6/Tet3 callers.
- Defines a soundness predicate `bitmap_built_correctly` and a lemma
  `rg_contains_token_sound` capturing the contrapositive needed for
  prune correctness: if the bitmap was built faithfully, a `false`
  result is a definitive "no row in this rg has that token" — the
  exact invariant Yod6/Tet3's prune relies on.
- The lemma uses `admit ()` because the spec-side ground truth (the
  full quad set per rg) is not yet plumbed; this is documented in
  the source. The lemma's *statement* is what the prune logic relies
  on; the *proof* will be discharged when `RDF.CottasStore.fst`'s
  rg-level row enumeration is exposed in Phase 2.6 follow-up.

The module does NOT modify Yod6 or Tet3 OCaml patches (Rule #11
freeze respected). Migration of those patches to call into this module
is the Phase 2.6 follow-up.

## Phase 2.6 follow-up plan (not in this commit)

1. Yod6: replace `Cottas_ondisk_lazy.pred_rg_could_contain` body with
   a call to `Rdf_CottasStore_PresenceBitmap.rg_contains_token`. Drop
   the `pred_presence_by_path` Hashtbl.
2. Tet3: same for subj+obj.
3. Lamed3 (offset index, separate module `RDF.CottasStore.OffsetIndex.fst`).

After all three migrate, the per-rg presence pre-warm in
`ensure_predicates_loaded` / `ensure_subjects_loaded` /
`ensure_objects_loaded` becomes obsolete (Vav3's writer already
materialises the same data on disk).
