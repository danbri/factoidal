# RDF.CottasStore.PageCache.Bounds.fst — diagnosis (issue #422)

Date: 2026-08-14. Branch: `cottas-bounds`.

## Reproduction

`make verify-RDF.CottasStore.PageCache.Bounds` on a clean checkout of
`origin/claude/main`, zero local diff, fails:

```
fstar.exe --z3version 4.13.3 --cache_checked_modules RDF.CottasStore.PageCache.Bounds.fst
* Error 189 at RDF.CottasStore.PageCache.Bounds.fst(215,35-215,36):
  - Expected expression of type RDF.CottasStore.ColumnSeq.cottas_column
    got expression v
    of type Prims.list (FStar.Pervasives.Native.option Prims.string)
  - See also RDF.CottasStore.PageCache.Bounds.fst(210,38-210,39)

1 error was reported (see above)
```

## Plain-terms explanation

`RDF.CottasStore.PageCache.Bounds.fst` is a bounds-proof module for the
page cache in `RDF.CottasStore.PageCache.fst`. It is absent from
`build-ocaml.sh`'s module list (confirmed by `grep`, see below), so
nothing in CI type-checks it — the same class of gap issue #327
flagged.

The page cache module went through "Phase 2.5c" (issue #118): the
cached value type `pcache_entry.pce_value` changed from
`list (option string)` to the abstract `cottas_column` type (an
array-backed decode result, cheaper to build than a cons list).
`pcache_put`'s third argument changed to match: `v : cottas_column`.

`Bounds.fst` was never updated for that change. Its lemma
`pcache_put_capacity_bound` still declares `v : list (option string)`
(line 210) and its `ensures` clause calls the real `pcache_put cache k
v capacity` (line 215) — but the real `pcache_put` now wants a
`cottas_column` there, not a list. Hence Error 189: the two types
disagree.

The same staleness runs deeper once you fix line 210 and look at the
downstream lemmas:

- `pcache_decode_capacity_bound` (lemma 3, ~line 304-325) calls
  `probe_parquet_column_decode_in_row_group` — the OLD
  `list (option string)`-returning decoder in `Parquet.Footer.fst`.
  The function the real `pcache_decode_in_row_group` (PageCache.fst
  line 174) actually calls is
  `probe_parquet_column_decode_in_row_group_seq`
  (`RDF.CottasStore.ColumnSeq.fst`), which returns `option
  cottas_column`. The lemma is proving a bound using the wrong
  decoder.
- `filter_zipped_rows_limited_bound` / `walk_candidate_rgs_search_limited_bound`
  (lemma 4, ~lines 352-441) are typed over `list (option string)`
  columns and call `filter_zipped_rows_limited` (RDF.CottasStore.fst
  line 2215, explicitly commented "Legacy list-shape (no in-tree
  callers post-2.5c; kept for compat)"). The REAL
  `walk_candidate_rgs_search_limited` (RDF.CottasStore.fst line 2268)
  calls `filter_zipped_rows_limited_seq` instead — a `cottas_column`-
  indexed sibling with an extra `n`/`i` row-window pair, decreasing on
  `n - i` rather than list structure. So lemma 4's `ensures` clause
  names the real walker, but its proof body reasons about a
  compat-only function the real walker does not call. Even after a
  type fix, the proof would not be establishing what its statement
  claims.

## Decision

Category (a): a real bug — the module fell out of sync with the
Phase 2.5c (`issue #118`) `cottas_column` migration because nothing
verifies it. It is not superseded (no replacement bounds module
exists) and it is not a from-scratch WIP (three of its four lemmas are
sound in shape, just typed against the pre-migration API).

Evidence nothing else references this module (safe to fix in place,
no downstream consumers to break):

```
$ grep -rn "PageCache.Bounds" --include=*.fst --include=*.fsti --include=*.sh formal/fstar/ | grep -v "PageCache.Bounds.fst:"
formal/fstar/build-ocaml.sh:999:  # check that identified the dead PageCache.Bounds module, #327). The purge
```

That one hit is a comment in `build-ocaml.sh` recounting issue #327's
history — not a build-list entry or a code reference. No `.fst`/`.fsti`
imports the module, and it is not named in any `build-ocaml.sh` module
list.

## Plan

1. Lemma 1 (`pcache_put_capacity_bound`) + Lemma 3
   (`pcache_decode_capacity_bound`): retype `v` as `cottas_column` and
   switch the decoder call to `probe_parquet_column_decode_in_row_group_seq`.
   Mechanical — the proof structure is decoder-shape-agnostic.
2. Lemma 4: rewrite `filter_zipped_rows_limited_bound` to state the
   invariant over `filter_zipped_rows_limited_seq` (`cottas_column` +
   `n`/`i` window, decreasing on `n - i`), and rewrite
   `walk_candidate_rgs_search_limited_bound`'s proof body to call the
   `_seq` helper the real walker calls, matching the `n = row_group_row_count ...`
   pattern the real walker uses.
3. Verify clean, then decide whether to add the module to
   `build-ocaml.sh` (only if it is added to the verify path AND stays
   green).

This note is committed first per the session's 15-minute-first-commit
rule; the fix (if it lands this session) is a separate commit on this
branch.
