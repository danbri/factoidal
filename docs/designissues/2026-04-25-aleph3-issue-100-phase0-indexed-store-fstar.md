# Aleph3 / Aleph4 — Issue #100 Phase 0: F* indexed graph backend

**Status:** complete (one commit by Aleph4 on top of Aleph3's tree edits)
**Started:** 2026-04-25 12:43 (Aleph3)
**Finished:** 2026-04-25 (Aleph4 wiring + patch 97 deletion)
**Scope:** issue #100 Phase 0 only (no Phase 1+ changes)

## Goal

Promote the OCaml-only indexed graph store (post-extraction patch 97) to F*.
Add a `GB_Indexed` constructor in `SPARQL11.Store.graph_backend` whose
`backend_search` consults three F*-side index lookups (predicate / subject /
object) before filtering — same algorithm patch 97 implements in OCaml today,
just F*-verified and extraction-target-portable.

## Design

### Key/value store choice

`FStar.Map` is purely logical (function + set, uses
`FunctionalExtensionality`) — does **not** extract usefully to OCaml.
`FStar.OrdMap` likewise builds on `restricted_t` / `on_dom`.

Project convention is sorted/unsorted association lists with
`List.Tot.assoc` (used in `solution_mapping`, `mu_lookup`, etc.). I use the
same: a `bucket_map = list (string * list triple)` with a tiny lookup helper.
This extracts to a real OCaml `list` of pairs — semantically correct, just
O(n_keys) per lookup. The OCaml runtime can later swap in hashtables via a
small post-extraction patch (similar to patch 95/97), but the algorithm and
correctness story live in F*.

Performance note for Phase 0: even a list-keyed bucket map gives big wins
when the bound-component bucket is much smaller than the full graph. The
"three indexes" plus "pick smallest" logic is identical to patch 97; we
trade O(1) hashtable lookup for O(n_keys) assoc lookup, but the inner
candidate scan is still proportional to the chosen bucket, not the entire
graph. A future patch can swap the assoc list for a hashtable underneath
the same F* signature with no semantic change. Patch 97 stays alive for
the `graph_store` path until that work happens — see Phase 1.

### `indexed_graph` shape

Lives in `RDF.Graph.Executable.fst` next to `rdf_graph`:

```
type bucket_map = list (string * list triple)
noeq type indexed_graph = {
  ig_triples : list triple;     (* source-of-truth *)
  ig_pred    : bucket_map;       (* keyed by predicate IRI string *)
  ig_subj    : bucket_map;       (* keyed by subject_to_key string *)
  ig_obj     : bucket_map;       (* keyed by term_to_key string *)
}
```

Helpers:
- `subject_to_key_opt : subject -> option string` (literals not handled — n/a)
- `term_to_key_opt : rdf_term -> option string` (literals → None; same
  selectivity decision as patch 97)
- `bucket_lookup : bucket_map -> string -> list triple` (assoc, default [])
- `bucket_push : string -> triple -> bucket_map -> bucket_map` (cons-to-front)
- `build_indexed : rdf_graph -> Tot indexed_graph` (one-pass fold)
- `ig_search : indexed_graph -> triple_pattern_bound -> Tot (list triple)`

`ig_search`'s job: pick whichever bound component has the smallest bucket
among (p_bucket, s_bucket, o_bucket), then `triple_matches_bound` filters.
If no component is bound (or none indexable, e.g. only a literal object),
fall back to `ig_triples`.

### `graph_backend` constructor

In `SPARQL11.Store.fst`:

```
| GB_Indexed : indexed_graph -> graph_backend
```

`backend_search` adds a case calling `ig_search`.
`backend_estimate` adds a case calling `List.Tot.length (ig_search ...)`.
`backend_predicate_present` adds a case using a tiny helper.

`list_graph_backend` continues to return `GB_List`, but a new
`indexed_graph_backend : rdf_graph -> graph_backend` returns
`GB_Indexed (build_indexed g)`. Callers can opt in. **For this commit
I won't change the call sites' default** — that's a follow-up after sweep
confirms zero regression.

### Termination

All new functions are `Tot`. `decreases` on the source list / bucket map
length where applicable. No mutual recursion required.

## Files touched

- `formal/fstar/RDF.Graph.Executable.fst` — add `indexed_graph` + helpers.
- `formal/fstar/SPARQL11.Store.fst` — add `GB_Indexed`, dispatch in
  `backend_search` / `backend_estimate` / `backend_predicate_present`,
  add `indexed_graph_backend`.
- `docs/designissues/2026-04-25-aleph3-issue-100-phase0-indexed-store-fstar.md` — this doc.

That's 3 files. No branch needed.

## Out of scope (per issue #100 Phase plan)

- Compound (S,P)/(P,O)/(S,O) indexes — Phase 1.
- mmap'd Parquet reader — Phase 2.
- RLE_DICT / multi-row-group — Phase 3.
- Persistence / INSERT-DELETE incremental maintenance — Phases 4-5.
- Patch 97 deletion — separate follow-up commit.
- Default-callsite migration to `GB_Indexed` — also a follow-up after
  sweep confirms no regressions.
- Hashtable-backed `bucket_map` swap (perf) — small follow-up patch.

## Acceptance

1. `make verify` clean for `RDF.Graph.Executable` + `SPARQL11.Store`.
2. `GB_Indexed g` flowing through `eval_single_tp_backend` returns the
   same triple set as `GB_List g`.
3. Sweep delta after rebuild: 0 (no regression vs current 1656 PASS).

## Notes / mid-flight observations

(filled in as work progresses)

## Aleph4 completion notes

The user redirected the wiring axis: instead of keeping `GB_Indexed`
as a parallel-but-opt-in backend (Aleph3's plan), Aleph4 wired
`indexed_graph` directly into `graph_store` so every `graph_to_store`
call materialises the index. This makes the F* side fully sufficient
and obsoletes post-extraction patch 97.

### Final F* shape (Aleph4)

`SPARQL11.Algebra.fst`:

- `graph_store` now carries both `gs_graph : rdf_graph` (round-trip into
  `store_to_dataset`) and `gs_indexed : indexed_graph` (the lookup
  axis). Lines 140-143.
- `graph_to_store` builds the index up-front: line 156.
- New helper functions `pick_smaller_bucket`, `ig_search`, `ig_estimate`
  (already added by Aleph3) at lines 196-225.
- `store_search` and `store_estimate` reinstated as one-line wrappers
  delegating to `ig_search` / `ig_estimate`, at lines 227-235. Aleph3's
  edit had deleted them; the existing call sites at line 1788/1796
  (`eval_single_tp_store` and `estimate_tp_store_mu`) needed them back.

`SPARQL11.Store.fst`:

- `GB_Indexed` constructor + dispatch is preserved (Aleph3's work).
  This stays useful for callers that already have a built
  `indexed_graph` and want to avoid re-wrapping through `graph_store`.
- `indexed_graph_backend` / `indexed_dataset_backend` exposed for the
  same reason. Lines 41-54.

### Patch 97 deleted

`formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/97_indexed_graph_store.sh`
removed in this commit. Per CLAUDE.md rule #10: when the F* side
subsumes a patch (issue resolved), the patch file goes. The directory
listing now has 14 patches (was 15 with patch 97, now down to 14).

### Verification

`make verify` clean across all five Makefile-listed modules
(`RDF.Graph.Executable`, `SPARQL11.Algebra`, `Tableau`,
`SPARQL.ServiceDescription`, `SPARQL.GraphStore`), plus a separate
`fstar.exe SPARQL11.Store.fst` run. No `--lax`, no
`--admit_smt_queries`. All new functions are `Tot` with `decreases`.

### Sweep prediction

Index is purely physical-layer. Same triples, same set semantics,
just smaller candidate pools. Expected sweep delta vs current
1656 PASS / 2 FAIL = 0.
