# kaph2 — issue #100 Phase 2.5: factoidal_http.ml backend wiring

Date: 2026-04-25
Branch: `claude/100-phase2.5-backend-wiring` (parent: `claude/100-phase2-cottas-ondisk` / PR #101)
Author: kaph2 subagent

## Goal

Replace the eager `dataset_ref : rdf_dataset ref` in `factoidal_http.ml` with a
backend-shaped `backend_ref : dataset_backend ref`, so that
`--data-cottas <file>` runs queries through `GB_CottasOnDisk` (Bet4's PR #101)
without materialising a full `rdf_dataset` in RAM.

The `graph_backend` ADT in `SPARQL11.Store.fst` already presents a uniform API
to the engine; the work here is the OCaml plumbing that selects which backend
gets handed to the F\*-extracted evaluator.

## Plan

1. Carry **two** refs side by side:
   - `dataset_ref : rdf_dataset ref` — used by SPARQL UPDATE, by
     `dump_rw_graphs`, and by `/backend-info.json` (counts only).
   - `backend_ref : dataset_backend ref` — used by SELECT/ASK/CONSTRUCT
     queries through the new `eval_*_backend_dataset` evaluators.

   Initially I considered collapsing UPDATE into a backend overlay too, but
   that's a multi-day change (UPDATE only operates on `rdf_dataset` today
   in `SPARQL11.Algebra`'s `apply_update`). Phase 2.5 is plumbing only.

2. Loaders:
   - `--dataset` only → in-memory `rdf_dataset`, wrap with
     `SPARQL11_Store.indexed_dataset_backend` (GB_Indexed for default +
     each named graph). UPDATE keeps mutating `dataset_ref`; on each
     UPDATE we rebuild `backend_ref` from the new dataset.
   - `--data-cottas` only → call `cottas_ondisk_open file` (NOT
     `cottas_open_dataset_store`!), wrap with
     `SPARQL11_Store.cottas_ondisk_dataset_backend`. `dataset_ref` stays
     empty. UPDATE → 501 (cannot mutate read-only on-disk store).
   - Mixed (`--dataset` + `--data-cottas`) → backend is `GB_Union` of
     the indexed in-memory side + the cottas-ondisk side. UPDATE writes
     to `dataset_ref` only and the in-memory half is rebuilt; the COTTAS
     half is unchanged.

3. Query path:
   - `run_query` calls `SPARQL11_Store.eval_select_query_backend_dataset`
     and `eval_ask_query_backend_dataset`, both of which return options
     (None for unsupported forms — fall back is empty rows).

4. Bind-port-first (Mim's #99) preserved: the listener still binds at
   t=0; the COTTAS load happens on the worker thread; the `loading` flag
   gates SPARQL endpoints with 503 until both refs are populated.

## Risks / open issues

- **`compile` step against current branch state**: this branch (PR #101)
  has the F\* updates but the extracted `.ml` has NOT yet been refreshed
  (Yod4 is fixing patches separately). The new
  `eval_select_query_backend_dataset` / `cottas_ondisk_dataset_backend`
  symbols are missing from `SPARQL11_Store.ml`. My `factoidal_http.ml`
  edits compile against the post-extract state. This will be resolved
  when Yod4 + a fresh extract land into PR #101 before merge.
- UPDATE on COTTAS-only is rejected with 501. This was implicitly the
  case anyway (the eager `cottas_open_dataset_store` path materialised a
  copy and any UPDATE only mutated the copy, not the COTTAS file). The
  semantics are now explicit.
- `/backend-info.json`: keeps showing in-memory triple counts. For
  COTTAS-only paths that's "0 default-graph triples" plus the COTTAS
  summary. We could later wire this up to `cottas_ondisk_summary`.

## Files touched

- `formal/fstar/ocaml-output/factoidal_http.ml` — main edit.

Out of scope (Yod4): patch 65, mmap'd page-LRU (Phase 3), persistence.
