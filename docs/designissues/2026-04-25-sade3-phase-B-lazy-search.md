# Sade3 — Issue #100 Phase B: lazy F* search over multi-row-group COTTAS

Date: 2026-04-25
Branch: claude/main
Builds on: 967ed4f (Resh3 Phase A)

## Goal

Migrate `cottas_ondisk_search` and `cottas_ondisk_estimate` from `assume val`
to F* `Tot` definitions in `RDF.CottasStore.fst`, so the on-disk COTTAS
backend lazily walks all 26 row groups (3,143,406 rows) instead of eagerly
loading row-group-0 (122,880 rows) into OCaml `int[]` arrays.

## Problem

After Resh3 Phase A:

- 11/13 lookup fns are F*-pure.
- 2 remain as `assume val` with OCaml glue:
  - `cottas_ondisk_search`
  - `cottas_ondisk_estimate`
- The OCaml glue's `Cottas_ondisk_runtime.load_handle` (in
  `experimental_ocaml_glue/cottas_ondisk_runtime.sh`) calls
  `Parquet_Footer.probe_parquet_column_decode_all` (single-row-group entry
  point) → only sees RG0 → only 122,880 of 3,143,406 rows.
- Open-time builds 4 `int[]` arrays sized 122,880; the daemon then crashes
  silently materialising results of unbounded queries.

## Design

### Open path stays eager-but-shallow

Switch the OCaml glue's `decode_column_strings` to call
`probe_parquet_column_decode_all_row_groups` (which Bet5 added in
`Parquet.Footer.fst:2537`). This walks every row group at open time and
emits the full string list — covering all 3,143,406 rows. The dictionaries
(`coh_subjects` / `coh_predicates` / `coh_objects` / `coh_graphs`) and the
4 revmaps then span the entire corpus, not just RG0.

### Drop the int[] columns

The `columns_bundle { s_ids; p_ids; o_ids; g_ids }` array bundle is removed.
Search/estimate no longer need it. The handle keeps just dictionaries +
revmaps + `coh_path`.

### F*-pure search via per-row-group walk

In `RDF.CottasStore.fst`, replace `assume val cottas_ondisk_search` with a
real `Tot` function:

```fstar
let cottas_ondisk_search (ds : cottas_ondisk_store) (bound : cottas_bound_qp)
  : Tot (list cottas_qp_row)
```

Implementation outline:

1. Use `bound` (already encoded term-IDs from open-time dict). For each
   bound `Some id`, decode it back to its raw column-token string via the
   handle's `coh_*` dictionaries + a new helper `*_to_column_token`. This
   gives an `option string` per column representing "this row's column-N
   raw token must equal this string, OR pass through".
2. Probe row-group count via `probe_parquet_row_group_count`.
3. For each `rg_index` in `[0 .. rg_count)`:
   a. Decode each of the 4 columns via
      `probe_parquet_column_decode_in_row_group`.
   b. Zip into a 4-tuple list.
   c. Filter by string-equality against the column-token bound.
   d. For each match, look up the row's IDs via the existing revmap
      (`revmap_lookup`).
   e. Accumulate (cons) onto the result list.
4. Return result list (in arbitrary order; backend_search doesn't require
   ordering).

For `cottas_ondisk_estimate` we do the same walk but only count matches —
no per-row revmap lookups.

### Why string-comparison, not ID-comparison

- Column strings come from Parquet decode in raw form: `<iri>`, `_:bnode`,
  `"lit"`, `"lit"^^<dt>`, `"lit"@en`, `"DEFAULT"`.
- Dictionary IDs are assigned at open time; same string maps to same ID.
- Re-deriving each row's ID would require revmap_lookup per row × 4 columns
  — O(N · dict_size) on a linked-list assoc-map, far too slow for 3.14M.
- Instead: reverse direction. Encode the **bound** to its column-token
  string (one-shot at search start). Compare each row's strings to the
  bound's string. Only ID-encode the small set of matching rows.

### Termination

`decreases` clause on the row-group fuel parameter, mirroring
`Parquet.Footer.collect_row_group_columns`.

## Helpers added

In `RDF.CottasStore.fst`:

- `subject_to_column_token : subject -> string`
- `iri_to_column_token : iri -> string`
- `object_to_column_token : rdf_term -> string`
- `graph_ref_to_column_token : ds -> option cottas_graph_ref -> option string`
  (None when the bound graph is None; "DEFAULT" semantic handled at row-match)
- `match_row : option string × option string × option string × option string ->
   (string × string × string × string) -> bool`
- `walk_row_group : ... -> Tot (list cottas_qp_row * nat)` — emits matches
  + count for one row group
- `walk_all_row_groups` recursive driver with fuel = rg_count

## Acceptance

- F* `make verify` clean
- `factoidal cottas-info` already shows 3,143,406 (eager path uses
  `_decode_all_row_groups` already)
- Daemon `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }` against
  `--data-cottas <parliament>` returns ?n ≈ 3,143,406 within 60 s
- W3C sweep 1657/1658 preserved

## Out of scope (deferred to Phase C/D)

- mmap of parquet pages
- buffer pool / LRU
- indexed bound predicate prune
- removing the in-memory dictionaries (those are still ~few MB; replacing
  with hash-table revmaps is a Phase C concern)
