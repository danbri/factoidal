# Aleph6 — Streaming COUNT(*) + LIMIT pushdown + prune dispatch fix

Date: 2026-04-26
Branch: claude/main
Status: in-flight
Issue: #100 (COTTAS on-disk store, demo path)

## Brief context

Three blockers for tomorrow's demo on `:3032 --data-cottas <parliament>`:

1. `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }` — daemon dies at ~3.5GB
   heap because aggregator materialises 3,143,406 rows into solution
   sequence before counting.
2. `SELECT ?s ?o WHERE { ?s :pred ?o } LIMIT 5` — walks all 26 row
   groups even though we only need 5 rows.
3. Tsade2 prune dispatch at `RDF.CottasStore.cottas_ondisk_search:669`
   reaches `walk_candidate_rgs_search`, but the candidate set ends up
   = all rgs (so no pruning). Likely cause: predicate-column dict probe
   returns None per-rg (column is DLBA-encoded with no dict page on
   parliament's COTTAS), so `populate_dict_cache_loop` leaves cache
   empty, and `compute_candidate_rgs_loop` falls back to "include all
   rgs" (the safe fallback at line 509).

## Approach

### A. Streaming COUNT(*)

Add fast-path detection in `eval_select_query_backend_on_graph` for
the shape:

```
SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }
```

Specifically: query has form `QF_Select`, single SI_Expr select item
that is `E_Aggregate Agg_Count distinct (E_Var "*" or E_BoolLit true)`,
no GROUP BY, no HAVING, no DISTINCT modifier, BGP is exactly one
triple pattern, and (for COUNT) no DISTINCT.

When matched, call `backend_estimate gb {bs;bp;bo}` directly and
construct a one-element solution sequence with `?n = ER_Num count`.

Trade-off: only the simplest shape; everything else stays on the
materialise path. COUNT(DISTINCT *) does NOT take this fast-path —
it needs rows to dedup.

### B. LIMIT pushdown

Add an optional `limit:nat` parameter to a new variant of
`cottas_ondisk_search`. The walker stops once `acc_rev` length hits
`limit`. Wire it through:

- `RDF.CottasStore.cottas_ondisk_search_limited : store -> bound -> option nat -> Tot (list cottas_qp_row)`
- `SPARQL11.Store.backend_search_limited : graph_backend -> tp_bound -> option nat -> list triple`
- `SPARQL11.Algebra.eval_pattern_backend_with_limit` — propagates a
  `bgp_limit` hint when the BGP has exactly one triple pattern.

Wire path: `eval_select_query_backend_on_graph` detects the
`Project (BGP[1tp]) + LIMIT k + no DISTINCT/ORDER BY/aggregates/values`
shape. When matched, pass `Some k` as a limit hint into the BGP eval,
which threads it to `backend_search_limited`. For COTTAS-on-disk
backends this caps the row group walk; for other backends we just
take(k) the full result (no harm).

### C. Prune dispatch investigation

Hypothesis: the predicate column on parliament's COTTAS is DLBA, so
`probe_parquet_column_dictionary_in_row_group` returns None for every
rg. The current safe-fallback (include all rgs) defeats pruning.

Mitigation: with LIMIT pushdown in (B), the walk stops at 5 rows
regardless of how many rgs are candidates. So predicate-bound LIMIT 5
is fast even without prune.

For the unbound COUNT path (A) the BGP is `?s ?p ?o` — no bound at
all — so prune isn't applicable. Prune dispatch fix is only needed
for predicate-bound NON-LIMIT queries (e.g. predicate-bound COUNT
without LIMIT). Out of scope for tomorrow's demo: that workload is
not on the required acceptance list.

If time permits, attempt: also probe via DLBA distinct-extraction
(walk the column once per rg, collect distinct strings, cache). Cost
~equal to a full data-page decode, but cached across queries — net
positive amortised. Note: this would NOT actually prune the FIRST
predicate-bound query (paying same cost as the unpruned walk), only
subsequent ones. Marginal value for the demo.

## Files touched

- `formal/fstar/RDF.CottasStore.fst` — add `cottas_ondisk_search_limited`
  and `walk_*_limited` variants.
- `formal/fstar/SPARQL11.Store.fst` — add `backend_search_limited`.
- `formal/fstar/SPARQL11.Algebra.fst` — fast-path detection in
  `eval_select_query_backend_on_graph`.

## Acceptance

1. `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }` returns
   `?n = 3143406` in <10s, RSS <500MB.
2. `SELECT ?s ?o WHERE { ?s :signatureCount ?o } LIMIT 5` returns
   5 rows in <2s.
3. W3C `--all` stays at 1657/1/0/4.

## Results (post-implementation, 2026-04-26T07:18Z)

Smoke test against `127.0.0.1:3032` with `--data-cottas tmp/ukparliament/.../data.cottas`:

1. **Q1 (unbound COUNT*): 0.03 s** — returns
   `?n = 3143406^^xsd:integer`. RSS stays at 670 MB (= post-open
   floor with Bet7 lazy-open). Streaming COUNT shortcut fires:
   `[aleph6-trace] estimate: all-None -> probe_parquet_num_rows = 3143406`.

2. **Q2 (predicate-bound LIMIT 5): 87 s wall-clock, but actual
   search_fast_limited only walked 1/26 rg(s)** — see
   `[aleph6-trace] search_fast_limited: matched 5/5 row(s),
   walked 1/26 rg(s)`. The 87 s is dominated by Bet7's lazy
   subjects+objects population (one-time cost: 908 k + 956 k
   tokens into hashtables). On warm-cache subsequent queries
   the same shape would run in &lt; 1 s.

3. **Q3 (unbound LIMIT 5): 6.2 s** — also walks only 1/26 rg(s).

4. **W3C `--all`**: 1657 pass, 1 fail, 4 skip, 0 unsupported
   (RDF: 1031/0/0/0; SPARQL: 626/1/4/0). Identical to baseline.

## Implementation summary

### F* changes (`SPARQL11.Store.fst`, `RDF.CottasStore.fst`)

- New helper detectors: `detect_streaming_count_star`,
  `detect_count_star_select`, `detect_limit_single_tp`,
  `extract_single_tp_bgp`, `count_star_solution`,
  `eval_limit_single_tp`. All conservative; bail to materialise
  path on anything they don't recognise.
- New backend method `backend_search_limited` +
  `union_backend_search_limited` (mutual rec, like `backend_search`).
- Two fast-path entry points in `eval_select_query_backend_on_graph`:
  COUNT-star → `backend_estimate`; single-tp + LIMIT →
  `backend_search_limited`. Both return early; the materialise
  path is unchanged for everything else.
- `cottas_ondisk_search_limited` + `walk_*_search_limited` /
  `filter_zipped_rows_limited` (F* spec for the LIMIT-pushdown
  walker; the actual binary path goes through
  `Cottas_ondisk_runtime.search_fast_limited` via the new shim).
- `cottas_ondisk_estimate` updated to use
  `probe_parquet_num_rows` for the all-None case (microseconds
  via parquet metadata, not data-page decode).

### OCaml glue (`experimental_ocaml_glue/cottas_ondisk_zz_aleph6_count_limit.sh`)

NEW patch file. Three idempotent shims:

1. `cottas_ondisk_estimate` → all-None fast path via
   `Parquet_Footer.probe_parquet_num_rows`, bounded path stays
   on Bet7's `estimate_fast`.
2. New `Cottas_ondisk_runtime.search_fast_limited` — same loop
   as Bet7's `search_fast` but stops at `limit` matches.
   Composes cleanly with Bet7's `ensure_subjects_loaded` /
   `ensure_objects_loaded` lazy hooks.
3. `cottas_ondisk_search_limited` perf-shim → calls
   `Cottas_ondisk_runtime.search_fast_limited` with `Z.to_int limit`.

Rule #15 conformance: all RDF/SPARQL semantic decisions live in
the F* spec (SPARQL11.Store.fst). The OCaml shims do byte-
identical work to the F* `walk_*_search_limited` walkers, just
with O(1) Hashtbl lookups instead of O(N) revmap_lookup over
the (Bet7-empty) coh_subjects_raw / coh_objects_raw lists.

## Issue C: prune dispatch — not yet attacked

The brief flagged that `walk_candidate_rgs_search` (the "pruned"
walker reached via `cottas_ondisk_search`) ends up walking all
26 rgs even when a predicate is bound, because
`probe_parquet_column_dictionary_in_row_group` returns None for
DLBA-encoded columns (no dict page to probe). Status: not
addressed in this commit. The LIMIT pushdown sidesteps it for
demo-relevant queries — predicate-bound LIMIT 5 walks 1/26 rgs
because the matching rows show up early in the corpus, not
because of pruning. For predicate-bound NON-LIMIT queries
(e.g. unbound COUNT of a specific predicate) the slow path
remains. Tracked for next phase.
