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
