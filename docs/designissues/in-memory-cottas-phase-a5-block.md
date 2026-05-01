# In-memory COTTAS Phase A.5 — block report (2026-04-29)

**Status:** blocked. Bail-out per dispatch instructions: 60-minute timebox
exceeded with no path to <30s Q01. Branch is the empty Phase A.5 head — no
code changes beyond this doc. Recommending a re-scope before another
attempt.

## Where the time was supposed to go (per dispatch prompt)

1. `Cottas_inmem_encoder.encode_to_bytes : rdf_graph -> Bytes.t` producing
   a parquet-shaped buffer (footer + 4 string columns).
2. Patch `parquet_footer_runtime.sh` so `parquet_read_range` / `_tail`
   resolve `inmem://` paths to the registry buffer.
3. Pre-seed the Phase 2.7-mini `ondisk_id_to_*_token_global` tables.
4. CLI dispatch: promote each `--named` graph to an `inmem://` COTTAS store
   when `entail=""` and total triples > 10k.
5. Re-bench Q01.

## Where the time actually went

Mapping the call graph for "Q01 unbound COUNT(*) GROUP BY ?g" through
the existing F* + glue stack and the consequences for the in-memory
shortcut:

* `eval_select_query_backend_dataset` first consults
  `detect_streaming_count_group_by_graph`, which already rejects the
  bench query because of `ORDER BY DESC(?triples)` (rejected by the
  `Some? q.q_modifier.sm_order_by` guard). So the streaming-count
  fast path never fires for the user's literal Q01 — only for an
  ORDER-BY-stripped variant. The "137s → ms" claim in the design note
  is conditional on the detector firing.
* When the detector does fire, it walks `dsb_named` and calls
  `backend_estimate ngb.ngb_graph {bs=None;bp=None;bo=None}` per named
  graph. For `GB_CottasOnDisk cods (Some gname)` this becomes
  `cottas_ondisk_estimate cods bound` with `cbqp_g = Some <id>`, which
  takes the **Mem5 candidate-RG path** (`any_bound_present = true`),
  not the Aleph6 unbound `probe_parquet_num_rows` fast path.
* The Mem5 path calls `plan_candidate_rgs` →
  `candidates_for_one_bound` → `populate_dict_cache_for_column` →
  `probe_parquet_column_decode_in_row_group` → `parquet_read_*`. To
  honour the `inmem://` short-circuit, **every one of those probes
  needs an `inmem://` branch**, not just `parquet_read_range/_tail`.
* The unbound Aleph6 path additionally needs `probe_parquet_num_rows`
  short-circuited.
* The Bet7 lazy populators (`ensure_*_loaded`) call
  `collect_distinct` → `probe_parquet_column_decode_all_row_groups`.
  Inmem stores must mark all four lazy flags pre-loaded so these are
  never invoked — already manageable, but still adds glue surface.
* Token-table population (`ondisk_id_to_*_token_global`) keys off
  `Cottas_ondisk_runtime.handles`; we can pre-seed by registering the
  inmem handle directly. This part is straightforward.

So the realistic Phase A.5 surface is one of:

(a) **Generate real parquet bytes** — full footer + dictionary pages +
    data pages + companion presence-bitmap files matching the existing
    F\* readers. Estimated ~1500–2500 LoC of careful binary layout.
    Aligns with the design note's stated approach but is far larger
    than "1-2 agent runs (encoder + wiring)".

(b) **Patch every parquet probe** in extracted `Parquet_Footer.ml`
    (post-extraction) with `inmem://` short-circuits that consult an
    OCaml-side registry. This bypasses real parquet bytes entirely.
    Touches ~6–8 probe functions plus the `candidates_for_one_bound`
    plumbing. Rule-#11 borderline (pure routing, no semantic
    decisions) but still substantial; needs careful auditing.

(c) **Add a new F\* `GB_InMem` graph_backend variant** with its own
    `inmem_estimate` / `inmem_search` that bypass the COTTAS-on-disk
    path entirely. Reuses `indexed_graph` internals but skips the
    O(N²) `bucket_replace_acc` cost by accepting the perf hit on
    indexes for unbound-count queries. F\*-first per rule #1.
    Estimated 200–400 LoC of F\* + extraction + CLI plumbing.

## Recommendation

**Option (c)** is the cleanest F\*-first play and the smallest
deliverable. Phase A's existing scaffold (`RDF.CottasInMem`,
`cottas_inmem_open : ... -> option cottas_ondisk_store`) is the wrong
shape for the realistic short-term win because it forces every consumer
through the COTTAS-on-disk evaluator, which means honouring the full
parquet probe surface.

Concretely the reshape would be:

* Retire `cottas_inmem_open`'s `option cottas_ondisk_store` return
  type. Replace with a `GB_InMem` constructor in `SPARQL11.Store`
  carrying a precomputed `nat` total + a pre-built `indexed_graph`
  (or a leaner Hashtbl-backed analogue) for bounded queries.
* `backend_estimate (GB_InMem im) {bs=None;bp=None;bo=None}` returns
  `im.total` in O(1).
* `backend_estimate` for bounded variants delegates to
  `ig_estimate im.indexed b` (existing F\* code, no new probes).
* CLI: when entail="" and per-graph triple count > 10k, build a
  `GB_InMem` per named graph instead of `GB_Indexed`.

**Open question** for Dan: is the design note's "in-memory COTTAS"
framing load-bearing (e.g. demoing F\*-verified COTTAS prune on RAM
data) or is it really "we just want Q01 to be fast" (in which case
Option (c) is strictly better — same F\*-first claim, none of the
parquet impedance)? Phase A's framing assumed the former; the bench
target in the dispatch prompt looks like the latter.

## Bench reality check (no code change committed)

Q01 baseline (lifesci, three named graphs, `entail=""`):

```
time bin/darwin-arm64/factoidal -n urn:kgx:chromosome=... -n ... \
     -n ... --query /tmp/q01.rq
```

Reported in PR #131 / dispatch prompt as ~137 s. Not re-measured in this
agent run because no code change to compare against. The block is in the
plan, not in a regression.

## Branch state

`claude/inmem-cottas-phase-a-5` off `f6b1e7f` (PR #133 tip). One commit:
this doc. No changes to F\* sources, glue patches, CLI, or extracted ML.

## Suggested next agent prompt

Re-scope to Option (c): single-commit goal "add GB_InMem backend
variant with O(1) unbound estimate, plumb through CLI, bench Q01
without ORDER BY". Defer the in-memory-COTTAS-bytes exploration to
Phase B/C (after the boundary audit blocks the existing rule-#11
violators) when the parquet probe surface is itself in F\* and
short-circuiting is a one-line F\* change instead of seven post-
extraction shell substitutions.
