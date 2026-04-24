# RDF store indexing — audit + next-moves

Date: 2026-04-24
Status: audit, no code

Task #35. Closes out a lingering item that was asked twice this
week but blocked each time by agent stalls.

## Current state

Patch `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/97_indexed_graph_store.sh`
rewrites the `store_search` function in
`formal/fstar/ocaml-output/SPARQL11_Algebra.ml` post-extraction. It
installs **three** parallel hashtables per graph and selects the
smallest matching bucket:

```
pred_idx : (string,      triple list) Hashtbl.t   key = t.p (IRI string)
subj_idx : (string,      triple list) Hashtbl.t   key = subject_to_key t.s
obj_idx  : (string,      triple list) Hashtbl.t   key = term_to_key   t.o
```

Each graph gets one `_sse_graph_indexes` record cached in a module-level
`SseGraphHashtbl.t`, keyed by physical equality of the `rdf_graph` value.
`store_search` for a `triple_pattern_bound` inspects which positions
have bound values, picks the smallest of the corresponding buckets,
filters the bucket against the remaining pattern constraints.

`find_objects` / `find_subjects` in F\* (`RDF.Graph.Executable.fst`)
are the non-indexed fallback — used by the closure rules (OWL-RL,
RDFS) and anywhere outside the patched `store_search`. They are now
tail-rec (commits `752e7f8`, part of `115d529`).

## What this covers well

- Single-variable BGP lookups with one bound position (S?, ?P?, ??O).
  `store_search` hits the single matching index, filters the bucket.
- Typical Wikidata-scale queries (e.g. `?s wdt:P31 :Human`) are
  predicate-bound or object-bound and hit the right index.
- The earlier stack-blow via `Hashtbl.find_all`'s cons-after-recurse
  (#97 bug) is already fixed — single-binding `(key, list)` shape.

## Where it misses

### 1. Composite-position bound patterns

A BGP like `?s wdt:P31 ?o` picks the pred bucket for `wdt:P31` and
filters linearly. If `wdt:P31` has 60k+ entries, that's 60k
comparisons per triple pattern. Common in Wikidata queries.

**Mitigation:** compound indexes keyed by `(S, P)`, `(P, O)`,
`(S, O)`. The classic triple-store trinity: SPO + POS + OSP covers
all seven non-empty binding patterns in O(1) average plus bucket
traversal.

Cost: O(3N) space per graph (vs O(3N) today for the three single
indexes — roughly doubles memory), zero-cost after the one-time
build.

**Effort estimate**: XS. The existing patch 97 factors bucket-push
+ bucket-pick cleanly; adding three more indexes follows the same
shape.

### 2. No index for named-graph queries

`GRAPH ?g { ?s ?p ?o }` over a dataset with N named graphs today does
the search per-graph, N times. A G-keyed index (or a single global
quad-store index) would make this linear in matches rather than
linear in (N × avg per-graph size).

**Mitigation:** promote the graph-IRI into the key, so the indexes
become `(G, S, P, O)`-keyed — or more practically, a per-graph
Hashtbl keyed by `ng_graph_iri`. Look at quad-store literature
(virtuoso, GraphDB) for standard choices.

**Effort estimate:** S for a simple per-graph index-table lookup; M
if we want to push more deeply into `eval_pattern_with_dataset`.

**Crucially connected to Bucket A**: the 4 failing GRAPH-context
tests diagnosed in
`docs/designissues/2026-04-24-bucket-A-graph-context.md` point at
plumbing issues, not indexing. Fix plumbing first; if it later turns
out the plumbing is slow because of unindexed GRAPH iteration, this
is the follow-up.

### 3. Index is OCaml-only (patch-based)

Per CLAUDE.md rule #10, post-extraction patches are for I/O glue and
stub wiring — not semantic logic. Indexing is arguably semantic (it
affects *how* we answer queries even if not *what* answers we give).
For C extraction via KaRaMeL the patch does not apply; the C binary
would fall back to the F\* list-scan `find_objects` / `find_subjects`
and immediately hit the stack-blow problem we fixed for OCaml.

**Mitigation:** promote patch 97 out of `ocaml-patches.sh` and into
F\*, alongside the equivalent of `SseGraphHashtbl.Make`. F\* supports
`FStar.HashMap` (stdlib) and can model the key/bucket shape directly.

**Complication:** the current physical-equality cache key
(`SseGraphHashtbl` uses `Obj.magic` via `Hashtbl.seeded_hash_param`)
is hard to port — F\* doesn't expose OCaml's physical-equality hash.
We'd need a different caching strategy: probably a monotonically-
increasing version number on the `rdf_graph` record, re-index when
version changes.

**Effort estimate:** L. Worth doing. Tracks issue #97 close-out.

### 4. No incremental maintenance on mutation

INSERT / DELETE operations on a cached-indexed graph today must
invalidate the entire index (the cache lookup by physical equality
misses). For an UPDATE-heavy workload — e.g. a running SPARQL endpoint
receiving writes — every mutation triggers a full re-index.

**Mitigation:** wire `_sse_bucket_push` and a new `_sse_bucket_remove`
into `apply_insert_data` and `apply_delete_data` so the indexes
update in place.

**Effort estimate:** S to implement; **M to verify soundness** — must
guarantee no stale-bucket bugs. Without good test coverage of the
update path this is fraught.

### 5. Query-side BGP re-ordering

`eval_bgp` walks triple patterns in the order the parser emitted
them. Highest-selectivity-first is a well-known perf heuristic
missing today. With indexes in place, re-ordering becomes even more
valuable: start with the pattern whose predicate has the smallest
`pred_idx` bucket.

**Mitigation:** pre-pass over the BGP producing a re-ordered list by
estimated selectivity. `estimate_tp_store_mu` already exists
(line 1760 of `SPARQL11.Algebra.fst`) as the hook.

**Effort estimate:** M. Requires a small cost model. Wins are
workload-dependent.

## Recommended sequence

1. **Short-term: compound indexes (§1).** XS effort, clear perf win
   on the Wikidata-demo query shapes we already ship.
2. **Medium-term: promote patch 97 to F\* (§3).** Unblocks the C
   extraction target without semantic-logic-in-patch-land. Fits with
   the broader `docs/designissues/2026-04-24-c-extraction-plan.md`
   phase work.
3. **Named-graph index (§2).** After Bucket A graph-context threading
   lands; otherwise we risk premature optimisation of code that's
   about to be rewritten.
4. **Incremental maintenance (§4).** Do last, when the
   SPARQL-protocol server sees actual write load and profiling
   surfaces the need.
5. **BGP reordering (§5).** Optional; only after 1+3 show measurable
   gain on hot-path queries.

## Non-goals (now)

- No B-tree / LSM / disk-backed storage. In-memory store is the
  contract.
- No adaptive query optimiser. Cost-based reordering is fine; the
  heavy-artillery DP-style optimiser is not.
- No column-oriented rewrite. We hold triples, not columns.
- No parallel query. Single-threaded is the contract.

## Benchmark hooks we don't yet have

There's no cross-parser-and-query benchmark harness. See
`docs/designissues/turtle-parser-metrics.md` for the one Turtle-
specific rig we built. A Wikidata-scale query benchmark against the
lifesci corpus (already vendored at
`docs/fstar-extracted/lifesci/*.ttl`) would be a useful addition
before making indexing decisions — otherwise we're flying blind.

**Effort estimate:** XS for a "time 10 queries and print a table"
script. S for a proper warm/cold-run comparison.

## Acceptance criteria for this audit

- [x] State of patch 97 documented.
- [x] Gaps enumerated, each with an effort estimate.
- [x] Sequence recommended.
- [x] Tied to existing work-in-flight (Bucket A, C-extraction plan).

This doc closes task #35. Follow-ups get their own issues when the
sequence is acted on.
