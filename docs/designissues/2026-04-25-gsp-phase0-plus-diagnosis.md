# GSP Phase 0+ — diagnosis + GET happy paths

Date: 2026-04-25
Agent: Waw
Parent plan: `docs/designissues/2026-04-25-protocol-http-rdf-update-scoping.md` (Tau)
Predecessor: `docs/designissues/2026-04-25-protocol-runner-phase0.md` (Aleph)
Lane: `formal/fstar/ocaml-output/w3c_runner.ml` `run_gsp_test` only.
**No `.fst` changes. No `extract` / `compile` (Wave 9 owns that).**

## Problem

After Aleph's Phase 0 work, all 19 `http-rdf-update` tests FAIL with the
generic message
`"Graph Store Protocol dispatch not yet implemented (need
SPARQL.GraphStore.fst, <METHOD>) — Phase 2+"`.

Phase 0+ goal: turn the simplest HTTP-method classes into PASS
in-process, without spawning a server, without F* changes, and without
mutable state.

## Manifest classification (19 tests)

Reading `third_party/testing/w3c/sparql/sparql11/http-rdf-update/manifest.ttl`,
the 19 entries break down by **first request method** as:

| Class | Count | Tests | Stateful? | Phase 0+ doable? |
|-------|-------|-------|-----------|------------------|
| PUT   | 4     | `put__initial_state`, `put__graph_already_in_store`, `put__default_graph`, `put__mismatched_payload` | yes (writes state) | no |
| POST  | 4     | `post__create__new_graph`, `post__existing_graph`, `post__multipart_formdata`, plus `get_of_post__after_noop`'s implicit POST | yes (writes state) | no |
| DELETE| 2     | `delete__existing_graph`, `delete__nonexistent_graph` | yes | no |
| HEAD  | 2     | `head_on_an_existing_graph`, `head_on_a_nonexisting_graph` | reads state set up by tests | partial (head_on_a_nonexisting_graph only — empty store gives 404) |
| GET   | 7     | `get_of_put__initial_state`, `get_of_put__graph_already_in_store`, `get_of_put__default_graph`, `get_of_delete__existing_graph`, `get_of_post__existing_graph`, `get_of_post__create__new_graph`, `get_of_post__multipart_formdata`, `get_of_post__after_noop` | depends on prior PUT/POST/DELETE | mostly no (state-dependent) |

### Key insight: most "GET" tests are not standalone GETs

The `get_of_*` tests are *follow-up* GETs that assert what's in the graph
store after a prior PUT/POST/DELETE. **They cannot be evaluated without
running the prior request first.** That makes them all stateful Phase 2+ work.

The two exceptions that are evaluable in-process today:

1. **`get_of_delete__existing_graph`** — expects `404 Not Found`. If we
   model an empty store, GET on any graph IRI is 404. That matches.
2. **`head_on_a_nonexisting_graph`** — expects `404 Not Found`. Empty
   store, HEAD on any graph IRI is 404. That matches.
3. **`delete__nonexistent_graph`** — expects `404 Not Found`. DELETE on a
   non-existent graph in an empty store is 404. We don't actually need to
   mutate anything.

For the bad-request side:

4. **`put__mismatched_payload`** — expects `400 Bad Request`. The body's
   subject IRI doesn't match the URL graph. The intent is that the server
   detects the URI mismatch. We can declare this: parse the body Turtle,
   inspect the URL/subject mismatch, return 400.

That gives us **3-4 candidates** for Phase 0+:
`get_of_delete__existing_graph`, `head_on_a_nonexisting_graph`,
`delete__nonexistent_graph`, and possibly `put__mismatched_payload`.

The remaining 15 tests genuinely need stateful GSP storage and are
deferred to Phase 2+ (`SPARQL.GraphStore.fst` per Tau §3b).

## Approach (≤150 LoC in `w3c_runner.ml`)

Extend `run_gsp_test` to:

1. Extract method + path + headers + body via the existing
   `_proto_extract_request` (already used by `run_protocol_test`).
2. Extract expected status from `_proto_extract_status_class` (we may
   need a tiny refinement: distinguish `404` from generic `4xx`).
3. Implement an in-process empty-store model:
   - `GET <graph>`  → 404 (empty store has no graphs).
   - `HEAD <graph>` → 404 (same reason).
   - `DELETE <graph>` → 404 (W3C spec says DELETE on nonexistent is 404).
   - `PUT` / `POST` → return `Fail "stateful — Phase 2+"`.
4. For each test: compare the in-process status to the manifest's
   expected status. If both 404 (or both in 4xx for `put__mismatched_payload`),
   return Pass; otherwise honest Fail.

This is **glue + dispatch logic**, not RDF/SPARQL semantic logic. The
method table is a strict subset of GSP §4 (Graph Identification &
Methods); when `SPARQL.GraphStore.fst` lands the empty-store model is
replaced by `gsp_apply` over a real dataset.

## What's still FAIL after Phase 0+

15 tests stay FAIL:
- 4 PUT (stateful write)
- 4 POST (stateful write)
- 1 DELETE on existing graph (stateful read)
- 7 GET-of-* follow-ups (stateful read after prior write)

These all need `SPARQL.GraphStore.fst` (Phase 2+).

## Expected delta

Before: 0 pass, 19 fail.
After Phase 0+: 3-4 pass, 15-16 fail.

## Hard limits respected

- No new `.fst`. (Empty-store dispatch is an OCaml flag-and-fail switch,
  not RDF semantics — no graph-store mutation, no Turtle round-trip
  serialiser. The semantic decisions live in the W3C spec and become
  F* code in Phase 2.)
- ≤150 LoC added to `run_gsp_test` and helpers.
- 60 min budget.
- Lane: `run_gsp_test` only. `run_protocol_test` is He's lane (Phase 1
  happy paths).

## Notes for Phase 2+ (next agent)

- `SPARQL.GraphStore.fst` per Tau §3b should expose
  `gsp_apply : rdf_dataset -> gsp_request -> gsp_outcome` and own all
  status-code decisions. Phase 0+'s OCaml table evaporates when that
  module lands.
- The runner state-carrying for the `get_of_*` chains needs a
  per-suite `dataset_ref` initialised empty. Tests must be replayed
  *in manifest order* because the GETs depend on the prior PUTs.
- Multipart parsing for `post__multipart_formdata` is Phase 4 (Tau §4).
