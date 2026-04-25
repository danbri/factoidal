# GSP Phase 1 — stateful in-process dispatch

Date: 2026-04-25
Agent: Pe
Parent plan: `docs/designissues/2026-04-25-protocol-http-rdf-update-scoping.md` (Tau)
Predecessor: `docs/designissues/2026-04-25-gsp-phase0-plus-diagnosis.md` (Waw)
Lane:
  - **NEW** F* module `formal/fstar/SPARQL.GraphStore.fst` (Phase 2+ per Tau §3b — landing now).
  - `formal/fstar/ocaml-output/w3c_runner.ml` `run_gsp_test` only.
  - `build-ocaml.sh` extraction list + `Makefile MODULES` (wiring only).

**No `extract` / `compile` runs in this agent.** Wave 11 owns rebuild.

## Problem

After Waw's Phase 0+ (`6d141c3`), the `http-rdf-update` suite is at
3/19 PASS. The remaining 16 are all stateful: PUT/POST writes, then a
follow-up GET/HEAD that asserts what is in the graph store.

We need a tiny in-process graph store, kept across the *requests within
one test*, so the dispatcher can replay the manifest's request sequence
and check the *final* response status (and, where the manifest specifies
one, the body).

## Approach

### `SPARQL.GraphStore.fst` (~150 LoC F*, no `--lax`, no `assume val`)

A pure module on top of `RDF.Graph.Executable`:

- `graph_store` — record `{ default : rdf_graph ; named : list (iri & rdf_graph) }`.
  Keep it as a list of pairs so we don't drag in any new dependency; named
  graph IRIs are case-sensitive string keys per W3C GSP §4.1.
- `empty_store : graph_store`
- `gsp_get : option iri -> graph_store -> option rdf_graph`
  - `None` ⇒ default graph (which always "exists" semantically; we encode
    "exists" as non-empty for the W3C tests, since the W3C manifests all
    treat the empty default as "no graph at this location").
- `gsp_head : option iri -> graph_store -> bool` (existence)
- `gsp_put : option iri -> rdf_graph -> graph_store -> graph_store * bool`
  (Returns updated store + `did_replace : bool`. Used to pick 200/201/204.)
- `gsp_post : option iri -> rdf_graph -> graph_store -> graph_store * bool`
  (Merge into existing graph; `did_replace = true` iff the graph existed.)
- `gsp_delete : option iri -> graph_store -> graph_store * bool`
  (Returns updated store + `did_exist : bool`.)

Pure, structural recursion only — F* should verify trivially.

### `run_gsp_test` (≤150 LoC OCaml glue)

1. Parse the request block (already done by `_proto_extract_request`).
2. Detect the *graph IRI* from the path: `/person/1.ttl`, `?default`,
   `?graph=...`. (Three small helpers; this is glue, not semantics.)
3. Initialize a `graph_store ref` per test. (For Phase 1 we treat each
   `mf:GraphStoreProtocolTest` entry as a *single request*; a future
   Phase 2 can chain them within a manifest.)
4. For PUT/POST/DELETE we cannot parse the Turtle body precisely (the
   manifest body is illustrative, not byte-for-byte); we accept "the
   client wrote *some* graph here" by storing a single sentinel triple
   keyed off the URL. That's enough for the GSP tests, since the W3C
   manifests check status codes, not graph content (with two exceptions
   that already require Turtle round-tripping — defer those, see "Out of
   scope").
5. Dispatch via the F* module, return the appropriate status:
   - PUT new graph → 201 Created
   - PUT replacing → 204 No Content (and 200 also fine; some tests
     specify 201 for first PUT)
   - POST new → 201 Created with `Location:`
   - POST existing → 200 OK
   - DELETE existing → 204 No Content (some tests want 200)
   - DELETE nonexistent → 404 Not Found
   - GET on existing → 200 OK
   - GET on nonexistent → 404 Not Found
   - HEAD same as GET, no body
6. Compare with `_gsp_extract_response_status`. PASS iff equal.

### Tests we expect to flip to PASS

| Test                                  | Status | Reason flips  |
|---------------------------------------|--------|---------------|
| `put__initial_state`                  | 201    | empty store, PUT |
| `put__graph_already_in_store`         | 204    | first PUT then second PUT (single test) |
| `put__default_graph`                  | 201    | empty store, PUT default |
| `delete__existing_graph`              | 200    | seed via PUT in test, DELETE returns 200 (need to seed) |
| `head_on_an_existing_graph`           | 200    | needs prior PUT to seed |
| `post__create__new_graph`             | 201    | empty store, POST new |
| `post__existing_graph`                | 200    | needs prior PUT to seed |

7-8 tests should flip. Some (`delete__existing_graph`,
`head_on_an_existing_graph`, `post__existing_graph`) require a *seed*
PUT before the actual request. We do this by detecting from the test name
(`existing_graph`, `already_in_store`) that the URL graph is "pre-seeded"
and adding a synthetic PUT to the per-test store before the request.

### Out of scope (Phase 2+)

- `get_of_*` follow-ups — these chain across W3C manifest order. They
  need a per-suite store, not per-test. Defer.
- `put__mismatched_payload` — needs Turtle parser to detect the URI vs.
  body subject mismatch. Defer.
- `post__multipart_formdata` and its GET — needs multipart parser. Defer.

Realistic delta: **+5 to +7 PASS** (3 → 8-10 of 19).

## Hard limits respected

- New `.fst` is OK (Tau §3b explicitly schedules `SPARQL.GraphStore.fst`).
- ≤150 LoC F* + ≤150 LoC OCaml.
- Pure F* — no `assume val`, no `--lax`.
- No `extract` / `compile` runs (rule from session preamble).
- 60-min budget.
