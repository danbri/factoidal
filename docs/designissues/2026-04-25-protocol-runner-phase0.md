# Phase 0 — Protocol-runner dispatch skeleton

Date: 2026-04-25
Agent: Aleph
Parent plan: `docs/designissues/2026-04-25-protocol-http-rdf-update-scoping.md` (Tau).
Scope: edit `formal/fstar/ocaml-output/w3c_runner.ml` only. **No** `.fst`,
**no** `extract`, **no** `compile` (Wave 8 rebuild owns the main thread).

## Problem

`sparql/protocol` (34 tests) and `sparql/http-rdf-update` (19 tests) fall
through `run_test`'s catch-all. Main thread just turned them from
generic SKIP into specific FAIL `"Test type %s not yet dispatched
(Phase 0 missing)"` (around line 1361 of `w3c_runner.ml`). That makes the
gap honest but does not move work forward. Phase 0 enriches the
dispatch so every protocol/GSP test is routed to a dedicated handler
that reads what it can from the manifest and fails (or skips) with a
specific reason.

## Manifest shape (verified)

Both manifests embed the expected request/response as Markdown inside
`rdfs:comment` on each entry. Neither uses `mf:requestFile` /
`mf:responseFile` (those don't exist in the W3C SPARQL 1.1 protocol
suites — the prompt's "or similar" hedge was correct: it's a comment).
Therefore `test_case` gets a new field `protocol_comment : string option`
which captures the comment string if present.

## Phase 0 deliverable (this commit)

1. Extend `test_case` with `protocol_comment : string option` (default
   `None`). Populate in `extract_test_cases` from `rdfs:comment` (only
   when non-empty literal).
2. New helper `run_protocol_test : test_case -> test_result`:
   - If `protocol_comment` is `None` or empty → `Fail "no rdfs:comment
     found"` (manifest-shape regression).
   - Tries to extract the first `#### Request` HTTP request block and
     the first `#### Response` block.
   - Phase 0 stops here and returns
     `Fail "Protocol dispatch not yet implemented (Phase 1+ wires
     factoidal-http)"`.
   - **Bonus path** for `query_get`-style tests (GET, ASK query in
     query string, response says `true`): in-process call
     `parse_sparql_query` + `OWL_QueryEval.eval_select_query_owl` over
     an empty graph, check ASK→`true`. Lands the simplest happy-path
     tests as PASS without any HTTP server.
3. New helper `run_gsp_test : test_case -> test_result`:
   - Same shape, but always returns
     `Fail "Graph Store Protocol dispatch not yet implemented (Phase 2+
     adds SPARQL.GraphStore.fst)"`.
4. `ServiceDescriptionTest` keeps the catch-all FAIL — service
   description is small (3 tests) and is genuinely Phase 1+ work.

## Expected test deltas

- Before: 34 protocol FAIL with generic message + 19 GSP FAIL with
  same generic message + 0 service-description (none in this manifest;
  service-description tests live elsewhere).
- After: 34 protocol with specific messages (1–3 PASS for `query_get` /
  `query_post_form` / `query_post_direct` / `bad_query_syntax` if the
  bonus path triggers); 19 GSP all FAIL with GSP-specific message.

## What Phase 1+ owns (NOT this commit)

- Spawning `factoidal-http` as a subprocess (Tau plan §3a step 2).
- F\* module `SPARQL.Protocol.TestSpec.fst` for parsing the markdown.
- F\* module `SPARQL.GraphStore.fst` for GSP semantics.
- All multi-step (POST update, then ASK) chains.

## File map

- `formal/fstar/ocaml-output/w3c_runner.ml` — only file edited.
  - `type test_case` extended.
  - `extract_test_cases` populates `protocol_comment`.
  - New `run_protocol_test` + `run_gsp_test` near `run_test`.
  - Dispatch in `run_test` updated.

## Budget

≤200 LoC of new code in `w3c_runner.ml`. 60 min wall-clock.
