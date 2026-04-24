# SPARQL SERVICE — Phase 1 GP_Service wiring plan

Date: 2026-04-25
Agent: Omicron
Goal: dispatch `GP_Service iri p silent` instead of returning `[]`.

## Phase 0 inventory (commit 59c3af3)

`SPARQL.HTTP.Client.fst` has:

- `http_request_msg`, `http_response`, `http_client_error` types.
- `format_request` (HTTP/1.1 request formatter).
- `parse_http_response` (status line + headers + body parser).

Phase 0 does NOT have:

- An `execute(iri, query)` one-shot.
- Any URL parser to split `http://host:port/path` into pieces.
- Any binding from F* to the OCaml socket glue (`perform_request`).

OCaml glue (`ocaml-output/factoidal_http_client.ml`) provides
`perform_request : ~host ~port ~req_bytes -> resp_bytes` but is not yet
exposed as an F* `assume val`.

`Parser.SRX.fst` already has `parse_srx_results` and `parse_srx_boolean`.
Good — that's the response decoder.

## W3C `service` suite: real semantics

All 7 tests use unreachable URIs (`http://example.org/sparql`,
`http://example1.org/sparql`, etc). Manifests bind those URIs to local
TTL files via `qt:serviceData` / `qt:endpoint` / `qt:data`. The W3C
test expectation is that the runner **intercepts** SERVICE requests
to those endpoints and treats the corresponding TTL as the remote
graph store.

So Phase 1 wiring must NOT actually do socket I/O for these tests.
It must be a hookable resolver: `wf_iri -> option graph_store`.
Real socket I/O is for live federation later.

## Design: service-resolver hook

Two-level dispatch:

1. **Local resolver**: `assume val service_endpoint_lookup : wf_iri ->
   Tot (option graph_store)`. Returns a pre-loaded graph_store for any
   IRI registered by the runner. Implemented in OCaml as a global
   hashtable. Pure from F*'s perspective (every call sees the same
   snapshot during one query evaluation).

2. **Remote fallback** (deferred to a future phase): if the resolver
   returns `None` and `silent` is false, error; if `silent` is true,
   return empty bindings. (Spec-correct silent semantics.)

This keeps `eval_pattern_store : Tot solution_sequence`. No `Dv`. No
effect-tracking churn. The W3C tests pass via the resolver because the
runner pre-registers each `qt:endpoint` -> graph mapping.

## GP_Service eval branch (≤25 new F* lines)

```
| GP_Service iri p' silent ->
  match service_endpoint_lookup iri with
  | Some remote_gs ->
    // Evaluate the inner GGP against the remote endpoint's graph.
    // Named graphs from the remote endpoint share the surrounding
    // dataset (matches Jena/Fuseki SERVICE semantics for the
    // common case — refinement deferred).
    eval_pattern_store p' remote_gs dss
  | None ->
    if silent then [] else []  // sentinel parity for now
```

`silent` true vs false handled identically (empty results) at this
phase; the spec wants an explicit error for non-silent unreachable
endpoints, but our existing `solution_sequence` type has no error
case. Deferred to a separate ticket.

## Stub registration

`assume val service_endpoint_lookup : wf_iri -> option graph_store`
gets a default `failwith "Not yet implemented"` from F* extraction.
Patch file `57_service_client_bind.sh` rewrites the body to reference
a global mutable hashtable (`service_endpoint_table`) maintained by
the runner. Patch is glue, not semantics, per rule #10/#15.

## Out of scope

- Live remote SERVICE (real HTTP I/O from inside `eval_pattern_store`).
  Requires `Dv` propagation through the entire algebra evaluator;
  separate refactor.
- SERVICE silent-error sentinel (`solution_sequence` would need an
  error variant or we'd need a sibling type).
- SERVICE federation across multiple endpoints with shared FROM /
  FROM NAMED — currently inner graph is the SERVICE endpoint's
  default graph only.
- BINDINGS / VALUES projection wired into the SERVICE call — works
  by accident for service04a because VALUES sits outside SERVICE.

## Expected pass count

Of the 7 SERVICE tests, with a runner-side resolver registered:
- service01, service04a, service07: should pass (single endpoint,
  simple BGP / VALUES join).
- service02, service03, service05, service06: depend on
  multi-endpoint; pass if runner registers both example1 and
  example2.

Realistic phase-1 outcome: 2-4 of 7 passing once runner registration
is wired (the runner side is a separate commit; this commit only
lands the F* dispatch).
