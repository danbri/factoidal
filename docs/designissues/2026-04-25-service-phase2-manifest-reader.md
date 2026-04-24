# SERVICE Phase 2: manifest-reader for `qt:serviceData`

**Agent**: Pi
**Date**: 2026-04-25
**Predecessor**: Agent Omicron — Phase 1 (`77c2969`) wired
`GP_Service` dispatch through `service_endpoint_lookup` and shipped patch
`57_service_client_bind.sh` exposing
`service_endpoint_register : wf_iri -> rdf_graph -> unit`,
`service_endpoint_clear : unit -> unit`, and a `Hashtbl`-backed
`service_endpoint_lookup` in `SPARQL11_Algebra`.

## Goal

Make the W3C SERVICE test runner in
`formal/fstar/ocaml-output/w3c_runner.ml` populate the SPARQL endpoint
table from each test's `mf:action` block before evaluating the query, and
clear the table after. This unlocks the W3C
`sparql11/service/service01..service04a, service06, service07` suites —
service05 uses `SERVICE ?service` (variable endpoint) and stays skipped
until the F* evaluator/parser supports it.

## Manifest shape

```
:service1 mf:action [
    qt:query  <service01.rq> ;
    qt:data   <data01.ttl> ;
    qt:serviceData [
        qt:endpoint <http://example.org/sparql> ;
        qt:data     <data01endpoint.ttl>
    ] ;
] .
```

Multiple `qt:serviceData` siblings are common (service2/3/4a/5).
`qt:` prefix = `http://www.w3.org/2001/sw/DataAccess/tests/test-query#`.

## Plan

1. **`type test_case` (line 199)** — add field
   `service_data : (string * string) list` (endpoint IRI, local TTL path).
2. **`extract_data_and_graphdata` (line 308)** — extend to also return
   the service-data list. Walk every `qt:serviceData` object (must be a
   bnode), follow `qt:endpoint` → IRI string and `qt:data` → local file
   path via `iri_to_local_path`. Return `(df, named, sd)`.
3. **`extract_test_cases` consumer (line 354 + record build at 446)** —
   thread the new list into the record.
4. **`run_query_eval_test` (line 628)** — before query evaluation:
   - For each `(endpoint_iri, ttl_path)` in `tc.service_data`, load the
     TTL via `load_triples` and call
     `SPARQL11_Algebra.service_endpoint_register endpoint_iri triples`.
   - After evaluation (regardless of pass/fail), call
     `SPARQL11_Algebra.service_endpoint_clear ()` so cross-test pollution
     is impossible.
5. **`UpdateEvaluationTest` and other callers of `run_query_eval_test`**
   — only `QueryEvaluationTest` and `CSVResultFormatTest` go through
   `run_query_eval_test`; service tests are exclusively
   `QueryEvaluationTest`. UPDATE has no SERVICE in its grammar.

## Glue, not semantics

The runner's job is to translate W3C manifest data structures into
runtime calls. Zero RDF/SPARQL semantic logic in this change — the F*
evaluator's `eval_pattern_store` for `GP_Service` is what does the work
(landed by Omicron in patched `SPARQL11_Algebra.fst`).

## Expected effect

`service01..service04a, service06, service07` should switch from skip /
fail to pass for the basic federated pattern (single fixed endpoint
IRI). service05 (variable endpoint) stays skipped — needs a parser /
evaluator extension.

## Out of scope (rule #15)

- Live HTTP federation. Phase N+ if ever.
- `SERVICE SILENT` semantics — already handled in F* (Omicron's wiring
  passes `silent` flag through to `service_endpoint_lookup` failure).
- Variable SERVICE endpoint — F* parser doesn't yet emit a variable
  service IRI; out-of-scope for this commit.
