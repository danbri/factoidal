# SPARQL 1.1 SERVICE — F* HTTP Client Scoping

Date: 2026-04-24
Status: Phase 0 scoping; client primitives in flight.

## Motivation

SPARQL 1.1 federated query (`SERVICE <iri> { ... }`) requires the
evaluator to dispatch a sub-query to a remote endpoint, receive a
SPARQL Results document, and join the rows back into the outer
solution set. Today `SPARQL11.Algebra.fst`'s `GP_Service iri g silent`
branch is a stub — no HTTP is attempted and all 7 tests in the W3C
`sparql/sparql11/service/` suite report UNMATCHED.

This document scopes the work required to close that gap while
respecting the iron rules in `CLAUDE.md`: F* is the source of truth,
no hand-written semantics in OCaml, and the verified boundary keeps
shrinking (not growing).

## What we already have (server side)

`formal/fstar/SPARQL.HTTP.fst` (commit `0ffa31a`) provides a verified
HTTP/1.1 *request* parser for the SPARQL *service* we host (think
`factoidal_http.ml` serving `/query`). Its shape:

- `noeq type http_request` — record with method / path / query string
  / version / headers / body.
- `type http_error` — typed parse errors (`HE_MalformedRequestLine`,
  `HE_MalformedHeader`, `HE_BadRequest`, `HE_BodyTooLarge`,
  `HE_HeadersTooLarge`, `HE_MissingCRLF`).
- `parse_request_line`, `parse_header_line`, `parse_header_lines`,
  `parse_http_request` — fuel-indexed total functions.
- ASCII-only scanners (`find_2byte`, `find_4byte`, `find_char`,
  `safe_substring`, `string_suffix`, `trim_ws`, `ascii_lower_string`).
- Smoke tests baked in as top-level `_test_*` bindings evaluated at
  extraction time.

The socket I/O (accept, read, write) lives *outside* F\*, in
`formal/fstar/ocaml-output/factoidal_http.ml`. The F\* side is
extraction-ready to C/WASM via KaRaMeL.

## What we need (client side)

A symmetric module, `SPARQL.HTTP.Client.fst`, that produces HTTP
*requests* as byte strings and consumes HTTP *responses*:

- `noeq type http_request_msg` — the message we're going to SEND:
  method, path, query string, headers, optional body.
- `noeq type http_response` — the parsed response: version, status
  code (nat), reason phrase, headers, body.
- `type http_client_error` — mirrors `http_error` for malformed
  responses plus connection-layer errors surfaced from the glue.
- `format_request : http_request_msg -> string` — serialise method +
  path?qs + version + headers + CRLFCRLF + body.
- `format_request_headers : list (string & string) -> string` — helper.
- `parse_status_line : string -> http_result (string & nat & string)`
  — `"HTTP/1.1 200 OK"`.
- `parse_http_response : string -> nat -> nat -> http_result http_response`
  — top-level, mirror of `parse_http_request`.

Total functions, fuel-indexed, no `Dv`, no `assume val`. All the
ASCII-only low-level scanners are reused (either `open`ed from
`SPARQL.HTTP` or duplicated locally if F*'s module graph resists).

## Unverified boundary (glue)

`formal/fstar/ocaml-output/factoidal_http_client.ml` — hand-authored,
small. Responsibilities:

- `socket_connect : host:string -> port:int -> Unix.file_descr`
- `send_all : Unix.file_descr -> string -> unit`
- `read_until_eof : Unix.file_descr -> string` (also honours
  `Content-Length` when present — initial version is the simplest:
  read until the peer closes).
- `perform_request : host:string -> port:int -> req_bytes:string -> string`
  — open, send, read, close. Returns the raw response buffer to be
  handed to the F\* parser.

No TLS. HTTPS endpoints are a Phase 5 concern (requires either
`ocaml-tls`, `ssl`, or shelling out to curl — TBD).

## Phased plan

- **Phase 0 — client primitives**: land `SPARQL.HTTP.Client.fst` with
  types, request formatter, response parser, smoke tests. Land
  `factoidal_http_client.ml` glue with `socket_connect` / `send_all` /
  `read_until_eof` / `perform_request` and an env-var-guarded smoke
  ping. Update `build-ocaml.sh` to extract the new module and include
  the glue in `COMMON_MODULES`. *(This commit.)*
- **Phase 1 — glue wiring into the runner**: expose a simple
  `sparql_remote_query : iri:string -> query_body:string -> string`
  in the OCaml glue that takes a URL, POSTs the form-encoded query,
  and returns the raw SRJ body. Runner only; no `SPARQL11.Algebra.fst`
  touches yet.
- **Phase 2 — SSE-to-POST integration**: serialise the inner pattern
  `g` of `GP_Service iri g silent` as a SPARQL SELECT query using the
  existing `sse_*` family (check `SPARQL11.Parser.fst`). Form-encode
  and dispatch through Phase 1 glue.
- **Phase 3 — SRJ response parsing**: route the response body through
  `Parser.JSONResults.fst`, convert rows to solution mappings (the
  SPARQL algebra's `solution_mapping` type).
- **Phase 4 — `GP_Service` join**: wire the decoded rows into
  `eval_pattern`. Honour `silent` by swallowing errors as empty
  solutions. Add W3C `service/` suite to the runner's routine pass.
- **Phase 5 — HTTPS**: pick a TLS path (ocaml-tls is the cleanest; the
  curl shell-out is a stopgap). Keep the F\* contract unchanged.

## Hard constraints

- **Termination**: every F\* function is `Tot` with an explicit
  `decreases`. Response parser uses fuel = buffer length + 1, same
  pattern as the server.
- **No `Dv` effect**: all I/O lives in the OCaml glue. The F\* side
  is pure string-in / string-out.
- **C-extraction-ready**: avoid `noeq` in types that need KaRaMeL; if
  we cannot avoid it, accept OCaml-only extraction as Phase 0 (same
  position as the server today) and revisit with the Parser.JSONResults
  C-extraction work.
- **CLAUDE.md rule #10**: the glue file contains zero RDF/SPARQL
  semantics. It is literally socket open / send / read / close. All
  decisions about how a SPARQL SERVICE call is shaped live in F\*.
- **CLAUDE.md rule #13**: never hand-edit `ocaml-output/*.ml` that is
  produced by extraction. The new glue file is *hand-authored* and
  is a sibling of `factoidal_http.ml`; it is not produced by
  extraction, so rule #13 does not apply to it.
- **No `--lax`, no `admit()`**.

## Open questions (deferred to later phases)

- How do we identify the endpoint from the IRI `iri`? Parse with
  `Parser.IRI` + `RFC3986_*` helpers; extract host/port/path. Phase 2.
- What do we do with `silent`? Empty solution mapping set with no
  variables bound, per spec. Phase 4.
- Chunked transfer encoding? Assume `Content-Length` or
  connection-close for Phase 0. Chunked is a Phase 3/4 concern if it
  trips W3C suite.
- Response size cap? Mirror `max_body_bytes` from the server; default
  16 MiB to start.

## References

- `formal/fstar/SPARQL.HTTP.fst` — server-side parser (template).
- `formal/fstar/ocaml-output/factoidal_http.ml` — server-side I/O glue.
- `formal/fstar/SPARQL11.Algebra.fst` — `GP_Service` stub site.
- `formal/fstar/Parser.JSONResults.fst` — SRJ decoder for Phase 3.
- W3C: <https://www.w3.org/TR/sparql11-federated-query/>
- W3C: <https://www.w3.org/TR/sparql11-protocol/>
