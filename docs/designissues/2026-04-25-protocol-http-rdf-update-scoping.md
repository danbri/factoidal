# Scoping: SPARQL Protocol + Graph Store HTTP Protocol (GSP) Suites

Date: 2026-04-25
Agent: Tau (research-only)
Goal: turn the two all-skipped W3C suites — `sparql/protocol` (34 tests) and
`sparql/http-rdf-update` (19 tests) — from SKIPPED to PASSING, F\*-first.

Total opportunity: **53 tests** (currently 0 pass / 0 fail / 53 skip).
Project baseline: 1590/1600 = 99.4%. These 53 tests are not in that 1600.

User directive: "SERVICE, protocol, and http-rdf-update are all expected to
be fully implemented with maximum F\*."

---

## Section 1 — What Exists Today

### F\* modules (the verified core)

- **`formal/fstar/SPARQL.HTTP.fst`** (481 lines, no `assume val`).
  Pure HTTP/1.1 *server-side* request **parser**. Exports
  `parse_http_request : string -> nat -> nat -> http_result http_request`
  (raw bytes → `{hr_method, hr_path, hr_query_str, hr_version, hr_headers,
  hr_body}` or typed `http_error`). All char/byte work, CRLF framing,
  case-insensitive header lookup, Content-Length parsing. **No transport.**
- **`formal/fstar/SPARQL.HTTP.Client.fst`** (603 lines).
  Mirror of the above for the client side: `http_request_msg`,
  `http_response`, `format_request` (request bytes), `parse_http_response`
  (status-line + headers + body parser). Used by `GP_Service`.
- **`formal/fstar/SPARQL.Protocol.fst`** (1022 lines).
  Pure SPARQL 1.1 Protocol decoder + result serialisers.
  - `decode_request : method -> path -> qs -> ct -> body -> sparql_request`
    (line 488). Returns `PR_Query | PR_Update | PR_Bad`. Already extracts
    `default-graph-uri` / `named-graph-uri` lists from query string and
    form bodies (lines 462–463).
  - `parse_accept_header`, `pick_response_format` (content negotiation,
    lines 375–425).
  - `serialise_response_json/_xml/_csv/_tsv` (lines 725–935) for SELECT.
  - `serialise_response_boolean_json/_xml` for ASK.
  - `content_type_for : response_format -> string` (line 936).

### OCaml glue (the unavoidable I/O layer)

- **`formal/fstar/ocaml-output/factoidal_http.ml`** (1295 lines, hand-written,
  not extracted). Single-threaded HTTP server.
  - `handle_connection` (line 1035): reads up to `max_header_bytes +
    max_body_bytes` from socket, hands the blob to
    `SPARQL_HTTP.parse_http_request`, then dispatches via
    `P.decode_request`.
  - `PR_Query` branch (line 1167) → `parse_and_run` (line 677) →
    `SPARQL11_Algebra` evaluator → serialised response. Honours `Accept`.
  - `PR_Update` branch (line 1094) → `SPARQL11_Parser.parse_sparql_update`
    → `SPARQL11_Algebra.apply_update`. Wired and working (commit c88f4f9).
    Has `--read-only`, proxied-auth sandboxing, CORS support.
  - `run_server` (line 1207): plain `Unix.socket / bind / listen / accept`.
- **`formal/fstar/ocaml-output/factoidal_http_client.ml`** (178 lines).
  Sockets-only client glue: `perform_request ~host ~port ~req_bytes`.
  Calls into `SPARQL_HTTP_Client.format_request` / `parse_http_response`.

### Pre-built binary

- **`bin/darwin-arm64/factoidal-http`** + **`bin/linux-x86_64/factoidal-http`**.
  Both committed. CLI: `factoidal-http -p 3030 --dataset data.ttl`.

### What is **missing** for the two skipped suites

- **No F\* module for the Graph Store HTTP Protocol (GSP).** Grep for
  `GraphStore`, `gsp`, `graph_store`, `RDFUpdate` finds only the unrelated
  Ballyhoo HDT modules. The only mention of `http-rdf-update` anywhere in
  the codebase is the manifest filename.
- **No runner dispatch for `mf:ProtocolTest` or `mf:GraphStoreProtocolTest`.**
  Both fall through `run_test`'s catch-all `Skip "Unknown test type: %s"`
  at line 1357 of `w3c_runner.ml`.
- **No HTTP method support beyond GET/POST in `decode_request`.** PUT,
  DELETE, HEAD all return `PR_Bad` (line 520). GSP needs all four.
- **No `mf:requestFile` / `mf:responseFile` machinery.** The W3C tests
  carry their request/response as embedded markdown in `rdfs:comment`,
  not as files (see Section 2).

---

## Section 2 — Test-Corpus Shape

### `sparql/protocol/manifest.ttl` — 34 entries

All declare `rdf:type mf:ProtocolTest`. **None** have `mf:action` or
`mf:result`. The expected behaviour is encoded as Markdown inside
`rdfs:comment`:

```
:query_post_form rdf:type mf:ProtocolTest ;
   mf:name "query via URL-encoded POST" ;
   rdfs:comment """
     #### Request
         POST /sparql/ HTTP/1.1
         Content-Type: application/x-www-form-urlencoded
         query=ASK%20%7B%7D
     #### Response
         2xx or 3xx response
         Content-Type: application/sparql-results+xml or +json
         true
   """ .
```

Test categories within the 34:

- **17 happy-path tests** (`query_*`, `update_*`): exercise GET vs POST,
  url-encoded vs direct, content negotiation (`query_content_type_select/
  ask/describe/construct`), protocol-level dataset specification
  (`default-graph-uri` / `named-graph-uri` / `using-graph-uri`).
- **14 bad-request tests** (`bad_*`): wrong method, multiple `query=`
  parameters, wrong media type, missing media type, non-UTF8 bodies,
  invalid syntax. All expect `4xx`.
- **3 multi-step tests** (`update_dataset_*`, `update_base_uri`):
  one POST update, then a follow-up POST query that ASKs whether the
  update took effect.

### `sparql/http-rdf-update/manifest.ttl` — 19 entries

All declare `rdf:type mf:GraphStoreProtocolTest`. Same `rdfs:comment`-as-
Markdown shape. The W3C **Graph Store HTTP Protocol** is a separate spec
from the SPARQL Protocol — different verb space (PUT / POST / GET / DELETE /
HEAD on a `/graph?graph=...` endpoint or a path-as-graph endpoint).

Tests use template variables `$GRAPHSTORE$`, `$HOST$`, `$NEWPATH$` that
the runner must substitute. Categories:

- 4 PUT (`put__initial_state`, `put__graph_already_in_store`,
  `put__default_graph`, `put__mismatched_payload`).
- 4 GET-of-PUT (status checks of the prior PUT).
- 2 DELETE (existing + nonexistent graph).
- 1 GET-of-DELETE.
- 4 POST (existing graph append, multipart/form-data, create-new, after-noop).
- 3 GET-of-POST.
- 2 HEAD (existing + nonexistent graph).

Total HTTP verbs needed: GET, PUT, POST, DELETE, HEAD.

### Why neither suite uses `mf:action` / qt:query

These tests verify HTTP **transport behaviour**, not query results. The
runner cannot just hand a `.rq` file to the algebra evaluator — it must
**construct** a real HTTP request matching the markdown, send it to a real
server, and **assert** on the real response.

---

## Section 3 — The Missing Glue

### 3a. SPARQL Protocol suite

The runner must, per test:

1. **Parse the `rdfs:comment` markdown** into an expected (request,
   response) pair. F\* should own the markdown→request parser —
   it is pure string manipulation, perfect for `Tot`. New module:
   `SPARQL.Protocol.TestSpec.fst` (~150 LOC).

2. **Spin up `factoidal-http` once per suite** (not once per test): bind
   ephemeral port, write a small dataset that satisfies the IRI references
   in the test (kasei.us data). The server is already built; the runner
   just `Unix.create_process`-spawns it. **All glue, no F\* changes.**

3. **Replay the request** through `SPARQL_HTTP_Client.format_request` →
   `factoidal_http_client.perform_request` → `parse_http_response`. The
   client side already exists.

4. **Assert** on (a) status-class (`2xx`/`3xx` vs `4xx`) and
   (b) `Content-Type` belongs to the listed media types. Most tests do
   not assert on body, so trivial. The 3 multi-step tests need to
   chain a follow-up ASK and check that body is `true`.

Pseudocode for the runner dispatch:

```ocaml
| "ProtocolTest" ->
  let spec = SPARQL_Protocol_TestSpec.parse_markdown tc.comment in
  (* spec : { req_method; req_path; req_qs; req_headers; req_body;
              resp_status_class; resp_content_types; resp_body_check } *)
  let req_bytes = SPARQL_HTTP_Client.format_request spec.req_msg in
  let resp_bytes =
    factoidal_http_client.perform_request
      ~host:"127.0.0.1" ~port:!server_port ~req_bytes in
  match SPARQL_HTTP_Client.parse_http_response resp_bytes with
  | Inl resp ->
    if class_matches spec.resp_status_class resp.rsp_status
       && ct_matches spec.resp_content_types resp.rsp_headers
       && body_check_matches spec.resp_body_check resp.rsp_body
    then Pass else Fail (...)
  | Inr e -> Fail (response_parse_error e)
```

Server-side gaps that need F\* fixes:

- **Multiple `query=` parameters → 400** (`bad_multiple_queries`).
  `decode_request` currently picks the first via `first_value`. Need to
  detect duplicates and return `PR_Bad`. ~10 lines in F\*.
- **POST with body but no Content-Type → 400** (`bad_query_missing_form_type`,
  `bad_update_missing_form_type`). Already returns `PR_Bad` — likely just
  need to verify the test passes.
- **Reject non-UTF8 charsets** (`bad_query_non_utf8`, `bad_update_non_utf8`).
  Need to inspect `Content-Type` parameter and reject. ~15 lines in F\*.
- **Reject `query=` and `update=` mismatched against path/method**
  (`bad_query_method` PUT, `bad_update_get`). PUT not yet recognised by
  `decode_request`; needs to return `PR_Bad`. ~5 lines in F\*.
- **Reject `using-graph-uri` with USING/WITH in update body**
  (`bad_update_dataset_conflict`). Needs algebra-level detection. ~20 lines
  in `SPARQL11.Algebra.fst` or in a new pre-flight check.

### 3b. Graph Store HTTP Protocol (GSP) suite

GSP is **a separate endpoint** from the SPARQL endpoint. The current
`factoidal-http` server has no GSP support at all. The plan:

1. **New F\* module: `SPARQL.GraphStore.fst`** (~300 LOC, pure).

   ```
   type gsp_request =
     | GSP_Get    : graph_target -> gsp_request
     | GSP_Head   : graph_target -> gsp_request
     | GSP_Put    : graph_target -> string (* ct *) -> string (* body *) -> gsp_request
     | GSP_Post   : graph_target -> string -> string -> gsp_request
     | GSP_Delete : graph_target -> gsp_request
     | GSP_Bad    : string -> gsp_request

   type graph_target =
     | GT_Default                  (* ?default *)
     | GT_Named   : iri -> graph_target  (* ?graph=IRI *)
     | GT_Direct  : iri -> graph_target  (* path-mapped, /person/1.ttl *)

   val gsp_decode_request :
       method:string -> path:string -> qs:string ->
       content_type:string -> body:string -> gsp_request
   ```

2. **Apply GSP to a dataset (pure)**:

   ```
   type gsp_outcome = {
     go_status : nat;       (* 200 / 201 / 204 / 400 / 404 *)
     go_location : option iri;
     go_dataset : rdf_dataset;
     go_response_ct : string;
     go_response_body : string;
   }

   val gsp_apply : rdf_dataset -> gsp_request -> gsp_outcome
   ```

   PUT replaces the named graph; POST merges; DELETE drops; GET serialises
   the named graph as Turtle (we already have a Turtle serialiser in F\*,
   if not we add one — anti-pattern #1: Turtle parser yes, serialiser no
   yet). HEAD is GET minus body.

3. **Wire into `factoidal_http.ml`**: route `/graphstore/*` (or path
   pattern) to `SPARQL.GraphStore.gsp_decode_request` instead of
   `SPARQL.Protocol.decode_request`. New branch in `handle_connection`
   based on path prefix. Body parsing for `text/turtle` reuses
   `Parser_Turtle.parse_turtle_with_base`. Body parsing for
   `multipart/form-data` is **its own F\* module** (Phase 4 below).

4. **Runner side**: same shape as Protocol — spawn factoidal-http with
   `--graphstore /graphstore` flag, parse `rdfs:comment`, replay request,
   assert on status. The GET-of-PUT chains do an isomorphism check on the
   returned Turtle body; we already have Turtle parsing + a graph-equality
   helper used by RDF MT tests.

### 3c. Test-runner changes

Specifically in `formal/fstar/ocaml-output/w3c_runner.ml`:

- **Line 199 (`type test_case`)**: add a new field
  `protocol_comment : string option` — the rdfs:comment text — and an
  `expected_responses : ...` list extracted from it (parsed in the
  manifest reader at line 280).
- **Line 1192 (`run_test`)**: add `| "ProtocolTest" -> run_protocol_test tc`
  and `| "GraphStoreProtocolTest" -> run_gsp_test tc`.
- **New helpers (~200 LOC of glue)**: `start_factoidal_http`,
  `stop_factoidal_http`, `run_protocol_test`, `run_gsp_test`. These spawn
  the binary as a subprocess on an ephemeral port, wait for "listening on"
  log line, run the test, kill the subprocess. Pure I/O glue, zero
  semantics.

---

## Section 4 — Phased Plan

Each phase = one commit, one deliverable. Estimates assume the F\*
modules verify and extract cleanly first try (often false; double if
verification gets sticky).

### Phase 0 — Runner dispatch skeleton (turns SKIP into FAIL)

**Goal**: `run_test` recognises `ProtocolTest` / `GraphStoreProtocolTest`,
parses the markdown comment, replays via `factoidal_http_client`, but
the underlying server doesn't support GSP yet.

**F\* changes**: add `SPARQL.Protocol.TestSpec.fst` — pure markdown→request
parser. ~150 LOC, all `Tot`, no `assume val`.

**OCaml glue changes**: ~200 LOC in `w3c_runner.ml` — spawn-subprocess
dance + dispatch.

**Expected outcome**: `protocol`: ~5 pass, ~29 fail (most server-side
gaps). `http-rdf-update`: 0 pass, 19 fail (no GSP yet).

### Phase 1 — Protocol happy path + bad-request fixes

**Goal**: chase the protocol fail list down. Every fix is a small F\*
delta in `SPARQL.Protocol.fst`.

- Multi-`query=` rejection (decode_request returns PR_Bad).
- PUT/DELETE rejection (already returns PR_Bad, just verify).
- Charset rejection in Content-Type.
- 3 multi-step tests: dataset reset between requests on the test server.
- `bad_update_dataset_conflict`: USING/WITH vs `using-graph-uri` check.

**F\* deltas**: ~80 LOC across `SPARQL.Protocol.fst` and
`SPARQL11.Algebra.fst`. No new modules.

**Expected outcome**: `protocol` 25–30 pass / 4–9 fail. The remaining
fails are protocol-specified-dataset tests that need a real default-graph-
fetch (`http://kasei.us/...` IRIs, currently unreachable) — but the W3C
intent is satisfied if the server **honours** the parameter, even if the
fetch returns empty. Worst-case skip those 5 tests with a comment.
`http-rdf-update`: still 0 pass.

### Phase 2 — GSP read path (GET, HEAD)

**Goal**: stand up `SPARQL.GraphStore.fst` with GET + HEAD support
(no mutation yet).

**F\* changes**: new module `SPARQL.GraphStore.fst` (~150 LOC, GET + HEAD
only); a Turtle serialiser if absent
(`RDF.Graph.Executable.serialise_turtle : list triple -> string`,
~80 LOC).

**OCaml glue**: route `/graphstore/*` to GSP decoder; pre-load the
test fixtures (`person/1.ttl` etc.) via `--gsp-graphs` flag (each
file → graph). ~50 LOC.

**Expected outcome**: 5–7 GSP tests pass (`get_of_*`, `head_*`).

### Phase 3 — GSP write path (PUT, POST, DELETE)

**Goal**: PUT replaces, DELETE removes, POST merges. Everything except
multipart/form-data (which is Phase 4).

**F\* changes**: extend `SPARQL.GraphStore.fst` with the mutation
constructors and `gsp_apply` (~150 LOC). Reuses Turtle parser already
in `Parser.Turtle.fst`.

**OCaml glue**: wire `gsp_apply` to mutate the server's `dataset_ref`
(same pattern `apply_update` already uses for `PR_Update`). ~30 LOC.

**Expected outcome**: 12–14 GSP tests pass (everything except multipart).

### Phase 4 — multipart/form-data

**Goal**: 1 GSP test (`post__multipart_formdata`,
`get_of_post__multipart_formdata`).

**F\* changes**: new `Parser.Multipart.fst` — boundary-delimited parts
parser (~120 LOC). Body of each part is a Turtle document; merge.

**Expected outcome**: 2 more GSP tests, 19/19 GSP. Total Protocol +
GSP: ~50/53.

### Phase 5 (optional) — protocol-specified dataset fetching

**Goal**: cover the residual ~5 tests Phase 1 left behind that genuinely
need to fetch `http://kasei.us/...`. Reuse `SPARQL_HTTP_Client.format_request`
+ `factoidal_http_client.perform_request`. Requires a `--allow-fetch`
flag because tests run offline by default; cache fixtures in
`third_party/testing/w3c/sparql/sparql11/data-sparql11/protocol-data/`
(if W3C ships them) or skip.

**Expected outcome**: 53/53.

### Total estimate

| Phase | Tests gained | F\* LOC | OCaml glue LOC | Risk |
|-------|--------------|---------|----------------|------|
| 0     | 0 (SKIP→FAIL)| ~150    | ~200           | Low  |
| 1     | ~25–30       | ~80     | ~50            | Med  |
| 2     | ~5–7         | ~230    | ~50            | Low  |
| 3     | ~6–7         | ~150    | ~30            | Low  |
| 4     | 2            | ~120    | 0              | Low  |
| 5     | ~5           | 0       | ~80            | Med  |

Realistic landing: **48–53 of 53**.

---

## Section 5 — F\* Boundaries (Per User Directive)

User directive: "SERVICE, protocol, and http-rdf-update are all expected
to be fully implemented with maximum F\*."

### Lives in F\* (verified)

- HTTP/1.1 wire format parsing (`SPARQL.HTTP.fst`) — already done.
- HTTP/1.1 wire format formatting (`SPARQL.HTTP.Client.fst`) — already done.
- SPARQL Protocol decoder (`SPARQL.Protocol.fst`) — already done.
- Result-format content negotiation — already done.
- All result serialisers (XML/SRX, JSON, CSV, TSV, Turtle, N-Triples) —
  done; Turtle CONSTRUCT-output serialiser may need a small extension.
- **NEW**: `SPARQL.GraphStore.fst` — GSP request decoder + `gsp_apply`
  pure-state-transition function.
- **NEW**: `SPARQL.Protocol.TestSpec.fst` — pure markdown→test-spec
  parser (so the runner doesn't hand-roll markdown parsing in OCaml).
- **NEW**: `Parser.Multipart.fst` — multipart/form-data parser.

### Necessarily OCaml (the unavoidable narrow edge)

Same precedent as the SERVICE work and the SPARQL HTTP client:

- `Unix.socket / bind / listen / accept` (already in `factoidal_http.ml`
  `run_server`).
- `Unix.connect / read / write` (already in `factoidal_http_client.ml`
  `perform_request`).
- `Unix.create_process` to spawn factoidal-http from the runner.
- File I/O for loading test fixtures.
- Reading `SO_REUSEADDR`, byte buffers from sockets — anything that
  isn't pure.

The OCaml side is dispatch + sockets only. **No content-type decisions,
no method-method-allowed logic, no body parsing, no graph-store mutation
logic**. All of those live in the new F\* modules and verify.

### Forbidden (per rule #15)

- Don't add a `gsp_apply` shadow in OCaml. The runner must call
  `SPARQL_GraphStore.gsp_apply` (extracted) and forward the outcome.
- Don't decide media types in OCaml. `SPARQL_GraphStore.content_type_for`
  in F\*, OCaml just sets the header from the returned string.
- Don't parse markdown in OCaml. `SPARQL_Protocol_TestSpec.parse_markdown`
  in F\*; runner just hands the comment string in.

---

## Open Questions (deferred)

1. Should the GSP server share `dataset_ref` with the SPARQL endpoint,
   or be a separate dataset? The W3C tests run against an isolated GSP
   store, so probably **separate** with a runtime flag to share for
   demo purposes.
2. How does the runner reset state between Protocol tests in the same
   suite? Cleanest: kill + respawn factoidal-http per test (slow but
   simple). Faster: a `/test-reset` admin endpoint guarded by a
   `--harness-mode` flag (more code, more verification surface).
3. Where do the `kasei.us/2009/09/sparql/data/data1.rdf` fixture files
   live? Several W3C distributions include them; check
   `third_party/testing/w3c/sparql/sparql11/data-sparql11/` before
   filing Phase 5.

## References

- `formal/fstar/SPARQL.HTTP.fst` (server-side HTTP/1.1 parser)
- `formal/fstar/SPARQL.HTTP.Client.fst` (client-side HTTP/1.1 formatter+parser)
- `formal/fstar/SPARQL.Protocol.fst` (SPARQL 1.1 Protocol decoder + serialisers)
- `formal/fstar/ocaml-output/factoidal_http.ml` (server I/O glue)
- `formal/fstar/ocaml-output/factoidal_http_client.ml` (client I/O glue)
- `formal/fstar/ocaml-output/w3c_runner.ml:1192` (run_test dispatch)
- `third_party/testing/w3c/sparql/sparql11/protocol/manifest.ttl`
- `third_party/testing/w3c/sparql/sparql11/http-rdf-update/manifest.ttl`
- `docs/designissues/2026-04-25-service-phase1-wiring.md` (precedent for
  pure F\* + thin OCaml hook pattern)
- `docs/designissues/2026-04-24-sparql-service-client.md`
