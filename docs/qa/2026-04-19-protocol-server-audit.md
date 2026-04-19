# factoidal-http — SPARQL 1.1 Protocol Server Audit

**Date:** 2026-04-19
**Binary under test:** `bin/darwin-arm64/factoidal-http` (from commit `b4e9fff`)
**Auditor:** read-only subagent, auto mode
**Method:** spawned the server once against a tiny Turtle fixture, ran the
full curl matrix below, killed with SIGTERM, analysed responses. No source
was modified.

## Test bed

```
./bin/darwin-arm64/factoidal-http \
    -p 3030 \
    --dataset tests/w3c/rdf/rdf11/rdf-turtle/prefix_only_IRI.ttl \
    -v &
```

Dataset is a single triple:

```
<http://a.example/s> <http://a.example/p> <http://a.example/o> .
```

Server startup log reported **1 triple loaded**. All curl calls hit
`127.0.0.1:3030`.

Full server access log:
`/Users/danbri/working/factoidal/.claude-runs/http-audit-20260419.log`.

## Results matrix

| # | Test | Request | Status | Size | Content-Type | Notes |
|---|------|---------|--------|------|--------------|-------|
| 2 | Basic GET | `GET /query?query=SELECT * WHERE {?s ?p ?o}` | 200 | 202 | `application/sparql-results+json` | 1 binding row. OK. |
| 3 | POST sparql-query (direct) | `POST /query` + `Content-Type: application/sparql-query` | 200 | 202 | `application/sparql-results+json` | OK. |
| 4 | POST urlencoded | `POST /query` + `Content-Type: application/x-www-form-urlencoded` with `query=…` | 200 | 202 | `application/sparql-results+json` | OK. |
| 5a | Accept SRX | `Accept: application/sparql-results+xml` | 200 | 366 | `application/sparql-results+xml` | OK. |
| 5b | Accept CSV | `Accept: text/csv` | 200 | 65 | `text/csv` | OK. Columns `o,p,s`. |
| 5c | Accept TSV | `Accept: text/tab-separated-values` | 200 | 72 | `text/tab-separated-values` | OK. Header `?o\t?p\t?s`, IRIs wrapped in `<>`. |
| 5d | Accept JSON explicit | `Accept: application/sparql-results+json` | 200 | 202 | `application/sparql-results+json` | OK. |
| 5e | Accept `*/*` | `Accept: */*` | 200 | 202 | `application/sparql-results+json` | Fallback to JSON. OK. |
| 5f | Accept `application/xml` | `Accept: application/xml` | 200 | 366 | `application/sparql-results+xml` | **Surprise:** server returns SRX. Reasonable by family match (`+xml`), but not RFC 7231 strict. See below. |
| 6a | ASK true (JSON) | `ASK {?s ?p ?o}` | 200 | 26 | `application/sparql-results+json` | `{"head":{},"boolean":true}`. OK. |
| 6b | ASK true (SRX) | same, `Accept: application/sparql-results+xml` | 200 | 122 | `application/sparql-results+xml` | `<boolean>true</boolean>`. OK. |
| 6c | ASK false | `ASK { <http://nope/> <http://nope/> <http://nope/> }` | 200 | 27 | `application/sparql-results+json` | `{"head":{},"boolean":false}`. OK. Confirms the ASK-evaluation fix from commit `00c1a7b` ships in this binary. |
| 7 | CONSTRUCT, no Accept | `CONSTRUCT {?s ?p ?o} WHERE {?s ?p ?o}` | 200 | 46 | `application/sparql-results+json` | **BUG**: returned `{"head":{"vars":[]},"results":{"bindings":[]}}`, i.e. an *empty SPARQL-results document*. CONSTRUCT should return an RDF graph in an RDF media type (e.g. `text/turtle`). The help text does disclose that CONSTRUCT is a stub. |
| 7b | CONSTRUCT, `Accept: text/turtle` | as #7 + `Accept: text/turtle` | 200 | 46 | `application/sparql-results+json` | **BUG**: Accept header ignored; server still returns empty sparql-results JSON. Should 406 or return (empty) Turtle. |
| 8a | Missing `query` param | `GET /query` | 400 | 24 | `text/plain` | `missing query parameter`. OK. |
| 8b | Empty `query` | `GET /query?query=` | 400 | 65 | `text/plain` | `SPARQL parse error: expected SELECT, ASK, CONSTRUCT, or DESCRIBE`. OK. |
| 8c | Malformed SPARQL | `GET /query?query=SELECT NONSENSE` | 400 | 46 | `text/plain` | `SPARQL parse error: expected select variables`. OK. |
| 8d | Wrong path (no query) | `GET /sparql` | 400 | 24 | `text/plain` | **Deviation:** 400 + `missing query parameter`. Should be 404. |
| 8d-2 | Arbitrary path (no query) | `GET /totally-random` | 400 | 24 | `text/plain` | Same as 8d. Server ignores URL path entirely on GET. |
| 8d-3 | Wrong path *with* query | `GET /sparql?query=…` | 200 | 202 | `application/sparql-results+json` | **BUG**: responds as if it were `/query`. URL path is not being enforced. |
| 8e | Wrong method | `PUT /query` | 400 | 29 | `text/plain` | `unsupported HTTP method: PUT`. Should be **405** with `Allow: GET, POST`, not 400. Minor RFC-7231 deviation. |
| 8f | POST `/update` | `POST /update` + `Content-Type: application/sparql-update`, body `INSERT DATA { <http://a.example/new_s> <http://a.example/new_p> <http://a.example/new_o> }` | 501 | 108 | `text/plain` | `SPARQL UPDATE execution is not yet implemented. Stage 1 of factoidal-http only supports query (SELECT/ASK).` See "deferred" below. |
| 8f-2 | Verify mutation | `GET /query?query=SELECT *` after 8f | 200 | 202 | `application/sparql-results+json` | Still exactly one triple. Confirms UPDATE was a no-op (as 501 promised). |
| 8g | Large query | POST urlencoded, ~5.6 KB body with 200-var OPTIONAL | 200 | 11582 | `application/sparql-results+json` | OK. No documented body-size limit hit. |
| 9 | Concurrency (3 parallel) | SELECT \*, ASK, SELECT COUNT(\*) | 200 × 3 | 202 / 26 / ~100 | JSON × 3 | All three got correct, distinct responses. No cross-talk. Server log shows them at the same second, so connection handling is at least safely serialised. |
| 10 | SIGTERM | `kill -TERM $PID; wait` | — | — | — | Exited cleanly, port 3030 freed, no core dump. |

## What works

- All three query transports (`GET`, `POST sparql-query`, `POST urlencoded`).
- All four SPARQL-results media types: JSON, SRX, CSV, TSV. The per-format
  output bodies match what the native `factoidal -o <fmt>` path produces.
- `Accept: */*` correctly falls back to JSON (per spec default).
- ASK queries — both `true` and `false` — return the correct
  `{"head":{},"boolean":…}` document and its SRX equivalent. The ASK fix
  from commit `00c1a7b` is in this binary.
- 400s are returned for missing `query`, empty `query`, and malformed SPARQL,
  all with human-readable `text/plain` error bodies that include the
  parser's diagnostic.
- 501 is returned for UPDATE, with a body explaining the stage-1 limitation.
  The 501 is honest — no silent partial mutation observed (follow-up SELECT
  confirmed the graph was unchanged).
- ~5.6 KB POST body handled without issue, response ~11.6 KB.
- 3 concurrent requests all returned correct, distinct responses (no
  cross-talk, no truncation).
- Clean shutdown on `SIGTERM`; port released.

## Bugs found (in priority order)

1. **CONSTRUCT returns empty sparql-results JSON instead of an RDF graph.**
   `CONSTRUCT {?s ?p ?o} WHERE {?s ?p ?o}` against a non-empty graph
   returned `{"head":{"vars":[]},"results":{"bindings":[]}}` at
   `Content-Type: application/sparql-results+json`. Per SPARQL 1.1 Protocol,
   CONSTRUCT must return an RDF graph in an RDF media type (`text/turtle`,
   `application/n-triples`, `application/rdf+xml`, `application/n-quads`).
   Both the *body format* and the *Content-Type* are wrong here. The help
   text does say "CONSTRUCT/DESCRIBE return empty results (evaluator
   stub)", but the stub is emitting a *solutions* document, not an (empty)
   *graph* document — wrong document class.

2. **`Accept: text/turtle` is silently ignored on CONSTRUCT.** Same request
   as #1 but with `Accept: text/turtle` still produced
   `application/sparql-results+json`. Should 406 or honour the Accept.

3. **URL path is not enforced.** `GET /sparql?query=…`, `GET /totally-random
   ?query=…`, and any other path are all handled as if they were `/query`.
   `POST /update` does dispatch to the update path (it 501s there), so
   `/update` is recognised, but GET routing treats every path as `/query`.
   A client sending `GET /admin?query=…` gets a full query response,
   which is surprising and non-conformant.

4. **PUT returns 400, not 405.** `PUT /query` should be `405 Method Not
   Allowed` with an `Allow: GET, POST` header (RFC 7231 §6.5.5). The
   server currently returns `400 Bad Request`.

5. **`Accept: application/xml` returns SRX.** Not strictly wrong (SRX *is*
   XML), and `application/xml` is a superset media type, but a strict
   Protocol client might expect `406 Not Acceptable` since
   `application/xml` is not in the Protocol-advertised output list. Borderline
   call — document it either way.

Nothing in the (1)–(5) list is a data-corruption bug. #1 is the most
serious because it breaks CONSTRUCT clients; the others are protocol
polish.

## Deferred / known-not-implemented

| Item | Status | Notes |
|------|--------|-------|
| `POST /update` (any UPDATE) | **501** in this binary | Even though INSERT DATA / DELETE DATA / DELETE WHERE / U_Modify executors landed in commits `9136d8e` / `a7acff5` / `fe3e168`, the `factoidal-http` binary was built at commit `b4e9fff` and has not been rebuilt since. The HTTP layer is still rejecting at stage 1. A rebuild + wiring work is needed before UPDATE-over-HTTP can be exercised — it is **not** usable today via this binary, despite the F\* executor existing. |
| `CONSTRUCT` / `DESCRIBE` | Stub (see bug #1) | Evaluator needs to route CONSTRUCT through the F\* CONSTRUCT path and emit a Turtle/N-Triples serializer result. |
| `default-graph-uri` / `named-graph-uri` request params | Ignored | Disclosed in `--help`. |
| HTTPS / TLS | Absent | Disclosed. |
| HTTP keep-alive, pipelining, chunked request bodies | Not supported | Disclosed. |
| Service Description (`GET /query` with no params → SD doc) | Not supported | 8a returned 400. Protocol says `GET` with no query MAY return a service description document. |
| Path-based routing | Not enforced (see bug #3) | Any GET with `?query=…` is treated as a query regardless of path. |

## What UPDATE-over-HTTP would need (for the next iteration)

1. Rebuild `factoidal-http` against current `SPARQL11_Algebra.ml` so the
   binary has access to `apply_update` / `apply_insert_data` / etc.
2. Wire the `/update` POST handler to parse the body through
   `SPARQL11_Parser.parse_update`, call `apply_update`, and return
   `204 No Content` on success (Protocol §2.2.3) or `400` on parser
   failure.
3. Add a mutation lock so concurrent `/update` + `/query` requests are
   serialised (they are already effectively serial because the Unix
   `accept` loop is single-threaded, but that should be an explicit
   invariant, not an accident).

Once (1)–(3) land, 13–17 of the 34 Protocol tests should unblock, per
the worklog's Protocol-HTTP priority-4a breakdown.

## Artifacts

- Server log: `/Users/danbri/working/factoidal/.claude-runs/http-audit-20260419.log`
- Transient response bodies: were under `/tmp/http_audit/` during the
  audit; not retained.

## Summary (one line)

Query-over-HTTP (SELECT / ASK) is solid, with all four result formats
working and honest 400/501 error handling; five polish bugs to fix before
calling it Protocol-conformant; UPDATE-over-HTTP is advertised and still
501 in this binary because the server predates the UPDATE-executor
landing and needs a rebuild.
