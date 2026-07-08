---
title: "Reaching out to other data: the SPARQL client, SERVICE tool-wrapping, and virtual RML"
description: "Three ways factoidal answers SPARQL over data it doesn't hold locally — a SPARQL 1.1 Protocol client, SERVICE-wrapped REST/tool sources, and non-materialized (D2RQ-style) RML query answering — as a CLI-transcript-and-architecture page, since all three need the network or a process and cannot run in a sandboxed browser cell."
layout: hub.njk
series: docs-hub
series_order: 22
vocab: none
status: published
tests: tests/local/sparql_client_protocol.sh, tests/local/service_wrap_stage12.sh, tests/local/virtual_rml_stage5.sh
---

Every hub post before this one asked factoidal a question about data it
already held — a Turtle document you pasted, a fixture it loaded from
disk. This post is about the other direction: answering SPARQL over
data factoidal does **not** hold locally. Three features do this, each
reaching outward a different way:

1. **The SPARQL client** — `factoidal query --endpoint URL` sends your
   query to a remote SPARQL 1.1 Protocol endpoint and parses whatever
   comes back.
2. **SERVICE tool-wrapping** — `SERVICE <wrap+http://...>` fetches an
   arbitrary REST/JSON (or CSV, or Turtle) resource, triplifies it, and
   joins it into your query like any other graph. This is factoidal's
   [SPARQL-Anything](https://github.com/SPARQL-Anything/sparql.anything)-adjacent
   capability.
3. **Virtual RML** — `factoidal query --data-rml mapping.ttl` answers
   SPARQL against a JSON or CSV source *through* an RML mapping without
   ever materializing all its triples first, the way
   [Ontop](https://ontop-vkg.org/) and D2RQ answer SPARQL against a
   relational database by rewriting instead of running an ETL step.

The design that ties all three together is
[`docs/designissues/2026-07-06-virtual-sources-design.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-06-virtual-sources-design.md):
a virtual source is not a new evaluation path, it is a new *producer*
of a value the evaluator already knew how to consume — a `graph_store`
for a `SERVICE` clause, or a `store_caps` capability record for a
dataset member. The last section makes that seam concrete.

## Why this page is a CLI transcript, not a live cell

Every other post in this series runs its examples in your browser, in a
live `observable-js` cell, against the F\*-extracted engine compiled to
JavaScript. This one can't. All three features here need a capability a
sandboxed browser cell does not have — an outbound socket to a remote
endpoint, an HTTP fetch to a wrapped API, or (for some `wrap+` schemes)
a spawned process. The
[cell-authoring contract](./README/)'s first constraint is *"Same-origin
only. Don't `fetch()` an external URL from inside a cell."* So faking a
live network call here would be dishonest.

Instead, every fenced block below is a **real transcript** — the exact
command and its exact output, captured by running the committed
`bin/linux-x86_64/factoidal` binary against a local fixture server.
Each transcript maps to an acceptance script under `tests/local/` (named
per section), which is what the `tests:` front-matter field points at
in place of a browser test file.

## 1. The SPARQL 1.1 Protocol client

Point `--endpoint` at any SPARQL 1.1 Protocol server and factoidal
becomes a client instead of an engine. The examples below run against a
factoidal server started with `factoidal serve` over a three-triple
fixture (`ex:alice ex:name "Alice"`, `ex:alice ex:knows ex:bob`,
`ex:bob ex:name "Bob"`), but the endpoint is any conformant SPARQL 1.1
Protocol server.

SELECT over `GET`, JSON results:

```console
$ factoidal query --endpoint http://127.0.0.1:PORT/sparql \
    -e 'SELECT ?name WHERE { ?s <http://example.org/name> ?name }' --via get -o json
{
  "head": { "vars": ["name"] },
  "results": {
    "bindings": [
      { "name": {"type":"literal","value":"Bob"} },
      { "name": {"type":"literal","value":"Alice"} }
    ]
  }
}
```

The same query rendered as a table (`-o table`), and an `ASK` (default
dispatch is a direct `POST`):

```console
$ factoidal query --endpoint .../sparql \
    -e 'SELECT ?name WHERE { ?s <http://example.org/name> ?name }' --via get -o table
+---------+
| ?name   |
+---------+
| "Bob"   |
| "Alice" |
+---------+
2 result(s)

$ factoidal query --endpoint .../sparql \
    -e 'ASK { <http://example.org/alice> <http://example.org/knows> <http://example.org/bob> }' -o json
{
  "head": {},
  "boolean": true
}
```

A malformed query gets a clean, non-crashing error — the server's
`400`, surfaced verbatim, with a non-zero exit code:

```console
$ factoidal query --endpoint .../sparql -e 'SELECT ?x WHERE { this is not sparql'
Error: endpoint returned HTTP 400:
SPARQL parse error: unresolved prefix
$ echo $?
1
```

### What is verified, and what is glue

The protocol shape is decided entirely in verified F\*:
[`SPARQL.Protocol.Client.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL.Protocol.Client.fst)
(commit
[`2bec68e`](https://github.com/danbri/factoidal/commit/2bec68e)) does
RFC 3986 percent-encoding over full Unicode (UTF-8 byte decomposition,
pure F\*), builds the three request forms (`--via get` / `--via post` /
`--via form`), selects the `Accept` header per query kind
(SELECT/ASK prefer SPARQL-results media types; CONSTRUCT/DESCRIBE prefer
`text/turtle`), and dispatches the response **purely on the returned
`Content-Type`** to one of five parsers already in the tree
(`Parser.JSONResults`, `Parser.SRX`, `Parser.CSVResults`,
`Parser.Turtle`, `Parser.NTriples`). No new `assume val` was
introduced: the only I/O is the socket read/write, which was already
solved as consumer-side glue in
[`bin/factoidal-http-client`](https://github.com/danbri/factoidal/blob/claude/main/bin/factoidal-http-client/README.md).

One limitation, disclosed rather than papered over: this binary links
no TLS stack, so an `https://` endpoint errors clearly instead of
half-working. Tracked as issue
[`#284`](https://github.com/danbri/factoidal/issues/284):

```console
$ factoidal query --endpoint https://query.wikidata.org/sparql -e 'ASK{}'
Error: https:// endpoints are not supported yet (no TLS stack linked into this binary).
Use an http:// endpoint, or front the HTTPS endpoint with a local http:// proxy.
```

Acceptance:
[`tests/local/sparql_client_protocol.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/local/sparql_client_protocol.sh)
starts a real factoidal server and exercises SELECT-over-GET,
SELECT-over-POST with XML forced via `--accept`, ASK true/false,
CONSTRUCT dispatch, and the malformed-query error path — **14 pass, 0
fail (out of 14)**.

## 2. SERVICE tool-wrapping

The SPARQL client above talks to something that already speaks SPARQL.
The `wrap+` scheme is for everything that doesn't: a REST endpoint, a
CSV export, a plain JSON API. Put its URL inside a `SERVICE` clause with
a `wrap+` prefix and factoidal fetches it, triplifies it, and joins the
result into the surrounding query like an ordinary graph.

Take a REST resource that returns plain JSON:

```console
$ curl -s http://127.0.0.1:PORT/person.json
{"name": "Ada", "age": 36}
```

A `SERVICE <wrap+http://.../person.json>` clause triplifies it with a
default, [Facade-X](https://sparql-anything.readthedocs.io/stable/)-equivalent
mapping (object keys become predicates under a fixed synthetic
namespace, the document root becomes a blank-node subject) and joins it
with a local BGP. The `<http://example.org/marker>` triple echoed back
in the output is the *local* side of the join, so its presence proves
the wrapped source and the local graph were joined, not evaluated in
isolation:

```console
$ FACTOIDAL_SERVICE_HTTP=1 FACTOIDAL_SERVICE_HTTP_ALLOWED_HOSTS=127.0.0.1 \
    factoidal query --data local.ttl -o ntriples -e '
      CONSTRUCT { <http://example.org/marker> <http://example.org/label> ?local . ?s ?p ?o }
      WHERE { <http://example.org/marker> <http://example.org/label> ?local .
              SERVICE <wrap+http://127.0.0.1:PORT/person.json> { ?s ?p ?o } }'
_:wrapdoc <http://factoidal.example/ns/wrap#name> "Ada" .
<http://example.org/marker> <http://example.org/label> "local" .
_:wrapdoc <http://factoidal.example/ns/wrap#age> "36"^^<http://www.w3.org/2001/XMLSchema#integer> .
```

The `wrap+` IRI scheme keeps the real target legible — everything
between `wrap+` and an optional `#` fragment is the literal URL. The
fragment is resolver-only, never sent over the wire, and its `#rml=`
key overrides the default mapping with a named `rml:TriplesMap` already
loaded in the query's own graphs — so wrapping an API you have an RML
mapping for reuses that mapping against the *fetched* bytes instead of
a file. The `tests/local` acceptance below checks that path is
byte-equal (sorted N-Quads) to what `bin/rml-runner` materializes from
the same mapping against the same bytes read from disk.

### Security posture: opt-in, allowlisted, no ambient trust

A `wrap+` IRI is untrusted input the moment a query variable can build
one, so the gates are deliberate and default-closed:

- **Off by default.** With no opt-in, a `wrap+` IRI behaves exactly
  like any other unregistered `SERVICE` endpoint: an empty result (or
  the `silent`-dependent empty per SPARQL semantics), never a fetch.
  There is nothing to bypass because there is nothing installed.
- **`FACTOIDAL_SERVICE_HTTP=1`** turns on `wrap+http:`/`wrap+https:`
  registration — the same "absent = off" idiom the HTTP-client smoke
  test already uses.
- **`FACTOIDAL_SERVICE_HTTP_ALLOWED_HOSTS`** is an exact-host
  allowlist. Empty means nothing is allowed; there is no wildcard-on
  default. This restricts what factoidal may *call*, the mirror image
  of the CORS allowlist that restricts who may call it.

With the opt-in flag unset, the same query produces a clean empty
result and exits 0 — indistinguishable from any unknown `SERVICE`
scheme, never a crash:

```console
$ factoidal query --data local.ttl -o ntriples \
    -e 'CONSTRUCT { ?s ?p ?o } WHERE { SERVICE <wrap+http://.../person.json> { ?s ?p ?o } }'
$ echo $?
0
```

### What is verified, and what is glue

The split is the same as the SPARQL client's. All the triplification
logic — the `wrap+` IRI-scheme parser, format detection, the default
Facade-X-equivalent mapping (one F\* constant per format), and the RML
term-map evaluation — lives in verified F\*
([`SPARQL.Service.Wrap.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL.Service.Wrap.fst),
commit
[`fec0602`](https://github.com/danbri/factoidal/commit/fec0602), reusing
`RML.Mapping`/`RML.Sources`/`RML.Eval`). The only I/O is the HTTP
fetch, reusing the exact same socket consumer the SPARQL client uses —
zero new `assume val`. The host allowlist and opt-in flag are
consumer-side deployment policy in `bin/`, not verified computation.

One caveat the acceptance script documents in full: factoidal's CLI has
a fast backend executor for local `SELECT`/`ASK` whose `SERVICE` arm is
not yet wired, so `wrap+` results are visible today through
`CONSTRUCT`-shaped queries (or with `--entail` set), which route
through the `eval_pattern_store` path this feature hooks into. That is a
pre-existing SELECT-fast-path gap, not a resolver bug.

Acceptance:
[`tests/local/service_wrap_stage12.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/local/service_wrap_stage12.sh)
covers JSON, CSV, and Turtle-passthrough default mappings, the `#rml=`
byte-equal override, the opt-out, a non-http `wrap+` scheme, and a
closed-port fetch failure — **15 pass, 0 fail (out of 15)**.

## 3. Virtual RML — SPARQL through a mapping, nothing materialized

The RML post ([post 9](./09-mapping-tables-to-triples-rml.md)) turned a
CSV or JSON source into RDF triples up front. Virtual RML answers the
query *against the mapping* without doing that — the D2RQ/Ontop move,
narrowed to what a document source can actually support.

The mapping here (a vendored rml-core fixture, RMLTC0012b-JSON) has two
`TriplesMap`s over two separate JSON files — `persons.json` produces
`foaf:name` triples, `lives.json` produces `ex:city` triples, three
rows each:

```console
$ cat persons.json
{ "persons": [
    {"fname":"Bob","lname":"Smith","amount":30},
    {"fname":"Sue","lname":"Jones","amount":20},
    {"fname":"Bob","lname":"Smith","amount":30} ] }
$ cat lives.json
{ "lives": [
    {"fname":"Bob","lname":"Smith","city":"London"},
    {"fname":"Sue","lname":"Jones","city":"Madrid"},
    {"fname":"Bob","lname":"Smith","city":"London"} ] }
```

`--data-rml` answers SPARQL straight over that mapping. A bound-predicate
query and a `COUNT`, both computed by walking the sources through the
mapping on demand — no intermediate RDF file ever exists:

```console
$ factoidal query --data-rml mapping.ttl -o csv \
    -e 'SELECT * WHERE { ?s <http://example.com/city> ?o }'
o,s
London,_:BobSmith
Madrid,_:SueJones

$ factoidal query --data-rml mapping.ttl -o csv \
    -e 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
n
4
```

### Byte-equal to materialized

The premise the whole feature rests on: a virtual answer must equal the
materialized one. `bin/rml-runner` reproduces the fixture's own
`output.nq` byte-for-byte via the full materializing path
(`RML.Eval.eval_triples_map`), so loading that file with plain `--data`
is the materialized baseline. Same query, both ways:

```console
$ factoidal query --data-rml mapping.ttl -o csv -e 'SELECT * WHERE { ?s ?p ?o }'   # virtual
$ factoidal query --data output.nq   -o csv -e 'SELECT * WHERE { ?s ?p ?o }'       # materialized
virtual      sorted-rows sha256 = 441b5863fe22b52d40b358230550411082629b9f761448943a195b550dc6ba4e
materialized sorted-rows sha256 = 441b5863fe22b52d40b358230550411082629b9f761448943a195b550dc6ba4e
MATCH
```

### The pushdown narrows which rows are touched

Virtual, here, is a specific claim: `sc_solve` does **not** materialize
every triple and filter afterward. A bound triple pattern's constants
are pushed into the source's own iteration — first ruling out whole
`TriplesMap`s whose predicate term-map can't produce the bound
predicate, then dropping non-matching rows before the per-row term-map
machinery runs. The stage-5 script compiles a probe that reports rows
considered per candidate map:

```console
UNBOUND (?s ?p ?o):
    .../TriplesMap2 rows_considered=3
    .../TriplesMap1 rows_considered=3
    TOTAL rows_considered=6 candidate_maps=2 out_of=2
BOUND bp=<http://example.com/city>:
    .../TriplesMap2 rows_considered=3
    TOTAL rows_considered=3 candidate_maps=1 out_of=2
BOUND bp=<http://example.com/city> AND bs=_:BobSmith:
    .../TriplesMap2 rows_considered=2
    TOTAL rows_considered=2 candidate_maps=1 out_of=2
```

An unbound scan reads all 6 rows. Binding the predicate to `ex:city`
rules out `TriplesMap1` structurally — `persons.json`'s 3 rows are
never read at all — leaving 3. Adding a bound subject (`_:BobSmith`,
from an earlier join) drops the non-matching `Sue Jones` row via subject-
template pushdown, leaving 2. Fewer rows touched as the query gets more
specific, which is the whole point.

One honesty note the design doc states plainly: joins do **not** push
down. Unlike Ontop's SQL unfolding — which hands a whole join to the
RDBMS in one statement — factoidal's sources are opaque documents and
APIs with no query language to receive a join, so a cross-source join
stays a SPARQL-level `join` over two independently-produced solution
sequences. The pushdown is per-pattern, and stated as a floor rather
than implied as parity with Ontop.

Acceptance:
[`tests/local/virtual_rml_stage5.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/local/virtual_rml_stage5.sh)
checks virtual-vs-materialized equality for unbound scan,
bound-predicate, bound-subject join, ASK, and COUNT, plus the
row-count pushdown evidence above — **8 pass, 0 fail (out of 8)**.

## The seam that unifies all three

None of these three features added a new query-evaluation path. They
each plug into a seam the local backends already use:

- The **SPARQL client** is a consumer front-end: it builds a request in
  F\* and dispatches the response to parsers the engine already has.
- **SERVICE wrap** populates one entry of the `service_endpoint_lookup`
  table with a `graph_store` — the same value a statically-declared
  `SERVICE` endpoint produces. The `GP_Service` evaluation arm runs
  unmodified; only *when* the table gets an entry changed (lazily, on
  first miss, instead of only up front).
- **Virtual RML** is one more realisation of `store_caps`, the
  capability record
  ([`RDF.Store.Capabilities.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Store.Capabilities.fst),
  commit
  [`34944ec`](https://github.com/danbri/factoidal/commit/34944ec)) every
  backend realises — `GB_List`, `GB_Indexed`, `GB_HDT`, `GB_COTTAS`,
  the on-disk column store. A `caps_of_rml_source` member can sit inside
  a `GB_Union` next to a materialized COTTAS store with zero new
  plumbing; the union combinator does not know or care that one member's
  `sc_solve` walks an in-memory JSON tree while another reads an on-disk
  column file.

That is why the split between "verified F\*" and "I/O glue" is the same
in all three: the decision logic (protocol shape, IRI-scheme parsing,
triplification, pattern narrowing) is F\*; the outbound socket or file
read is a consumer-side `assume val` realisation, and the allowlists and
opt-in flags are deployment policy in `bin/`. Per the project's standing
qualifier: parser and algebra spec verified in F\*; the on-disk backend
still carries unverified OCaml-side optimization layers being migrated
back to F\* — the virtual-RML `store_caps` member itself is F\*, the
socket/file I/O beneath the client and `wrap+` fetch is the acknowledged
glue.

## Beyond the three

The design doc sketches more that is not yet implemented: `wrap+mcp:`
(wrapping an MCP tool over JSON-RPC), `wrap+exec:` (a spawned local
binary behind an allowlist, a new process-I/O primitive), an XML/XPath
source through RML, and a TTL-keyed cross-query cache. None are
promised; each is gated on a real corpus showing the need.

Because these are native and network features, they have no live cell —
the transcripts above are the demonstration, and they are pinned by the
three `tests/local/` acceptance scripts named in each section rather
than a `tests/hub/` browser test. Run any of them against a fresh clone
with a compiled `bin/<platform>/factoidal` to reproduce this page's
output exactly.
