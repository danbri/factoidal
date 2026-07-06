# Virtual sources — SERVICE-wrapped tools and virtual RML query answering

**Status:** design doc, no code. Territory: this file only. Reads the
SERVICE seam, the new SPARQL 1.1 Protocol client, the store-capability
seam, and the RML triplifier, but edits none of them.

Two programs share one goal — answer SPARQL queries against data that
is not sitting in one of our own materialized stores — via two
different entry points into the query evaluator:

- **Part A.** Make an arbitrary REST API, MCP tool, or local CLI
  program answerable through `SERVICE <iri> { ... }`, the way
  [SPARQL-Anything](https://github.com/SPARQL-Anything/sparql.anything)
  makes a file or API answerable through
  `SERVICE <x-sparql-anything:...>`.
- **Part B.** Make an RML-mapped external source (a CSV export, a JSON
  API response) answerable as an ordinary graph in the default/named
  dataset, without ever materializing its content as RDF — the way
  [Ontop](https://ontop-vkg.org/) and D2RQ answer SPARQL against a
  relational database through query rewriting instead of an ETL step.

Both land through the same seam this codebase already has for "a
graph_store that isn't backed by triples we hold": the `store_caps`
capability record ([`RDF.Store.Capabilities.fst`](../../formal/fstar/RDF.Store.Capabilities.fst))
and the `SERVICE` endpoint hook
(`service_endpoint_lookup`, [`SPARQL11.Algebra.fst:1916`](../../formal/fstar/SPARQL11.Algebra.fst)).
Neither seam needs to change shape — a virtual source is just a new
*producer* of a `graph_store` (Part A) or a new *realisation* of
`store_caps` (Part B).

## 0. What exists today (read first, cited)

### 0.1 The SERVICE seam

- AST: `GP_Service : wf_iri -> group_graph_pattern -> bool -> group_graph_pattern`
  (fixed IRI) and `GP_ServiceVar : var_name -> ... -> group_graph_pattern`
  (variable-bound IRI, resolved to a fixed IRI once the variable binds)
  — [`SPARQL11.Algebra.fst:514-517`](../../formal/fstar/SPARQL11.Algebra.fst).
- The one hook: `assume val service_endpoint_lookup : wf_iri -> option graph_store`
  — [`SPARQL11.Algebra.fst:1916`](../../formal/fstar/SPARQL11.Algebra.fst),
  with the comment block at
  [`SPARQL11.Algebra.fst:1906-1916`](../../formal/fstar/SPARQL11.Algebra.fst)
  already stating "Live HTTP federation is a future phase". This
  doc is that phase, scoped narrower: not full live SPARQL federation,
  but wrapped non-SPARQL sources.
- Dispatch: `eval_pattern_store`'s `GP_Service`/`GP_ServiceVar` arms
  ([`SPARQL11.Algebra.fst:2166`](../../formal/fstar/SPARQL11.Algebra.fst),
  arms at
  [`2171-2214`](../../formal/fstar/SPARQL11.Algebra.fst) and
  [`2281-2298`](../../formal/fstar/SPARQL11.Algebra.fst)). The fixed-IRI
  case is three lines: look up, evaluate the inner pattern against the
  resolved `graph_store`, or return `[]`/`[[]]` per `silent` on a miss.
  The `?var` case evaluates the left/right pattern first, then calls
  `service_endpoint_lookup` **once per distinct binding of the
  variable**, which is exactly the shape a wrap+ IRI built from query
  data needs (§2.4 below).
- Realisation today:
  [`57_service_client_bind.sh`](../../formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/57_service_client_bind.sh)
  patches the extracted `service_endpoint_lookup` into a global
  `Hashtbl.t` (`service_endpoint_table`), populated **statically** by
  `w3c_runner.ml` from `qt:serviceData` manifest declarations before
  the query runs. Rule #15-compliant by the patch's own banner: "zero
  RDF/SPARQL semantic logic... The decision of HOW to dispatch a
  SERVICE request lives in F*". A virtual source is the same
  `iri -> graph_store` table, populated **lazily** on first miss
  instead of only up front — a change in *when* the table gets an
  entry, not in the F*-side contract at all.

### 0.2 The SPARQL 1.1 Protocol client (landed today, 2fe187f's parent 2bec684)

[`SPARQL.Protocol.Client.fst`](../../formal/fstar/SPARQL.Protocol.Client.fst)
is the template Part A's HTTP fetch path reuses almost unchanged:

- RFC 3986 percent-encoding (`pct_encode`,
  [:165-182](../../formal/fstar/SPARQL.Protocol.Client.fst)) — full
  Unicode via UTF-8 byte decomposition, pure F*.
- Three request builders (`build_get_request`/`build_post_direct_request`/
  `build_post_form_request`,
  [:305-359](../../formal/fstar/SPARQL.Protocol.Client.fst)) producing
  an `SPARQL.HTTP.Client.http_request_msg` — transport-agnostic, no I/O.
- `handle_http_response`
  ([:428-438](../../formal/fstar/SPARQL.Protocol.Client.fst)) dispatches
  purely on the response's actual `Content-Type` to one of five
  existing W3C parsers (`Parser.JSONResults`, `Parser.SRX`,
  `Parser.CSVResults`, `Parser.Turtle`, `Parser.NTriples`).
- The module's own banner states the precedent this doc leans on
  hardest: *"everything that decides SPARQL protocol shape lives here
  in F*; no new `assume val` is introduced because there is no new
  I/O primitive to realise — socket I/O was already solved as
  consumer-side glue"*
  ([:11-17](../../formal/fstar/SPARQL.Protocol.Client.fst)).
- The consumer glue,
  [`bin/factoidal-http-client/factoidal_http_client.ml`](../../bin/factoidal-http-client/factoidal_http_client.ml),
  does socket I/O only (CONSUMER class, not `assume val`), gated behind
  `FACTOIDAL_HTTP_CLIENT_SMOKE=1` for its own smoke test
  ([README](../../bin/factoidal-http-client/README.md)). There is
  already a jsoo variant,
  `bin/factoidal-http-client/factoidal_http_client_jsoo.ml`, proving
  this transport already has a browser-`fetch`-backed realisation
  path — Part A's `wrap+https:`/`wrap+http:` fetch reuses that
  precedent directly (§1.5).
- Issue #284 (per this task's brief) tracks HTTPS options for this
  client; today it is HTTP-only. Part A's `wrap+https:` scheme
  inherits that exact same limitation and the same follow-up issue —
  it does not reopen the TLS question, it depends on #284's answer.

### 0.3 The store-capability seam

[`RDF.Store.Capabilities.fst`](../../formal/fstar/RDF.Store.Capabilities.fst)
defines `store_caps` — the one record every backend realises instead
of the evaluator matching on a `graph_backend` tag:

```
sc_solve            : triple_pattern_bound -> Tot (list triple)
sc_solve_limited     : triple_pattern_bound -> nat -> Tot (list triple)
sc_estimate          : triple_pattern_bound -> Tot nat
sc_count_exact       : triple_pattern_bound -> Tot nat
sc_predicate_present : wf_iri -> Tot bool
sc_decode_failure    : unit -> Tot bool
```
([:125-158](../../formal/fstar/RDF.Store.Capabilities.fst)). `caps_of_backend`
([`SPARQL11.Store.fst:233`](../../formal/fstar/SPARQL11.Store.fst)) is
the single dispatch point that builds one of these per `graph_backend`
constructor (`GB_List`/`GB_Indexed`/`GB_HDT`/`GB_COTTAS`/
`GB_CottasOnDisk`/`GB_Union`); `union_caps`
([`RDF.Store.Capabilities.fst:272`](../../formal/fstar/RDF.Store.Capabilities.fst))
is a read-only combinator over a `list store_caps` with **real
per-member LIMIT pushdown** (`union_solve_limited`,
[:252-270](../../formal/fstar/RDF.Store.Capabilities.fst) — each member
gets asked for only its remaining budget, not "solve everything, then
truncate"). Part B is one more `store_caps` realisation
(`caps_of_rml_source`, §3) that a deployment can drop into a
`GB_Union` next to a COTTAS-on-disk member with **zero new plumbing** —
the union combinator does not know or care that one member's `sc_solve`
walks an in-memory JSON tree instead of an on-disk column file.

### 0.4 The triplifier (RML), materializing today

- [`RML.Mapping.fst`](../../formal/fstar/RML.Mapping.fst) — the
  `rml:` mapping-document AST (`triples_map`/`logical_source`/
  `term_map`/`predicate_object_map`) decoded out of an already-parsed
  Turtle graph (`decode_mapping_document`,
  [:748-751](../../formal/fstar/RML.Mapping.fst)).
- [`RML.Sources.fst`](../../formal/fstar/RML.Sources.fst) — a
  JSONPath **subset** evaluator over `Parser.JSON`'s `json_val` tree
  (`eval_jsonpath`, [:258-259](../../formal/fstar/RML.Sources.fst)) and
  an RFC 4180 CSV tokenizer + row-binding model (`csv_iterate`,
  [:373-384](../../formal/fstar/RML.Sources.fst)). `reference_formulation`
  already carries an `RF_XPath` constructor
  ([`RML.Mapping.fst:343`](../../formal/fstar/RML.Mapping.fst)) but no
  evaluator consumes it yet — RML program-plan Stage 4, "not yet
  built" per the plan's own staged table
  ([`docs/designissues/2026-07-05-rml-program-plan.md:277`](2026-07-05-rml-program-plan.md)).
  `XPath.Eval.fst` and `Parser.XML.fst` exist independently (used by
  JSON-LD/XML-adjacent work) and are the natural reuse target when
  Stage 4 lands; this doc does not depend on it (§4).
- [`RML.Eval.fst`](../../formal/fstar/RML.Eval.fst) —
  `eval_triples_map : triples_map -> list source_row -> option string -> list triple`
  ([:587](../../formal/fstar/RML.Eval.fst)), plus `eval_triples_map_json`/
  `eval_triples_map_csv` convenience wrappers
  ([:604](../../formal/fstar/RML.Eval.fst),
  [:619](../../formal/fstar/RML.Eval.fst)) that call `RML.Sources.json_iterate`/
  `csv_iterate` first. **This is exactly the materializing path Part
  B's virtual backend must NOT call per-query** — it walks every row
  and builds every triple, unconditionally.
- The program plan already settled the precedent Part A and B both
  lean on for "is this an `assume val` or F*": *"JSONPath/XPath: F\*
  subset, not assume-val... the path-matching *is* mapping semantics,
  not I/O... An assume-val here would put term-selection logic ...
  outside the verified boundary"*
  ([`2026-07-05-rml-program-plan.md:189-216`](2026-07-05-rml-program-plan.md)).
  Format detection, mapping selection, and pushdown filtering in this
  doc are all the same class of decision — they stay in F*.

### 0.5 The property-function dispatch precedent

[`SPARQL.FullText.fst`](../../formal/fstar/SPARQL.FullText.fst) is the
other live example of "a special predicate IRI changes evaluation,"
relevant to Part A's IRI-scheme choice: `eval_single_tp_store`
([`SPARQL11.Algebra.fst:1814-1826`](../../formal/fstar/SPARQL11.Algebra.fst))
checks `tp.tp_p = fulltext_query_pred` and, on a match, decodes an
internally-tagged literal (`decode_fulltext_literal`) instead of
running the default triple match. That pattern — recognize a
sentinel, decode structured arguments, dispatch to a purpose-built
evaluator, fall through to default otherwise — is the same shape
`service_endpoint_lookup`'s hashtable-miss branch gets extended with in
§2.5: recognize a `wrap+` IRI scheme, decode the encoded target/mapping,
dispatch to the resolver, fall through to `None` (today's exact
"unregistered SERVICE endpoint" behaviour) otherwise.

## 1. Prior art — what we adopt, what we don't, and why

- **[SPARQL-Anything](https://github.com/SPARQL-Anything/sparql.anything)**
  overloads `SERVICE` with a custom scheme, `x-sparql-anything:`, and
  passes triplification options as `fx:property` triples *inside* the
  SERVICE group graph pattern (Facade-X:
  [`SPARQL Anything docs`](https://sparql-anything.readthedocs.io/stable/)).
  **We adopt** the "custom SERVICE scheme, no protocol change" idea and
  the "one generic facade covering many formats" idea (§2.3's default
  mapping). **We do not adopt** encoding options as sibling BGP
  triples (`fx:properties ...`) — our parser has no equivalent
  post-parse rewrite pass for arbitrary predicates the way `text:query`
  needed one purpose-built rewrite (§0.5's own banner already
  disclaims that as "a query-planning restructuring out of scope"); an
  IRI fragment (§2.1) carries the same information with zero new
  parser surface.
- **[Ontop](https://ontop-vkg.org/)/D2RQ** rewrite a SPARQL BGP into
  one SQL statement over the mapped relational schema — joins,
  filters, and multiple triples maps unfold into a single query the
  RDBMS executes, because SQL is expressive enough to encode a join.
  **We do not adopt** cross-pattern/cross-source unfolding: our
  sources are documents and APIs, not a query engine we can hand a
  join to. **We adopt** the narrower half of the same idea — pushing
  a *single bound pattern's* constant(s) into the source's own
  iteration (a JSONPath step, a CSV column-equality filter) — and say
  so plainly rather than imply SQL-grade unfolding (§3.2).
- **Jena's `SERVICE` extension points**
  (`ServiceExecutorRegistry`/custom `Service` implementations) let a
  Jena deployment register a Java class per scheme, evaluated
  in-process. **We adopt** the "registry keyed by scheme, in-process,
  no separate federation engine" shape — `service_endpoint_lookup`
  already has exactly that shape (a table populated before dispatch);
  §2.5 only changes when a table entry gets computed, not the
  registry-per-scheme idea.
- **[Comunica](https://comunica.dev/)**'s source federation treats
  every queryable thing (SPARQL endpoint, file, TPF interface) as a
  peer `IQuerySource` behind one interface, with per-source capability
  metadata driving the query plan. **We adopt** the capability-record
  idea directly — it is exactly what `store_caps` already is
  (§0.3) — rather than invent a second capability abstraction next to
  it. **We do not adopt** Comunica's link-traversal/discovery model
  (following `rdfs:seeAlso` etc. mid-query); every virtual source in
  this doc is named explicitly by the query author, in the IRI or the
  dataset's declared graphs, never discovered.

## 2. Part A — tool wrapping via SERVICE

### 2.1 IRI scheme

Three prefixed schemes, `wrap+<transport>:`, chosen so a `wrap+https:`/
`wrap+http:` IRI keeps the real target 100% legible as a normal URL —
copy-pasteable, greppable, and re-usable with any other HTTP tool —
rather than opaquely percent-encoded end to end.

```
wrap+https://api.example.org/v1/users?id=42#rml=urn:mapping:users-api
wrap+http://internal.example.org/status
wrap+mcp:geocoder/geocode?%7B%22address%22%3A%22...%22%7D#rml=urn:mapping:geo
wrap+exec:whois-cli?arg=example.org#mime=text/plain&rml=urn:mapping:whois
```

- **`wrap+https:` / `wrap+http:`.** Everything between the scheme and
  an optional `#` is the literal target URL, unmodified (scheme swapped
  back to `https`/`http` before the real fetch). A literal `#` inside
  the *target's own* query string must already be percent-encoded as
  `%23` by whoever constructs the IRI — RFC 3986 already requires this
  for any URL, so this is not a new authoring burden, only a
  reaffirmation that the outer IRI's fragment delimiter wins.
- **`wrap+mcp:`.** The authority position is **not** a network host —
  it is an alias into an operator-configured MCP server table (§2.6):
  `wrap+mcp:<alias>/<tool-name>?<pct-encoded JSON args object>`. No
  wrap+mcp: IRI ever carries a raw host/port; the alias is looked up,
  never dialed directly, so an attacker who controls IRI construction
  cannot make the resolver talk to an arbitrary MCP endpoint (§2.7).
- **`wrap+exec:`.** Same alias-only-authority rule:
  `wrap+exec:<alias>?arg=<pct-encoded-value>&arg=<pct-encoded-value>...`.
  `<alias>` exact-matches a key in the exec allowlist (§2.6), which
  maps to an absolute binary path plus a fixed argv *template* with
  named placeholder slots; repeated `arg=` parameters fill those slots
  **in declared order**. The query can supply *values*, never new
  flags, a different binary, or extra argv entries.
- **Control fragment**, shared by all three schemes: `#k=v&k=v...`
  (never sent over the wire — every request builder in
  `SPARQL.Protocol.Client.fst` already takes `rm_path`/`rm_query_str`
  and never a fragment, so "the fragment is resolver-only, not
  wire-visible" costs nothing new to enforce). Recognized keys:
  - `rml=<pct-encoded IRI>` — names a `rml:TriplesMap` (or the whole
    mapping document containing several) already present in the
    query's own default/named graphs, whose `rml:logicalSource`'s
    bytes are overridden with the freshly fetched/spawned bytes
    instead of read from `rml:source`/`rml:path` (§2.3).
  - `mime=<pct-encoded media type>` — declares the format when no
    `Content-Type` header exists (`wrap+exec:`'s stdout, some
    `wrap+mcp:` tool results) or when the declared type disagrees with
    what auto-detection would guess.
  - `ttl=<seconds>` — v2 only (§2.4's caching section); ignored (fetch
    every time, per-query only) in v1.
- **Alias/tool-name charset.** `<alias>` and `<tool-name>` are
  restricted to `[A-Za-z0-9_-]`; the resolver rejects (returns `None`,
  same as an unregistered endpoint) any IRI whose alias or tool-name
  contains a byte outside that set, and matches by exact bytes only —
  never percent-decode-then-match, which would otherwise let two
  differently-encoded IRIs collide on the same allowlist entry.

### 2.2 Resolver pipeline

Four stages, all but the first two purely functional in F*:

1. **Fetch** (transport-specific, I/O):
   - `wrap+https:`/`wrap+http:` — build an HTTP GET via
     `SPARQL.Protocol.Client`-shaped request construction (reusing
     `pct_encode`/query-pair assembly verbatim; POST is out of scope
     for v1 — wrapping a tool for read-only query answering has no
     SPARQL-Update-shaped need for a request body), hand the formatted
     bytes to the existing `factoidal_http_client.ml` socket-I/O
     consumer (§0.2) — **zero new assume val**, this transport is
     already solved.
   - `wrap+mcp:` over an HTTP-transport MCP server — build a JSON-RPC
     2.0 `tools/call` envelope (new, small, pure F* — a JSON object
     literal builder, the same size class as `SPARQL.Protocol.Client`'s
     request builders), POST it over the *same* existing HTTP consumer
     glue — again **zero new assume val**.
   - `wrap+mcp:` over a stdio-transport MCP server, and `wrap+exec:` —
     both need to spawn a process and exchange bytes with it; this is
     the one genuinely new I/O primitive (§2.7).
2. **Format detection or declared mapping.** `Content-Type` (HTTP/MCP)
   or the `mime=` control key (exec/undeclared) selects a parser:
   `application/json` → `Parser.JSON`, `text/csv` → `RML.Sources`'s
   CSV tokenizer, `text/turtle`/`application/n-triples`/
   `application/n-quads` → parse straight as RDF and **skip
   triplification entirely** (wrapping another RDF-serving endpoint
   needs no mapping at all — this is the degenerate, cheapest case).
   No recognized type and no `mime=` override → treat the whole body
   as one `xsd:string` literal (RML-IO's own natural-typing fallback
   for an unrecognized reference formulation), producing at most a
   single triple under the default mapping.
3. **Triplify**, via the shared layer (§4):
   - `rml=` present → `RML.Mapping.decode_mapping_document` already
     ran once (the query's own FROM/dataset load parsed the mapping
     graph); look up the named `TriplesMap`, and instead of an OCaml
     consumer reading `rml:source`'s file path and handing bytes to
     `RML.Sources.json_iterate`/`csv_iterate` (today's only call
     shape, per `RML.Eval.fst`'s own banner: *"json_root is supplied
     by the (OCaml-side, rule #11) caller that read + parsed the
     logical source's file"*), the wrap resolver hands those same
     functions the **freshly fetched** bytes instead of file bytes —
     same F* function signature, different (still OCaml-side, still
     rule #11) byte source.
   - `rml=` absent → apply one canned default mapping per detected
     format (§2.3) — a Facade-X-equivalent generic triplification, not
     a second code path per format.
4. **`graph_store`.** `RML.Eval.eval_triples_map`'s output
   (`list triple`) becomes a `graph_store` via the exact same
   `graph_to_store` call `service_endpoint_lookup`'s realisation
   already makes
   ([`57_service_client_bind.sh:88-104`](../../formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/57_service_client_bind.sh))
   — from here on, `eval_pattern_store`'s `GP_Service` arm
   ([`SPARQL11.Algebra.fst:2281-2296`](../../formal/fstar/SPARQL11.Algebra.fst))
   runs completely unmodified. A wrap+ IRI is not a new evaluation
   path; it is a new way to populate one table entry the evaluator
   already knew how to consume.

### 2.3 Default (Facade-X-equivalent) mapping

One canned `RML.Mapping.mapping_document` F* value per detected
format, built once, not reimplemented per source:

- **JSON.** Object keys become predicates under a fixed synthetic
  namespace (e.g. `http://factoidal.example/ns/wrap#<key>`); object
  values become object-map term values (nested objects recurse as
  blank-node subjects, arrays fan out as repeated predicate-object
  pairs — Facade-X's own choice of "container membership as repeated
  triples" over `rdf:List`, since a SPARQL BGP over an unbounded
  `rdf:rest` chain is exactly the awkward query shape Facade-X's
  design writeup calls out). The document root is one blank-node
  subject.
- **CSV.** Header row → predicate names (same synthetic namespace);
  each data row → one blank-node subject, one triple per non-null
  cell — literally `RML.Sources.csv_iterate`'s row-binding model with
  a canned, header-derived `predicate_object_map` list instead of a
  user-authored one.
- **XML** — deferred to when RML Stage 4 (XPath) lands (§4); this doc
  does not block on it.

This is one F* constant plus the machinery already in §0.4 — no new
evaluator logic, only a fixed `mapping_document` value per format.

### 2.4 Caching and invalidation

v1: **per-query only.** The resolver's table (§0.1) is populated
lazily on first miss during one query's evaluation and reused for any
repeated `SERVICE`/`GP_ServiceVar` dispatch to the same IRI within that
same query — this is not new semantics, it is `service_endpoint_lookup`'s
existing `Hashtbl` (§0.1) accepting writes during evaluation instead of
only before it. No entry ever outlives the query that fetched it, so
"stale data" cannot happen by construction. This is also exactly the
per-binding cost `GP_ServiceVar`'s dispatch already pays today
(§0.1's `?var` case calls `service_endpoint_lookup` once per distinct
binding) — a wrap+ IRI bound to N different variable values across a
join still fetches N times, same as N distinct fixed-IRI `SERVICE`
clauses would.

v2 (not built, flagged as a follow-up, per the perf-benchmarking
skill's "no perf claim without measurement"): an opt-in, TTL-keyed
cross-query cache in the CONSUMER (`bin/factoidal-http`/
`bin/factoidal-cli`), keyed on the wrap+ IRI string, honoring the `ttl=`
fragment key. This is deliberately a CONSUMER-side decision (rule #11:
"how long may a stale answer be served" is deployment policy, not a
verified-computation question) — the F* contract
(`wf_iri -> option graph_store`) is unaffected either way.

### 2.5 Extending the resolver (F* side)

`SPARQL11.Algebra.fst`'s `service_endpoint_lookup` stays an `assume
val` with the *same signature*. The stub patch
([`57_service_client_bind.sh`](../../formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/57_service_client_bind.sh))
gets a disclosed extension (still one patch, same issue #57 family, or
a sibling patch if the diff is cleaner as its own file — decide at
implementation time): on a static-table miss, check whether the IRI
matches a `wrap+` prefix (a small, pure F* predicate/parser —
`SPARQL.Service.Wrap.fst`, §4 — not a new `assume val`, exactly the
`SPARQL.FullText`-precedent shape of §0.5) and if so run the pipeline
in §2.2; otherwise return `None`, identical to today. This preserves
the patch's own rule-#15 claim ("zero RDF/SPARQL semantic logic... The
decision of HOW to dispatch a SERVICE request lives in F*") — the *how*
(fetch → detect → triplify → graph_store) is entirely F* functions;
the *miss handler* is still just "which precomputed graph_store does
this IRI map to," computed instead of looked up.

### 2.6 Security — allowlists, opt-in, no ambient trust

Named reflex to hold onto: a `wrap+` IRI is untrusted input the moment
it can be built from a query variable (`GP_ServiceVar`,
§2.7) — every gate below applies identically whether the IRI came from
the query text literally or from a `?var` binding.

- **No opt-in, no registration at all.** By default, the wrap+
  resolver extension is not installed — a `wrap+` IRI behaves exactly
  like any other unregistered `SERVICE` endpoint (`None`, then
  `silent`-dependent empty result per
  [`SPARQL11.Algebra.fst:2292-2296`](../../formal/fstar/SPARQL11.Algebra.fst)).
  No code path exists to differentiate "wrap+ IRI, resolver not
  installed" from "any other unknown scheme" — there is nothing to
  bypass because there is nothing there.
- **`FACTOIDAL_SERVICE_HTTP=1`-shaped opt-in** (per this task's own
  brief) gates `wrap+https:`/`wrap+http:` registration, mirroring
  `factoidal_http_client.ml`'s existing `FACTOIDAL_HTTP_CLIENT_SMOKE=1`
  convention (§0.2) — same idiom, new variable name, same "absent =
  off" default.
- **Host allowlist** for `wrap+https:`/`wrap+http:`: an operator-
  supplied comma-separated exact-host list (or, explicitly, "empty =
  nothing allowed", never a wildcard-on default), the same shape as
  `bin/factoidal-http`'s existing CORS origin allowlist
  ([`factoidal_http.ml:337-345`](../../bin/factoidal-http/factoidal_http.ml):
  *"off (explicit opt-in...) or a comma-separated allowlist of exact
  ... origin"*). CORS restricts who may call **us**; this restricts
  what **we** may call — different direction, identical config shape,
  and reuse the parsing helper if `factoidal_http.ml` already factors
  one out, or write a twin rather than a third bespoke parser.
- **MCP/exec allowlist**: alias → connection info (MCP: transport +
  host/port or spawn command; exec: absolute binary path + argv
  template with named placeholders), loaded from an operator-supplied
  config file, default empty. No alias, no ambient `$PATH` lookup, no
  binary-name-from-query-string path ever reaches `process_run` (§2.7)
  — see §2.1's exact-byte-match rule.
- **No shell.** `process_run` always spawns via an explicit argv array
  (OCaml `Unix.create_process`/`create_process_env`, never
  `Unix.open_process` / `/bin/sh -c`), so a query-supplied `arg=` value
  is a single argv element, never re-parsed for shell metacharacters —
  `arg=$(rm -rf /)` reaches the target binary as the **literal string**
  `$(rm -rf /)`, not a subshell invocation.
- **Injection surface, stated plainly.** A `GP_ServiceVar`-bound wrap+
  IRI lets the query choose (a) *which* allowlisted alias to invoke, if
  the operator exposed more than one, and (b) the *values* slotted into
  that alias's declared placeholder positions. It cannot choose a new
  binary, add flags, alter argv[0], or reach an alias absent from the
  allowlist — the allowlist is consulted on every resolution, not
  cached-then-trusted, and gives the same `None` on a miss the static
  SERVICE table already gives for an unregistered IRI, so there is no
  new failure shape at the SPARQL-semantics layer, only a new way to
  reach the existing "endpoint not found" outcome.

### 2.7 New `assume val`s and what runs where

**One new `assume val`, not two** — `wrap+exec:` and stdio-transport
`wrap+mcp:` are the same OS primitive (spawn a process, optionally
write to its stdin, capture its stdout) and share one realisation:

```
assume val process_run
  : binary_path:string
 -> argv:list string
 -> stdin_bytes:option string
 -> Tot (either string string)   (* Inl stdout | Inr error_message *)
```

- ASSUME-IO per the [`ocaml-boundary`](../../skills/ocaml-boundary/SKILL.md)
  taxonomy (ASSUME-IO: "realises `assume val` for file/clock/socket
  I/O" — process I/O is the same class, not a new one). `wrap+exec:`
  calls it with `stdin_bytes = None`; stdio-`wrap+mcp:` calls it with
  `stdin_bytes = Some <json-rpc request bytes>`.
- Stub patch: a new file in
  `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/`,
  named `<issue>_process_run_bind.sh` per Iron Rule #3, following
  `57_service_client_bind.sh`'s exact idiom (idempotent grep-marker
  check, python regex-replace of the extracted `failwith` stub,
  qualifier-alternation regex per that patch's own 2026-07-05 lesson
  about extraction qualifiers moving — §0.1's file, lines 51-68, is
  the cautionary precedent to copy defensively, not just the happy
  path). `<issue>` is a new GitHub issue, number to be minted at
  implementation time (next available after #284); the issue text
  should name this doc and both call sites (`wrap+exec:`, stdio-MCP).
- Realisation: `Unix.create_process` with an explicit argv array
  (never `Unix.open_process`/`/bin/sh -c`, per §2.6), a pipe for
  stdout (and stdin when `stdin_bytes = Some _`), a hard wall-clock
  timeout (reuse anti-pattern #17's existing "cap at 10 min, capture
  exit code explicitly" discipline — a hung wrapped tool must not hang
  the query), and no shell interpolation anywhere in the call chain.
- **`wrap+https:`/`wrap+http:`, HTTP-transport `wrap+mcp:`: zero new
  `assume val`s** — both are ordinary HTTP requests through the
  already-solved socket-I/O consumer (§0.2), exactly the reuse
  `SPARQL.Protocol.Client.fst`'s own banner promises for any future
  caller of that transport.

**What runs where:**

| Scheme | Native CLI | Browser (js_of_ocaml/wasm) |
|---|---|---|
| `wrap+https:`/`wrap+http:` | works (socket I/O) | works IF the consumer glue swaps in `fetch()`, exactly the precedent `factoidal_http_client_jsoo.ml` already set for the plain SPARQL Protocol client (§0.2) |
| `wrap+mcp:` (HTTP transport, e.g. this repo's own `fstar-mcp` server per the [`mcp-setup-readme`](../../skills/mcp-setup-readme/SKILL.md) skill) | works | works, same as above, subject to same-origin/CORS on the MCP endpoint |
| `wrap+mcp:` (stdio transport) | works (`process_run`) | **no realisation** — process spawn is not a capability js_of_ocaml/wasm_of_ocaml expose |
| `wrap+exec:` | works (`process_run`) | **no realisation** |

A browser/wasm build never registers the `process_run`-backed branch of
the resolver — this is the same "capability record, unimplemented
field defaults inert" discipline `store_caps.sc_decode_failure`
defaults `false` for backends that cannot detect it, or
`SPARQL.FullText`'s Slice 1 shipping "no ranking, dataset order only"
rather than partially faking a feature. A `wrap+exec:` IRI in a
wasm build resolves to `None` — indistinguishable from an unregistered
SERVICE endpoint, never a crash, because no code path to crash exists.

## 3. Part B — virtual RML backend

### 3.1 A `store_caps` realisation over an RML mapping

New module (placement, §4): `caps_of_rml_source`, a builder with the
same shape as `caps_of_indexed`
([`RDF.Store.Capabilities.fst:294-310`](../../formal/fstar/RDF.Store.Capabilities.fst))
and `caps_of_cottas` — construction is allowed to be effectful (reading
the source file/API response is exactly the same one-time ML read
`caps_of_indexed`'s caller already does to build an `indexed_graph`
before wrapping it); the resulting closures captured in the record are
`Tot` over the **already-read, already-parsed** in-memory value (a
`json_val` or `list source_row`) the builder captured, walked fresh on
every `sc_solve` call rather than pre-materialized into triples once.
That is the honest v1 boundary, and it is worth stating plainly against
Ontop's own claim of "virtual": **we do not re-fetch the source per
triple pattern call** (that would need a live streaming/pushdown API
the source itself doesn't offer, most sources here being static
files or a single REST response) — **we do not materialize RDF
triples** (there is no `list triple` sitting in memory or on disk
between queries) — the middle ground is "read+parse once per store
lifetime, re-walk per pattern," the same cost shape `caps_of_indexed`
already has for its own in-memory `indexed_graph`.

### 3.2 Pushdown model, stated in two sentences

`sc_solve`'s bound `{bs; bp; bo}` first narrows which `TriplesMap`s in
the mapping *could* produce a matching triple by structural inspection
of each map's predicate/subject term-map shape (a `bp = Some p` bound
rules out any `TriplesMap` whose predicate term map is a
different `TMF_Constant`, but not one using `TMF_Template`/
`TMF_Reference`, which must stay a candidate since evaluating it is the
only way to know); within a surviving candidate, the bound value is
then pushed into the *source's own iteration* — a JSONPath sub-step
evaluated per row and compared before running the row through
`RML.Eval`'s full term-map machinery, or (CSV) a plain column-equality
check via `RML.Sources.csv_reference_values` before constructing a
triple — rather than materializing every row's triple and filtering
after the fact. **Joins do not push down**: unlike Ontop's SQL
unfolding, which can express a join across multiple mapped tables in
one SQL statement the RDBMS executes, our sources are opaque documents
and APIs with no query language of their own to hand a join to, so
`RefObjectMap`/`joinCondition` evaluation stays exactly where it is
today — a SPARQL-level `join` (`SPARQL11.Algebra.fst`'s existing `join`
function) over two already-produced solution sequences, the same shape
a plain BGP already has over two independent `SERVICE` endpoints. This
is the v1 floor, stated as a floor rather than implied as parity with
Ontop's unfolding.

New small F* functions needed, additive to `RML.Sources`/`RML.Eval`,
reused verbatim otherwise (§4): `csv_iterate_filtered`/
`json_iterate_filtered`-shaped variants taking an extra early-exit
predicate over the row/JSONPath-step value, built by wrapping
`csv_parse_rows`/`eval_jsonpath` with a `List.Tot.filter` before the
existing per-row term-map evaluation runs — no new parsing, no new
term-map logic.

### 3.3 Estimate/count semantics for the planner

Because v1's `sc_solve` walks an already-in-memory row list (§3.1),
`sc_count_exact` is **genuinely exact** — a full linear scan over data
already resident in memory, not an approximation — so
`scf_estimate_is_exact = true` is honest here, unlike the COTTAS-on-disk
backend's bounds-based approximation
([`RDF.Store.Capabilities.fst:110-112`](../../formal/fstar/RDF.Store.Capabilities.fst)).
It is exact but not *cheap*: there is no index, so every `sc_estimate`/
`sc_count_exact` call is O(rows). This is fine for the sources this
program targets (an API response, a CSV export bounded by whatever the
source itself returns) and is precisely why materialize-and-cache wins
once a source stops being small (§3.4).

### 3.4 Materialize-and-cache vs virtual — a policy note, not a switch

Small/bounded/volatile sources (a REST endpoint's response, a modest
CSV export that changes between queries) → virtual: no caching
infrastructure, always current, acceptable O(rows) scans. Large/stable
sources (a big CSV dump that rarely changes) → materialize once via
the **existing** path: `RML.Eval.eval_triples_map` → `list triple` →
the same `materialize_dataset_backend`-shaped reuse
([`SPARQL11.Store.fst:381-390`](../../formal/fstar/SPARQL11.Store.fst))
already used for compaction → the existing COTTAS/indexed import
pipeline (rule #15: no new store-writing logic). These are **not
mutually exclusive per deployment** — a `GB_Union` of "this source's
`caps_of_rml_source`" and "that source's materialized-and-compacted
COTTAS store" is expressible **today**, with zero new plumbing, via
`union_caps` ([`RDF.Store.Capabilities.fst:272`](../../formal/fstar/RDF.Store.Capabilities.fst)) —
an operator pins whichever sources warrant materialization, per source,
without a global on/off switch.

## 4. Shared triplifier layer

One interface, consumed by both parts, reusing `RML.Mapping`/
`RML.Sources`/`RML.Eval` **verbatim** wherever the input shape matches:

| Function | Reused as-is by | New for this doc |
|---|---|---|
| `RML.Mapping.decode_mapping_document` | Part A (`rml=` lookup), Part B (mapping load) | — |
| `RML.Sources.json_iterate`/`csv_iterate`/`eval_jsonpath`/`csv_reference_values` | Part A (materializing path) | Part B's filtered variants (§3.2) wrap these, do not replace them |
| `RML.Eval.eval_triples_map` | Part A (batch materialize per fetch) | Part B does **not** call this in the hot `sc_solve` path (§3.1) — it is the parity-check target for Stage 5's acceptance test (§5) |
| Default Facade-X mapping (§2.3) | Part A only (no named `rml=`) | net-new, one F* constant per format |
| `caps_of_rml_source` / pushdown iterators | Part B only | net-new (§3) |

Module placement: a new `RML.VirtualSource.fst` (Part B's
`caps_of_rml_source` + filtered iterators) sits above `RML.Eval`/
`RML.Sources`/`RML.Mapping` and, like `RDF.Store.Capabilities.fst`
itself, transitionally opens `SPARQL11.Algebra` for `store_caps`'s
`triple_pattern_bound` type (same DAG position discipline that
module's own banner already documents,
[`RDF.Store.Capabilities.fst:16-28`](../../formal/fstar/RDF.Store.Capabilities.fst));
`RML.Eval.fst` already opens `SPARQL11.Algebra` today
([`RML.Eval.fst:35`](../../formal/fstar/RML.Eval.fst)), so no new DAG
edge is introduced, only a new module at the same layer —
**verify no cycle at implementation time**, per this doc's own
disclosure discipline rather than asserted as fact here. Part A's IRI
scheme parsing/request-building (`SPARQL.Service.Wrap.fst`) sits above
`SPARQL.Protocol.Client`/`RML.Eval`, consumed only by the OCaml-side
resolver glue (§2.5) — it produces no new evaluator entry point, only
functions the extended `service_endpoint_lookup` patch calls.

## 5. Staged rollout, with acceptance tests

One subagent, one commit per stage (Anti-pattern #23). Every stage's
fixture is vendored locally — no live network/process dependency in
CI, per the sandboxed, reproducible-build discipline this repo already
holds runners to.

| Stage | Deliverable | Acceptance test |
|---|---|---|
| 0 | This doc. | n/a |
| 1 | `wrap+https:`/`wrap+http:` GET fetch, format auto-detection, default Facade-X-equivalent mapping (§2.3), host allowlist + `FACTOIDAL_SERVICE_HTTP=1` opt-in (§2.6). No `rml=` yet. | Vendor a captured real public REST JSON response (e.g. a small GitHub repo-info payload, stored under `tests/fixtures/virtual-sources/http/`) served by a tiny local fixture HTTP server the test script starts; a `SERVICE <wrap+http://127.0.0.1:PORT/...>` BGP query recovers the expected default-mapped triples. |
| 2 | `rml=` fragment override, reusing an already-loaded `TriplesMap`. | Same fixture, an explicit `mapping.ttl` (reusing an `rml-runner` fixture shape), `SERVICE` query result triples byte-equal (canonical N-Quads comparison, `RDF.Canonical`) to what `bin/rml-runner` produces materializing the **identical** mapping against the **identical** bytes read from a file instead of fetched — proves the "hand fetched bytes to the same functions" claim in §2.2 step 3. |
| 3 | `wrap+mcp:` over HTTP JSON-RPC. | Vendor a canned `tools/call` request/response pair (fixture files, no live MCP server needed for the F*-side envelope-builder/parser unit test) plus a thin integration test against a local fixture HTTP server returning the canned response — proves the JSON-RPC envelope construction and the reused HTTP consumer glue both work end to end. |
| 4 | `wrap+exec:` behind the allowlist + `process_run`. | An allowlist config naming exactly one vendored local script (e.g. a repo-local Python/shell fixture emitting canned JSON to stdout) proves (a) the allowlisted alias resolves and triplifies correctly, (b) a non-allowlisted alias, or an attempted ambient-binary-name IRI, resolves to `None` (SERVICE-miss / silent-dependent empty result), matching `service_endpoint_lookup`'s existing miss contract exactly. |
| 5 | `RML.VirtualSource.fst` — `caps_of_rml_source`, pushdown iterators (§3). | Same fixture + mapping as Stage 2. Answer an identical BGP two ways: (a) `RML.Eval.eval_triples_map` materializing the full source then filtering (today's path), (b) `caps_of_rml_source`'s `sc_solve` under the SAME bound pattern, never calling `eval_triples_map`. Canonical N-Quads of both answers must be byte-equal — the explicit virtual-vs-materialized parity test this program's whole premise rests on. |
| 6 (indefinite, follow-up) | v2 TTL cross-query cache (§2.4); pushdown perf measurement (perf-benchmarking skill: no claim without a number); `wrap+` support for the RML XML/XPath source once RML Stage 4 lands; cross-source join pushdown — explicitly **not promised**, revisit only if a real corpus shows the need, per the RML program plan's own "don't build ahead of measured need" discipline. |

## 6. Iron-rules fit

All triplification decision logic — mapping decode, JSONPath/CSV
evaluation and its pushdown-filtered variants, the default Facade-X
mapping, the `wrap+` IRI scheme parser, the MCP JSON-RPC envelope
builder, `caps_of_rml_source`'s pattern-narrowing and pushdown — is F*,
extracted, per rules #1/#2/#4/#7. The only OCaml additions inside the
verified boundary are `assume val` realisations:

- **`process_run`** (§2.7) — ASSUME-IO, one new primitive, covering
  both `wrap+exec:` and stdio-transport `wrap+mcp:`.
- **Zero new realisations** for `wrap+https:`/`wrap+http:` and
  HTTP-transport `wrap+mcp:` — both reuse the existing
  `factoidal_http_client.ml` socket-I/O consumer verbatim (§0.2/§2.7),
  exactly the reuse that module's own banner promised any future
  caller.
- The resolver's "hashtable hit, else check wrap+ prefix, else `None`"
  extension to `57_service_client_bind.sh` (§2.5) stays rule-#15
  compliant — dispatch wiring, not semantic logic; the *how* to
  triplify is 100% F*.
- Allowlist/config-file parsing (host list, MCP/exec alias tables) is
  CONSUMER code in `bin/factoidal-http`/`bin/factoidal-cli` (rule
  #11's CONSUMER class) — deployment policy, not verified computation,
  same classification the existing CORS-origin allowlist already has.

No new byte-layout decision is introduced anywhere in this doc — every
new OCaml function is either a straight `Tot`-boundary I/O call
(`process_run`) or a thin dispatch/config reader, never a serializer.
