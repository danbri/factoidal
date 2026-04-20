# LWSP1 Phase 1 — Architectural decision

**Date:** 2026-04-18. Read-only planning doc, no code in this commit.
**Tracks:** [#88 LWSP1](https://github.com/danbri/factoidal/issues/88).
**Scope:** Decide language/stack, directory layout, backend-trait reuse,
Phase-1 sub-deliverables, and surface the known risks before the first
code commit lands.

This doc is deliberately opinionated. Where a question is a genuine
judgement call (rather than an obvious call), it is flagged as such.

## 1. Language and stack

**Decision: extend `factoidal-http` in OCaml, on top of the existing
F\*-extracted core.**

`docs/lws/implementation-spec.md` §15 notes Rust-plus-Oxigraph and
TypeScript-plus-fastify as reasonable. A third option was not listed
because the spec was written without presuming our codebase: **reuse
the F\*-verified pieces we already have, and write the LWS-specific
glue in OCaml as a sibling to `factoidal_http.ml`.**

### What we would reuse by picking OCaml

| Factoidal asset | F\*-verified? | LWS use |
|---|---|---|
| `SPARQL.HTTP.parse_http_request` | yes (commit `0ffa31a`, no `assume val`, no `--admit_smt_queries`) | request framing for every LWS endpoint |
| `SPARQL.Protocol.parse_accept_header` / `pick_response_format` | yes | content negotiation (`text/turtle`, `application/ld+json`, `application/linkset+json`) |
| `Parser.Turtle` | yes (296/313 W3C) | GET/PUT of `text/turtle` resources |
| `Parser.NTriples` / `Parser.NQuads` / `Parser.TriG` | yes (majority of W3C pass) | multi-format backend-read support "for free" |
| `Parser.RDFXML` | yes (121/166) | bonus format, no extra work |
| `RDF.Graph.Executable.rdf_dataset` | yes | LWS resource representation when an RDF source is in memory |
| `SPARQL11.Algebra.apply_update` | yes | phase 3/N3-Patch can reuse delete-then-insert semantics |
| `Parser.NQuads.emit_nquads` (being added per #87 §3) | will be | phase 3 atomic-apply dump |
| `factoidal_http.ml` accept loop + socket glue | unverified glue — but already debugged, CORS-aware, `--read-only` flag, signal handlers | starting point for the LWS listener |

### What Rust-plus-axum-plus-Oxigraph buys us

- Mature async runtime (tokio), robust WebSocket libs (tokio-tungstenite).
- Oxigraph is a well-tested embedded quad store — phase-6 SQL backend
  ships almost-free.
- Wider pool of Solid server implementations to crib from.

### What Rust-plus-axum costs us

- Zero reuse of the F\*-verified core. Either (a) re-extract our F\*
  modules to Rust via a KaRaMeL-to-Rust path (research-grade; today
  KaRaMeL targets C only), or (b) reimplement Turtle/N-Quads/TriG/
  RDF/XML parsers, Accept-header parsing, and SPARQL Update evaluation
  against a different library. Both violate CLAUDE.md rule #7 ("no
  cobbling") unless the F\* specs are ported forward.
- Dual-stack deployment: a Rust LWS server and an OCaml Protocol
  server, with different operational profiles (build systems, CVE
  tracking, container images).
- No shared mtime/ETag/validator code between the two.

### TypeScript-plus-fastify

Worse than Rust on the reuse axis (no KaRaMeL-to-JS path is comparable
— js_of_ocaml is our current JS target, and it's already shipping our
F\* code). TS also fails the "formally verified" story harder: the
only verified surface left would be the shim around F\*-extracted-to-JS
modules. Not an improvement over extending the OCaml server.

### One-line rationale

**OCaml lets us ship an LWS Phase-1 read path where ~70% of the code
below the handler dispatcher is already F\*-verified.** Rewriting
those 5–7 k lines in Rust just to get `axum` is not a good trade in
this codebase.

### Honest caveats

- **Async story**. OCaml 4.14 + plain `Unix` sockets is single-threaded
  per-connection (see `factoidal_http.ml`). Phase 5 WebSocket
  notifications will force us to pick between `lwt`-based dream,
  `eio` (OCaml 5-only), or a thread-per-connection model. This is a
  real cost. See §7 Risks.
- **JSON-LD document parsing**. We have `Parser.JSONResults.fst`
  (SPARQL results JSON) and no F\* JSON-LD *document* parser. Inbound
  JSON-LD (phase 2 write path) will need either an assume-val'd
  OCaml stub (`ezjsonm` + hand-rolled context expansion) or a new F\*
  module. See §7.
- **Extraction overhead**. Every F\* module added is ~2× its OCaml
  equivalent in LOC. This cost has already been amortised for the
  RDF/SPARQL core; new LWS modules pay it fresh.

## 2. Directory layout

**Decision: keep F\* modules together in `formal/fstar/`, with a clean
module prefix.** Do not create a `formal/fstar/LWS/` subdirectory.

### Why the flat layout wins

- Every existing F\* module (`SPARQL.HTTP`, `SPARQL.Protocol`,
  `SPARQL11.Algebra`, `Parser.NQuads`, etc.) lives directly in
  `formal/fstar/`. Build tooling (`Makefile`, `build-ocaml.sh`,
  `ocaml-patches.sh`) assumes that layout. Adding a subdirectory
  splits the convention and forces `build-ocaml.sh` surgery.
- F\* module naming already gives us namespacing: `LWS.Resource`,
  `LWS.Linkset`, `LWS.Storage`. The filename-to-module mapping F\*
  uses (`LWS.Resource.fst` for `module LWS.Resource`) keeps the flat
  directory readable.
- Extracted OCaml files will then be `LWS_Resource.ml` etc., matching
  the pattern of `SPARQL_HTTP.ml`.

### Proposed F\* modules (added over Phase 1–4)

| Module file | Phase | Purpose |
|---|---|---|
| `formal/fstar/LWS.Resource.fst` | 1 | Core abstract operations (`resource_state`, `operation_outcome`, HTTP binding glue-side of §5). |
| `formal/fstar/LWS.Linkset.fst` | 1 | RFC 9264 linkset AST, `application/linkset+json` serialiser, `Link` header emitter. |
| `formal/fstar/LWS.Storage.fst` | 1 | Storage description resource, root-container logic, `pim:Storage` detection. |
| `formal/fstar/LWS.Container.fst` | 1 | Container representation (Turtle + JSON-LD round-trip), `ldp:contains` derivation. |
| `formal/fstar/LWS.ACL.fst` | 4 | WAC engine — authorization decision over `acl:*` triples. |
| `formal/fstar/LWS.N3Patch.fst` | 3 | N3 Patch parser + evaluator (blank nodes allowed in `?insertions` per LWS delta). |

### Proposed OCaml glue (hand-written, unverified boundary)

| File | Content | Rule |
|---|---|---|
| `formal/fstar/ocaml-output/factoidal_lws.ml` | New binary entry point. Socket accept loop (cribbed from `factoidal_http.ml`), filesystem I/O (`open_in`/`stat`/`rename`/`Unix.lockf`), Signal handlers. Calls `LWS_*.ml` modules for all RDF/linkset/resource decisions. | Glue only per rule #15. |
| `formal/fstar/ocaml-output/lws_fs_backend.ml` | Filesystem `StorageStore` implementation: maps IRIs to paths, atomic writes via `rename(2)`, sidecar `.linkset.jsonld` files. No RDF parsing here — delegates to `Parser_Turtle.parse_turtle` etc. | I/O glue. |
| `bin/darwin-arm64/factoidal-lws`, `bin/linux-x86_64/factoidal-lws` | Compiled binaries, committed per rule #9. | — |

### Why a separate binary, not a flag on `factoidal-http`

SPARQL Protocol and LWS are different wire protocols that happen to
share a transport. `factoidal-http` today is an ~1300-LOC file
specialised for `/query` + `/update` with SPARQL-specific content
negotiation, CORS, and UPDATE sandboxing. Stuffing LWS resource
routing into the same binary would muddle both. Build tooling
already compiles multiple binaries from the same module set
(`factoidal`, `factoidal-http`, `w3c_runner`, `parquet_probe`); one
more is cheap.

**Judgement call, not slam-dunk:** shared-binary mode has an appeal
if a deployment wants `/query` + `/resources/*` on the same port. We
can retrofit this in phase 6 by extracting `factoidal_http.ml`'s
listener into a shared module and dispatching on path prefix. For
now, two binaries.

## 3. Backend trait — reuse versus new

The LWS spec's §11 `StorageStore` trait defines eight operations.
Our existing `rdf_dataset` has none of them — it's a pure
representation, not a backend abstraction.

**Decision: define the trait in F\* (`LWS.Resource.fst` or a new
`LWS.Backend.fst`) as a typeclass-equivalent record of function
pointers. Filesystem backend is hand-written OCaml glue in
`lws_fs_backend.ml` and `assume val`-wired per our pattern.**

### What we reuse from factoidal

- `factoidal_cli.ml`'s RDF file loaders (`load_rdf_dataset`,
  `detect_format`). These already handle all six RDF formats we
  support. `lws_fs_backend.ml` can call them directly for any
  read-of-RDF-resource.
- `rdf_dataset` as the in-memory representation once a file has
  been parsed. That is the type the LWS container-representation
  logic will operate on.
- `Parser.NQuads.emit_nquads` (once #87 §3 lands) for dump-friendly
  serialisation of RDF sources.

### What we add

- `LWS.Backend.storage_store` record with fields mirroring §11:
  `bs_get`, `bs_head`, `bs_put`, `bs_patch_rdf`, `bs_delete`,
  `bs_list_contained`, `bs_linkset`, `bs_put_linkset`. Each field is
  an `assume val`-able function with an OCaml stub.
- For Phase 1, only `bs_get`, `bs_head`, `bs_list_contained`,
  `bs_linkset` need to be wired. Write-side stubs return
  `not_supported` until phase 2.

### Why not just extend `rdf_dataset`

`rdf_dataset` is the *model*, not a backend. We want the model to
stay pure and verified; the backend is where non-RDF concerns (file
sizes, mtimes, paths, atomicity) enter. Mixing them breaks the
abstraction already proven in `SPARQL11.Store.fst` (`graph_backend`
dispatches over List / HDT / COTTAS backends).

### Honest caveat

For Phase 1 read-only the backend can be a lot thinner than §11's
full trait. We only need:
- "map IRI to absolute filesystem path", which is string surgery —
  lives in F\* as `iri_to_fs_path`;
- "load representation at path in requested media type", which is
  exactly `factoidal_cli.ml`'s `load_rdf_dataset` plus a
  serialisation pass (Turtle or JSON-LD).

We should **not** define the full eight-method trait in Phase 1. Start
with two methods (`bs_get`, `bs_list_contained`) and grow as phases
2–3 add write/patch. This keeps the Phase-1 diff small.

## 4. F\* modules reusable verbatim

Rough estimate of how much LWS functionality these cover, by phase:

| Module | Phase-1 coverage | Phase-2 | Phase-3 | Phase-4 | Phase-5 |
|---|---:|---:|---:|---:|---:|
| `SPARQL.HTTP.parse_http_request` | 100% of framing | 100% | 100% | 100% | (WebSocket: new) |
| `SPARQL.Protocol.parse_accept_header` | 100% of conneg | 100% | 100% | — | — |
| `Parser.Turtle.parse_turtle` | 100% of Turtle read | 100% (plus write stub) | 100% | — | — |
| `Parser.NTriples`, `Parser.NQuads`, `Parser.TriG` | multi-format GET | multi-format PUT | — | — | — |
| `Parser.RDFXML` | bonus format | — | — | — | — |
| `Parser.JSONResults` | **not reusable**; it's SPARQL-results JSON, not JSON-LD documents | — | — | — | — |
| `RDF.Graph.Executable` (rdf_dataset, triple, literal, lang_tag, datatype) | 100% of model | 100% | 100% | — | — |
| `SPARQL11.Algebra.apply_update` | — | — | reference for delete-then-insert atomicity | — | — |
| `Parser.NQuads.emit_nquads` (after #87 §3) | dump-format | serialise backend | — | — | — |

**Rough coverage estimate for Phase 1 read path:** ~60–70% of the
non-glue logic is already verified. The new F\* LOC Phase 1 needs is
roughly: linkset AST + emitter (~200 LOC), container representation
builder (~150 LOC), path-to-IRI helper (~50 LOC), storage-description
emitter (~80 LOC). Call it ~500 LOC of new F\* for Phase 1.

## 5. Phase-1 concrete deliverables

Each bullet is a candidate one-commit subagent task. Self-contained,
can be executed in any order, but the build-after-each-commit rule
(#9, #11) applies. **Pick 5–8 and sequence them.**

1. **`LWS.Linkset.fst` — linkset AST and JSON serialiser.**
   Types: `link_item = { li_anchor : string; li_rel : string; li_href : string; li_attrs : list (string & string) }`,
   `linkset = list link_item`. Functions:
   `emit_linkset_json : linkset -> string` producing
   `application/linkset+json` per RFC 9264. Also
   `emit_link_header : linkset -> string` producing the `Link:`
   header. Round-trip smoke test: at least one linkset with `up`,
   `acl`, `describedby`, `storageDescription`, and one `item` link.
   No `assume val`, no `--admit_smt_queries`. ~200 LOC F\*.

2. **`LWS.Storage.fst` — storage description emitter.**
   Function `emit_storage_description : owner:option iri -> quota:option nat -> supported_auth:list string -> string` producing a
   Turtle document with `rdf:type pim:Storage` and the optional
   fields. Round-trip through `Parser.Turtle`. ~80 LOC F\*.

3. **`LWS.Container.fst` — container representation builder.**
   Input: `container_iri : wf_iri`, `members : list wf_iri`,
   `mtimes : list (wf_iri & nat)`. Outputs:
   `emit_container_turtle : ... -> string` (LDP Basic Container with
   `ldp:contains` triples), `emit_container_jsonld : ... -> string`
   (JSON-LD with `@type: Container`, `items: [...]`). Both verified,
   both round-trip through `Parser.Turtle` / a future JSON-LD loader.
   ~150 LOC F\*.

4. **`LWS.Resource.fst` — Phase-1 outcome mapper.**
   `type operation_outcome = OC_Created | OC_Success of representation | OC_NotFound | OC_Unauthenticated | OC_NotPermitted | OC_Conflict | OC_Malformed of string | OC_Unsupported`.
   `map_outcome_to_status : operation_outcome -> method -> nat` implements the §6.1 table. ~50 LOC F\*. (Write-path outcomes
   stubbed; only Phase-1-relevant arms wired.)

5. **`factoidal_lws.ml` skeleton — new binary.**
   Copy of `factoidal_http.ml`'s accept loop and CORS/`write_response`
   plumbing. Stripped of SPARQL dispatch. Routes: `GET /.storage`
   (storage description), `GET /` (root container), `GET /<path>`
   (resource), `HEAD /<path>`, `OPTIONS /<path>`. All routes 501 in
   the first commit except a hard-coded `GET /.storage`. ~300 LOC OCaml.
   `bin/<platform>/factoidal-lws` built by `build-ocaml.sh compile`.

6. **`lws_fs_backend.ml` — filesystem read-only backend.**
   Helpers: `iri_to_fs_path : root:string -> iri:string -> option string`
   (checks the IRI is under the server's root, refuses `..`),
   `load_resource : path:string -> accept:media_type -> result`.
   Uses existing `Parser.Turtle` / `Parser.JSONResults` / etc. Writes
   nothing. ~200 LOC OCaml glue.

7. **CLI wiring for `factoidal-lws`.**
   `--storage-root DIR`, `--port N`, `--host H`, `--cors`, `--base IRI`.
   Start-up: read the root directory, verify it contains a
   `.storage.ttl` and a `.acl` (phase 4 will populate these; phase 1
   writes a trivial default if absent). Health endpoint `GET /.ping`
   → 200 `"ok"`. ~100 LOC OCaml.

8. **Linkset GET handler wiring.**
   `GET /<path>?linkset` returns the linkset for `<path>` as
   `application/linkset+json`. Pulls anchors, rels, hrefs from
   `LWS_Linkset.linkset_for_resource` (a new function in
   `LWS.Linkset.fst` that takes a path + members + parent and yields
   a `linkset`). Exercises the end-to-end path: F\* AST → F\* emitter
   → OCaml socket write. Good first-commit integration test.

### Suggested commit order

1, 2, 4 (pure F\* additions, no OCaml touch). Then 5+7 together
(binary skeleton, useful-but-minimal). Then 3 and 8 (container +
linkset wiring). 6 can slot anywhere after 5.

## 6. Out-of-scope for Phase 1

Matches `docs/lws/implementation-spec.md` §14 phase-1 scope; listed
explicitly so the first few commits don't accrete scope:

- **Authentication** — no OIDC, no did:key, no SAML, no SSI-CID. All
  Phase-1 requests are treated as public-read. `WWW-Authenticate`
  header emission is deferred to Phase 4.
- **Authorization / WAC / ACP** — no ACL resolution. `Link: rel="acl"`
  *is* emitted in linksets (points to where the ACL *would* live),
  but the GET on that URL returns 404. Phase 4 fills this in.
- **Write path** — PUT, POST, DELETE all return 501. No intermediate
  container creation, no Content-Type enforcement (since nothing is
  being written), no ETag / If-Match / If-None-Match bookkeeping.
  Phase 2.
- **N3 Patch** — no PATCH handling. `Accept-Patch` is not emitted on
  GET/HEAD responses. Phase 3.
- **Notifications** — no LDN inbox POST, no Solid Notifications
  Protocol, no WebSocket. `Link: rel="http://www.w3.org/ns/ldp#inbox"`
  not emitted. Phase 5.
- **Quad-store backend** — filesystem only. Oxigraph / Jena TDB /
  object-storage backends are Phase 6.
- **Problem details (RFC 9457)** — Phase 6 hardening. Phase 1 errors
  are plain `text/plain` like `factoidal_http.ml` already produces.
- **Tombstones / 410** — resources either exist (200) or don't (404).
  No bookkeeping for deleted URIs. Spec §16 open question; don't fix.

## 7. Risks and unknowns

### 7.1 OCaml WebSocket support (Phase 5)

The realistic options for OCaml 4.14 + `Unix`-socket environment we
have today:

- **`websocket.ocaml` / `websocket-lwt-unix`** (mature, Lwt-based).
  Would force an Lwt runtime on the LWS server. Our current
  `factoidal_http.ml` is synchronous; adopting Lwt is invasive but
  survivable. ~2–3 k LOC of structural change.
- **`dream` (Aantron).** High-level Lwt-based HTTP server + built-in
  WebSocket support. Would essentially replace `factoidal_http.ml`'s
  accept loop. Pro: modern, idiomatic, one-dep. Con: pulls in a
  large dependency tree and moves us away from the
  thin-Unix-glue aesthetic of the rest of the codebase.
- **`cohttp-lwt-unix` + handrolled WebSocket framing.** Too much
  work; avoid.
- **OCaml 5 + `eio` + `piaf`.** Clean async story, but requires
  OCaml 5 across the whole project. Not currently on our switch
  (`ocaml-base-compiler.4.14.1`).

**Best-fit recommendation for Phase 5:** `dream` + `dream-websocket`.
It is purpose-built for this problem and the WebSocket handler
signature is minimal. The migration from our `factoidal_http.ml`
synchronous accept loop to a `dream`-hosted handler is a Phase-5
commit, not a Phase-1 concern.

**Phase-1 impact:** zero. Phase 1 is request/response HTTP only.
Flag this now so Phase 5 planners don't rediscover it.

### 7.2 JSON-LD document parsing and serialisation

We have no F\* JSON-LD parser. `Parser.JSONResults.fst` parses the
SPARQL Results JSON format (a specific, narrow shape), not arbitrary
JSON-LD documents.

**Phase 1 needs:** JSON-LD *serialisation* only (container
representations, linkset representation). Serialisation is
straightforward because we control the shape — no context expansion,
no compaction. A hand-written F\* emitter in `LWS.Container.fst` and
`LWS.Linkset.fst` is fine for Phase 1.

**Phase 2 needs:** JSON-LD *parsing* (inbound PUT of
`application/ld+json`). Options:

- `assume val parse_jsonld_document : string -> iri -> result (list triple)`,
  stubbed in `ocaml-patches.sh` with an OCaml call to
  `ezjsonm` + a hand-rolled context expansion. **Acceptable for Phase
  2; tracked as a new issue.** Parses the flattened form we
  serialise; rejects anything requiring real context expansion.
- Write `Parser.JSONLD.fst`. ~1 k LOC of F\* work, real ambition.
  Would be the right answer eventually but is Phase-3-or-later scope.

**Phase-1 impact:** serve `application/ld+json` on GET only; if PUT
arrives with that content-type, respond 501 with "JSON-LD write path
not yet implemented." Phase 2 swaps in the stub. This punts the
interesting work to when we actually need it.

### 7.3 File-locking for atomic writes

POSIX `Unix.lockf` works on macOS and Linux. Atomic rename (`rename(2)`)
gets us most of what we need for Phase 2. Windows cross-compat is
**out of scope** — our build matrix is `darwin-arm64` and
`linux-x86_64`. Skip.

**Phase-1 impact:** zero, since Phase 1 is read-only.

### 7.4 `wf_iri` refinement at the filesystem boundary

`iri_to_fs_path` takes a `wf_iri` (passed `is_iri` check). The inverse
— turning a filesystem path back into a `wf_iri` for the `@id` of a
container representation — requires us to construct a string and
re-check `is_iri`. The check will pass for well-formed path segments
but may not for files with exotic characters.

**Mitigation:** reject resource creation with a path segment that
wouldn't round-trip to a valid IRI (phase 2 concern). Phase-1 is
read-only; any file on disk is fair game to serve, but the `@id`
must be valid — refuse-or-fudge decision belongs to phase 2.

### 7.5 Shared state between LWS writes and SPARQL updates

If we ever want to run `factoidal-http` and `factoidal-lws` against
the same filesystem root (or worse, the same in-memory dataset),
we need cross-process synchronisation. Out of scope for Phase 1
(two separate binaries, different datasets). Flag for phase 6.

### 7.6 Build system

`build-ocaml.sh` will need one new section to compile
`factoidal_lws.ml`. Follows the pattern at
`build-ocaml.sh:221–228`. Binaries land in
`bin/<platform>/factoidal-lws` and must be committed per rule #9.
Zero novelty; called out for completeness.

## 8. What this decision is NOT committing us to

- **Not** committing to `factoidal-lws` being the final product name.
  `factoidal-solid`, `factoidal-resource`, or a merged `factoidal`
  CLI-with-subcommands are all still on the table.
- **Not** committing to the OCaml runtime library set. If
  Phase 5's WebSocket work pulls in `dream`, we may migrate
  `factoidal-http` to the same runtime simultaneously — that's a
  separate decision.
- **Not** committing to ACL file format beyond "WAC-compatible
  Turtle." Phase 4 will nail down the ACR / ACP dual-stack question.

## 9. Summary

| Question | Answer |
|---|---|
| Language / stack | OCaml + F\*-verified core, extending the factoidal codebase. |
| New binary | `bin/<platform>/factoidal-lws`, built by `build-ocaml.sh compile`. |
| F\* module prefix | `LWS.*` (flat, in `formal/fstar/`). |
| OCaml glue | `factoidal_lws.ml` + `lws_fs_backend.ml`. |
| Backend trait | Defined in F\* (`LWS.Backend.storage_store`), Phase-1 wires only the 2–3 read methods we actually use. |
| Reuse | `SPARQL.HTTP`, `SPARQL.Protocol` (Accept), `Parser.Turtle/NTriples/NQuads/TriG/RDFXML`, `RDF.Graph.Executable`. ~60–70% of Phase-1 non-glue logic is already verified. |
| Out of scope | Auth, N3 Patch, notifications, write path, non-FS backends. |
| Phase-5 hinge | WebSockets → likely Dream migration, not a Phase-1 decision. |
| Phase-2 hinge | JSON-LD write-side parser, likely an `assume val`-wired stub. |

This is one of those decisions where the "right" answer depends on
whether you weigh the F\*-verification reuse story as a strategic
asset or as a historical accident. Given CLAUDE.md iron rule #7 and
the existing investment in extraction, **OCaml reuse wins.** A
future deployer who prefers the Rust ecosystem can build an
independent LWS server against our F\*-extracted-to-C (via KaRaMeL)
core, once that path is productionised. That is a Phase-6+
conversation, not a Phase-1 blocker.
