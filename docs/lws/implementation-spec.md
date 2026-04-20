# Linked Web Storage — implementation spec

A pragmatic implementation brief for a server conforming to the draft W3C
Linked Web Storage Protocol (FPWD, 31 March 2026), informed by but not
bound to the non-client-side portions of the Solid Protocol 0.11.0 CG
Report.

Status: implementation brief, not a standards document. Where it
restates normative requirements from published specs, the cited
specification is authoritative. Where it diverges, the divergence is
marked and justified.

## 1. Sources

Normative:

- LWS Protocol 1.0, W3C FPWD, <https://www.w3.org/TR/lws-protocol/> and
  editor's draft <https://w3c.github.io/lws-protocol/lws10-core/>.
- LWS Use Cases, W3C Group Note Draft, <https://www.w3.org/TR/lws-ucs/>.
- Solid Protocol 0.11.0 CG Report, <https://solidproject.org/TR/protocol>.
  Treated here as a substantive input, not rubber-stamped.
- WAC, <https://solidproject.org/TR/wac>.
- Solid Notifications Protocol, <https://solidproject.org/TR/notifications-protocol>.
- LDP 1.0, RFC 9110/9111/9112, RFC 8288, RFC 5789, RFC 6570, RFC 9264
  (Linksets), RFC 6892 (`describes` link relation), N3, JSON-LD 1.1,
  Turtle, RDF 1.1 Concepts.

Informative: Fedora API 1.0 (referenced in the WG charter as a
comparison point), LDN, Solid-OIDC.

## 2. Scope and non-goals

In scope:

- An HTTP server that exposes resources, containers and associated
  metadata according to the LWS resource model.
- Pluggable authentication via authentication suites. Ship OIDC (via
  Solid-OIDC where compatible) and `did:key` suites; stub SAML and
  self-signed controlled-identifier (SSI-CID) suites behind a common
  interface.
- Web Access Control as the default authorization engine, with an
  extension seam for ACP.
- N3 Patch processor for RDF sources.
- Notifications: LDN receiver plus a WebSocket channel per Solid
  Notifications Protocol.
- CORS conforming to the Solid Protocol rules.
- A storage backend abstraction so the same HTTP layer can run against
  filesystem, object storage (S3 or compatible) and a SQL/quad-store
  backend.

Out of scope in this brief:

- Client-side libraries, browser login UIs, pod management dashboards,
  Solid-OIDC relying-party flows above what the server itself needs.
- Application-level data-shape enforcement (SHACL), data
  interoperability panels, "type indexes" as a first-class feature.
- Profile-document social features (inbox semantics beyond LDN,
  follower graphs, etc.).
- Migration tooling from existing Solid pods.

## 3. Architecture

Three layers, orthogonal:

1. **Resource core.** Abstract operations on resources: create, read,
   update, delete, enumerate members. Defined in terms of states and
   responses, without reference to HTTP. A resource is either a
   container or a data resource; both have representations and a
   linkset.

2. **HTTP binding.** The REST binding maps the abstract operations to
   HTTP/1.1 and HTTP/2 (RFC 9110, 9112, 9113), with content negotiation,
   `Link` headers, CORS and problem details. This layer owns
   representation formats and status codes.

3. **Authentication and authorization.** Authentication is delegated to
   a pluggable suite that, on success, returns a set of verified
   identifier claims about the requesting agent. Authorization is a
   separate engine (WAC by default) that decides whether a given agent
   may perform a given operation on a given resource.

The split between (1) and (2) follows the LWS editors' intent: abstract
operations first, so responses are uniform across PUT, PATCH and
extension bindings. An implementation that exposes only the HTTP
binding is conformant; the abstraction exists mainly to keep the code
testable and to leave room for non-HTTP bindings (e.g. a CoAP or
MQTT-backed variant) without rewriting the authorization engine.

## 4. Resource model

### 4.1 URIs and hierarchy

- Storage is a tree of containers rooted at a container resource of
  type `pim:Storage`. Slash semantics from Solid Protocol §3.1 apply:
  a URI ending in `/` denotes a container, a URI not ending in `/`
  denotes a data resource. If both `foo` and `foo/` are requested and
  only one exists, the server MAY 301 to the existing form; it MUST
  authorize before redirecting.
- The server MUST support more than one storage per host. Storages
  occupy non-overlapping URI paths.
- URI allocation on POST: the new resource URI is under the request
  URI's container. The server is responsible for uniqueness. The
  `Slug` header is not honoured (per the 0.11 delta removing the
  optional requirement).

### 4.2 Resources

Every LWS resource has:

- A URI.
- A current representation (zero or more bytes plus a media type).
- A linkset (see §4.4) holding typed links to associated resources
  including the ACL/ACR, the linkset itself, `describedby` targets,
  the storage description, and `rel="up"` to the containing container.
- A last-modified timestamp. The HTTP server MUST generate
  `Last-Modified` on GET and HEAD responses. This is a LWS delta from
  Solid 0.11 which left it as SHOULD; the new text makes it MUST.

A container additionally has a containment set: an ordered collection
of contained resource URIs. Containment is expressed in the container's
RDF representation via `ldp:contains` and, for LWS, mirrored in the
container's linkset as `item` link relations. The preferred JSON-LD
property is `items` per the LWS ED.

### 4.3 Containers

- The server MUST represent containers as LDP Basic Containers for
  backwards compatibility.
- For container representations, the server MUST include containment
  triples (`ldp:contains`) and SHOULD include contained-resource
  metadata: `rdf:type` (using the IANA media-type URI template), size,
  `dcterms:modified` and `stat:mtime`. These are server-generated and
  protected: POST/PUT/PATCH attempts to modify them MUST return 409.
- Intermediate containers MUST be created automatically on PUT or
  PATCH to a deep path.
- DELETE on a non-empty container MUST return 409. DELETE on the root
  container or its ACL/ACR MUST return 405.

### 4.4 Linksets (LWS delta from Solid auxiliary resources)

Solid 0.11 uses "auxiliary resources" — separate RDF documents for ACL
and for descriptive metadata, discovered via `Link: rel="acl"` and
`Link: rel="describedby"`. LWS generalizes this to a single linkset per
resource, per RFC 9264, discovered via `Link: rel="linkset"`.

Implementation implications:

- Every resource MUST have an associated linkset resource, served as
  `application/linkset+json` (and optionally `application/linkset`).
- The linkset MUST carry at minimum: `type` (media-type-based), `acl`
  or equivalent authorization-resource link, `describedby` targets,
  `storageDescription`, `up` (parent container), `author`, and — for
  containers — `item` links to contained resources.
- The `Link` HTTP header MUST continue to advertise the individual
  relations in responses. The linkset is an additional, single
  discovery artefact, not a replacement for headers. This keeps
  existing clients working.
- Clients manipulate containment and other relations by PATCHing the
  linkset, not the container's RDF representation directly. This is
  the mechanism by which a container's membership can be edited
  without violating the rule that containment triples in the container
  representation itself are protected.

Rationale for the departure from Solid auxiliary resources: a single
discovery document is easier to cache, easier to reason about, and
reduces round trips. The FPWD editors' notes and UCS issues #47/#48
signal intent to standardize on linksets.

### 4.5 Storage description

Each storage has a storage description resource discoverable from any
resource in the storage via `Link: rel="http://www.w3.org/ns/solid/terms#storageDescription"`.
The description MUST include `rdf:type pim:Storage` and MAY include
owner, quota, supported authentication suites, supported authorization
engines, and server version.

## 5. Operations

### 5.1 Core operations

For each operation the server produces one of the following outcomes,
mapped to HTTP status codes in §6:

- `created` — new resource was created (CREATE only).
- `success` — operation completed, possibly with a representation.
- `unchanged` — conditional request short-circuited (e.g. `If-None-Match`).
- `not_found` — target did not exist.
- `unauthenticated` — no valid credential presented.
- `not_permitted` — credential valid, authorization denied.
- `conflict` — precondition violated or state conflict (e.g. non-empty
  container DELETE, protected triples edited, N3 Patch `?where`
  unsatisfied).
- `malformed` — syntactically invalid request (bad RDF, bad patch, bad
  media type).
- `unsupported` — method or media type not supported on this resource.
- `unknown_error` — reserved for unanticipated failures.

### 5.2 Read

HEAD, GET and OPTIONS MUST be supported. `Allow`, `Accept-Patch`,
`Accept-Post` and `Accept-Put` MUST appear in responses, reflecting
what the authenticated agent may actually do.

### 5.3 Create, update

- POST to a container creates a new contained resource with a
  server-assigned URI under the container's path.
- PUT to a URI creates the resource if absent, or replaces its
  representation if present.
- Both require `Content-Type`; absence MUST be rejected with 400.
- PUT or PATCH to the container's RDF representation that would alter
  containment or protected metadata MUST return 409.
- PUT or PATCH to a linkset is the supported route for editing
  containment or link metadata; the server validates shape and
  re-derives the container representation.
- On POST success the response MUST set `Location` to the new URI and
  return 201.

### 5.4 N3 Patch

For RDF-bearing data resources and for linksets, the server MUST accept
`PATCH` with `Content-Type: text/n3` following Solid Protocol §5.3.1,
with one divergence:

- The LWS ED removes the Solid constraint that `?insertions` MUST NOT
  contain blank nodes. Implementations MUST allow blank nodes in
  `?insertions`; each blank node in `?insertions` yields a freshly
  allocated blank node in the target graph.

All other constraints hold: exactly one patch resource of type
`solid:InsertDeletePatch`, formulae are flat (no nesting), variables
in `?insertions` and `?deletions` must be bound by `?conditions`,
multiple or zero bindings of `?conditions` yield 409, missing
`?deletions` triples yield 409, malformed patches yield 422.

A straightforward implementation strategy: parse N3 with a permissive
parser; translate the patch into an in-memory RDF dataset diff plus a
SPARQL-style BGP matcher for `?where`; apply deletions then insertions
atomically; persist.

### 5.5 Delete

DELETE MUST cascade to linksets and any other associated auxiliary
resources. DELETE on root storage container or its ACL MUST 405.
DELETE on a non-empty container MUST 409. Subsequent GET on a deleted
URI SHOULD return 410 if the server tracks tombstones, else 404.

## 6. HTTP binding

### 6.1 Status codes

| Outcome | Method(s) | Status |
| --- | --- | --- |
| created | POST, PUT | 201 |
| success with representation | GET | 200 |
| success no content | PUT, PATCH, DELETE | 204 |
| unchanged | GET conditional | 304 |
| not_found | any | 404 (or 410 for tombstones) |
| unauthenticated | any | 401 |
| not_permitted | any | 403 (server MAY respond 404 to untrusted origins) |
| conflict | PUT, PATCH, DELETE | 409 |
| malformed | PUT, POST, PATCH | 400 or 422 (422 specifically for well-formed RDF but invalid patch) |
| unsupported method | any | 405 |
| unsupported media | PUT, POST, PATCH | 415 |

### 6.2 Headers

Required response headers on success:

- `Content-Type` whenever content is returned.
- `Last-Modified` on GET/HEAD.
- `ETag` SHOULD be emitted (strong) for RDF resources to enable
  `If-Match`.
- `Link` with at least: `type`, `acl`, `describedby` where applicable,
  `storageDescription`, `linkset`, `up` for contained resources.
- `Allow`, `Accept-Patch`, `Accept-Post`, `Accept-Put` on GET/HEAD/OPTIONS
  of the target resource where applicable.
- `Accept-Post` on containers MUST list at least `text/turtle` and
  `application/ld+json`.
- `Accept-Patch` on RDF resources and linksets MUST list `text/n3`.

### 6.3 CORS

Follow Solid Protocol §8 verbatim: if a valid `Origin` appears, echo
it in `Access-Control-Allow-Origin`; list `Origin` in `Vary`; expose
all used response headers by name in `Access-Control-Expose-Headers`;
list `Accept` in `Access-Control-Allow-Headers`; support preflight via
`OPTIONS`. CORS is not the authorization layer — access control is
enforced independently regardless of Origin.

### 6.4 Content negotiation

For RDF sources the server MUST satisfy requests for `text/turtle` and
`application/ld+json`. It SHOULD also serve `application/n-triples`.
For containers the default representation SHOULD be `text/turtle`; JSON-LD
responses MUST use the LWS JSON-LD context (§10).

### 6.5 Problem details

Failure responses SHOULD use RFC 9457 problem detail documents
(`application/problem+json`) and SHOULD include a `Link` with
`rel="http://www.w3.org/ns/ldp#constrainedBy"` identifying the
constraint document.

## 7. Authentication

### 7.1 Suite model

The server MUST implement an authentication-suite interface of the
form:

```
trait AuthSuite {
    fn id() -> IRI;
    fn verify(req: &Request) -> Result<VerifiedClaims, AuthError>;
    fn challenge(req: &Request) -> WwwAuthenticate;
}
```

`VerifiedClaims` yields at least an agent IRI (typically a WebID, a
DID, or a controlled-identifier URL) and a set of capability claims.

On receiving an unauthenticated request to a protected resource the
server MUST respond 401 with a `WWW-Authenticate` that advertises all
configured suites. Servers MAY return 404 instead of 403 to untrusted
origins, per Solid Protocol §13.1.

### 7.2 Suites to ship

Priority 1, must ship:

- **OIDC suite.** Solid-OIDC compatible: verify DPoP-bound access
  tokens issued by OIDC providers listed in the relying-party
  trust configuration, extract the WebID claim, dereference the WebID
  document and check it lists the issuer.
- **did:key suite.** Per the LWS authn-ssi-did-key draft: accept
  HTTP Message Signatures signed with a `did:key` identifier; verify
  the signature against the key encoded in the DID.

Priority 2, stub with a working verifier but no production hardening:

- **SSI-CID suite.** Self-signed controlled-identifier per the
  W3C Controlled Identifiers draft: resolve the controlled identifier
  document, verify a proof using the listed verification method.
- **SAML 2.0 suite.** Accept SAML assertions; minimum viable path is
  verifying a bearer assertion against a configured IdP metadata
  document.

All four suites are defined as separate W3C drafts (`lws10-authn-*`).
The server's job is to make them plug-replaceable.

### 7.3 Identity document

The server MUST, when asked, resolve an agent IRI to an identity
document (a WebID profile document, a DID document, or a CID document).
Resolution is either HTTP GET for http(s) IRIs, or a registered
resolver for non-HTTP schemes (did:key is local computation; other DID
methods require a resolver plugin).

The server SHOULD NOT require that an agent's identity document live
in the same storage the agent is accessing. Owners of identity
documents served from an LWS storage should note that other resources
in the same storage may reveal ownership, per Solid Protocol §13.2.

## 8. Authorization

### 8.1 WAC first

Ship WAC as the default engine. Implement per
<https://solidproject.org/TR/wac>. Summary:

- Each resource has an associated ACL resource, discoverable via
  `Link: rel="acl"` and now also as the `acl` slot in the linkset.
- The ACL resource is an RDF document using `http://www.w3.org/ns/auth/acl#`.
- Authorizations grant combinations of `acl:Read`, `acl:Write`,
  `acl:Append`, `acl:Control` to agents identified by `acl:agent`,
  `acl:agentClass`, `acl:agentGroup`, or `acl:origin`-constrained
  combinations.
- If no ACL exists for a resource, the server walks up the container
  hierarchy and applies the nearest inherited ACL with
  `acl:default`-marked authorizations.
- The root container MUST have an ACL; create one at storage
  provisioning granting owner `acl:Control` over `acl:default`.

### 8.2 ACP as an option

Provide an ACP engine behind the same authorization interface. Do not
require a deployment to enable it. The interface is:

```
trait AuthzEngine {
    fn decide(agent: Option<&VerifiedClaims>,
              operation: Operation,
              resource: &ResourceRef) -> Decision;
}
```

ACP's "policies referencing matchers referencing rules" model slots
into this trait cleanly. Ship WAC; add ACP when there is demand.

### 8.3 Operation mapping

- Read operation (GET, HEAD, OPTIONS, PATCH-with-`?where`-non-empty
  and zero deletions): requires `acl:Read`.
- Append operation (POST to container, PATCH with `?insertions` only):
  requires `acl:Append` or `acl:Write`.
- Write operation (PUT, DELETE, PATCH with `?deletions`): requires
  `acl:Write`.
- Control operation (reading or writing ACL/ACR resources): requires
  `acl:Control`.

### 8.4 Contextual conditions

The UCS identifies contextual access control (time windows, group
membership, location) as a requirement. Expose hooks in the
authorization engine for context predicates, but do not define a
vocabulary here; leave that to ACP or a WAC extension.

## 9. Notifications

### 9.1 LDN receiver

Every container SHOULD have an inbox discoverable via
`Link: rel="http://www.w3.org/ns/ldp#inbox"`. POSTs of JSON-LD
notifications to that inbox create notification resources inside it,
per LDN. Inbox access control is the usual WAC/ACP mechanism.

### 9.2 Solid Notifications Protocol

Implement the Resource Server, Subscription Server, Notification
Sender and Notification Receiver roles. Minimum viable channel type:
WebSocket (`solid:WebSocketChannel2023`). Subscription flow:

1. Client GETs the target resource.
2. Server advertises `rel="http://www.w3.org/ns/solid/terms#subscription"`
   linking to the subscription service.
3. Client POSTs a subscription description (JSON-LD) to the
   subscription service specifying the channel type and topic.
4. Server returns a channel description with the WebSocket URL.
5. Client connects; server authenticates the connection (reuse the
   same auth suites as HTTP); server sends Activity Streams 2.0
   notifications on resource state changes.

Webhook (`WebhookChannel2023`) and Server-Sent Events channels are
optional follow-ons.

### 9.3 Change events

A resource change event MUST be emitted on:

- create, update, delete of a resource;
- membership change in a container (derived from create/delete on
  contained resources);
- ACL/linkset changes.

The event MUST identify the resource, the operation, the timestamp and
the agent (subject to authorization on the agent identity).

## 10. JSON-LD context and vocabulary

Publish a JSON-LD context at a stable URL (e.g.
`https://www.w3.org/ns/lws/v1`) containing terms for: `Storage`,
`Container`, `Resource`, `Linkset`, `items`, `acl`, `describedby`,
`storageDescription`, `up`, `inbox`, `subscription`, and the expected
`dcterms`, `rdf`, `rdfs`, `ldp`, `pim`, `stat`, `solid` prefix bindings.

Default container representation in JSON-LD uses this context with
`@type: Container`, `items: [ {...}, {...} ]`, and a `linkset`
property. The same data MUST round-trip to Turtle.

## 11. Storage backend

Define a `StorageStore` abstraction:

```
trait StorageStore {
    fn get(iri: &IRI, accept: MediaType) -> Result<Representation>;
    fn head(iri: &IRI) -> Result<Metadata>;
    fn put(iri: &IRI, repr: Representation, if_none_match: Option<ETag>) -> Result<Metadata>;
    fn patch_rdf(iri: &IRI, patch: N3Patch) -> Result<Metadata>;
    fn delete(iri: &IRI) -> Result<()>;
    fn list_contained(container: &IRI, range: Option<Range>) -> Result<ContainedSet>;
    fn linkset(iri: &IRI) -> Result<Linkset>;
    fn put_linkset(iri: &IRI, links: Linkset) -> Result<()>;
}
```

Ship at least two backends:

- **Filesystem backend.** Resources are files; containers are
  directories; linksets live in a sibling `.linkset.jsonld` file or a
  single `.linkset.jsonld` per resource; ACL resources in a `.acl`
  sibling. Atomic writes via rename; file locking for N3 Patch
  apply-and-replace.
- **SQL-plus-quad-store backend.** Binary resources in the filesystem
  or an object store; RDF sources parsed into a quad store (Oxigraph
  embedded, or Apache Jena TDB if the implementer picks a JVM stack)
  for efficient PATCH and query; metadata and linksets as named graphs.

An object-storage backend (S3 or MinIO) is a reasonable third target
but not required.

## 12. Conformance

The server is conformant if it:

1. Implements the HTTP binding per §6.
2. Implements the resource model per §4.
3. Implements at least one authentication suite and publishes which
   suites are supported.
4. Implements WAC per §8.
5. Implements LDN receiver and Solid Notifications Protocol per §9.
6. Passes the Solid QA test suite for Solid Protocol 0.11 modulo the
   documented deltas (§13).
7. Passes an LWS-specific test suite for linkset discovery, the
   stricter `Last-Modified` behaviour, and blank-node N3 Patch
   insertions.

The implementer SHOULD publish an implementation report identifying
the deltas.

## 13. Documented deltas from Solid Protocol 0.11

For the record, when the implementation differs from Solid 0.11 it
follows the LWS FPWD / ED:

| # | Topic | Solid 0.11 | LWS / this spec |
| --- | --- | --- | --- |
| 1 | `Last-Modified` on GET/HEAD | SHOULD | MUST |
| 2 | N3 Patch `?insertions` blank nodes | forbidden | allowed, server mints fresh bnodes |
| 3 | Resource metadata discovery | per-relation auxiliary resources | unified linkset resource, in addition to `Link` headers |
| 4 | `Slug` header on POST | optional | not used |
| 5 | Authentication | Solid-OIDC centric | pluggable suites (OIDC, SAML, SSI-CID, did:key) |
| 6 | Authorization | WAC or ACP | WAC default, ACP pluggable |
| 7 | Societal Impact section | stubs | implementer SHOULD fill out for deployment |

Where the Solid Protocol is silent and the LWS FPWD has not yet
written the section (e.g. "Logical Resource Organization",
"Operations" subsections, "LWS Media Type"), this spec treats the
Solid 0.11 text as the baseline and notes where the LWS ED editors'
notes suggest a direction.

## 14. Phased delivery

Suggested phasing for Claude Code. Each phase leaves a runnable server.

Phase 1 — read path.

- HTTP layer with GET/HEAD/OPTIONS, CORS.
- Filesystem backend, RDF parsing for Turtle and JSON-LD.
- `Link` header generation; linkset GET.
- Storage description, root container, owner seed.
- No authentication — treat everything as public-read.

Phase 2 — write path, unauthenticated.

- PUT, POST, DELETE.
- Automatic intermediate container creation.
- Container membership derivation.
- Content-Type enforcement, 409 on protected-triple edits.
- ETag and `If-Match` / `If-None-Match`.

Phase 3 — N3 Patch.

- PATCH with `text/n3`, full `solid:InsertDeletePatch` semantics
  including blank nodes in `?insertions`.
- Atomic apply with file lock or transaction.

Phase 4 — authentication and authorization.

- OIDC suite, did:key suite.
- WAC engine with inheritance.
- `WWW-Authenticate` advertising, 401/403 handling.
- Protect ACL resources with `acl:Control`.

Phase 5 — notifications.

- LDN receiver inboxes.
- Solid Notifications Protocol subscription service and WebSocket
  channel.
- Event emission on resource mutations.

Phase 6 — conformance hardening.

- Problem details, all `Accept-*` headers accurate, 415/422/409 coverage.
- Run Solid QA test suite, record deltas.
- SAML and SSI-CID suites.
- Second backend (quad store or object store).

## 15. Implementation notes for Claude Code

- Language is the implementer's choice. Rust with `axum` or `hyper`
  and Oxigraph for the quad store is a tight fit. TypeScript on
  `fastify` with `n3.js` or `rdflib.js` is equally reasonable and has
  a broader pool of existing Solid server code to crib from
  (Community Solid Server is the reference there, but do not copy its
  auxiliary-resource model — use linksets).
- Keep the authentication and authorization engines as injected
  dependencies behind traits/interfaces. Do not thread WebID-specific
  types through the HTTP handlers.
- Representations should be lazy: the container JSON-LD representation
  is derived from the backend's metadata at request time, not stored.
- Test with `curl` plus a small Python or Deno script for PATCH; add
  the public Solid test suites once Phase 4 is done.
- When in doubt about a Solid 0.11 MUST that the LWS ED has not yet
  addressed, implement the Solid 0.11 MUST but record the issue so
  the deployment can track WG movement.
- A deployment needs to decide storage provisioning: who mints a
  storage, how the root ACL is seeded, whether multi-tenancy is on
  the same host or per subdomain. This is deliberately outside the
  spec; document your choice.

## 16. Open questions for the implementer

- Tombstones: keep deleted URIs as 410 responses, or return 404 and
  allow URI re-use? Solid Protocol discourages re-use but leaves the
  mechanism open.
- Quota enforcement: not specified. If enforced, respond 507.
- Versioning and Memento: not in scope here but a storage that
  supports history makes UCS "recovering previous versions"
  achievable. Consider Memento (RFC 7089) integration as a later
  extension.
- Data integrity: the UCS asks for tamper-evident storage. A minimum
  implementation is content hashes in the linkset; signed linksets
  are a natural extension once the SSI-CID suite is in place.
- Concurrency model for PATCH on shared resources under high write
  contention: document the strategy (serialized per resource, CRDT
  merge, or optimistic with `If-Match`)
