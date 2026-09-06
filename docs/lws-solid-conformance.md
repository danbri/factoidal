# LWS 1.0 Core and Solid Protocol — conformance ledger

Design record: [`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](designissues/2026-09-06-lws-and-solid-protocols.md).
Tracking issue: <https://github.com/danbri/factoidal/issues/659>.

The Lean modules are `formal/lean4/L4Factoidal/LWS/` and
`formal/lean4/L4Factoidal/Solid/`. Every row below names one normative
statement of a specification, quotes it verbatim, names the Lean module that
decides it, and gives its status.

Status values (`L4Factoidal.LWS.Conformance.Status`):

| value | meaning |
|---|---|
| `proved` | a Lean theorem discharges the statement; the row names the theorem |
| `guarded` | a `#guard` in `Tests.lean` evaluates the statement at build time; the row names the guard |
| `hostVerified` | the decision needs bytes, a socket, a clock or a token the Lean side does not hold; a host test decides it |
| `open` | not decided yet |

Scores are always written "N pass, M fail (out of T)".

## wasm ABI

The host agent codes against this section. The operations are registered in
`formal/lean4/Wasm/Dispatch.lean` and reachable through `L4Wasm.callIO`
(they hold state, so the pure `L4Wasm.call` answers `unknown op` for them).
Arguments arrive as the dispatch ABI's JSON array of strings; every answer is
one envelope, `{"ok":true,…}` or `{"ok":false,"error":"…"}`.

### Request and response documents

A request is a JSON object:

```json
{"method":"PUT",
 "target":"/alice/card",
 "headers":[["content-type","text/turtle"]],
 "body":"<#me> <http://xmlns.com/foaf/0.1/name> \"Alice\" ."}
```

* `method` — an HTTP method token, upper case.
* `target` — the request target as a path within the storage, beginning with
  `/`. A path that ends with `/` names a container (Solid Protocol §3.1).
* `headers` — an array of two-element arrays. Names are compared case
  insensitively; the engine lower-cases them on the way in.
* `body` — a UTF-8 string. Binary bodies are not carried by this ABI yet; a
  host with binary content stores it outside the engine and gives the engine
  the metadata.

Every member is optional except `method` and `target`.

A response is a JSON object with the same shape minus the method:

```json
{"status":201,
 "headers":[["location","/alice/card"],["last-modified","Thu, 01 Jan 1970 00:00:01 GMT"]],
 "body":""}
```

### Operations

| op | arguments | answer |
|---|---|---|
| `lwsOpen` | `[configJson]` | `{"ok":true,"handle":"lws1","root":"/"}` |
| `lwsStep` | `[handle, requestJson]` | `{"ok":true,"response":{…}}` |
| `lwsClose` | `[handle]` | `{"ok":true}` |
| `solidOpen` | `[configJson]` | `{"ok":true,"handle":"solid1","root":"/","storage":"…"}` |
| `solidStep` | `[handle, requestJson]` | `{"ok":true,"response":{…}}` |
| `solidClose` | `[handle]` | `{"ok":true}` |
| `solidClientRequest` | `[kind, argsJson]` | `{"ok":true,"request":{…}}` |
| `solidClientResponse` | `[kind, responseJson]` | `{"ok":true,"interpretation":{…}}` |

`configJson` is a JSON object. Members, all optional:

| member | default | meaning |
|---|---|---|
| `baseIri` | `"http://localhost/"` | the absolute IRI the storage root maps to. A request target `/a/b` denotes `baseIri` + `a/b`. |
| `now` | `0` | the clock, in seconds since the Unix epoch. Every mutation stamps `Last-Modified` from it and then advances it by one second, so a sequence of writes has a strictly increasing modification time with no call to a real clock. |
| `owner` | absent | the WebID the storage advertises through `Link: rel="http://www.w3.org/ns/solid/terms#owner"`. |
| `agent` | absent | the WebID of the requesting agent for every request on this handle. A handle with no `agent` is an unauthenticated agent. This member is what a host uses when it has verified the credential itself; since 2026-09-06 the engine can verify a Solid-OIDC access token and its DPoP proof instead (`L4Factoidal/Solid/Server/Auth.lean`, `ServerConfig.auth`), and `agent` is what stands while `auth.enforceAuth` is false, which is the default. |
| `enforceWac` | `false` | `solidOpen` only. With it false the Web Access Control decision is computed and reported in `WAC-Allow` but never refuses a request, which is the first slice's public storage. With it true the decision is enforced and a target with no effective ACL resource is denied, as Web Access Control §5.3 requires. |
| `rootAcl` | absent | the ACL document (Turtle) of the storage root, written when the storage is created. Web Access Control §3.2 requires the root container's ACL resource to have a representation, and under enforcement a storage cannot write its own: the request that would write it is the first request it would authorize. It is therefore a host provisioning input. |

A request document may override the clock and the agent for one step with the
members `now` and `agent` beside `method`; this is what a host with a real
clock and a real token verifier uses.

`solidClientRequest` kinds: `read`, `create`, `replace`, `patch`, `delete`,
`discoverStorage`, `readProfile`. `argsJson` is a JSON object whose members
depend on the kind; `target` is required by all of them, `body` and
`contentType` by `create`, `replace` and `patch`, and `state` by the second
and later steps of a multi-step operation (see below).

`solidClientResponse` kinds: `storage`, `containment`, `auxiliaries`,
`profile`, `wacAllow`, `created`. The interpretation object is documented
per kind in `formal/lean4/L4Factoidal/Solid/Client/Responses.lean`.

The response document carries members some kinds need beside `status`,
`headers` and `body`: `webId` and `baseIri` for `profile`, and `target` —
the request target the reply answers — for `storage`.

### Multi-step operations

An interpretation may answer `"continue": true` with a `"state"`. The host
then calls `solidClientRequest` again for the SAME kind, with `state` added
to the arguments, sends the request it gets back, and interprets the reply
the same way. The loop ends on the first interpretation with
`"continue": false`. The host attaches no meaning to `state`; it passes the
value through.

`discoverStorage` is the operation that uses it. Solid Protocol §4.1:
"Clients can determine the storage of a resource by moving up the URI path
hierarchy until the response includes a `Link` header field with
`rel="type"` targeting `http://www.w3.org/ns/pim/space#Storage`." The
`storage` interpretation of a reply that carries no such link answers
`"continue": true` and a `state` naming the parent container of the reply's
`target` — the last path segment dropped, the trailing slash kept. The
status code does not end the walk: a 404 or a 403 on a resource that does
not exist yet, or that this agent may not read, says nothing about where the
storage is.

The walk ends in one of two ways, both with `"continue": false`:

* the reply carries the storage type link, and the `storage` member is the
  `target` of that reply — the storage the resource belongs to;
* the `target` is `/`, which has no parent, and `storage` is `null`.

The `storage` interpretation therefore has these members:

| member | meaning |
|---|---|
| `isStorage` | does THIS reply carry the storage type link |
| `storage` | the resource whose reply carried it, `null` until then |
| `storageDescription` | the `solid:storageDescription` link target |
| `owner` | the `solid:owner` link target |
| `lastModified` | the `Last-Modified` field value |
| `allow` | the methods the `Allow` field named |
| `continue` | is a further request part of this operation |
| `state` | the resource to ask about next, `null` when `continue` is false |

A caller that names no `target` gets the facts of one reply, `storage` null
and `continue` false: §4.1's rule is about the path hierarchy of a named
resource, so with no name there is no walk.

### Errors

An operation that cannot answer at all — an unknown handle, a request
document that is not JSON, an unknown client kind — answers
`{"ok":false,"error":"…"}`. A request the protocol REFUSES is not an error:
it answers `{"ok":true,"response":{"status":405,…}}`, because the status code
is the protocol's own answer.

## LWS 1.0 Core

Source: <https://w3c.github.io/lws-protocol/lws10-core/>, W3C Linked Web
Storage Working Group editor's draft, read 2026-09-06.

The draft's `Operations`, `Containers`, `Discovery`, `Authentication` and
`Authorization` sections are headings with no content, and it defines no HTTP
binding, no status codes and no test suite. Where a row needs a binding, the
Solid Protocol's binding is used and the row says so.

Score, from `lake exe l4lws-probe`:

```
guarded checks: 9 pass, 0 fail (out of 9)
registry: 2 proved, 9 guarded, 0 host-verified, 7 open (out of 18)
```

Table generated by `lake exe l4lws-probe -- --markdown`.

| id | section | statement | module | status | decided by |
|---|---|---|---|---|---|
| `lws-core-01` | Resource Access | A LWS Server is an HTTP server [RFC9112] that complies with all of the relevant "MUST" statements in this specification. | `L4Factoidal.LWS.Operations` | open | the draft's Operations, Containers, Discovery, Authentication and Authorization sections have empty bodies, so the class is not yet closed |
| `lws-core-02` | Resource Access | An LWS Client is an HTTP client [RFC9112] that complies with all of the relevant "MUST" statements in this specification. | `L4Factoidal.Solid.Client` | open | same empty sections as lws-core-01 |
| `lws-core-03` | For Editors (CG-to-ED delta) | HTTP Server MUST generate a Last-Modified header field in response to GET and HEAD requests. | `L4Factoidal.LWS.Operations.step` | guarded | lwsGuardLastModifiedOnGet, lwsGuardLastModifiedOnHead |
| `lws-core-04` | For Editors (CG-to-ED delta) | The PATCH ?insertions formulae MUST NOT contain blank nodes. | `L4Factoidal.LWS.Patch.wellFormed` | guarded | lwsGuardInsertionsRefuseBlankNodes |
| `lws-core-05` | Terminology | container — an LWS resource that is able to enumerate a collection of LWS resources, conforming to the conventions described in Section 8. Containers. | `L4Factoidal.LWS.Operations.containedPaths` | guarded | lwsGuardContainerEnumerates |
| `lws-core-06` | Terminology | storage root — a container at the root of a containment hierarchy of a storage. The storage root is the only LWS resource that does not have a parent in the LWS containment hierarchy nor a primary resource. | `L4Factoidal.LWS.Model.parent?` | proved | L4Factoidal.LWS.Tests.rootHasNoParent |
| `lws-core-07` | Terminology | auxiliary resource — an LWS resource that plays a particular role with respect to a LWS resource, called its primary resource, and whose lifetime is bound to the primary resource. | `L4Factoidal.Solid.Server.Auxiliary` | proved | L4Factoidal.Solid.Server.auxiliariesDeletedWithSubject |
| `lws-core-08` | Terminology | Auxiliary resources are discovered using web links [RFC8288] of a specific type (see Section ). | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | lwsGuardAuxiliaryLinksAdvertised |
| `lws-core-09` | Terminology | linkset resource — a type of auxiliary resource whose representation conforms to [RFC9264]. | `L4Factoidal.LWS.Model.ResourceKind` | open | the kind and its linkset link relation exist; RFC 9264 linkset serialisation is not implemented |
| `lws-core-10` | Terminology | metadata resource — an auxiliary resource, managed by a storage, that describes an LWS resource and conforms to the conventions described in TBD. | `L4Factoidal.LWS.Model.ResourceKind` | open | the draft marks the metadata-resource conventions TBD; the kind and its describedby link exist |
| `lws-core-11` | Resource Access | An operation is any of the following actions that can be performed on a served resource: create resource, read resource, update resource, delete resource. | `L4Factoidal.LWS.Operations.step` | guarded | lwsGuardCreateReadUpdateDelete |
| `lws-core-12` | Resource Access | success - the operation is believed to have completed. This may be accompanied by a resource representation conveying the contents of a served resource. A success response is not defined for the create resource operation. See instead created. | `L4Factoidal.LWS.Operations.step` | guarded | lwsGuardCreatedIsNotSuccess |
| `lws-core-13` | Resource Access | not permitted | `L4Factoidal.Solid.Server.WAC` | guarded | solidGuardWacDenies |
| `lws-core-14` | Resource Access | unknown requester | `L4Factoidal.Solid.Server.Auth` | guarded | solidGuardSolidOidcDpop |
| `lws-core-15` | Authentication | LWS makes use of user authentication as defined in specifications for OpenID Connect, SAML 2.0, and self-signed controlled identifiers (CIDs), for example. | `L4Factoidal.Solid.Server.Auth` | guarded | solidGuardSolidOidcDpop |
| `lws-core-16` | Notifications | notification — a message describing an event that has occurred on a resource. | `(none)` | open | not in the first slice |
| `lws-core-17` | Access Requests and Grants | access grant — a data object created by a storage controller, expressing an ability for an agent to perform specific actions on storage resources within certain defined constraints. | `(none)` | open | not in the first slice |
| `lws-core-18` | Terminology | storage description — an LWS resource, conforming to the requirements of a W3C Controlled Identifier document [CID-1.0], that describes a storage along with its services and capabilities. | `L4Factoidal.LWS.Discovery.storageDescriptionPath` | open | the link is advertised; the description document does not yet conform to CID 1.0 |

## Solid Protocol

Source: <https://solidproject.org/TR/protocol>, version 0.11.0, modified
2024-05-12, read 2026-09-06. Web Access Control:
<https://solidproject.org/TR/wac>.

Score, from `lake exe l4solid-probe`:

```
guarded checks: 63 pass, 0 fail (out of 63)
registry: 3 proved, 63 guarded, 4 host-verified, 7 open (out of 77)
```

Table generated by `lake exe l4solid-probe -- --markdown`.

| id | section | statement | module | status | decided by |
|---|---|---|---|---|---|
| `solid-02-01` | Solid Protocol §2.1 HTTP Server | Servers MUST conform to HTTP Semantics [RFC9110]. […] Servers MUST conform to HTTP/1.1 [RFC9112]. | `L4Factoidal.HTTP.Server (message framing) plus the Node host` | host-verified | tests/solid/server/protocol.mjs — the framing is the host's; the engine sees a parsed request |
| `solid-02-02` | Solid Protocol §2.1 HTTP Server | Server MUST reject PUT, POST, and PATCH requests that contain content but lack the Content-Type header field, with a status code of 400. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardContentTypeRequired400 |
| `solid-02-03` | Solid Protocol §2.1 HTTP Server | When a client does not provide valid credentials when requesting a resource that requires it (see WebID), servers MUST send a response with a 401 status code (unless 404 is preferred for security reasons). | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardWacEnforced |
| `solid-02-04` | Solid Protocol §2.1 HTTP Server | When both http and https URI schemes are supported, the server MUST redirect all http URIs to their https counterparts using a response with a 301 status code and a Location header. | `(the host)` | host-verified | tests/solid/server/protocol.mjs — the scheme is the listener's, not the engine's |
| `solid-02-05` | Solid Protocol §2.1 HTTP Server | Server MUST generate a Content-Type header field in a message that contains content. | `L4Factoidal.LWS.Operations.readHeaders` | guarded | solidGuardAcceptHeaders |
| `solid-02-06` | Solid Protocol §2.2 HTTP Client | Clients MUST use the Content-Type HTTP header field in PUT, POST, and PATCH requests that contain content [RFC9110]. | `L4Factoidal.Solid.Client.Requests.buildRequest` | proved | L4Factoidal.Solid.Client.buildRequest_contentTypePresent |
| `solid-03-01` | Solid Protocol §3.1 URI Slash Semantics | Paths ending with a slash denote a container resource. | `L4Factoidal.LWS.Model.pathIsContainer` | guarded | solidGuardContainment |
| `solid-03-02` | Solid Protocol §3.1 URI Slash Semantics | If two URIs differ only in the trailing slash, and the server has associated a resource with one of them, then the other URI MUST NOT correspond to another resource. Instead, the server MAY respond to requests for the latter URI with a 301 redirect to the former. | `L4Factoidal.Solid.Server.Storage.slashRedirect?` | guarded | solidGuardSlashRedirect |
| `solid-03-03` | Solid Protocol §3.1 URI Slash Semantics | Servers MUST authorize prior to this optional redirect. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardWacEnforced |
| `solid-04-01` | Solid Protocol §4.1 Storage Resource | Servers MUST provide one or more storages. | `L4Factoidal.Solid.Server.Storage.storageRootPath` | guarded | solidGuardStorageTypeLink |
| `solid-04-02` | Solid Protocol §4.1 Storage Resource | When a server supports multiple storages, the URIs MUST be allocated to non-overlapping space. | `Wasm/Ops/Solid.lean (one storage per handle)` | host-verified | tests/solid/server/protocol.mjs — two storages are two handles with different base IRIs |
| `solid-04-03` | Solid Protocol §4.1 Storage Resource | Servers MUST advertise the storage resource by including the HTTP Link header field with rel="type" targeting http://www.w3.org/ns/pim/space#Storage when responding to storage's request URI. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardStorageTypeLink |
| `solid-04-04` | Solid Protocol §4.1 Storage Resource | Servers MUST include the Link header field with rel="http://www.w3.org/ns/solid/terms#storageDescription" targeting the URI of the storage description resource in the response of HTTP GET, HEAD and OPTIONS requests targeting a resource in a storage. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardStorageDescriptionLink |
| `solid-04-05` | Solid Protocol §4.1 Storage Resource | Servers MUST include statements about the storage as part of the storage description resource. | `L4Factoidal.Solid.Server.Storage.storageDescriptionGraph` | open | the graph is built; the storage description resource is not yet served at its own path |
| `solid-04-06` | Solid Protocol §4.1 Storage Resource | Servers MUST keep track of at least one owner of a storage in an implementation defined way. | `L4Factoidal.LWS.Operations.Config.owner` | guarded | solidGuardOwnerLink |
| `solid-04-07` | Solid Protocol §4.1 Storage Resource | When a server wants to advertise the owner of a storage, the server MUST include the Link header field with rel="http://www.w3.org/ns/solid/terms#owner" targeting the URI of the owner in the response of HTTP HEAD or GET requests targeting the root container. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardOwnerLink |
| `solid-04-15` | Solid Protocol §4.1 Storage Resource | Clients can determine the storage of a resource by moving up the URI path hierarchy until the response includes a Link header field with rel="type" targeting http://www.w3.org/ns/pim/space#Storage. | `L4Factoidal.Solid.Client.Discovery.storageStepOf, Responses.storageReading` | guarded | solidGuardClientStorageWalkSteps |
| `solid-04-08` | Solid Protocol §4.2 Resource Containment | There is a 1-1 correspondence between containment triples and relative reference within the path name hierarchy. | `L4Factoidal.Solid.Server.Containment` | proved | L4Factoidal.Solid.Server.containerOfChildUnique, containedByParent, memContainedPaths_iff |
| `solid-04-09` | Solid Protocol §4.2 Resource Containment | The representation and behaviour of containers in Solid corresponds to LDP Basic Container and MUST be supported by server. | `L4Factoidal.Solid.Server.Containment.containerGraph` | guarded | solidGuardContainment |
| `solid-04-10` | Solid Protocol §4.2.1 Contained Resource Metadata | Servers SHOULD include resource metadata about contained resources as part of the container description, unless that information is inapplicable to the server. | `L4Factoidal.Solid.Server.Containment.containedMetadata` | guarded | solidGuardContainment |
| `solid-04-11` | Solid Protocol §4.3 Auxiliary Resources | Servers MUST support auxiliary resources defined by this specification and manage the association between a subject resource and auxiliary resources. When a subject resource is deleted its auxiliary resources are also deleted by the server. | `L4Factoidal.Solid.Server.Auxiliary` | proved | L4Factoidal.Solid.Server.auxiliariesDeletedWithSubject |
| `solid-04-12` | Solid Protocol §4.3 Auxiliary Resources | Servers MUST advertise auxiliary resources associated with a subject resource by responding to HEAD and GET requests by including the HTTP Link header field with the rel parameter [RFC8288]. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardAuxiliaryLinks |
| `solid-04-13` | Solid Protocol §4.3.2 Description Resource | Servers MUST NOT directly associate more than one description resource to a subject resource. | `L4Factoidal.Solid.Server.Auxiliary.auxiliaryPaths` | guarded | solidGuardDescriptionAuthorizedAsSubject |
| `solid-04-14` | Solid Protocol §4.3.2 Description Resource | When an HTTP request targets a description resource, the server MUST apply the authorization rule that is used for the subject resource with which the description resource is associated. | `L4Factoidal.Solid.Server.Auxiliary.authorizationSubject` | guarded | solidGuardDescriptionAuthorizedAsSubject |
| `solid-05-01` | Solid Protocol §5 Reading and Writing Resources | Servers MUST respond with the 405 status code to requests using HTTP methods that are not supported by the target resource. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardUnsupportedMethod405 |
| `solid-05-02` | Solid Protocol §5.1 Resource Type Heuristics | When a successful POST request creates a resource, the server MUST assign a URI to that resource. | `L4Factoidal.LWS.Operations.assignedName` | guarded | solidGuardPostAssignsName |
| `solid-05-03` | Solid Protocol §5.2 Reading Resources | Servers MUST support the HTTP GET, HEAD and OPTIONS methods [RFC9110] for clients to read resources or to determine communication options. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardAllowHeader |
| `solid-05-04` | Solid Protocol §5.2 Reading Resources | Servers MUST indicate the HTTP methods supported by the target resource by generating an Allow header field in successful responses. | `L4Factoidal.LWS.Operations.allowFor` | guarded | solidGuardAllowHeader |
| `solid-05-05` | Solid Protocol §5.2 Reading Resources | When responding to authorized requests, servers MUST indicate supported media types in the HTTP Accept-Patch [RFC5789], Accept-Post [LDP] and Accept-Put [The Accept-Put Response Header] response header fields that correspond to acceptable HTTP methods listed in Allow header field value in response to HTTP GET, HEAD and OPTIONS requests. | `L4Factoidal.LWS.Operations.readHeaders` | guarded | solidGuardAcceptHeaders |
| `solid-05-06` | Solid Protocol §5.3 Writing Resources | Servers MUST support the HTTP PUT, POST and PATCH methods [RFC9110]. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardPostAssignsName |
| `solid-05-07` | Solid Protocol §5.3 Writing Resources | Servers MUST create intermediate containers and include corresponding containment triples in container representations derived from the URI path component of PUT and PATCH requests. | `L4Factoidal.LWS.Operations.ensureAncestors` | guarded | solidGuardIntermediateContainers |
| `solid-05-08` | Solid Protocol §5.3 Writing Resources | Servers MUST allow creation of new resources by a POST request to a URI path ending with /. Servers MUST create resources with URI paths ending with /{id} in container /. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardPostAssignsName |
| `solid-05-09` | Solid Protocol §5.3 Writing Resources | When a POST method request targets a resource without an existing representation, the server MUST respond with the 404 status code. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardPostMissingTarget404 |
| `solid-05-10` | Solid Protocol §5.3 Writing Resources | When a PUT or PATCH request targets an auxiliary resource, the server MUST create or update it. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardPutAuxiliary |
| `solid-05-11` | Solid Protocol §5.3 Writing Resources | Servers MUST NOT allow HTTP PUT or PATCH on a container to update its containment triples; if the server receives such a request, it MUST respond with a 409 status code. | `L4Factoidal.Solid.Server.Methods.bodyEditsContainment` | guarded | solidGuardPutRefusesContainmentEdit409 |
| `solid-05-12` | Solid Protocol §5.3 Writing Resources | Servers MUST NOT allow HTTP POST, PUT and PATCH to update a container's resource metadata statements; if the server receives such a request, it MUST respond with a 409 status code. | `L4Factoidal.Solid.Server.Methods.step` | open | the containment-triple half of the rule is decided; server-managed metadata statements of a container are not yet distinguished from author-supplied ones |
| `solid-05-13` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | Servers MUST accept a PATCH request with an N3 Patch body when the target of the request is an RDF document [RDF11-CONCEPTS]. | `L4Factoidal.Solid.Server.N3Patch` | guarded | solidGuardN3PatchApplies |
| `solid-05-14` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | Servers MUST indicate support of N3 Patch by listing text/n3 as a field value of the Accept-Patch header field [RFC5789] of relevant responses. | `L4Factoidal.LWS.Operations.readHeaders` | guarded | solidGuardN3PatchAcceptPatch |
| `solid-05-15` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | When present, ?deletions, ?insertions, and ?conditions MUST be non-nested cited formulae [N3] consisting only of triples and/or triple patterns [SPARQL11-QUERY]. | `L4Factoidal.Solid.Server.N3Patch.takeToBrace` | guarded | solidGuardN3PatchBlankNode422 |
| `solid-05-16` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | A patch resource MUST contain a triple ?patch rdf:type solid:InsertDeletePatch. | `L4Factoidal.Solid.Server.N3Patch.parseN3Patch` | guarded | solidGuardPatchMediaType415 |
| `solid-05-17` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | The ?insertions and ?deletions formulae MUST NOT contain variables that do not occur in the ?conditions formula. | `L4Factoidal.LWS.Patch.wellFormed` | guarded | lwsGuardInsertionsRefuseBlankNodes (L4Factoidal.LWS.Tests) |
| `solid-05-18` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | The ?insertions and ?deletions formulae MUST NOT contain blank nodes. | `L4Factoidal.LWS.Patch.wellFormed` | guarded | solidGuardN3PatchBlankNode422 |
| `solid-05-19` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | Servers MUST respond with a 422 status code [RFC4918] if a patch document does not satisfy all of the above constraints. | `L4Factoidal.Solid.Server.N3Patch.N3PatchError.status` | guarded | solidGuardN3PatchBlankNode422 |
| `solid-05-20` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | When ?conditions is non-empty, servers MUST treat the request as a Read operation. When ?insertions is non-empty, servers MUST (also) treat the request as an Append operation. When ?deletions is non-empty, servers MUST treat the request as a Read and Write operation. | `L4Factoidal.LWS.Patch.patchOperations` | guarded | solidGuardN3PatchOperations |
| `solid-05-21` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | If no such mapping exists, or if multiple mappings exist, the server MUST respond with a 409 status code. | `L4Factoidal.LWS.Patch.applyPatch` | guarded | solidGuardN3PatchNoMatch409, solidGuardN3PatchMultipleMatch409 |
| `solid-05-22` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | If the set of triples resulting from ?deletions is non-empty and the dataset does not contain all of these triples, the server MUST respond with a 409 status code. | `L4Factoidal.LWS.Patch.applyPatch` | guarded | solidGuardN3PatchDeletionsAbsent409 |
| `solid-05-30` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches, with RFC 3986 §5.1.3 | The base URI of a representation is the URI used to retrieve it. (RFC 3986 §5.1.3 Base URI from the Retrieval URI; the Solid Protocol states no base of its own, and its own N3 Patch examples and every client use relative references such as <> and <#it>.) | `L4Factoidal.Solid.Server.N3Patch.parseFormula` | guarded | solidGuardN3PatchRelativeIri |
| `solid-05-23` | Solid Protocol §5.4 Deleting Resources | Servers MUST support the HTTP DELETE method [RFC9110]. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardDeleteRemovesContainment |
| `solid-05-24` | Solid Protocol §5.4 Deleting Resources | When a DELETE request targets storage's root container or its associated ACL resource, the server MUST respond with the 405 status code. Server MUST exclude the DELETE method in the field value of the Allow header field, in response to requests to these resources. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardDeleteRootRefused405 |
| `solid-05-25` | Solid Protocol §5.4 Deleting Resources | When a contained resource is deleted, the server MUST also remove the corresponding containment triple. | `L4Factoidal.Solid.Server.Containment.containmentTriples` | guarded | solidGuardDeleteRemovesContainment |
| `solid-05-26` | Solid Protocol §5.4 Deleting Resources | When a contained resource is deleted, the server MUST also delete the associated auxiliary resources. | `L4Factoidal.Solid.Server.Auxiliary.deleteWithAuxiliaries` | guarded | solidGuardDeleteRemovesAuxiliaries |
| `solid-05-27` | Solid Protocol §5.4 Deleting Resources | When a DELETE request targets a container, the server MUST delete the container if it contains no resources. If the container contains resources, the server MUST respond with the 409 status code. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardDeleteNonEmptyContainer409 |
| `solid-05-28` | Solid Protocol §5.5 Resource Representations | When a server creates an RDF source on HTTP PUT, POST, or PATCH requests, the server MUST satisfy GET requests on this resource when the Accept header field requests text/turtle or application/ld+json. | `L4Factoidal.LWS.Operations.step` | open | text/turtle is answered; content negotiation to application/ld+json is not wired to the JSON-LD serialiser yet |
| `solid-05-29` | Solid Protocol §5.5 Resource Representations | When a PUT, POST, PATCH or DELETE method request targets a representation URL that is different than the resource URL, the server MUST respond with a 307 or 308 status code. | `(none)` | open | this server has no separate representation URLs, so the condition never arises; it becomes a rule when content negotiation adds them |
| `solid-06-01` | Solid Protocol §6 Linked Data Notifications | A Solid server MUST conform to the LDN specification by implementing the Receiver parts to receive notifications, and MAY implement the Sender or Consumer parts. | `L4Factoidal.Solid.Server.Ldn` | guarded | solidGuardInboxAcceptsPost |
| `solid-06-02` | Solid Protocol §6 Linked Data Notifications | A Solid client MUST conform to the LDN specification by implementing the Sender or Consumer parts to send or read notifications. | `L4Factoidal.Solid.Client.Discovery.inboxOf?` | guarded | solidGuardClientReadsLinks |
| `solid-06-03` | Linked Data Notifications §3.1 Discovery | make an HTTP HEAD or GET request on the target URL, and use the Link header with a rel value of http://www.w3.org/ns/ldp#inbox […] A resource MUST advertise only one Inbox. | `L4Factoidal.Solid.Server.Ldn.inboxLinks` | guarded | solidGuardInboxAdvertised |
| `solid-07-01` | Solid Protocol §7.1 Solid Notifications Protocol | Servers MUST conform to the Solid Notifications Protocol by implementing the Resource Server, Subscription Server, Notification Sender and Notification Receiver. | `(none)` | open | not in the first slice; the design record lists notification channels as later work |
| `solid-08-01` | Solid Protocol §8.1 CORS Server | A server MUST implement the CORS protocol [FETCH] such that browsers allow Solid apps to send any request and combination of request headers to the server, and allow the app to read any response and response headers received from the server. | `L4Factoidal.Solid.Server.Cors` | guarded | solidGuardCorsHeaders |
| `solid-08-02` | Solid Protocol §8.1 CORS Server | The server MUST set the Access-Control-Allow-Origin header field value to the valid Origin header field value from the request and list Origin in the Vary header field value. | `L4Factoidal.Solid.Server.Cors.corsHeaders` | guarded | solidGuardCorsHeaders |
| `solid-08-03` | Solid Protocol §8.1 CORS Server | The server MUST make all used response headers readable for the Solid app through Access-Control-Expose-Headers. | `L4Factoidal.Solid.Server.Cors.exposedHeaders` | guarded | solidGuardCorsHeaders |
| `solid-08-04` | Solid Protocol §8.1 CORS Server | A server MUST also support the HTTP OPTIONS method such that it can respond appropriately to CORS preflight requests. | `L4Factoidal.Solid.Server.Cors.isPreflight` | guarded | solidGuardCorsPreflight |
| `solid-09-01` | Solid Protocol §9.1 WebID | When a WebID is dereferenced, server provides a representation of the WebID Profile in an RDF document. | `L4Factoidal.Solid.Client.Profile` | guarded | solidGuardClientProfile |
| `solid-10-01` | Solid Protocol §10.1 Solid-OIDC | Servers MUST conform to the Solid-OIDC specification. | `L4Factoidal.Solid.Server.Auth` | guarded | solidGuardSolidOidcDpop |
| `solid-11-01` | Solid Protocol §11 Authorization | Servers MUST conform to either or both Web Access Control and Access Control Policy specifications. | `L4Factoidal.Solid.Server.WAC` | guarded | solidGuardWacEnforced |
| `solid-wac-01` | Web Access Control §5.3 Authorization Evaluation | Access is granted when conforming Authorizations are matched, otherwise access is denied. | `L4Factoidal.Solid.Server.WAC.decideAccess` | guarded | solidGuardWacDenies |
| `solid-wac-02` | Web Access Control §5.3.3 Authorization Matching | Match an Authorization with a specific resource, agent and access mode. | `L4Factoidal.Solid.Server.WAC.decideAccess` | guarded | solidGuardWacAccessToAgentMode |
| `solid-wac-03` | Web Access Control §5.3.3 Authorization Matching | Match an Authorization with a specific container resource, agent class membership and access mode. | `L4Factoidal.Solid.Server.WAC.decideAccess` | guarded | solidGuardWacDefaultAgentClassSuperclassMode |
| `solid-wac-04` | Web Access Control §5.3.3 Authorization Matching | Match an Authorization with a specific resource, agent with any group membership, and specific access mode. | `L4Factoidal.Solid.Server.WAC.subjectMatches` | guarded | solidGuardWacAgentGroup |
| `solid-wac-05` | Web Access Control §5.1 Effective ACL Resource Algorithm | If resource has an associated aclResource with a representation, return aclResource. Otherwise, repeat the steps using the container resource of resource. | `L4Factoidal.Solid.Server.WAC.effectiveAcl` | guarded | solidGuardWacEnforced |
| `solid-wac-06` | Web Access Control §5.3.2 Web Origin Authorization | When a server participates in the CORS protocol [FETCH] and authorization is granted to an HTTP request including the Origin header, the server MUST include the HTTP Access-Control-Allow-Origin and Access-Control-Allow-Headers headers in the response of the HTTP request. | `L4Factoidal.Solid.Server.WAC.subjectMatches, Cors.corsHeaders` | open | the CORS fields are generated; the acl:origin CONDITION on the access decision is read into the model but not applied |
| `solid-wac-07` | Web Access Control §5.3.4 Access Privileges | Servers MUST advertise client's access privileges on a resource by including the WAC-Allow HTTP header in the response of HTTP GET and HEAD requests. | `L4Factoidal.Solid.Server.WAC.wacAllow` | guarded | solidGuardWacAllowHeader |
| `solid-wac-08` | Web Access Control §5.3.4 Access Privileges | Clients MUST discover access privileges on a resource by making an HTTP GET or HEAD request on the target resource, and checking the WAC-Allow header value for access parameters listing the allowed access modes per permission group. | `L4Factoidal.Solid.Client.Responses.parseWacAllow` | guarded | solidGuardClientWacAllowParsing |
| `solid-wac-09` | Web Access Control §3.1 ACL Resource Discovery | Clients MUST discover the ACL resource associated with a resource by making an HTTP request on the target URL, and checking the HTTP Link header with the rel parameter. […] Clients MUST NOT derive the URI of the ACL resource through string operations on the URI of the resource. | `L4Factoidal.Solid.Client.Discovery.aclOf?` | guarded | solidGuardClientReadsLinks |
| `solid-wac-10` | Web Access Control §3.2 ACL Resource Representation | Root container ACL resources MUST have representations. The ACL resource of the root container MUST include an Authorization allowing the acl:Control access privilege. | `(none)` | open | a storage is created without a root ACL; enforcement is therefore off by default (ServerConfig.enforceWac) and a root ACL is a host provisioning step |
| `solid-cl-01` | Solid Protocol §4.1 Storage Resource | Clients can determine the storage of a resource by moving up the URI path hierarchy until the response includes a Link header field with rel="type" targeting http://www.w3.org/ns/pim/space#Storage. | `L4Factoidal.Solid.Client.Discovery.storageWalk` | guarded | solidGuardClientStorageWalk |
| `solid-cl-02` | RFC 9110 §5.1 Field Names, RFC 8288 §3 Link Serialisation in HTTP Headers | Field names are case-insensitive. […] The Link header field provides a means for serialising one or more links into HTTP headers, [where] each link-value is separated by a comma and the parameters of a link-value by a semicolon; a comma or semicolon inside a URI-Reference or a quoted-string is not a separator. | `L4Factoidal.Solid.Client.Discovery.linksOf, Responses.headerOf` | guarded | solidGuardClientLinkFieldShapes |

## Host tests

The host side of both protocols is `npm/factoidal/lws/`,
`npm/factoidal/solid/server/` and `npm/factoidal/solid/client/`. Those
files decide nothing: they accept a socket, turn one request into the
JSON record above, call one operation, and write the answer back. What
the suites below gate is therefore the ROUND TRIP — that a request
reaching a socket arrives at the engine as the record this ABI states,
and that the engine's answer reaches the wire with its status, its
repeated headers and its body intact. The engine's decisions in
isolation are the `#guard`s of `Tests.lean`.

Scores are "N pass, M fail, S skipped (out of T)". The WebAssembly module
is rebuilt by whoever owns the Lean side; a module without these
operations answers `unknown op`, and every suite then probes once and
SKIPS each check by name with that reason printed. A skip is never a pass.

| file | runtimes | what it covers |
|---|---|---|
| `tests/lws/server.mjs` | Node, Deno | the server binds an ephemeral port; PUT creates a data resource; GET reads it back with `Last-Modified`; HEAD carries `Last-Modified` and no body; PUT updates it and `Last-Modified` moves; DELETE removes it; GET after DELETE answers 404; a PATCH whose insertion formula holds a blank node is refused with a 4xx |
| `tests/solid/server/protocol.mjs` | Node, Deno | the storage root advertises `pim:Storage` by `Link rel=type` (§4.1); OPTIONS reports `Allow`, `Accept-Post`, `Accept-Patch`, `Accept-Put` (§4.3); PUT creates a resource and its container gains the containment triple (§5.3); POST assigns a name and reports it in `Location` (§5.4); a PUT that edits a containment triple is refused with 409 (§5.3); DELETE on the storage root is refused with 405 (§5.5); a resource advertises its `describedby` auxiliary and the auxiliary dies with its subject (§4.2); PATCH applies an N3 Patch (§5.6); a CORS preflight is answered with the allow headers (§6); the LDN inbox is advertised and accepts a notification (§7) |
| `tests/solid/client/against-own-server.mjs` | Node, Deno | our client at an in-process instance of our server: `discoverStorage`, `replace`, `read`, `create` with a `Location`, `delete`, that a deleted resource is gone while its POSTed sibling survives, and that every request reached the socket through the engine |
| `tests/solid/client/against-community-server.mjs` | Node | the same five operations with the far end replaced by Community Solid Server, so a misreading our own two sides share cannot pass. Driven by `tools/solid-client-interop.sh` |

Interop scripts, all three exiting `0` passed, `1` failed, `2` could not
run here with the reason printed — never a green skip:

| script | suite | condition it needs |
|---|---|---|
| `tools/solid-server-interop.sh` | `solid-crud-tests`, `web-access-control-tests` | the Solid server operations; `npm ci` for each suite; the access-control suite additionally logs in through an external Solid-OIDC issuer before its first request |
| `tools/solid-client-interop.sh` | our client against Community Solid Server | the Solid client operations; `npx`; 2 GB free for the ~250 MB download |
| `tools/solid-conformance-harness.sh` | `solid-specification-tests` | a Docker daemon and a `SOLID_HARNESS_ENV` credentials file |

Measured 2026-09-06 against the committed WebAssembly module, which does
not carry these operations: `tests/lws/server.mjs` 0 pass, 0 fail, 8
skipped (out of 8); `tests/solid/server/protocol.mjs` 0 pass, 0 fail, 12
skipped (out of 12); `tests/solid/client/against-own-server.mjs` 0 pass,
0 fail, 7 skipped (out of 7); all three interop scripts exit 2.

## F* statement list

The F* tree states the same requirement identifiers over an abstract
resource store: [`formal/fstar/LWS.Core.Spec.fsti`](../formal/fstar/LWS.Core.Spec.fsti)
with its model and proofs in `LWS.Core.Spec.fst`, and
[`formal/fstar/Solid.Protocol.Spec.fsti`](../formal/fstar/Solid.Protocol.Spec.fsti)
which imports it and adds the Solid layer, its server statements in Part 8
and its client statements in Part 9. The list below is generated from
[`formal/fstar/LWS.Solid.Registry.fst`](../formal/fstar/LWS.Solid.Registry.fst),
whose rows carry the same identifiers and the same verbatim statements as the
Lean registries, and which proves that no identifier appears twice.

The F* modules are specifications, not an engine: each one declares the
operations over an abstract store and states the requirement as a `val` or a
lemma, and the accompanying `.fst` gives one model that discharges every law.
The engine is the Lean tree. A row with no F* statement is one the F* side
does not state yet; the Lean rows above say how that row is decided.

Verified with z3 4.13.3, no `--lax` and no `--admit_smt_queries`:
`fstar.exe --z3version 4.13.3 --cache_checked_modules <module>`.

51 of the 91 rows carry an F* statement (18 LWS rows: 10 stated;
73 Solid rows: 41 stated).

| requirement | source | section | F* statement |
|---|---|---|---|
| `lws-core-01` | LWS | Resource Access | - |
| `lws-core-02` | LWS | Resource Access | - |
| `lws-core-03` | LWS | For Editors (CG-to-ED delta) | `LWS.Core.Spec.lws_core_03_last_modified_on_get`, `LWS.Core.Spec.lws_core_03_last_modified_on_head` |
| `lws-core-04` | LWS | For Editors (CG-to-ED delta) | `LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes`, `LWS.Core.Spec.lws_core_04_ill_formed_patch_refused` |
| `lws-core-05` | LWS | Terminology | `LWS.Core.Spec.lws_core_05_create_updates_containment`, `LWS.Core.Spec.lws_core_05_delete_updates_containment`, `LWS.Core.Spec.contained_are_children` |
| `lws-core-06` | LWS | Terminology | `LWS.Core.Spec.lws_core_06_root_has_no_parent`, `LWS.Core.Spec.lws_core_06_only_root_has_no_parent`, `LWS.Core.Spec.containment_acyclic`, `LWS.Core.Spec.containment_single_parent`, `LWS.Core.Spec.lws_core_root_not_deleted` |
| `lws-core-07` | LWS | Terminology | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `lws-core-08` | LWS | Terminology | `LWS.Core.Spec.lws_core_08_auxiliary_links_advertised` |
| `lws-core-09` | LWS | Terminology | - |
| `lws-core-10` | LWS | Terminology | - |
| `lws-core-11` | LWS | Resource Access | `LWS.Core.Spec.lws_core_11_four_operations` |
| `lws-core-12` | LWS | Resource Access | `LWS.Core.Spec.lws_core_12_created_is_not_success` |
| `lws-core-13` | LWS | Resource Access | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `lws-core-14` | LWS | Resource Access | - |
| `lws-core-15` | LWS | Authentication | - |
| `lws-core-16` | LWS | Notifications | - |
| `lws-core-17` | LWS | Access Requests and Grants | - |
| `lws-core-18` | LWS | Terminology | `LWS.Core.Spec.lws_core_18_storage_description_link` |
| `solid-02-01` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-02` | Solid | Solid Protocol §2.1 HTTP Server | `Solid.Protocol.Spec.solid_02_02_content_type_required` |
| `solid-02-03` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-04` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-05` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-06` | Solid | Solid Protocol §2.2 HTTP Client | `Solid.Protocol.Spec.solid_02_06_client_content_type` |
| `solid-03-01` | Solid | Solid Protocol §3.1 URI Slash Semantics | `Solid.Protocol.Spec.solid_03_01_slash_denotes_container` |
| `solid-03-02` | Solid | Solid Protocol §3.1 URI Slash Semantics | `Solid.Protocol.Spec.solid_03_02_slash_pair_distinct` |
| `solid-03-03` | Solid | Solid Protocol §3.1 URI Slash Semantics | - |
| `solid-04-01` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-02` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-03` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_03_storage_type_link` |
| `solid-04-04` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_04_storage_description_link` |
| `solid-04-05` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-06` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-07` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_07_owner_link` |
| `solid-04-08` | Solid | Solid Protocol §4.2 Resource Containment | `Solid.Protocol.Spec.solid_04_08_containment_iff_enumerated`, `Solid.Protocol.Spec.solid_04_08_containment_is_hierarchy` |
| `solid-04-09` | Solid | Solid Protocol §4.2 Resource Containment | - |
| `solid-04-10` | Solid | Solid Protocol §4.2.1 Contained Resource Metadata | - |
| `solid-04-11` | Solid | Solid Protocol §4.3 Auxiliary Resources | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `solid-04-12` | Solid | Solid Protocol §4.3 Auxiliary Resources | `Solid.Protocol.Spec.solid_04_12_auxiliary_links_advertised` |
| `solid-04-13` | Solid | Solid Protocol §4.3.2 Description Resource | `Solid.Protocol.Spec.solid_04_13_at_most_one_description` |
| `solid-04-14` | Solid | Solid Protocol §4.3.2 Description Resource | `Solid.Protocol.Spec.solid_04_14_description_authorized_as_subject` |
| `solid-05-01` | Solid | Solid Protocol §5 Reading and Writing Resources | `Solid.Protocol.Spec.solid_05_01_unsupported_method_405` |
| `solid-05-02` | Solid | Solid Protocol §5.1 Resource Type Heuristics | `Solid.Protocol.Spec.solid_05_02_post_assigns_uri` |
| `solid-05-03` | Solid | Solid Protocol §5.2 Reading Resources | - |
| `solid-05-04` | Solid | Solid Protocol §5.2 Reading Resources | `Solid.Protocol.Spec.solid_05_04_allow_header` |
| `solid-05-05` | Solid | Solid Protocol §5.2 Reading Resources | `Solid.Protocol.Spec.solid_05_05_accept_headers` |
| `solid-05-06` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-07` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_07_intermediate_container` |
| `solid-05-08` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_02_post_assigns_uri` |
| `solid-05-09` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_09_post_missing_target_404` |
| `solid-05-10` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-11` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_11_containment_edit_409` |
| `solid-05-12` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-13` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_13_n3_patch_accepted`, `LWS.Core.Spec.lws_patch_not_refused`, `LWS.Core.Spec.lws_patch_applied` |
| `solid-05-14` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_05_accept_headers` |
| `solid-05-15` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-16` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-17` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-18` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes` |
| `solid-05-19` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-20` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_20_patch_operations` |
| `solid-05-21` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-22` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-23` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_25_delete_removes_containment` |
| `solid-05-24` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_24_delete_root_405` |
| `solid-05-25` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_25_delete_removes_containment` |
| `solid-05-26` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `solid-05-27` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_27_delete_non_empty_container_409` |
| `solid-05-28` | Solid | Solid Protocol §5.5 Resource Representations | - |
| `solid-05-29` | Solid | Solid Protocol §5.5 Resource Representations | - |
| `solid-06-01` | Solid | Solid Protocol §6 Linked Data Notifications | - |
| `solid-06-02` | Solid | Solid Protocol §6 Linked Data Notifications | - |
| `solid-07-01` | Solid | Solid Protocol §7.1 Solid Notifications Protocol | - |
| `solid-08-01` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-02` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-03` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-04` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-09-01` | Solid | Solid Protocol §9.1 WebID | - |
| `solid-10-01` | Solid | Solid Protocol §10.1 Solid-OIDC | - |
| `solid-11-01` | Solid | Solid Protocol §11 Authorization | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `solid-wac-01` | Solid | Web Access Control §5.3 Authorization Evaluation | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `solid-wac-02` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_02_match_resource_agent_mode` |
| `solid-wac-03` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_03_default_is_inherited` |
| `solid-wac-04` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_04_agent_group` |
| `solid-wac-05` | Solid | Web Access Control §5.1 Effective ACL Resource Algorithm | - |
| `solid-wac-06` | Solid | Web Access Control §5.3.2 Web Origin Authorization | - |
| `solid-wac-07` | Solid | Web Access Control §5.3.4 Access Privileges | `Solid.Protocol.Spec.solid_wac_07_wac_allow_header` |
| `solid-wac-08` | Solid | Web Access Control §5.3.4 Access Privileges | `Solid.Protocol.Spec.solid_wac_08_client_reads_wac_allow` |
| `solid-wac-09` | Solid | Web Access Control §3.1 ACL Resource Discovery | `Solid.Protocol.Spec.solid_wac_09_client_acl_from_links` |
| `solid-wac-10` | Solid | Web Access Control §3.2 ACL Resource Representation | - |
| `solid-cl-01` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_cl_01_storage_walk_sound` |
