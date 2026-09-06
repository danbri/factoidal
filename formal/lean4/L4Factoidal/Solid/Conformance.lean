/-
L4Factoidal.Solid.Conformance — the MUST-statement registry of the Solid
Protocol and of Web Access Control.

Every statement is quoted VERBATIM from
https://solidproject.org/TR/protocol (v0.11.0, modified 2024-05-12) and
https://solidproject.org/TR/wac, both read 2026-09-06, with the section it
appears in.

The row type and the status values are `L4Factoidal.LWS.Conformance`'s, so
one probe format prints both registries.

Where a row is `guarded`, the name is a `def … : Bool` in
`L4Factoidal.Solid.Tests`. Where it is `proved`, the name is a theorem.
Where it is `hostVerified`, the decision needs a socket, a real clock or a
verified token, and the named suite under `tests/` decides it.
-/
import L4Factoidal.LWS.Conformance

namespace L4Factoidal.Solid.Conformance

open L4Factoidal.LWS.Conformance

def registry : List Requirement :=
[ -- §2.1 HTTP Server
  { id := "solid-02-01"
  , section_ := "Solid Protocol §2.1 HTTP Server"
  , statement := "Servers MUST conform to HTTP Semantics [RFC9110]. […] Servers MUST conform to HTTP/1.1 [RFC9112]."
  , module := "L4Factoidal.HTTP.Server (message framing) plus the Node host"
  , status := .hostVerified "tests/solid/server/protocol.mjs — the framing is the host's; the engine sees a parsed request" }
, { id := "solid-02-02"
  , section_ := "Solid Protocol §2.1 HTTP Server"
  , statement := "Server MUST reject PUT, POST, and PATCH requests that contain content but lack the Content-Type header field, with a status code of 400."
  , module := "L4Factoidal.Solid.Server.Methods.step"
  , status := .guarded "solidGuardContentTypeRequired400" }
, { id := "solid-02-03"
  , section_ := "Solid Protocol §2.1 HTTP Server"
  , statement := "When a client does not provide valid credentials when requesting a resource that requires it (see WebID), servers MUST send a response with a 401 status code (unless 404 is preferred for security reasons)."
  , module := "L4Factoidal.Solid.Server.Methods.step"
  , status := .guarded "solidGuardWacEnforced" }
, { id := "solid-02-04"
  , section_ := "Solid Protocol §2.1 HTTP Server"
  , statement := "When both http and https URI schemes are supported, the server MUST redirect all http URIs to their https counterparts using a response with a 301 status code and a Location header."
  , module := "(the host)"
  , status := .hostVerified "tests/solid/server/protocol.mjs — the scheme is the listener's, not the engine's" }
, { id := "solid-02-05"
  , section_ := "Solid Protocol §2.1 HTTP Server"
  , statement := "Server MUST generate a Content-Type header field in a message that contains content."
  , module := "L4Factoidal.LWS.Operations.readHeaders"
  , status := .guarded "solidGuardAcceptHeaders" }
  -- §2.2 HTTP Client
, { id := "solid-02-06"
  , section_ := "Solid Protocol §2.2 HTTP Client"
  , statement := "Clients MUST use the Content-Type HTTP header field in PUT, POST, and PATCH requests that contain content [RFC9110]."
  , module := "L4Factoidal.Solid.Client.Requests.buildRequest"
  , status := .proved "L4Factoidal.Solid.Client.buildRequest_contentTypePresent" }
  -- §3.1 URI Slash Semantics
, { id := "solid-03-01"
  , section_ := "Solid Protocol §3.1 URI Slash Semantics"
  , statement := "Paths ending with a slash denote a container resource."
  , module := "L4Factoidal.LWS.Model.pathIsContainer"
  , status := .guarded "solidGuardContainment" }
, { id := "solid-03-02"
  , section_ := "Solid Protocol §3.1 URI Slash Semantics"
  , statement := "If two URIs differ only in the trailing slash, and the server has associated a resource with one of them, then the other URI MUST NOT correspond to another resource. Instead, the server MAY respond to requests for the latter URI with a 301 redirect to the former."
  , module := "L4Factoidal.Solid.Server.Storage.slashRedirect?"
  , status := .guarded "solidGuardSlashRedirect" }
, { id := "solid-03-03"
  , section_ := "Solid Protocol §3.1 URI Slash Semantics"
  , statement := "Servers MUST authorize prior to this optional redirect."
  , module := "L4Factoidal.Solid.Server.Methods.step"
  , status := .guarded "solidGuardWacEnforced" }
  -- §4.1 Storage Resource
, { id := "solid-04-01"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "Servers MUST provide one or more storages."
  , module := "L4Factoidal.Solid.Server.Storage.storageRootPath"
  , status := .guarded "solidGuardStorageTypeLink" }
, { id := "solid-04-02"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "When a server supports multiple storages, the URIs MUST be allocated to non-overlapping space."
  , module := "Wasm/Ops/Solid.lean (one storage per handle)"
  , status := .hostVerified "tests/solid/server/protocol.mjs — two storages are two handles with different base IRIs" }
, { id := "solid-04-03"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "Servers MUST advertise the storage resource by including the HTTP Link header field with rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage when responding to storage's request URI."
  , module := "L4Factoidal.LWS.Discovery.discoveryLinks"
  , status := .guarded "solidGuardStorageTypeLink" }
, { id := "solid-04-04"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "Servers MUST include the Link header field with rel=\"http://www.w3.org/ns/solid/terms#storageDescription\" targeting the URI of the storage description resource in the response of HTTP GET, HEAD and OPTIONS requests targeting a resource in a storage."
  , module := "L4Factoidal.LWS.Discovery.discoveryLinks"
  , status := .guarded "solidGuardStorageDescriptionLink" }
, { id := "solid-04-05"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "Servers MUST include statements about the storage as part of the storage description resource."
  , module := "L4Factoidal.Solid.Server.Storage.storageDescriptionGraph"
  , status := .«open» "the graph is built; the storage description resource is not yet served at its own path" }
, { id := "solid-04-06"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "Servers MUST keep track of at least one owner of a storage in an implementation defined way."
  , module := "L4Factoidal.LWS.Operations.Config.owner"
  , status := .guarded "solidGuardOwnerLink" }
, { id := "solid-04-07"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "When a server wants to advertise the owner of a storage, the server MUST include the Link header field with rel=\"http://www.w3.org/ns/solid/terms#owner\" targeting the URI of the owner in the response of HTTP HEAD or GET requests targeting the root container."
  , module := "L4Factoidal.LWS.Discovery.discoveryLinks"
  , status := .guarded "solidGuardOwnerLink" }
, { id := "solid-04-15"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "Clients can determine the storage of a resource by moving up the URI path hierarchy until the response includes a Link header field with rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage."
  , module := "L4Factoidal.Solid.Client.Discovery.storageStepOf, Responses.storageReading"
  , status := .guarded "solidGuardClientStorageWalkSteps" }
  -- §4.2 Resource Containment
, { id := "solid-04-08"
  , section_ := "Solid Protocol §4.2 Resource Containment"
  , statement := "There is a 1-1 correspondence between containment triples and relative reference within the path name hierarchy."
  , module := "L4Factoidal.Solid.Server.Containment"
  , status := .proved "L4Factoidal.Solid.Server.containerOfChildUnique, containedByParent, memContainedPaths_iff" }
, { id := "solid-04-09"
  , section_ := "Solid Protocol §4.2 Resource Containment"
  , statement := "The representation and behaviour of containers in Solid corresponds to LDP Basic Container and MUST be supported by server."
  , module := "L4Factoidal.Solid.Server.Containment.containerGraph"
  , status := .guarded "solidGuardContainment" }
, { id := "solid-04-10"
  , section_ := "Solid Protocol §4.2.1 Contained Resource Metadata"
  , statement := "Servers SHOULD include resource metadata about contained resources as part of the container description, unless that information is inapplicable to the server."
  , module := "L4Factoidal.Solid.Server.Containment.containedMetadata"
  , status := .guarded "solidGuardContainment" }
  -- §4.3 Auxiliary Resources
, { id := "solid-04-11"
  , section_ := "Solid Protocol §4.3 Auxiliary Resources"
  , statement := "Servers MUST support auxiliary resources defined by this specification and manage the association between a subject resource and auxiliary resources. When a subject resource is deleted its auxiliary resources are also deleted by the server."
  , module := "L4Factoidal.Solid.Server.Auxiliary"
  , status := .proved "L4Factoidal.Solid.Server.auxiliariesDeletedWithSubject" }
, { id := "solid-04-12"
  , section_ := "Solid Protocol §4.3 Auxiliary Resources"
  , statement := "Servers MUST advertise auxiliary resources associated with a subject resource by responding to HEAD and GET requests by including the HTTP Link header field with the rel parameter [RFC8288]."
  , module := "L4Factoidal.LWS.Discovery.discoveryLinks"
  , status := .guarded "solidGuardAuxiliaryLinks" }
, { id := "solid-04-13"
  , section_ := "Solid Protocol §4.3.2 Description Resource"
  , statement := "Servers MUST NOT directly associate more than one description resource to a subject resource."
  , module := "L4Factoidal.Solid.Server.Auxiliary.auxiliaryPaths"
  , status := .guarded "solidGuardDescriptionAuthorizedAsSubject" }
, { id := "solid-04-14"
  , section_ := "Solid Protocol §4.3.2 Description Resource"
  , statement := "When an HTTP request targets a description resource, the server MUST apply the authorization rule that is used for the subject resource with which the description resource is associated."
  , module := "L4Factoidal.Solid.Server.Auxiliary.authorizationSubject"
  , status := .guarded "solidGuardDescriptionAuthorizedAsSubject" }
  -- §5 Reading and Writing Resources
, { id := "solid-05-01"
  , section_ := "Solid Protocol §5 Reading and Writing Resources"
  , statement := "Servers MUST respond with the 405 status code to requests using HTTP methods that are not supported by the target resource."
  , module := "L4Factoidal.LWS.Operations.step"
  , status := .guarded "solidGuardUnsupportedMethod405" }
, { id := "solid-05-02"
  , section_ := "Solid Protocol §5.1 Resource Type Heuristics"
  , statement := "When a successful POST request creates a resource, the server MUST assign a URI to that resource."
  , module := "L4Factoidal.LWS.Operations.assignedName"
  , status := .guarded "solidGuardPostAssignsName" }
, { id := "solid-05-03"
  , section_ := "Solid Protocol §5.2 Reading Resources"
  , statement := "Servers MUST support the HTTP GET, HEAD and OPTIONS methods [RFC9110] for clients to read resources or to determine communication options."
  , module := "L4Factoidal.LWS.Operations.step"
  , status := .guarded "solidGuardAllowHeader" }
, { id := "solid-05-04"
  , section_ := "Solid Protocol §5.2 Reading Resources"
  , statement := "Servers MUST indicate the HTTP methods supported by the target resource by generating an Allow header field in successful responses."
  , module := "L4Factoidal.LWS.Operations.allowFor"
  , status := .guarded "solidGuardAllowHeader" }
, { id := "solid-05-05"
  , section_ := "Solid Protocol §5.2 Reading Resources"
  , statement := "When responding to authorized requests, servers MUST indicate supported media types in the HTTP Accept-Patch [RFC5789], Accept-Post [LDP] and Accept-Put [The Accept-Put Response Header] response header fields that correspond to acceptable HTTP methods listed in Allow header field value in response to HTTP GET, HEAD and OPTIONS requests."
  , module := "L4Factoidal.LWS.Operations.readHeaders"
  , status := .guarded "solidGuardAcceptHeaders" }
, { id := "solid-05-06"
  , section_ := "Solid Protocol §5.3 Writing Resources"
  , statement := "Servers MUST support the HTTP PUT, POST and PATCH methods [RFC9110]."
  , module := "L4Factoidal.Solid.Server.Methods.step"
  , status := .guarded "solidGuardPostAssignsName" }
, { id := "solid-05-07"
  , section_ := "Solid Protocol §5.3 Writing Resources"
  , statement := "Servers MUST create intermediate containers and include corresponding containment triples in container representations derived from the URI path component of PUT and PATCH requests."
  , module := "L4Factoidal.LWS.Operations.ensureAncestors"
  , status := .guarded "solidGuardIntermediateContainers" }
, { id := "solid-05-08"
  , section_ := "Solid Protocol §5.3 Writing Resources"
  , statement := "Servers MUST allow creation of new resources by a POST request to a URI path ending with /. Servers MUST create resources with URI paths ending with /{id} in container /."
  , module := "L4Factoidal.LWS.Operations.step"
  , status := .guarded "solidGuardPostAssignsName" }
, { id := "solid-05-09"
  , section_ := "Solid Protocol §5.3 Writing Resources"
  , statement := "When a POST method request targets a resource without an existing representation, the server MUST respond with the 404 status code."
  , module := "L4Factoidal.LWS.Operations.step"
  , status := .guarded "solidGuardPostMissingTarget404" }
, { id := "solid-05-10"
  , section_ := "Solid Protocol §5.3 Writing Resources"
  , statement := "When a PUT or PATCH request targets an auxiliary resource, the server MUST create or update it."
  , module := "L4Factoidal.Solid.Server.Methods.step"
  , status := .guarded "solidGuardPutAuxiliary" }
, { id := "solid-05-11"
  , section_ := "Solid Protocol §5.3 Writing Resources"
  , statement := "Servers MUST NOT allow HTTP PUT or PATCH on a container to update its containment triples; if the server receives such a request, it MUST respond with a 409 status code."
  , module := "L4Factoidal.Solid.Server.Methods.bodyEditsContainment"
  , status := .guarded "solidGuardPutRefusesContainmentEdit409" }
, { id := "solid-05-12"
  , section_ := "Solid Protocol §5.3 Writing Resources"
  , statement := "Servers MUST NOT allow HTTP POST, PUT and PATCH to update a container's resource metadata statements; if the server receives such a request, it MUST respond with a 409 status code."
  , module := "L4Factoidal.Solid.Server.Methods.step"
  , status := .«open» "the containment-triple half of the rule is decided; server-managed metadata statements of a container are not yet distinguished from author-supplied ones" }
  -- §5.3.1 N3 Patch
, { id := "solid-05-13"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "Servers MUST accept a PATCH request with an N3 Patch body when the target of the request is an RDF document [RDF11-CONCEPTS]."
  , module := "L4Factoidal.Solid.Server.N3Patch"
  , status := .guarded "solidGuardN3PatchApplies" }
, { id := "solid-05-14"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "Servers MUST indicate support of N3 Patch by listing text/n3 as a field value of the Accept-Patch header field [RFC5789] of relevant responses."
  , module := "L4Factoidal.LWS.Operations.readHeaders"
  , status := .guarded "solidGuardN3PatchAcceptPatch" }
, { id := "solid-05-15"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "When present, ?deletions, ?insertions, and ?conditions MUST be non-nested cited formulae [N3] consisting only of triples and/or triple patterns [SPARQL11-QUERY]."
  , module := "L4Factoidal.Solid.Server.N3Patch.takeToBrace"
  , status := .guarded "solidGuardN3PatchBlankNode422" }
, { id := "solid-05-16"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "A patch resource MUST contain a triple ?patch rdf:type solid:InsertDeletePatch."
  , module := "L4Factoidal.Solid.Server.N3Patch.parseN3Patch"
  , status := .guarded "solidGuardPatchMediaType415" }
, { id := "solid-05-17"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "The ?insertions and ?deletions formulae MUST NOT contain variables that do not occur in the ?conditions formula."
  , module := "L4Factoidal.LWS.Patch.wellFormed"
  , status := .guarded "lwsGuardInsertionsRefuseBlankNodes (L4Factoidal.LWS.Tests)" }
, { id := "solid-05-18"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "The ?insertions and ?deletions formulae MUST NOT contain blank nodes."
  , module := "L4Factoidal.LWS.Patch.wellFormed"
  , status := .guarded "solidGuardN3PatchBlankNode422" }
, { id := "solid-05-19"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "Servers MUST respond with a 422 status code [RFC4918] if a patch document does not satisfy all of the above constraints."
  , module := "L4Factoidal.Solid.Server.N3Patch.N3PatchError.status"
  , status := .guarded "solidGuardN3PatchBlankNode422" }
, { id := "solid-05-20"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "When ?conditions is non-empty, servers MUST treat the request as a Read operation. When ?insertions is non-empty, servers MUST (also) treat the request as an Append operation. When ?deletions is non-empty, servers MUST treat the request as a Read and Write operation."
  , module := "L4Factoidal.LWS.Patch.patchOperations"
  , status := .guarded "solidGuardN3PatchOperations" }
, { id := "solid-05-21"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "If no such mapping exists, or if multiple mappings exist, the server MUST respond with a 409 status code."
  , module := "L4Factoidal.LWS.Patch.applyPatch"
  , status := .guarded "solidGuardN3PatchNoMatch409, solidGuardN3PatchMultipleMatch409" }
, { id := "solid-05-22"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches"
  , statement := "If the set of triples resulting from ?deletions is non-empty and the dataset does not contain all of these triples, the server MUST respond with a 409 status code."
  , module := "L4Factoidal.LWS.Patch.applyPatch"
  , status := .guarded "solidGuardN3PatchDeletionsAbsent409" }
, { id := "solid-05-30"
  , section_ := "Solid Protocol §5.3.1 Modifying Resources Using N3 Patches, with RFC 3986 §5.1.3"
  , statement := "The base URI of a representation is the URI used to retrieve it. (RFC 3986 §5.1.3 Base URI from the Retrieval URI; the Solid Protocol states no base of its own, and its own N3 Patch examples and every client use relative references such as <> and <#it>.)"
  , module := "L4Factoidal.Solid.Server.N3Patch.parseFormula"
  , status := .guarded "solidGuardN3PatchRelativeIri" }
  -- §5.4 Deleting Resources
, { id := "solid-05-23"
  , section_ := "Solid Protocol §5.4 Deleting Resources"
  , statement := "Servers MUST support the HTTP DELETE method [RFC9110]."
  , module := "L4Factoidal.LWS.Operations.step"
  , status := .guarded "solidGuardDeleteRemovesContainment" }
, { id := "solid-05-24"
  , section_ := "Solid Protocol §5.4 Deleting Resources"
  , statement := "When a DELETE request targets storage's root container or its associated ACL resource, the server MUST respond with the 405 status code. Server MUST exclude the DELETE method in the field value of the Allow header field, in response to requests to these resources."
  , module := "L4Factoidal.Solid.Server.Methods.step"
  , status := .guarded "solidGuardDeleteRootRefused405" }
, { id := "solid-05-25"
  , section_ := "Solid Protocol §5.4 Deleting Resources"
  , statement := "When a contained resource is deleted, the server MUST also remove the corresponding containment triple."
  , module := "L4Factoidal.Solid.Server.Containment.containmentTriples"
  , status := .guarded "solidGuardDeleteRemovesContainment" }
, { id := "solid-05-26"
  , section_ := "Solid Protocol §5.4 Deleting Resources"
  , statement := "When a contained resource is deleted, the server MUST also delete the associated auxiliary resources."
  , module := "L4Factoidal.Solid.Server.Auxiliary.deleteWithAuxiliaries"
  , status := .guarded "solidGuardDeleteRemovesAuxiliaries" }
, { id := "solid-05-27"
  , section_ := "Solid Protocol §5.4 Deleting Resources"
  , statement := "When a DELETE request targets a container, the server MUST delete the container if it contains no resources. If the container contains resources, the server MUST respond with the 409 status code."
  , module := "L4Factoidal.LWS.Operations.step"
  , status := .guarded "solidGuardDeleteNonEmptyContainer409" }
  -- §5.5 Resource Representations
, { id := "solid-05-28"
  , section_ := "Solid Protocol §5.5 Resource Representations"
  , statement := "When a server creates an RDF source on HTTP PUT, POST, or PATCH requests, the server MUST satisfy GET requests on this resource when the Accept header field requests text/turtle or application/ld+json."
  , module := "L4Factoidal.LWS.Operations.step"
  , status := .«open» "text/turtle is answered; content negotiation to application/ld+json is not wired to the JSON-LD serialiser yet" }
, { id := "solid-05-29"
  , section_ := "Solid Protocol §5.5 Resource Representations"
  , statement := "When a PUT, POST, PATCH or DELETE method request targets a representation URL that is different than the resource URL, the server MUST respond with a 307 or 308 status code."
  , module := "(none)"
  , status := .«open» "this server has no separate representation URLs, so the condition never arises; it becomes a rule when content negotiation adds them" }
  -- §6 Linked Data Notifications
, { id := "solid-06-01"
  , section_ := "Solid Protocol §6 Linked Data Notifications"
  , statement := "A Solid server MUST conform to the LDN specification by implementing the Receiver parts to receive notifications, and MAY implement the Sender or Consumer parts."
  , module := "L4Factoidal.Solid.Server.Ldn"
  , status := .guarded "solidGuardInboxAcceptsPost" }
, { id := "solid-06-02"
  , section_ := "Solid Protocol §6 Linked Data Notifications"
  , statement := "A Solid client MUST conform to the LDN specification by implementing the Sender or Consumer parts to send or read notifications."
  , module := "L4Factoidal.Solid.Client.Discovery.inboxOf?"
  , status := .guarded "solidGuardClientReadsLinks" }
, { id := "solid-06-03"
  , section_ := "Linked Data Notifications §3.1 Discovery"
  , statement := "make an HTTP HEAD or GET request on the target URL, and use the Link header with a rel value of http://www.w3.org/ns/ldp#inbox […] A resource MUST advertise only one Inbox."
  , module := "L4Factoidal.Solid.Server.Ldn.inboxLinks"
  , status := .guarded "solidGuardInboxAdvertised" }
  -- §7.1 Solid Notifications Protocol
, { id := "solid-07-01"
  , section_ := "Solid Protocol §7.1 Solid Notifications Protocol"
  , statement := "Servers MUST conform to the Solid Notifications Protocol by implementing the Resource Server, Subscription Server, Notification Sender and Notification Receiver."
  , module := "(none)"
  , status := .«open» "not in the first slice; the design record lists notification channels as later work" }
  -- §8.1 CORS Server
, { id := "solid-08-01"
  , section_ := "Solid Protocol §8.1 CORS Server"
  , statement := "A server MUST implement the CORS protocol [FETCH] such that browsers allow Solid apps to send any request and combination of request headers to the server, and allow the app to read any response and response headers received from the server."
  , module := "L4Factoidal.Solid.Server.Cors"
  , status := .guarded "solidGuardCorsHeaders" }
, { id := "solid-08-02"
  , section_ := "Solid Protocol §8.1 CORS Server"
  , statement := "The server MUST set the Access-Control-Allow-Origin header field value to the valid Origin header field value from the request and list Origin in the Vary header field value."
  , module := "L4Factoidal.Solid.Server.Cors.corsHeaders"
  , status := .guarded "solidGuardCorsHeaders" }
, { id := "solid-08-03"
  , section_ := "Solid Protocol §8.1 CORS Server"
  , statement := "The server MUST make all used response headers readable for the Solid app through Access-Control-Expose-Headers."
  , module := "L4Factoidal.Solid.Server.Cors.exposedHeaders"
  , status := .guarded "solidGuardCorsHeaders" }
, { id := "solid-08-04"
  , section_ := "Solid Protocol §8.1 CORS Server"
  , statement := "A server MUST also support the HTTP OPTIONS method such that it can respond appropriately to CORS preflight requests."
  , module := "L4Factoidal.Solid.Server.Cors.isPreflight"
  , status := .guarded "solidGuardCorsPreflight" }
  -- §9.1 WebID
, { id := "solid-09-01"
  , section_ := "Solid Protocol §9.1 WebID"
  , statement := "When a WebID is dereferenced, server provides a representation of the WebID Profile in an RDF document."
  , module := "L4Factoidal.Solid.Client.Profile"
  , status := .guarded "solidGuardClientProfile" }
  -- §10 Authentication
, { id := "solid-10-01"
  , section_ := "Solid Protocol §10.1 Solid-OIDC"
  , statement := "Servers MUST conform to the Solid-OIDC specification."
  , module := "L4Factoidal.Solid.Server.Auth"
  , status := .guarded "solidGuardSolidOidcDpop" }
  -- §11 Authorization, and Web Access Control
, { id := "solid-11-01"
  , section_ := "Solid Protocol §11 Authorization"
  , statement := "Servers MUST conform to either or both Web Access Control and Access Control Policy specifications."
  , module := "L4Factoidal.Solid.Server.WAC"
  , status := .guarded "solidGuardWacEnforced" }
, { id := "solid-wac-01"
  , section_ := "Web Access Control §5.3 Authorization Evaluation"
  , statement := "Access is granted when conforming Authorizations are matched, otherwise access is denied."
  , module := "L4Factoidal.Solid.Server.WAC.decideAccess"
  , status := .guarded "solidGuardWacDenies" }
, { id := "solid-wac-02"
  , section_ := "Web Access Control §5.3.3 Authorization Matching"
  , statement := "Match an Authorization with a specific resource, agent and access mode."
  , module := "L4Factoidal.Solid.Server.WAC.decideAccess"
  , status := .guarded "solidGuardWacAccessToAgentMode" }
, { id := "solid-wac-03"
  , section_ := "Web Access Control §5.3.3 Authorization Matching"
  , statement := "Match an Authorization with a specific container resource, agent class membership and access mode."
  , module := "L4Factoidal.Solid.Server.WAC.decideAccess"
  , status := .guarded "solidGuardWacDefaultAgentClassSuperclassMode" }
, { id := "solid-wac-04"
  , section_ := "Web Access Control §5.3.3 Authorization Matching"
  , statement := "Match an Authorization with a specific resource, agent with any group membership, and specific access mode."
  , module := "L4Factoidal.Solid.Server.WAC.subjectMatches"
  , status := .guarded "solidGuardWacAgentGroup" }
, { id := "solid-wac-05"
  , section_ := "Web Access Control §5.1 Effective ACL Resource Algorithm"
  , statement := "If resource has an associated aclResource with a representation, return aclResource. Otherwise, repeat the steps using the container resource of resource."
  , module := "L4Factoidal.Solid.Server.WAC.effectiveAcl"
  , status := .guarded "solidGuardWacEnforced" }
, { id := "solid-wac-06"
  , section_ := "Web Access Control §5.3.2 Web Origin Authorization"
  , statement := "When a server participates in the CORS protocol [FETCH] and authorization is granted to an HTTP request including the Origin header, the server MUST include the HTTP Access-Control-Allow-Origin and Access-Control-Allow-Headers headers in the response of the HTTP request."
  , module := "L4Factoidal.Solid.Server.WAC.subjectMatches, Cors.corsHeaders"
  , status := .«open» "the CORS fields are generated; the acl:origin CONDITION on the access decision is read into the model but not applied" }
, { id := "solid-wac-07"
  , section_ := "Web Access Control §5.3.4 Access Privileges"
  , statement := "Servers MUST advertise client's access privileges on a resource by including the WAC-Allow HTTP header in the response of HTTP GET and HEAD requests."
  , module := "L4Factoidal.Solid.Server.WAC.wacAllow"
  , status := .guarded "solidGuardWacAllowHeader" }
, { id := "solid-wac-08"
  , section_ := "Web Access Control §5.3.4 Access Privileges"
  , statement := "Clients MUST discover access privileges on a resource by making an HTTP GET or HEAD request on the target resource, and checking the WAC-Allow header value for access parameters listing the allowed access modes per permission group."
  , module := "L4Factoidal.Solid.Client.Responses.parseWacAllow"
  , status := .guarded "solidGuardClientWacAllowParsing" }
, { id := "solid-wac-09"
  , section_ := "Web Access Control §3.1 ACL Resource Discovery"
  , statement := "Clients MUST discover the ACL resource associated with a resource by making an HTTP request on the target URL, and checking the HTTP Link header with the rel parameter. […] Clients MUST NOT derive the URI of the ACL resource through string operations on the URI of the resource."
  , module := "L4Factoidal.Solid.Client.Discovery.aclOf?"
  , status := .guarded "solidGuardClientReadsLinks" }
, { id := "solid-wac-10"
  , section_ := "Web Access Control §3.2 ACL Resource Representation"
  , statement := "Root container ACL resources MUST have representations. The ACL resource of the root container MUST include an Authorization allowing the acl:Control access privilege."
  , module := "(none)"
  , status := .«open» "a storage is created without a root ACL; enforcement is therefore off by default (ServerConfig.enforceWac) and a root ACL is a host provisioning step" }
, { id := "solid-cl-01"
  , section_ := "Solid Protocol §4.1 Storage Resource"
  , statement := "Clients can determine the storage of a resource by moving up the URI path hierarchy until the response includes a Link header field with rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage."
  , module := "L4Factoidal.Solid.Client.Discovery.storageWalk"
  , status := .guarded "solidGuardClientStorageWalk" }
, { id := "solid-cl-02"
  , section_ := "RFC 9110 §5.1 Field Names, RFC 8288 §3 Link Serialisation in HTTP Headers"
  , statement := "Field names are case-insensitive. […] The Link header field provides a means for serialising one or more links into HTTP headers, [where] each link-value is separated by a comma and the parameters of a link-value by a semicolon; a comma or semicolon inside a URI-Reference or a quoted-string is not a separator."
  , module := "L4Factoidal.Solid.Client.Discovery.linksOf, Responses.headerOf"
  , status := .guarded "solidGuardClientLinkFieldShapes" }
]

def counts : Nat × Nat × Nat × Nat :=
  ( (registry.filter isProved).length
  , (registry.filter isGuarded).length
  , (registry.filter isHost).length
  , (registry.filter isOpen).length )

/-- Every row is decided one way or another. -/
theorem countsTotal :
    counts.1 + counts.2.1 + counts.2.2.1 + counts.2.2.2 = registry.length := by
  rfl

end L4Factoidal.Solid.Conformance
