/-
L4Factoidal.Solid.Tests — one build-time check per `guarded` row of
`L4Factoidal.Solid.Conformance.registry`.

Every `#guard` is evaluated during `lake build`: a wrong answer is a build
failure. Each check is a named `def` returning `Bool`, so the registry row
names it and `Harness/SolidProbe.lean` prints the name beside the statement
it decides.

The Web Access Control checks reproduce the three worked ASK queries of
WAC §5.3.3 as ACL documents in Turtle, parsed by the Turtle parser and
decided by `Solid.Server.decideAccess`.
-/
import L4Factoidal.Solid.Server.Methods
import L4Factoidal.Solid.Server.Auth
import L4Factoidal.Solid.Client.Requests
import L4Factoidal.Solid.Client.Responses
import L4Factoidal.Solid.Client.Profile
import L4Factoidal.Solid.Conformance

namespace L4Factoidal.Solid.Tests

open L4Factoidal.RDF
open L4Factoidal.LWS
open L4Factoidal.Syntax
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.Solid.Server
open L4Factoidal.Solid.Client

/-! ## Fixtures -/

def base : String := "http://example.org/"

def cfg : ServerConfig :=
  { lws := { baseIri := base, owner := some "http://example.org/alice/card#me" } }

def emptyStorage : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := "", mtime := 0 }], clock := 1 }

def req (method target : String) (headers : List (String × String) := [])
    (body : String := "") : Request :=
  { method, path := target, queryStr := "", headers, body }

def run (c : ServerConfig) (r : Request) (st : MemState) : Response × MemState :=
  Server.step MemStore c r st

def runAll (c : ServerConfig) : List Request → MemState → List Response × MemState
  | [], st => ([], st)
  | r :: rest, st =>
      let (resp, st') := run c r st
      let (resps, st'') := runAll c rest st'
      (resp :: resps, st'')

def hdr (resp : Response) (name : String) : Option String :=
  (resp.headers.find? (fun (k, _) => k == name)).map (·.2)

def has (resp : Response) (name needle : String) : Bool :=
  match hdr resp name with
  | none => false
  | some v => (v.splitOn needle).length > 1

def turtle : List (String × String) := [("content-type", "text/turtle")]
def n3 : List (String × String) := [("content-type", "text/n3")]

/-- A storage holding `/alice/card`, `/alice/notes/` and `/alice/notes/one`. -/
def populated : MemState :=
  (runAll cfg [ req "PUT" "/alice/card" turtle "<http://example.org/alice/card#me> <http://xmlns.com/foaf/0.1/name> \"Alice\" ."
              , req "PUT" "/alice/notes/" turtle ""
              , req "PUT" "/alice/notes/one" turtle "<http://example.org/a> <http://example.org/b> <http://example.org/c> ."
              ] emptyStorage).2

/-! ## §4.1 — the storage resource -/

/-- "Servers MUST advertise the storage resource by including the HTTP Link
header field with rel=\"type\" targeting
http://www.w3.org/ns/pim/space#Storage when responding to storage's request
URI." -/
def solidGuardStorageTypeLink : Bool :=
  let (resp, _) := run cfg (req "GET" "/") populated
  has resp "link" "<http://www.w3.org/ns/pim/space#Storage>; rel=\"type\"" &&
  !has (run cfg (req "GET" "/alice/card") populated).1 "link"
       "<http://www.w3.org/ns/pim/space#Storage>; rel=\"type\""

/-- "Servers MUST include the Link header field with
rel=\"http://www.w3.org/ns/solid/terms#storageDescription\" targeting the
URI of the storage description resource in the response of HTTP GET, HEAD
and OPTIONS requests targeting a resource in a storage." -/
def solidGuardStorageDescriptionLink : Bool :=
  has (run cfg (req "GET" "/alice/card") populated).1 "link"
      "rel=\"http://www.w3.org/ns/solid/terms#storageDescription\""

/-- "When a server wants to advertise the owner of a storage, the server
MUST include the Link header field with
rel=\"http://www.w3.org/ns/solid/terms#owner\" targeting the URI of the
owner in the response of HTTP HEAD or GET requests targeting the root
container." -/
def solidGuardOwnerLink : Bool :=
  has (run cfg (req "GET" "/") populated).1 "link"
      "rel=\"http://www.w3.org/ns/solid/terms#owner\"" &&
  !has (run cfg (req "GET" "/alice/card") populated).1 "link"
       "rel=\"http://www.w3.org/ns/solid/terms#owner\""

#guard solidGuardStorageTypeLink
#guard solidGuardStorageDescriptionLink
#guard solidGuardOwnerLink

/-! ## §3.1 — slash semantics -/

/-- "Instead, the server MAY respond to requests for the latter URI with a
301 redirect to the former." This server takes the MAY. -/
def solidGuardSlashRedirect : Bool :=
  let (toContainer, _) := run cfg (req "GET" "/alice/notes") populated
  let (toResource, _) := run cfg (req "GET" "/alice/card/") populated
  toContainer.status == 301 && hdr toContainer "location" == some "/alice/notes/" &&
  toResource.status == 301 && hdr toResource "location" == some "/alice/card"

#guard solidGuardSlashRedirect

/-! ## §4.2 — containment -/

/-- "There is a 1-1 correspondence between containment triples and relative
reference within the path name hierarchy." A GET on a container answers its
containment triples. -/
def solidGuardContainment : Bool :=
  let (resp, _) := run cfg (req "GET" "/alice/") populated
  -- The response body is read back through the Turtle parser, so the check
  -- covers the serialisation as well as the containment relation.
  let served := aclGraphOf resp.body
  let contains := served.filter (fun t => t.p == ldpContains)
  resp.status == 200 && hdr resp "content-type" == some "text/turtle" &&
  contains.length == 2 &&
  contains.any (fun t => t.o == Term.iri ⟨"http://example.org/alice/card", by rfl⟩) &&
  contains.any (fun t => t.o == Term.iri ⟨"http://example.org/alice/notes/", by rfl⟩) &&
  -- §4.2.1: the metadata of each contained resource is in the description.
  served.any (fun t => t.p == statSize)

#guard solidGuardContainment

-- The container graph holds exactly one containment triple per contained
-- resource.
#guard (containmentTriples MemStore base populated "/alice/").length == 2
#guard (containmentTriples MemStore base populated "/alice/notes/").length == 1

/-! ## §4.3 — auxiliary resources -/

/-- "Servers MUST advertise auxiliary resources associated with a subject
resource by responding to HEAD and GET requests by including the HTTP Link
header field with the rel parameter [RFC8288]." -/
def solidGuardAuxiliaryLinks : Bool :=
  let (resp, _) := run cfg (req "HEAD" "/alice/card") populated
  has resp "link" "rel=\"acl\"" && has resp "link" "rel=\"describedby\""

#guard solidGuardAuxiliaryLinks

/-- "When an HTTP request targets a description resource, the server MUST
apply the authorization rule that is used for the subject resource with
which the description resource is associated." -/
def solidGuardDescriptionAuthorizedAsSubject : Bool :=
  authorizationSubject "/alice/card.meta" == "/alice/card" &&
  authorizationSubject "/alice/card.acl" == "/alice/card" &&
  authorizationSubject "/alice/card" == "/alice/card"

#guard solidGuardDescriptionAuthorizedAsSubject

/-! ## §5.2 — reading resources -/

/-- "Servers MUST indicate the HTTP methods supported by the target resource
by generating an Allow header field in successful responses." -/
def solidGuardAllowHeader : Bool :=
  let (resp, _) := run cfg (req "GET" "/alice/card") populated
  has resp "allow" "GET" && has resp "allow" "HEAD" && has resp "allow" "OPTIONS"

/-- "When responding to authorized requests, servers MUST indicate supported
media types in the HTTP Accept-Patch, Accept-Post and Accept-Put response
header fields." -/
def solidGuardAcceptHeaders : Bool :=
  let (container, _) := run cfg (req "GET" "/alice/") populated
  let (resource, _) := run cfg (req "GET" "/alice/card") populated
  hdr container "accept-patch" == some "text/n3" &&
  hdr container "accept-post" == some "text/turtle" &&
  hdr container "accept-put" == some "text/turtle" &&
  hdr resource "accept-patch" == some "text/n3" &&
  hdr resource "accept-put" == some "text/turtle"

#guard solidGuardAllowHeader
#guard solidGuardAcceptHeaders

/-! ## §5.3 — writing resources -/

/-- "Servers MUST create intermediate containers and include corresponding
containment triples in container representations derived from the URI path
component of PUT and PATCH requests." -/
def solidGuardIntermediateContainers : Bool :=
  let (_, st) := run cfg (req "PUT" "/a/b/c/d" turtle "x") emptyStorage
  (memLookup st "/a/").isSome && (memLookup st "/a/b/").isSome &&
  (memLookup st "/a/b/c/").isSome &&
  (containmentTriples MemStore base st "/a/b/").length == 1

/-- "Servers MUST allow creation of new resources by a POST request to a URI
path ending with /. Servers MUST create resources with URI paths ending with
/{id} in container /." -/
def solidGuardPostAssignsName : Bool :=
  let (resp, st) := run cfg (req "POST" "/alice/" turtle "x") populated
  match hdr resp "location" with
  | none => false
  | some loc =>
      resp.status == 201 && loc.startsWith "/alice/" &&
      (memLookup st loc).isSome && LWS.contains "/alice/" loc

/-- "When a POST method request targets a resource without an existing
representation, the server MUST respond with the 404 status code." -/
def solidGuardPostMissingTarget404 : Bool :=
  (run cfg (req "POST" "/nowhere/" turtle "x") populated).1.status == 404

/-- "Servers MUST NOT allow HTTP PUT or PATCH on a container to update its
containment triples; if the server receives such a request, it MUST respond
with a 409 status code." -/
def solidGuardPutRefusesContainmentEdit409 : Bool :=
  let bodyWithContainment :=
    "<http://example.org/alice/> <http://www.w3.org/ns/ldp#contains> <http://example.org/alice/x> ."
  (run cfg (req "PUT" "/alice/" turtle bodyWithContainment) populated).1.status == 409 &&
  (run cfg (req "PATCH" "/alice/" n3 "") populated).1.status == 409

/-- "When a PUT or PATCH request targets an auxiliary resource, the server
MUST create or update it." -/
def solidGuardPutAuxiliary : Bool :=
  let (resp, st) := run cfg (req "PUT" "/alice/card.meta" turtle "x") populated
  resp.status == 201 && (memLookup st "/alice/card.meta").isSome

#guard solidGuardIntermediateContainers
#guard solidGuardPostAssignsName
#guard solidGuardPostMissingTarget404
#guard solidGuardPutRefusesContainmentEdit409
#guard solidGuardPutAuxiliary

/-! ## §5.3.1 — N3 Patch -/

/-- The specification's own example patch document. -/
def renamePatch : String :=
"@prefix solid: <http://www.w3.org/ns/solid/terms#>.
@prefix ex: <http://www.example.org/terms#>.
_:rename a solid:InsertDeletePatch;
  solid:where   { ?person ex:familyName \"Garcia\". };
  solid:inserts { ?person ex:givenName \"Alex\". };
  solid:deletes { ?person ex:givenName \"Claudia\". }."

def claudiaTurtle : String :=
"@prefix ex: <http://www.example.org/terms#>.
<http://example.org/p/claudia> ex:familyName \"Garcia\"; ex:givenName \"Claudia\"."

/-- "Servers MUST accept a PATCH request with an N3 Patch body when the
target of the request is an RDF document." The specification's own example,
end to end: Claudia Garcia becomes Alex Garcia. -/
def solidGuardN3PatchApplies : Bool :=
  let (_, st) := run cfg (req "PUT" "/p/claudia" turtle claudiaTurtle) emptyStorage
  let (resp, st') := run cfg (req "PATCH" "/p/claudia" n3 renamePatch) st
  match memLookup st' "/p/claudia" with
  | none => false
  | some e =>
      resp.status == 204 &&
      (e.body.splitOn "Alex").length > 1 && (e.body.splitOn "Claudia").length == 1 &&
      (e.body.splitOn "Garcia").length > 1

/-- "Servers MUST indicate support of N3 Patch by listing text/n3 as a field
value of the Accept-Patch header field." -/
def solidGuardN3PatchAcceptPatch : Bool :=
  hdr (run cfg (req "GET" "/alice/card") populated).1 "accept-patch" == some "text/n3"

/-- "The ?insertions and ?deletions formulae MUST NOT contain blank nodes."
"Servers MUST respond with a 422 status code if a patch document does not
satisfy all of the above constraints." -/
def solidGuardN3PatchBlankNode422 : Bool :=
  let doc :=
"@prefix solid: <http://www.w3.org/ns/solid/terms#>.
@prefix ex: <http://www.example.org/terms#>.
_:p a solid:InsertDeletePatch;
  solid:where   { ?s ex:familyName \"Garcia\". };
  solid:inserts { _:b ex:givenName \"Alex\". }."
  (run cfg (req "PATCH" "/p/claudia" n3 doc) populated).1.status == 422

/-- "If no such mapping exists […] the server MUST respond with a 409 status
code." -/
def solidGuardN3PatchNoMatch409 : Bool :=
  let (_, st) := run cfg (req "PUT" "/p/claudia" turtle claudiaTurtle) emptyStorage
  let doc :=
"@prefix solid: <http://www.w3.org/ns/solid/terms#>.
@prefix ex: <http://www.example.org/terms#>.
_:p a solid:InsertDeletePatch;
  solid:where   { ?s ex:familyName \"Nobody\". };
  solid:inserts { ?s ex:givenName \"Alex\". }."
  (run cfg (req "PATCH" "/p/claudia" n3 doc) st).1.status == 409

/-- "or if multiple mappings exist, the server MUST respond with a 409
status code." -/
def solidGuardN3PatchMultipleMatch409 : Bool :=
  let two :=
"@prefix ex: <http://www.example.org/terms#>.
<http://example.org/p/a> ex:familyName \"Garcia\".
<http://example.org/p/b> ex:familyName \"Garcia\"."
  let (_, st) := run cfg (req "PUT" "/p/two" turtle two) emptyStorage
  let doc :=
"@prefix solid: <http://www.w3.org/ns/solid/terms#>.
@prefix ex: <http://www.example.org/terms#>.
_:p a solid:InsertDeletePatch;
  solid:where   { ?s ex:familyName \"Garcia\". };
  solid:inserts { ?s ex:givenName \"Alex\". }."
  (run cfg (req "PATCH" "/p/two" n3 doc) st).1.status == 409

/-- "If the set of triples resulting from ?deletions is non-empty and the
dataset does not contain all of these triples, the server MUST respond with
a 409 status code." -/
def solidGuardN3PatchDeletionsAbsent409 : Bool :=
  let (_, st) := run cfg (req "PUT" "/p/claudia" turtle claudiaTurtle) emptyStorage
  let doc :=
"@prefix solid: <http://www.w3.org/ns/solid/terms#>.
@prefix ex: <http://www.example.org/terms#>.
_:p a solid:InsertDeletePatch;
  solid:where   { ?s ex:familyName \"Garcia\". };
  solid:deletes { ?s ex:givenName \"Nobody\". }."
  (run cfg (req "PATCH" "/p/claudia" n3 doc) st).1.status == 409

/-- "When ?conditions is non-empty, servers MUST treat the request as a Read
operation. When ?insertions is non-empty, servers MUST (also) treat the
request as an Append operation. When ?deletions is non-empty, servers MUST
treat the request as a Read and Write operation." -/
def solidGuardN3PatchOperations : Bool :=
  match parseN3Patch renamePatch with
  | .error _ => false
  | .ok p =>
      let ops := LWS.patchOperations p
      ops.read && ops.append && ops.write

/-- A PATCH body that is not `text/n3` is refused. -/
def solidGuardPatchMediaType415 : Bool :=
  (run cfg (req "PATCH" "/alice/card" turtle "x") populated).1.status == 415

#guard solidGuardN3PatchApplies
#guard solidGuardN3PatchAcceptPatch
#guard solidGuardN3PatchBlankNode422
#guard solidGuardN3PatchNoMatch409
#guard solidGuardN3PatchMultipleMatch409
#guard solidGuardN3PatchDeletionsAbsent409
#guard solidGuardN3PatchOperations
#guard solidGuardPatchMediaType415

/-! ## §5.4 — deleting resources -/

/-- "When a DELETE request targets storage's root container or its
associated ACL resource, the server MUST respond with the 405 status code.
Server MUST exclude the DELETE method in the field value of the Allow header
field, in response to requests to these resources." -/
def solidGuardDeleteRootRefused405 : Bool :=
  let (resp, _) := run cfg (req "DELETE" "/") populated
  let (aclResp, _) := run cfg (req "DELETE" "/.acl") populated
  resp.status == 405 && aclResp.status == 405 &&
  !has resp "allow" "DELETE"

/-- "When a contained resource is deleted, the server MUST also remove the
corresponding containment triple." -/
def solidGuardDeleteRemovesContainment : Bool :=
  let before := (containmentTriples MemStore base populated "/alice/").length
  let (_, st) := run cfg (req "DELETE" "/alice/card") populated
  (containmentTriples MemStore base st "/alice/").length + 1 == before

/-- "When a contained resource is deleted, the server MUST also delete the
associated auxiliary resources." -/
def solidGuardDeleteRemovesAuxiliaries : Bool :=
  let (_, st) := runAll cfg
    [ req "PUT" "/alice/card.acl" turtle "x"
    , req "PUT" "/alice/card.meta" turtle "y"
    , req "DELETE" "/alice/card" ] populated
  (memLookup st "/alice/card").isNone &&
  (memLookup st "/alice/card.acl").isNone &&
  (memLookup st "/alice/card.meta").isNone

/-- "When a DELETE request targets a container, the server MUST delete the
container if it contains no resources. If the container contains resources,
the server MUST respond with the 409 status code." -/
def solidGuardDeleteNonEmptyContainer409 : Bool :=
  (run cfg (req "DELETE" "/alice/notes/") populated).1.status == 409 &&
  (runAll cfg [ req "DELETE" "/alice/notes/one"
              , req "DELETE" "/alice/notes/" ] populated).1.map (·.status) == [204, 204]

#guard solidGuardDeleteRootRefused405
#guard solidGuardDeleteRemovesContainment
#guard solidGuardDeleteRemovesAuxiliaries
#guard solidGuardDeleteNonEmptyContainer409

/-! ## §5 and §2.1 — method and content-type rules -/

/-- "Servers MUST respond with the 405 status code to requests using HTTP
methods that are not supported by the target resource." -/
def solidGuardUnsupportedMethod405 : Bool :=
  (run cfg (req "TRACE" "/alice/card") populated).1.status == 405 &&
  (run cfg (req "POST" "/alice/card" turtle "x") populated).1.status == 405

/-- "Server MUST reject PUT, POST, and PATCH requests that contain content
but lack the Content-Type header field, with a status code of 400." -/
def solidGuardContentTypeRequired400 : Bool :=
  (run cfg (req "PUT" "/alice/x" [] "body") populated).1.status == 400 &&
  (run cfg (req "POST" "/alice/" [] "body") populated).1.status == 400 &&
  (run cfg (req "PATCH" "/alice/card" [] "body") populated).1.status == 400

#guard solidGuardUnsupportedMethod405
#guard solidGuardContentTypeRequired400

/-! ## §8.1 — CORS -/

/-- "The server MUST set the Access-Control-Allow-Origin header field value
to the valid Origin header field value from the request and list Origin in
the Vary header field value." -/
def solidGuardCorsHeaders : Bool :=
  let (resp, _) := run cfg (req "GET" "/alice/card" [("origin", "https://app.example")]) populated
  hdr resp "access-control-allow-origin" == some "https://app.example" &&
  hdr resp "vary" == some "Origin" &&
  has resp "access-control-expose-headers" "WAC-Allow" &&
  has resp "access-control-expose-headers" "Link"

/-- "A server MUST also support the HTTP OPTIONS method such that it can
respond appropriately to CORS preflight requests." -/
def solidGuardCorsPreflight : Bool :=
  let (resp, _) := run cfg
    (req "OPTIONS" "/alice/card"
      [("origin", "https://app.example"), ("access-control-request-method", "PATCH")])
    populated
  resp.status == 204 &&
  has resp "access-control-allow-methods" "PATCH" &&
  has resp "access-control-allow-headers" "Accept"

#guard solidGuardCorsHeaders
#guard solidGuardCorsPreflight

/-! ## Web Access Control -/

def aclDoc : String :=
"@prefix acl: <http://www.w3.org/ns/auth/acl#>.
@prefix foaf: <http://xmlns.com/foaf/0.1/>.
@prefix vcard: <http://www.w3.org/2006/vcard/ns#>.
<http://example.org/acl#owner> a acl:Authorization;
  acl:agent <http://example.org/alice/card#me>;
  acl:accessTo <http://example.org/alice/card>;
  acl:mode acl:Read, acl:Write, acl:Control.
<http://example.org/acl#team> a acl:Authorization;
  acl:default <http://example.org/alice/>;
  acl:agentClass acl:AuthenticatedAgent;
  acl:mode acl:Write.
<http://example.org/acl#group> a acl:Authorization;
  acl:accessTo <http://example.org/alice/card>;
  acl:agentGroup <http://example.org/groups#friends>;
  acl:mode acl:Read.
<http://example.org/groups#friends> vcard:hasMember <http://example.org/bob/card#me>."

def aclGraph : List Triple := aclGraphOf aclDoc

def alice : Requester := { webId := some "http://example.org/alice/card#me" }
def bob : Requester := { webId := some "http://example.org/bob/card#me" }
def anon : Requester := {}

def cardIri : String := "http://example.org/alice/card"
def aliceContainer : String := "http://example.org/alice/"

/-- WAC §5.3.3, first example: "Match an Authorization with a specific
resource, agent and access mode." -/
def solidGuardWacAccessToAgentMode : Bool :=
  decideAccess aclGraph cardIri cardIri false alice .read &&
  decideAccess aclGraph cardIri cardIri false alice .write &&
  decideAccess aclGraph cardIri cardIri false alice .control

/-- WAC §5.3.3, second example: "Match an Authorization with a specific
container resource, agent class membership and access mode", including a
required mode that is a SUBCLASS of the granted one — `acl:Append` is a
subclass of `acl:Write`. -/
def solidGuardWacDefaultAgentClassSuperclassMode : Bool :=
  decideAccess aclGraph cardIri aliceContainer true bob .write &&
  decideAccess aclGraph cardIri aliceContainer true bob .append &&
  !decideAccess aclGraph cardIri aliceContainer true anon .write

/-- WAC §5.3.3, third example: "Match an Authorization with a specific
resource, agent with any group membership, and specific access mode." -/
def solidGuardWacAgentGroup : Bool :=
  decideAccess aclGraph cardIri cardIri false bob .read

/-- "Access is granted when conforming Authorizations are matched, otherwise
access is denied." Bob has no `acl:Control` on the card. -/
def solidGuardWacDenies : Bool :=
  !decideAccess aclGraph cardIri cardIri false bob .control &&
  !decideAccess aclGraph cardIri cardIri false anon .read

/-- "Servers MUST advertise client's access privileges on a resource by
including the WAC-Allow HTTP header in the response of HTTP GET and HEAD
requests." -/
def solidGuardWacAllowHeader : Bool :=
  let st := (run cfg (req "PUT" "/alice/card.acl" turtle aclDoc) populated).2
  let cfgAlice : ServerConfig :=
    { cfg with lws := { cfg.lws with agent := some "http://example.org/alice/card#me" } }
  let (resp, _) := run cfgAlice (req "GET" "/alice/card") st
  -- `append` is listed because acl:Append is a subclass of acl:Write, so an
  -- agent granted acl:Write may append.
  hdr resp "wac-allow" == some "user=\"read write append control\",public=\"\""

/-- With enforcement on, an unauthenticated agent is refused with 401 and an
authenticated one without the mode with 403. -/
def solidGuardWacEnforced : Bool :=
  let st := (run cfg (req "PUT" "/alice/card.acl" turtle aclDoc) populated).2
  let strict : ServerConfig := { cfg with enforceWac := true }
  let strictBob : ServerConfig :=
    { strict with lws := { strict.lws with agent := some "http://example.org/bob/card#me" } }
  (run strict (req "GET" "/alice/card") st).1.status == 401 &&
  (run strictBob (req "GET" "/alice/card.acl") st).1.status == 403 &&
  (run strictBob (req "GET" "/alice/card") st).1.status == 200

/-! ## Solid-OIDC (Solid Protocol §10.1, RFC 9449)

`L4Factoidal.Solid.Server.Auth` decides whether a request carries a valid
Solid-OIDC identity. The SIGNATURE part of that decision needs HACL*, which
does not evaluate at build time, so this guard runs the decision with a
stub verifier: everything except the signature check is exercised here, and
the signature is exercised by the `solid-oidc` section of
`lake exe l4jose-probe` with real Ed25519 signatures.
-/

open L4Factoidal.JOSE in
/-- A key the guard treats as the identity provider's. -/
def oidcKey : L4Factoidal.JOSE.Jwk :=
  (parseJwkString? ("{\"kty\":\"OKP\",\"crv\":\"Ed25519\"," ++
    "\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\"}")).getD
    (.okp ByteArray.empty)

open L4Factoidal.JOSE in
def oidcJkt : String := thumbprint oidcKey

open L4Factoidal.JOSE in
private def joseToken (header payload : String) : String :=
  Base64Url.encodeUtf8 header ++ "." ++ Base64Url.encodeUtf8 payload ++ "." ++
  Base64Url.encode ⟨#[0x00]⟩

open L4Factoidal.JOSE in
private def oidcStub : Verifiers :=
  { es256 := fun _ _ _ => true, rs256 := fun _ _ _ _ => true, eddsa := fun _ _ _ => true }

open L4Factoidal.JOSE in
private def oidcAccessToken : String :=
  joseToken "{\"alg\":\"EdDSA\"}"
    ("{\"iss\":\"https://idp.example/\",\"sub\":\"https://alice.example/card#me\"," ++
     "\"webid\":\"https://alice.example/card#me\",\"aud\":\"https://storage.example/\"," ++
     "\"exp\":1700000600,\"iat\":1700000000,\"cnf\":{\"jkt\":\"" ++ oidcJkt ++ "\"}}")

open L4Factoidal.JOSE in
private def oidcProof : String :=
  joseToken ("{\"typ\":\"dpop+jwt\",\"alg\":\"EdDSA\",\"jwk\":{\"kty\":\"OKP\"," ++
      "\"crv\":\"Ed25519\",\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\"}}")
    ("{\"jti\":\"j-1\",\"htm\":\"GET\",\"htu\":\"https://storage.example/alice/card\"," ++
     "\"iat\":1700000000,\"ath\":\"" ++ athFor oidcAccessToken.toUTF8 ++ "\"}")

open L4Factoidal.JOSE in
private def oidcCfg : ServerConfig :=
  { lws := { baseIri := "https://storage.example/" },
    auth := { enforceAuth := true, idpKeys := [oidcKey],
              policy := { now := 1700000000, leeway := 60,
                          issuer := "https://idp.example/",
                          audience := "https://storage.example/" },
              proofPolicy := { now := 1700000000, iatWindow := 60,
                               jtiFresh := fun _ => true } } }

open L4Factoidal.JOSE in
private def oidcReq (headers : List (String × String)) : L4Factoidal.HTTP.Request :=
  { method := "GET", path := "/alice/card", queryStr := "", headers := headers }

/-- Solid Protocol §10.1: "Servers MUST conform to the Solid-OIDC
specification." A DPoP-bound access token yields the WebID it carries; a
bearer presentation of the same token, a missing proof, a token bound to
another key, an expired token and a token from another issuer are all
refused; and with `enforceAuth` off the decision is `disabled` so the
first-slice behaviour is unchanged. -/
def solidGuardSolidOidcDpop : Bool :=
  let good := oidcReq [("authorization", "DPoP " ++ oidcAccessToken), ("dpop", oidcProof)]
  (authenticate oidcStub oidcCfg good
     == .authenticated "https://alice.example/card#me" oidcJkt) &&
  (authenticate oidcStub oidcCfg (oidcReq [("authorization", "Bearer " ++ oidcAccessToken)])
     == .refused (.wrongScheme "Bearer")) &&
  (authenticate oidcStub oidcCfg (oidcReq [("authorization", "DPoP " ++ oidcAccessToken)])
     == .refused .missingProof) &&
  (authenticate oidcStub oidcCfg (oidcReq []) == .anonymous) &&
  (authenticate oidcStub { oidcCfg with auth := { oidcCfg.auth with idpKeys := [] } } good
     == .refused (.noTrustedKey [])) &&
  (authenticate oidcStub { oidcCfg with auth := { oidcCfg.auth with
      policy := { oidcCfg.auth.policy with now := 1700000700 } } } good
     == .refused (.claimsRefused .expired)) &&
  (authenticate oidcStub { oidcCfg with auth := { oidcCfg.auth with
      policy := { oidcCfg.auth.policy with issuer := "https://evil.example/" } } } good
     == .refused (.claimsRefused .issuerMismatch)) &&
  (authenticate oidcStub oidcCfg { good with path := "/bob/card" }
     == .refused (.proofRefused .htuMismatch)) &&
  (authenticate oidcStub { oidcCfg with auth := { oidcCfg.auth with
      proofPolicy := { oidcCfg.auth.proofPolicy with jtiFresh := fun _ => false } } } good
     == .refused (.proofRefused .jtiReplayed)) &&
  (authenticate oidcStub { oidcCfg with auth := { oidcCfg.auth with enforceAuth := false } } good
     == .disabled)

#guard solidGuardSolidOidcDpop

#guard solidGuardWacAccessToAgentMode
#guard solidGuardWacDefaultAgentClassSuperclassMode
#guard solidGuardWacAgentGroup
#guard solidGuardWacDenies
#guard solidGuardWacAllowHeader
#guard solidGuardWacEnforced

-- The method-to-mode mapping of WAC 5.3.1.
#guard requiredMode "GET" false == Mode.read
#guard requiredMode "POST" false == Mode.append
#guard requiredMode "DELETE" false == Mode.write
#guard requiredMode "GET" true == Mode.control

/-! ## §6 — Linked Data Notifications -/

/-- "A Solid server MUST conform to the LDN specification by implementing
the Receiver parts to receive notifications." -/
def solidGuardInboxAcceptsPost : Bool :=
  let st := (run cfg (req "PUT" "/inbox/" turtle "") populated).2
  let (ok, _) := run cfg (req "POST" "/inbox/" [("content-type", "application/ld+json")] "{}") st
  let (bad, _) := run cfg (req "POST" "/inbox/" [("content-type", "text/plain")] "hi") st
  ok.status == 201 && bad.status == 415

#guard solidGuardInboxAcceptsPost
#guard (inboxLink base).rel == "http://www.w3.org/ns/ldp#inbox"
#guard (inboxLink base).target == "http://example.org/inbox/"

/-! ## The client -/

/-- §4.3: "Clients can discover auxiliary resources associated with a
subject resource by making an HTTP HEAD or GET request on the target URL,
and checking the HTTP Link header field with the rel parameter." -/
def solidGuardClientReadsLinks : Bool :=
  let (resp, _) := run cfg (req "GET" "/") populated
  let facts := resourceFacts resp
  facts.isStorage && facts.acl == some "/.acl" &&
  facts.describedBy == some "/.meta" &&
  facts.owner == some "http://example.org/alice/card#me" &&
  facts.lastModified.isSome

/-- §4.1: "Clients can determine the storage of a resource by moving up the
URI path hierarchy". -/
def solidGuardClientStorageWalk : Bool :=
  storageWalk "/alice/notes/one" == ["/alice/notes/", "/alice/", "/"] &&
  walkStep "/alice/notes/one" [] == WalkStep.ask "/alice/notes/" &&
  walkStep "/alice/notes/one" [("/alice/notes/", false), ("/alice/", false)]
    == WalkStep.ask "/" &&
  walkStep "/alice/notes/one" [("/alice/notes/", false), ("/", true)]
    == WalkStep.found "/"

/-- WAC §6.1's client parsing rule: unrecognised access modes are processed
as if absent. -/
def solidGuardClientWacAllowParsing : Bool :=
  parseWacAllow "user=\"read write frobnicate\",public=\"read\"" ==
    [("user", ["read", "write"]), ("public", ["read"])] &&
  parseWacAllow "nonsense" == []

/-- §9.1: "When a WebID is dereferenced, server provides a representation of
the WebID Profile in an RDF document." -/
def solidGuardClientProfile : Bool :=
  let doc :=
"@prefix pim: <http://www.w3.org/ns/pim/space#>.
@prefix foaf: <http://xmlns.com/foaf/0.1/>.
@prefix ldp: <http://www.w3.org/ns/ldp#>.
<http://example.org/alice/card#me> foaf:name \"Alice\";
  pim:storage <http://example.org/>;
  ldp:inbox <http://example.org/inbox/>."
  let p := readProfile "http://example.org/alice/card#me" base doc
  p.names == ["Alice"] && p.storages == ["http://example.org/"] &&
  p.inbox == some "http://example.org/inbox/"

#guard solidGuardClientReadsLinks
#guard solidGuardClientStorageWalk
#guard solidGuardClientWacAllowParsing
#guard solidGuardClientProfile

/-! ## The registry's own arithmetic -/

#guard (Conformance.registry.map (·.id)).eraseDups.length == Conformance.registry.length

end L4Factoidal.Solid.Tests
