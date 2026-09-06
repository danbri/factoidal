/-
L4Factoidal.Solid.Server.Methods — the HTTP methods of the Solid Protocol,
as ONE total function that REFINES `L4Factoidal.LWS.Operations.step`.

Wraps: `LWS.Operations.step`, which decides create, read, update and delete
and generates `Last-Modified`, `Allow` and the `Accept-*` fields.
Adds, in order of application:

1. the Web Access Control decision (`WAC.lean`) and its 401/403;
2. the slash-semantics redirect of §3.1, taken AFTER the access decision,
   which is what "Servers MUST authorize prior to this optional redirect"
   requires;
3. the container representation of §4.2 — a GET on a container answers its
   containment triples, not the bytes someone PUT;
4. the 409 of §5.3 for a PUT or PATCH that would edit containment triples;
5. the N3 Patch of §5.3.1 with its 415 and 422;
6. the auxiliary-resource deletion of §4.3 on DELETE;
7. the `WAC-Allow` field of Web Access Control §5.3.4 on GET and HEAD;
8. the CORS fields of §8.1.

Source: https://solidproject.org/TR/protocol, verbatim:

§5: "Servers MUST respond with the 405 status code to requests using HTTP
methods that are not supported by the target resource."

§2.1: "When a client does not provide valid credentials when requesting a
resource that requires it (see WebID), servers MUST send a response with a
401 status code (unless 404 is preferred for security reasons)."
"Server MUST reject PUT, POST, and PATCH requests that contain content but
lack the Content-Type header field, with a status code of 400."

§5.2: "Servers MUST support the HTTP GET, HEAD and OPTIONS methods for
clients to read resources or to determine communication options."
"Servers MUST indicate the HTTP methods supported by the target resource by
generating an Allow header field in successful responses."
"When responding to authorized requests, servers MUST indicate supported
media types in the HTTP Accept-Patch, Accept-Post and Accept-Put response
header fields."

§5.3: "Servers MUST support the HTTP PUT, POST and PATCH methods."
"Servers MUST create intermediate containers and include corresponding
containment triples in container representations derived from the URI path
component of PUT and PATCH requests."
"Servers MUST allow creation of new resources by a POST request to a URI
path ending with /. Servers MUST create resources with URI paths ending with
/{id} in container /."
"When a POST method request targets a resource without an existing
representation, the server MUST respond with the 404 status code."
"When a PUT or PATCH request targets an auxiliary resource, the server MUST
create or update it."
"Servers MUST NOT allow HTTP PUT or PATCH on a container to update its
containment triples; if the server receives such a request, it MUST respond
with a 409 status code."

§5.4: "Servers MUST support the HTTP DELETE method."
"When a DELETE request targets storage's root container or its associated
ACL resource, the server MUST respond with the 405 status code."
"When a contained resource is deleted, the server MUST also remove the
corresponding containment triple."
"When a contained resource is deleted, the server MUST also delete the
associated auxiliary resources."
"When a DELETE request targets a container, the server MUST delete the
container if it contains no resources. If the container contains resources,
the server MUST respond with the 409 status code."

§5.5: "When a server creates an RDF source on HTTP PUT, POST, or PATCH
requests, the server MUST satisfy GET requests on this resource when the
Accept header field requests text/turtle or application/ld+json."

## Access control in the first slice

`ServerConfig.enforceWac` is `false` by default. With it false the access
decision is COMPUTED and reported in `WAC-Allow`, but never refuses a
request: the storage serves public resources and unauthenticated writes,
which is what the design record says the first slice does. With it true the
decision is enforced, and a target with no effective ACL resource is denied,
as Web Access Control §5.3 requires. The registry row states the condition
rather than leaving the default unsaid.
-/
import L4Factoidal.Solid.Server.WAC
import L4Factoidal.Solid.Server.Auxiliary
import L4Factoidal.Solid.Server.N3Patch
import L4Factoidal.Solid.Server.Cors
import L4Factoidal.Solid.Server.Ldn
import L4Factoidal.Syntax.TurtleSerialize

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.LWS
open L4Factoidal.Syntax
open L4Factoidal.HTTP (Request Response)

/-- The server's configuration: the LWS storage configuration, plus whether
the access decision is enforced. -/
structure ServerConfig where
  lws : LWS.Config := {}
  enforceWac : Bool := false
deriving Inhabited

/-- Parse an ACL resource body. Web Access Control §3.2: "Servers MUST
accept an HTTP GET and HEAD request targeting an ACL resource when the value
of the Accept header requests a representation in text/turtle." A body that
does not parse holds no Authorization, so it grants nothing. -/
def aclGraphOf (body : String) : List Triple :=
  match parseTurtle body none .rdf11 with
  | .ok g    => g
  | .error _ => []

/-- Parse a request body or a stored representation as Turtle, resolving
relative references against `base`.

RFC 3986 §5.1.3: the base IRI of a retrieved representation is the URI of
the resource it was retrieved from. For a PUT or a PATCH that is the request
target, so `<>` in the body denotes the target and `<#it>` a fragment of it.
Parsing with no base makes both a parse error, which is how a body that
edits a containment triple slipped past the §5.3 refusal. -/
def graphOf (base : Option String) (body : String) : List Triple :=
  match parseTurtle body base .rdf11 with
  | .ok g    => g
  | .error _ => []

/-- Does this path name an ACL resource? Access to one needs `acl:Control`
rather than the mode the method would otherwise need. -/
def targetsAcl (p : String) : Bool := p.endsWith ".acl"

/-! ## Reading a request -/

def hasContent (r : Request) : Bool := r.body != ""

def contentTypeOf (r : Request) : Option String :=
  (r.header? "content-type").map (fun ct => (ct.splitOn ";").headD ct)

/-- The requester of a request. The WebID comes from the handle
configuration, which the host fills in after IT verified the credential. -/
def requesterOf (cfg : ServerConfig) (r : Request) : Requester :=
  { webId := cfg.lws.agent, origin := r.header? "origin" }

/-! ## Refusals -/

def refuse (status : Nat) (msg : String) : Response :=
  ⟨status, [("content-type", "text/plain")], msg⟩

/-! ## The step function -/

variable {σ : Type}

/-- Does this body, read as Turtle, carry a containment triple? §5.3:
"Servers MUST NOT allow HTTP PUT or PATCH on a container to update its
containment triples". -/
def bodyEditsContainment (baseIri target body : String) : Bool :=
  (graphOf (some (iriOfPath baseIri target)) body).any (fun t => t.p == ldpContains)

/-- One Solid request. Total, like the LWS `step` it refines. -/
def step (S : Store σ) (cfg : ServerConfig) (r : Request) (st : σ) :
    Response × σ :=
  let target := r.path
  let who := requesterOf cfg r
  let mode := requiredMode r.method (targetsAcl target)
  let subject := authorizationSubject target
  let granted :=
    !cfg.enforceWac ||
    allowed S aclGraphOf cfg.lws.baseIri st subject who mode
  if !granted then
    let resp := match who.webId with
      | none   => refuse 401 "Unauthorized"
      | some _ => refuse 403 "Forbidden"
    (withCors r resp, st)
  else
    match slashRedirect? S st target with
    | some other => (withCors r ⟨301, [("location", other)], ""⟩, st)
    | none =>
        let (resp, st') := solidStep S cfg r st target
        let resp := withInboxLink cfg r.path resp
        let resp := if r.method == "GET" || r.method == "HEAD" then
            { resp with headers := resp.headers ++
                [("wac-allow", wacAllowFor S cfg st target who)] }
          else resp
        (withCors r resp, st')
where
  /-- Add the LDN inbox link to the storage root's `Link` field. RFC 8288
  allows several link-values in one field, comma separated, which is what
  `LWS.renderLinks` already builds. -/
  withInboxLink (cfg : ServerConfig) (target : String) (resp : Response) : Response :=
    if target != rootPath then resp
    else
      { resp with headers := resp.headers.map (fun (k, v) =>
          if k == "link" then
            (k, if v == "" then renderLinks (inboxLinks cfg.lws.baseIri true)
                else v ++ ", " ++ renderLinks (inboxLinks cfg.lws.baseIri true))
          else (k, v)) }
  /-- The `WAC-Allow` field value for a target. Computed whether or not the
  decision is enforced, so a client always learns its privileges. -/
  wacAllowFor (S : Store σ) (cfg : ServerConfig) (st : σ) (target : String)
      (who : Requester) : String :=
    match effectiveAcl S st target with
    | none => "user=\"\",public=\"\""
    | some (owner, inherited) =>
        match S.lookup st (aclPathOf owner) with
        | none => "user=\"\",public=\"\""
        | some e =>
            wacAllow (aclGraphOf e.body) (iriOfPath cfg.lws.baseIri target)
                     (iriOfPath cfg.lws.baseIri owner) inherited who
  /-- Everything after the access decision and the redirect. -/
  solidStep (S : Store σ) (cfg : ServerConfig) (r : Request) (st : σ)
      (target : String) : Response × σ :=
    match r.method with
    | "GET" | "HEAD" =>
        match S.lookup st target with
        | some e =>
            if e.kind.isContainer then
              let g := containerGraph S cfg.lws.baseIri st target
              let (base, st') := LWS.step S cfg.lws r st
              ({ base with
                 body := if r.method == "HEAD" then "" else turtleOfGraphAuto g,
                 headers := base.headers.map (fun (k, v) =>
                   if k == "content-type" then (k, "text/turtle") else (k, v)) }, st')
            else LWS.step S cfg.lws r st
        | none => LWS.step S cfg.lws r st
    | "PUT" =>
        if hasContent r && (r.header? "content-type").isNone then
          (refuse 400 "PUT with content requires a Content-Type header field", st)
        else if pathIsContainer target &&
                bodyEditsContainment cfg.lws.baseIri target r.body then
          (refuse 409 "a container's containment triples cannot be edited", st)
        else LWS.step S cfg.lws r st
    | "POST" =>
        if hasContent r && (r.header? "content-type").isNone then
          (refuse 400 "POST with content requires a Content-Type header field", st)
        else if isNotificationPost r && !acceptableNotification r then
          (refuse 415 "the inbox accepts application/ld+json, text/turtle or application/n-triples", st)
        else LWS.step S cfg.lws r st
    | "PATCH" =>
        if hasContent r && (r.header? "content-type").isNone then
          (refuse 400 "PATCH with content requires a Content-Type header field", st)
        else if contentTypeOf r != some "text/n3" then
          (refuse 415 "PATCH accepts text/n3 (N3 Patch)", st)
        else if pathIsContainer target then
          (refuse 409 "a container's containment triples cannot be edited", st)
        else
          let existing := S.lookup st target
          let targetIri := iriOfPath cfg.lws.baseIri target
          let current := match existing with
            | some e => graphOf (some targetIri) e.body
            | none   => []
          match applyN3Patch r.body current (some targetIri) with
          | .error e => (refuse e.status e.message, st)
          | .ok g' =>
              let st1 := ensureAncestors S (ancestors target) st
              let e : Entry := { path := target, kind := .dataResource,
                                 contentType := "text/turtle",
                                 body := turtleOfGraphAuto g', mtime := S.now st1 }
              let st2 := touchContainer S (S.tick (S.put st1 e)) target
              match existing with
              | none   => (⟨201, [("location", target),
                                  ("last-modified", httpDate e.mtime)], ""⟩, st2)
              | some _ => (⟨204, [("last-modified", httpDate e.mtime)], ""⟩, st2)
    | "DELETE" =>
        if target == rootPath || target == aclPathOf rootPath then
          (⟨405, [("allow", String.intercalate ", "
                    (allowFor .storageRoot (target == rootPath)))], ""⟩, st)
        else
          let (resp, st') := LWS.step S cfg.lws r st
          if resp.status == 204 then
            (resp, (auxiliaryPaths target).foldl (fun s a => S.remove s a) st')
          else (resp, st')
    | _ => LWS.step S cfg.lws r st

end L4Factoidal.Solid.Server
