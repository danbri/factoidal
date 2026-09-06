/-
L4Factoidal.Solid.Server.WAC — the Web Access Control decision as a pure
function from an ACL graph, an agent and an access mode to allow or deny.

Wraps: nothing of `L4Factoidal.LWS` — the LWS draft's `Authorization`
section is an empty heading, so this whole layer is Solid's addition.
Adds: the effective-ACL walk, the Authorization conformance test, the
authorization match, and the `WAC-Allow` header field value.

Source: https://solidproject.org/TR/wac (Web Access Control, read
2026-09-06). Verbatim:

§4.2 Access Modes:
  "acl:Read — Allows access to a class of read operations on a resource,
  e.g., to view the contents of a resource on HTTP GET requests."
  "acl:Write — Allows access to a class of write operations on a resource,
  e.g., to create, delete or modify resources on HTTP PUT, POST, PATCH,
  DELETE requests."
  "acl:Append — Allows access to a class of append operations on a resource,
  e.g., to add information, but not remove, information on HTTP POST, PATCH
  requests."
  "acl:Control — Allows access to a class of read and write operations on an
  ACL resource associated with a resource."
  "acl:Append is a subclass of acl:Write."

§4.1 Access Objects:
  "The acl:accessTo predicate denotes the resource to which access is being
  granted."
  "The acl:default predicate denotes the container resource whose
  Authorization can be applied to a resource lower in the collection
  hierarchy."

§4.3 Access Subjects:
  "The acl:agent predicate denotes an agent being given the access
  permission."
  "foaf:Agent — Allows access to any agent, i.e., the public."
  "acl:AuthenticatedAgent — Allows access to any authenticated agent."
  "The acl:agentGroup predicate denotes a group of agents being given the
  access permission. The object of an acl:agentGroup statement is an
  instance of vcard:Group, where the members of the group are specified with
  the vcard:hasMember predicate."

§5.1 Effective ACL Resource Algorithm:
  "Let resource be the resource. Let aclResource be the ACL resource of
  resource. If resource has an associated aclResource with a representation,
  return aclResource. Otherwise, repeat the steps using the container
  resource of resource."

§5.2 Authorization Conformance:
  "An applicable Authorization has the following properties: At least one
  rdf:type property whose object is acl:Authorization. At least one
  acl:accessTo or acl:default property value. At least one acl:mode property
  value. At least one acl:agent, acl:agentGroup, acl:agentClass or
  acl:origin property value."

§5.3 Authorization Evaluation:
  "Access is granted when conforming Authorizations are matched, otherwise
  access is denied."

§5.3.4 Access Privileges:
  "Servers MUST advertise client's access privileges on a resource by
  including the WAC-Allow HTTP header in the response of HTTP GET and HEAD
  requests."

The three worked ASK queries of §5.3.3 are the `#guard`s in
`L4Factoidal.Solid.Tests`: one match on `acl:accessTo` with `acl:agent`,
one on `acl:default` with `acl:agentClass` and a superclass mode, and one on
`acl:agentGroup` through `vcard:hasMember`.

`acl:origin` is read into the model but the origin condition of §5.3.2 is
not decided here: it needs the request's `Origin` header field, which
`Cors.lean` handles, and the combination is the open registry row
`solid-wac-06`.
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.RDF.Graph
import L4Factoidal.Solid.Server.Containment

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.LWS

/-! ## Vocabulary -/

def aclNs : String := "http://www.w3.org/ns/auth/acl#"
def aclAuthorization : String := aclNs ++ "Authorization"
def aclAccessTo : WfIri := ⟨"http://www.w3.org/ns/auth/acl#accessTo", by rfl⟩
def aclDefault : WfIri := ⟨"http://www.w3.org/ns/auth/acl#default", by rfl⟩
def aclAgent : WfIri := ⟨"http://www.w3.org/ns/auth/acl#agent", by rfl⟩
def aclAgentClass : WfIri := ⟨"http://www.w3.org/ns/auth/acl#agentClass", by rfl⟩
def aclAgentGroup : WfIri := ⟨"http://www.w3.org/ns/auth/acl#agentGroup", by rfl⟩
def aclOrigin : WfIri := ⟨"http://www.w3.org/ns/auth/acl#origin", by rfl⟩
def aclMode : WfIri := ⟨"http://www.w3.org/ns/auth/acl#mode", by rfl⟩
def foafAgent : String := "http://xmlns.com/foaf/0.1/Agent"
def aclAuthenticatedAgent : String := "http://www.w3.org/ns/auth/acl#AuthenticatedAgent"
def vcardHasMember : WfIri := ⟨"http://www.w3.org/2006/vcard/ns#hasMember", by rfl⟩

/-! ## Access modes -/

/-- The four access modes of §4.2. -/
inductive Mode where
  | read | write | append | control
deriving DecidableEq, Repr, Inhabited

def Mode.iri : Mode → String
  | .read => aclNs ++ "Read"
  | .write => aclNs ++ "Write"
  | .append => aclNs ++ "Append"
  | .control => aclNs ++ "Control"

def Mode.name : Mode → String
  | .read => "read" | .write => "write" | .append => "append" | .control => "control"

def Mode.ofIri? (s : String) : Option Mode :=
  if s == Mode.read.iri then some .read
  else if s == Mode.write.iri then some .write
  else if s == Mode.append.iri then some .append
  else if s == Mode.control.iri then some .control
  else none

/-- Does a granted mode satisfy a required one?

§4.2: "acl:Append is a subclass of acl:Write", and §5.3.3's second example
matches "Authorizations that use a superclass of the required access mode".
An agent granted `acl:Write` may therefore append; an agent granted
`acl:Append` may not write. -/
def Mode.satisfies (granted required : Mode) : Bool :=
  granted == required || (granted == .write && required == .append)

/-! ## Reading an ACL graph -/

/-- The objects of `s p ?o` in `g`, as IRI strings. -/
def objectIris (g : List Triple) (s : Subject) (p : WfIri) : List String :=
  g.filterMap (fun t =>
    if Subject.eqb t.s s && t.p == p then
      match t.o with
      | .iri i => some i.val
      | _ => none
    else none)

/-- Every subject that the graph types as an `acl:Authorization`. §5.2: "At
least one rdf:type property whose object is acl:Authorization." -/
def authorizations (g : List Triple) : List Subject :=
  g.filterMap (fun t =>
    if t.p == rdfType then
      match t.o with
      | .iri i => if i.val == aclAuthorization then some t.s else none
      | _ => none
    else none)

/-- Is this subject an APPLICABLE Authorization? §5.2 lists four properties,
all of which must be present. An Authorization that is not applicable "has
no effect on the outcome of the evaluation". -/
def isApplicable (g : List Triple) (a : Subject) : Bool :=
  let hasObject := !(objectIris g a aclAccessTo).isEmpty ||
                   !(objectIris g a aclDefault).isEmpty
  let hasMode := !(objectIris g a aclMode).isEmpty
  let hasSubject := !(objectIris g a aclAgent).isEmpty ||
                    !(objectIris g a aclAgentGroup).isEmpty ||
                    !(objectIris g a aclAgentClass).isEmpty ||
                    !(objectIris g a aclOrigin).isEmpty
  hasObject && hasMode && hasSubject

/-! ## The decision -/

/-- What the server knows about the requester when it decides. The WebID is
the one the HOST verified — this engine never validates a token. -/
structure Requester where
  /-- The WebID, or nothing for an unauthenticated request. -/
  webId : Option String := none
  /-- The `Origin` header field value, if the request carried one. -/
  origin : Option String := none
deriving Repr, Inhabited

/-- Does the Authorization `a` grant access to this requester? §4.3, the
four kinds of access subject. `acl:origin` is recorded as a subject here but
the origin CONDITION of §5.3.2 is not applied; see the module header. -/
def subjectMatches (g : List Triple) (a : Subject) (who : Requester) : Bool :=
  let classes := objectIris g a aclAgentClass
  let publicGranted := classes.contains foafAgent
  let authenticatedGranted := classes.contains aclAuthenticatedAgent
  match who.webId with
  | none => publicGranted
  | some me =>
      publicGranted || authenticatedGranted ||
      (objectIris g a aclAgent).contains me ||
      (objectIris g a aclAgentGroup).any (fun grp =>
        match mkIri? grp with
        | none => false
        | some gi =>
            g.any (fun t =>
              Subject.eqb t.s (.iri gi) && t.p == vcardHasMember &&
              (match t.o with | .iri i => i.val == me | _ => false)))

/-- Does the Authorization apply to this target? `acl:accessTo` names the
resource itself; `acl:default` names a container whose Authorizations are
inherited by resources below it, and is the one that applies when the
effective ACL resource was found on an ANCESTOR. -/
def objectMatches (g : List Triple) (a : Subject) (targetIri aclOwnerIri : String)
    (inherited : Bool) : Bool :=
  if inherited then (objectIris g a aclDefault).contains aclOwnerIri
  else (objectIris g a aclAccessTo).contains targetIri ||
       (objectIris g a aclDefault).contains aclOwnerIri

/-- Does the Authorization grant the required mode? -/
def modeMatches (g : List Triple) (a : Subject) (required : Mode) : Bool :=
  (objectIris g a aclMode).any (fun m =>
    match Mode.ofIri? m with
    | some granted => granted.satisfies required
    | none => false)      -- §7.2: an unrecognised mode is processed as absent

/-- The access decision. §5.3: "Access is granted when conforming
Authorizations are matched, otherwise access is denied."

`targetIri` is the resource being accessed; `aclOwnerIri` is the resource
whose ACL resource was found by the effective-ACL walk, and `inherited` says
whether that was an ancestor rather than the target itself. -/
def decideAccess (aclGraph : List Triple) (targetIri aclOwnerIri : String)
    (inherited : Bool) (who : Requester) (required : Mode) : Bool :=
  (authorizations aclGraph).any (fun a =>
    isApplicable aclGraph a &&
    objectMatches aclGraph a targetIri aclOwnerIri inherited &&
    subjectMatches aclGraph a who &&
    modeMatches aclGraph a required)

/-- The modes granted, in the fixed order read, write, append, control. -/
def grantedModes (aclGraph : List Triple) (targetIri aclOwnerIri : String)
    (inherited : Bool) (who : Requester) : List Mode :=
  [Mode.read, .write, .append, .control].filter
    (fun m => decideAccess aclGraph targetIri aclOwnerIri inherited who m)

/-- The `WAC-Allow` header field value of §6.1.

  `wac-allow = "WAC-Allow" ":" OWS #access-param OWS`
  `access-param = permission-group OWS "=" OWS access-modes`

The two permission groups this specification defines are `user`
("Permissions granted to the agent requesting the resource") and `public`
("Permissions granted to the public"). -/
def wacAllow (aclGraph : List Triple) (targetIri aclOwnerIri : String)
    (inherited : Bool) (who : Requester) : String :=
  let modes (w : Requester) : String :=
    String.intercalate " " ((grantedModes aclGraph targetIri aclOwnerIri inherited w).map Mode.name)
  "user=\"" ++ modes who ++ "\",public=\"" ++ modes { webId := none, origin := who.origin } ++ "\""

/-! ## The method-to-mode mapping — §5.3.1 -/

/-- The access mode an HTTP method requires on the target resource.

§5.3.1, verbatim: "GET — The HTTP GET method request targeting a resource
can only be allowed with the acl:Read access mode." "POST — The HTTP POST
can be used to create a new resource in a container or add information to
existing resources (but not remove resources or its contents) with either
acl:Append or acl:Write." "PUT — […] Replacing an existing resource requires
only acl:Write access to the resource itself." "DELETE — As the HTTP DELETE
method requests to remove a resource, the acl:Write access mode would be
required."

POST and an insert-only PATCH require `acl:Append`, which `acl:Write`
satisfies through `Mode.satisfies`; that is how "either acl:Append or
acl:Write" is decided with one required mode rather than two. -/
def requiredMode (method : String) (targetsAcl : Bool) : Mode :=
  if targetsAcl then .control
  else match method with
    | "GET" | "HEAD" | "OPTIONS" => .read
    | "POST" => .append
    | "PATCH" => .append
    | _ => .write

/-! ## The effective ACL resource — §5.1 -/

variable {σ : Type}

/-- The effective ACL resource of a path: the ACL of the path itself if it
has a representation, otherwise the ACL of the closest ancestor container
that has one, heading towards the storage root.

Returns the path whose ACL was found and whether it was inherited. The walk
is bounded by the ancestor list, which is finite by construction, so no fuel
parameter is needed. -/
def effectiveAcl (S : Store σ) (st : σ) (p : String) : Option (String × Bool) :=
  match S.lookup st (aclPathOf p) with
  | some _ => some (p, false)
  | none =>
      -- ancestors are storage root first; the closest container is last
      let candidates := (ancestors p).reverse
      match candidates.find? (fun a => (S.lookup st (aclPathOf a)).isSome) with
      | some a => some (a, true)
      | none   => none

/-- The whole server-side access decision for one request.

No effective ACL resource means no Authorization can be matched, so access
is denied — §5.3: "Access is granted when conforming Authorizations are
matched, otherwise access is denied." -/
def allowed (S : Store σ) (parseAcl : String → List Triple)
    (baseIri : String) (st : σ) (target : String) (who : Requester)
    (required : Mode) : Bool :=
  match effectiveAcl S st target with
  | none => false
  | some (owner, inherited) =>
      match S.lookup st (aclPathOf owner) with
      | none => false
      | some e =>
          decideAccess (parseAcl e.body) (iriOfPath baseIri target)
                 (iriOfPath baseIri owner) inherited who required

end L4Factoidal.Solid.Server
