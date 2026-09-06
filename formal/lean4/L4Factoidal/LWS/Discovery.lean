/-
L4Factoidal.LWS.Discovery — the RFC 8288 web links a storage advertises.

Source: https://w3c.github.io/lws-protocol/lws10-core/ (editor's draft, read
2026-09-06). Its `Discovery` section is a heading with no body; what the
draft DOES say about discovery is in the Terminology and Introduction:

  "Auxiliary resources are discovered using web links [RFC8288] of a
  specific type (see Section )."

  "A client navigates the resource hierarchy from a root container,
  discovering contained resources and their relations through links provided
  in server responses."

The concrete link relations therefore come from the Solid Protocol v0.11.0,
§4.1 and §4.3, which the LWS draft's Acknowledgements name as its source:

  "Servers MUST advertise the storage resource by including the HTTP Link
  header field with rel="type" targeting
  http://www.w3.org/ns/pim/space#Storage when responding to storage's
  request URI."

  "Servers MUST include the Link header field with
  rel="http://www.w3.org/ns/solid/terms#storageDescription" targeting the
  URI of the storage description resource in the response of HTTP GET, HEAD
  and OPTIONS requests targeting a resource in a storage."

  "When a server wants to advertise the owner of a storage, the server MUST
  include the Link header field with
  rel="http://www.w3.org/ns/solid/terms#owner" targeting the URI of the
  owner in the response of HTTP HEAD or GET requests targeting the root
  container."

  "Servers MUST advertise auxiliary resources associated with a subject
  resource by responding to HEAD and GET requests by including the HTTP Link
  header field with the rel parameter [RFC8288]."

`L4Factoidal.Solid.Server.*` uses these functions unchanged; the Solid layer
adds the `acl` link's ACL semantics, not the link itself.
-/
import L4Factoidal.LWS.Model

namespace L4Factoidal.LWS

/-! ## Vocabulary -/

def pimStorage : String := "http://www.w3.org/ns/pim/space#Storage"
def solidStorageDescription : String :=
  "http://www.w3.org/ns/solid/terms#storageDescription"
def solidOwner : String := "http://www.w3.org/ns/solid/terms#owner"
def ldpResource : String := "http://www.w3.org/ns/ldp#Resource"
def ldpContainer : String := "http://www.w3.org/ns/ldp#Container"
def ldpBasicContainer : String := "http://www.w3.org/ns/ldp#BasicContainer"
def ldpRdfSource : String := "http://www.w3.org/ns/ldp#RDFSource"

/-- The path of the storage description resource. Relative to the storage
root, so a storage that is not at the origin root still names it. -/
def storageDescriptionPath : String := "/.well-known/solid"

/-- The path of the ACL auxiliary resource of a subject resource. A CLIENT
must not derive it (WAC §3.1: "Clients MUST NOT derive ACL resource URIs
through string operations on resource URIs"); a SERVER chooses it, and this
is the choice this server makes. -/
def aclPathOf (p : String) : String := p ++ ".acl"

/-- The path of the description (metadata) auxiliary resource. -/
def describedByPathOf (p : String) : String := p ++ ".meta"

/-! ## The links -/

/-- The `Link` header field values a GET, HEAD or OPTIONS response carries
for `path`.

`isRoot` decides the `type` link to `pim:Storage` and the `owner` link;
`kind` decides the LDP type links; both auxiliary links are advertised for
every resource, because both exist for every resource in this storage. -/
def discoveryLinks (baseIri : String) (owner : Option String) (path : String)
    (kind : ResourceKind) (isRoot : Bool) : List Link :=
  let typeLinks : List Link :=
    (if isRoot then [{ target := pimStorage, rel := "type" }] else []) ++
    (if kind.isContainer then
       [ { target := ldpBasicContainer, rel := "type" }
       , { target := ldpContainer, rel := "type" }
       , { target := ldpResource, rel := "type" } ]
     else
       [ { target := ldpRdfSource, rel := "type" }
       , { target := ldpResource, rel := "type" } ])
  let auxLinks : List Link :=
    [ { target := aclPathOf path, rel := "acl" }
    , { target := describedByPathOf path, rel := "describedby" } ]
  let storageLinks : List Link :=
    { target := iriOfPath baseIri storageDescriptionPath,
      rel := solidStorageDescription } ::
    (match owner with
     | some o => if isRoot then [{ target := o, rel := solidOwner }] else []
     | none   => [])
  typeLinks ++ auxLinks ++ storageLinks

/-- Does a link list advertise the storage type? The client side of the
storage walk (`L4Factoidal.Solid.Client.Discovery`) asks exactly this. -/
def advertisesStorage (ls : List Link) : Bool :=
  ls.any (fun l => l.rel == "type" && l.target == pimStorage)

end L4Factoidal.LWS
