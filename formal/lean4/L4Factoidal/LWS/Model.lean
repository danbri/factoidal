/-
L4Factoidal.LWS.Model — the resource model of the Linked Web Storage
Protocol 1.0 Core.

Source: https://w3c.github.io/lws-protocol/lws10-core/ (W3C Linked Web
Storage Working Group editor's draft, read 2026-09-06), section
"Terminology". The definitions this module encodes, verbatim from that
section:

  "LWS resource — an HTTP resource as defined in [RFC9110] which supports
  the read operations defined by the Linked Web Storage Protocol."

  "container — an LWS resource that is able to enumerate a collection of
  LWS resources, conforming to the conventions described in Section 8.
  Containers."

  "data resource — a data-bearing LWS resource such as a document, image,
  or structured information whose support for update and delete operations
  follows the requirements outlined in Section 9. Operations."

  "storage root — a container at the root of a containment hierarchy of a
  storage. The storage root is the only LWS resource that does not have a
  parent in the LWS containment hierarchy nor a primary resource."

  "metadata resource — an auxiliary resource, managed by a storage, that
  describes an LWS resource and conforms to the conventions described in
  TBD. The lifecycle of a metadata resource is bound to the LWS resource it
  describes."

  "linkset resource — a type of auxiliary resource whose representation
  conforms to [RFC9264]."

  "containment — the relationship between a container and the LWS resources
  whose lifecycle the container manages."

  "auxiliary resource — an LWS resource that plays a particular role with
  respect to a LWS resource, called its primary resource, and whose lifetime
  is bound to the primary resource. […] Auxiliary resources are discovered
  using web links [RFC8288] of a specific type."

The draft gives no URI syntax for the containment hierarchy — its
`Resource Identification` section is an empty heading. This module uses the
Solid Protocol's slash semantics (§3.1, "Paths ending with a slash denote a
container resource"), because a containment hierarchy needs one and Solid's
is the binding the draft acknowledges it draws from. Every function that
depends on that choice says so.

Identifiers are `RDF.WfIri`, so a resource identifier and an RDF subject are
the same kind of thing and no conversion is needed when a container
enumerates its members as triples.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.LWS

open L4Factoidal.RDF

/-! ## Resource kinds -/

/-- The kinds of LWS resource the draft's Terminology section names.

`storageRoot` is a container (the draft: "a container at the root of a
containment hierarchy of a storage") and is kept a separate constructor
because the delete operation refuses it, which no other container refuses. -/
inductive ResourceKind where
  | container
  | dataResource
  | storageRoot
  | metadataResource
  | linksetResource
deriving DecidableEq, Repr, Inhabited

/-- A container in the containment sense: the storage root is one. -/
def ResourceKind.isContainer : ResourceKind → Bool
  | .container | .storageRoot => true
  | _ => false

/-- An auxiliary resource: "an LWS resource that plays a particular role
with respect to a LWS resource, called its primary resource, and whose
lifetime is bound to the primary resource." -/
def ResourceKind.isAuxiliary : ResourceKind → Bool
  | .metadataResource | .linksetResource => true
  | _ => false

/-! ## Identifiers

A path is the request target inside one storage: `/` for the storage root,
`/a/` for a container, `/a/b` for a data resource. An absolute identifier is
the base IRI of the storage with the path appended, minus the path's leading
slash. -/

/-- Build a well-formed IRI, or nothing. The RDF core's gate is non-empty
and containing a colon (`RDF.isIri`); a request target reaches Lean as a
plain string, so the proof cannot be by `rfl` and this is the only way in. -/
def mkIri? (s : String) : Option WfIri :=
  if h : isIri s = true then some ⟨s, h⟩ else none

/-- A path names a container when it ends with a slash — Solid Protocol
§3.1, used here because the LWS draft's own `Resource Identification`
section is empty. -/
def pathIsContainer (p : String) : Bool := p.endsWith "/"

/-- The storage root path. -/
def rootPath : String := "/"

/-- Drop a leading slash so a path can be appended to a base IRI that ends
with one. -/
def pathSuffix (p : String) : String :=
  if p.startsWith "/" then String.ofList (p.toList.drop 1) else p

/-- The absolute identifier of a path within a storage. `baseIri` is
expected to end with a slash; `iriOfPath "http://ex/" "/a/b" = "http://ex/a/b"`. -/
def iriOfPath (baseIri p : String) : String := baseIri ++ pathSuffix p

/-- The segments of a path, with empty segments removed. `"/a/b/"` gives
`["a", "b"]`, and the root gives `[]`. -/
def segments (p : String) : List String :=
  (p.splitOn "/").filter (fun s => s != "")

/-- The parent container of a path, or nothing for the storage root.

`parent? "/a/b" = some "/a/"`, `parent? "/a/b/" = some "/a/"`,
`parent? "/a" = some "/"`, `parent? "/" = none`. -/
def parent? (p : String) : Option String :=
  if p == rootPath || p == "" then none else
  let segs := segments p
  if segs.isEmpty then none
  else some ("/" ++ String.join (segs.dropLast.map (fun s => s ++ "/")))

/-- Every ancestor container of a path, storage root first. -/
def ancestors (p : String) : List String :=
  let segs := (segments p).dropLast
  (List.range (segs.length + 1)).map (fun k =>
    "/" ++ String.join ((segs.take k).map (fun s => s ++ "/")))

/-- Is `child` DIRECTLY contained by the container `c`? Containment is the
relation the draft names: "the relationship between a container and the LWS
resources whose lifecycle the container manages". Direct containment is one
segment deeper, which is what a container enumerates. -/
def contains (c child : String) : Bool :=
  pathIsContainer c && parent? child == some c

/-- The last segment of a path — the name a container enumerates it under. -/
def leafName (p : String) : String :=
  match (segments p).getLast? with
  | some s => if pathIsContainer p then s ++ "/" else s
  | none   => ""

/-! ## Auxiliary links

The draft: "Auxiliary resources are discovered using web links [RFC8288] of
a specific type." It names two types and leaves the link relations to the
sections that are still empty, so the relations used here are Solid's
(`acl`, `describedby`) plus RFC 9264's `linkset`. -/

/-- A web link as it appears in an RFC 8288 `Link` header field. -/
structure Link where
  target : String
  rel    : String
deriving DecidableEq, Repr, Inhabited

/-- Serialise one link into `Link` header field value syntax. -/
def Link.render (l : Link) : String :=
  "<" ++ l.target ++ ">; rel=\"" ++ l.rel ++ "\""

/-- Serialise a list of links into ONE `Link` header field value. RFC 8288
allows several links in one field, comma separated. -/
def renderLinks (ls : List Link) : String :=
  String.intercalate ", " (ls.map Link.render)

/-- The link relation of each auxiliary kind. `metadataResource` uses
`describedby` (POWDER-DR, as Solid Protocol §4.3.2 does); `linksetResource`
uses `linkset` (RFC 9264 §4). -/
def auxiliaryRel : ResourceKind → Option String
  | .metadataResource => some "describedby"
  | .linksetResource  => some "linkset"
  | _                 => none

/-! ## The stored form of a resource -/

/-- One resource as a storage holds it.

`mtime` is seconds since the Unix epoch. It is a FIELD, not a call into a
clock: the operations take the current time from the state, and the state
takes it from the host. That is what keeps `step` a total function.

`contentType` is the media type of `body`. A resource whose representation
is not text is held by the host, which gives the engine the metadata; this
first slice carries a UTF-8 string. -/
structure Entry where
  path        : String
  kind        : ResourceKind
  contentType : String
  body        : String
  mtime       : Nat
deriving Repr, Inhabited

end L4Factoidal.LWS
