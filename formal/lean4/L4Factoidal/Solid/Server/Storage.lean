/-
L4Factoidal.Solid.Server.Storage — the storage resource, its advertisement,
and slash semantics.

Wraps: `L4Factoidal.LWS.Model` (paths, links) and
`L4Factoidal.LWS.Discovery` (`discoveryLinks`).
Adds: the `pim:Storage` type link, the storage description and owner links
as Solid states them, and the slash-semantics rule, which LWS leaves to its
empty `Resource Identification` section.

Source: https://solidproject.org/TR/protocol (Solid Protocol v0.11.0,
modified 2024-05-12, read 2026-09-06).

§3.1 URI Slash Semantics, verbatim:

  "Paths ending with a slash denote a container resource."

  "If two URIs differ only in the trailing slash, and the server has
  associated a resource with one of them, then the other URI MUST NOT
  correspond to another resource. Instead, the server MAY respond to
  requests for the latter URI with a 301 redirect to the former. Servers
  MUST authorize prior to this optional redirect."

§4.1 Storage Resource, verbatim:

  "Servers MUST provide one or more storages."

  "When a server supports multiple storages, the URIs MUST be allocated to
  non-overlapping space."

  "Servers MUST advertise the storage resource by including the HTTP Link
  header field with rel=\"type\" targeting
  http://www.w3.org/ns/pim/space#Storage when responding to storage's
  request URI."

  "Servers MUST include the Link header field with
  rel=\"http://www.w3.org/ns/solid/terms#storageDescription\" targeting the
  URI of the storage description resource in the response of HTTP GET, HEAD
  and OPTIONS requests targeting a resource in a storage."

  "Servers MUST keep track of at least one owner of a storage in an
  implementation defined way."

  "When a server wants to advertise the owner of a storage, the server MUST
  include the Link header field with
  rel=\"http://www.w3.org/ns/solid/terms#owner\" targeting the URI of the
  owner in the response of HTTP HEAD or GET requests targeting the root
  container."
-/
import L4Factoidal.LWS.Operations

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.LWS

/-- One storage per handle, rooted at `/`. §4.1: "Servers MUST provide one
or more storages." A handle serves exactly one, so the non-overlapping-space
requirement holds by construction: two storages are two handles with
different base IRIs. -/
def storageRootPath : String := rootPath

/-- The storage description resource, whose path §4.1 requires a link to.
Its representation carries `rdf:type pim:Storage`, which is the statement
§4.1 requires: "Servers MUST include statements about the storage as part of
the storage description resource." -/
def storageDescriptionGraph (baseIri : String) : Option Triple :=
  match mkIri? (iriOfPath baseIri rootPath), mkIri? pimStorage with
  | some s, some o =>
      some { s := .iri s, p := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", by rfl⟩,
             o := .iri o }
  | _, _ => none

/-! ## Slash semantics — §3.1 -/

/-- The counterpart of a path under the trailing slash: `/a` ↔ `/a/`. The
storage root has none, because `""` is not a path. -/
def slashCounterpart (p : String) : Option String :=
  if p == rootPath then none
  else if p.endsWith "/" then some (String.ofList p.toList.dropLast)
  else some (p ++ "/")

/-- What the server does with a request whose target's counterpart is the
resource that exists.

§3.1: "If two URIs differ only in the trailing slash, and the server has
associated a resource with one of them, then the other URI MUST NOT
correspond to another resource. Instead, the server MAY respond to requests
for the latter URI with a 301 redirect to the former."

This server takes the MAY: it redirects. The redirect is decided AFTER the
access decision, which is what "Servers MUST authorize prior to this
optional redirect" requires; `Methods.step` calls the WAC decision first and
this function second. -/
def slashRedirect? {σ : Type} (S : Store σ) (st : σ) (target : String) :
    Option String :=
  match S.lookup st target with
  | some _ => none
  | none =>
      match slashCounterpart target with
      | none => none
      | some other => match S.lookup st other with
                      | some _ => some other
                      | none   => none

/-- A path and its counterpart never both resolve. This is the state
invariant §3.1 requires ("the other URI MUST NOT correspond to another
resource"); `Methods.step` preserves it by refusing a PUT whose counterpart
exists. -/
def slashInvariant {σ : Type} (S : Store σ) (st : σ) : Prop :=
  ∀ p, (S.lookup st p).isSome = true →
    ∀ q, slashCounterpart p = some q → S.lookup st q = none

end L4Factoidal.Solid.Server
