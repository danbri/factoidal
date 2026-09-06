/-
L4Factoidal.Solid.Client.Profile — read a WebID profile document.

Wraps: `L4Factoidal.Syntax.Turtle.parseTurtle` — the profile is an RDF
document and is parsed by the Turtle parser, not by anything written here.
Adds: the reading of the properties §9.1 and §4.1 name.

Source: https://solidproject.org/TR/protocol §9.1 WebID, verbatim:

  "When a WebID is dereferenced, server provides a representation of the
  WebID Profile in an RDF document [RDF11-CONCEPTS]."

§4.1 Storage Resource, verbatim:

  "Clients can discover a storage by making an HTTP GET request on the
  target URL to retrieve an RDF representation [RDF11-CONCEPTS], whose
  encoded RDF graph contains a relation of type
  http://www.w3.org/ns/pim/space#storage. The object of the relation is the
  storage (pim:Storage)."

§6 Linked Data Notifications: an inbox is `ldp:inbox`.

Solid-OIDC names `solid:oidcIssuer` in a profile; it is read here so a
client host can start an authentication flow, but no token is verified in
Lean (see `docs/lws-solid-conformance.md`, the host-verified rows).
-/
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Graph

namespace L4Factoidal.Solid.Client

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## Vocabulary -/

def pimStorageProperty : String := "http://www.w3.org/ns/pim/space#storage"
def ldpInboxProperty : String := "http://www.w3.org/ns/ldp#inbox"
def solidOidcIssuer : String := "http://www.w3.org/ns/solid/terms#oidcIssuer"
def foafName : String := "http://xmlns.com/foaf/0.1/name"

/-- What a client reads out of a WebID profile document. -/
structure Profile where
  webId : String
  /-- The storages the profile points at, through `pim:storage`. -/
  storages : List String
  /-- The LDN inbox, through `ldp:inbox`. -/
  inbox : Option String
  /-- The OpenID Connect issuers, through `solid:oidcIssuer`. -/
  oidcIssuers : List String
  /-- The `foaf:name` values, as lexical forms. -/
  names : List String
deriving Repr, Inhabited

private def objectsOf (g : List Triple) (subj : String) (pred : String) :
    List String :=
  g.filterMap (fun t =>
    let sMatches := match t.s with
      | .iri i => i.val == subj
      | .bnode _ => false
    if sMatches && t.p.val == pred then
      match t.o with
      | .iri i => some i.val
      | .literal l => some l.val.lexicalForm
      | _ => none
    else none)

/-- Read a profile document. The WebID is the subject the caller
dereferenced; a profile usually describes it with a fragment identifier, so
the caller passes the full WebID including any `#me`. -/
def readProfileGraph (webId : String) (g : List Triple) : Profile :=
  { webId
  , storages := objectsOf g webId pimStorageProperty
  , inbox := (objectsOf g webId ldpInboxProperty).head?
  , oidcIssuers := objectsOf g webId solidOidcIssuer
  , names := objectsOf g webId foafName }

/-- Parse a `text/turtle` profile document and read it. A document that does
not parse yields a profile with nothing in it rather than an error, because
a client that cannot read a profile is in the same position as one that read
an empty profile: it has no storage to walk to. -/
def readProfile (webId baseIri body : String) : Profile :=
  match parseTurtle body (some baseIri) .rdf11 with
  | .ok g    => readProfileGraph webId g
  | .error _ => { webId, storages := [], inbox := none,
                  oidcIssuers := [], names := [] }

end L4Factoidal.Solid.Client
