/-
L4Factoidal.Solid.Client.Discovery — the client side of discovery: read the
`Link` header field, walk up to the storage, find the auxiliaries and the
inbox.

Wraps: `L4Factoidal.LWS.Model.Link` (the link record) and
`L4Factoidal.LWS.Discovery` (the relations).
Adds: the PARSING direction. The server renders links; the client reads
them. The two directions are separate on purpose — a client must not derive
what it can read.

Source: https://solidproject.org/TR/protocol, verbatim:

§4.1: "Clients can determine a resource is of type storage by making an HTTP
HEAD or GET request on the target URL, and checking for the Link header
field with rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage."

§4.1: "Clients can determine the storage of a resource by moving up the URI
path hierarchy until the response includes a Link header field with
rel=\"type\" targeting http://www.w3.org/ns/pim/space#Storage."

§4.1: "Clients can discover a storage by making an HTTP GET request on the
target URL to retrieve an RDF representation, whose encoded RDF graph
contains a relation of type http://www.w3.org/ns/pim/space#storage."

§4.3: "Clients can discover auxiliary resources associated with a subject
resource by making an HTTP HEAD or GET request on the target URL, and
checking the HTTP Link header field with the rel parameter [RFC8288]."

Web Access Control §3.1, verbatim:

  "Clients MUST discover the ACL resource associated with a resource by
  making an HTTP request on the target URL, and checking the HTTP Link
  header with the rel parameter."

  "Clients MUST NOT derive the URI of the ACL resource through string
  operations on the URI of the resource."

That last rule is why this module has no `aclPathOf`: the client reads the
`acl` link or it has nothing. The SERVER's `aclPathOf` is in
`L4Factoidal.LWS.Discovery`, where a client never reaches it.

This module performs no request. It says what to ask for next, and reads
what came back; `npm/factoidal/solid/client/` moves the bytes.
-/
import L4Factoidal.LWS.Discovery
import L4Factoidal.HTTP.Server

namespace L4Factoidal.Solid.Client

open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

/-! ## Reading the `Link` header field -/

private def trimWs (s : String) : String :=
  String.ofList
    (((s.toList.dropWhile (fun c => c == ' ' || c == '\t')).reverse.dropWhile
        (fun c => c == ' ' || c == '\t')).reverse)

/-- Split a `Link` field value on the commas that separate link-values,
leaving commas inside `<…>` alone. -/
private def splitLinksGo : Bool → List Char → List Char → List String
  | _, [], acc => [String.ofList acc.reverse]
  | inAngle, c :: rest, acc =>
      if c == '<' then splitLinksGo true rest (c :: acc)
      else if c == '>' then splitLinksGo false rest (c :: acc)
      else if c == ',' && !inAngle then
        String.ofList acc.reverse :: splitLinksGo false rest []
      else splitLinksGo inAngle rest (c :: acc)

/-- The target inside `<…>`. -/
private def angleTarget (s : String) : Option String :=
  match (s.toList.dropWhile (fun c => c != '<')) with
  | '<' :: rest => some (String.ofList (rest.takeWhile (fun c => c != '>')))
  | _ => none

/-- The value of the `rel` parameter, with or without quotes. -/
private def relValue (s : String) : Option String :=
  ((s.splitOn ";").drop 1).findSome? (fun param =>
    let p := trimWs param
    if p.startsWith "rel=" then
      let v := trimWs (String.ofList (p.toList.drop 4))
      some (String.ofList (v.toList.filter (fun c => c != '"')))
    else none)

/-- Parse one `Link` header field value into links. -/
def parseLinkValue (v : String) : List Link :=
  (splitLinksGo false v.toList []).filterMap (fun part =>
    match angleTarget part, relValue part with
    | some t, some r => some { target := t, rel := r }
    | _, _ => none)

/-- Every link of every `Link` field of a response. RFC 8288 allows the
field to be repeated, so all of them are read. -/
def linksOf (resp : Response) : List Link :=
  (resp.headers.filterMap (fun (k, v) =>
    if k == "link" then some v else none)).flatMap parseLinkValue

/-! ## What the links say -/

/-- Does this response come from the storage root? §4.1's client rule. -/
def isStorage (resp : Response) : Bool :=
  advertisesStorage (linksOf resp)

/-- The target of the first link with this relation. -/
def linkTarget? (resp : Response) (rel : String) : Option String :=
  ((linksOf resp).find? (fun l => l.rel == rel)).map (·.target)

/-- The ACL resource of a subject resource, read from the `acl` link — never
derived. -/
def aclOf? (resp : Response) : Option String := linkTarget? resp "acl"

/-- The description resource, read from the `describedby` link. -/
def describedByOf? (resp : Response) : Option String :=
  linkTarget? resp "describedby"

/-- The storage description resource. -/
def storageDescriptionOf? (resp : Response) : Option String :=
  linkTarget? resp solidStorageDescription

/-- The storage owner, advertised only on the root container. -/
def ownerOf? (resp : Response) : Option String := linkTarget? resp solidOwner

/-- The LDN inbox. -/
def inboxOf? (resp : Response) : Option String :=
  linkTarget? resp "http://www.w3.org/ns/ldp#inbox"

/-! ## The storage walk -/

/-- The paths to try, in order, when moving up the URI path hierarchy from
`p` looking for the storage: the resource's own container first, then each
container above it, then the root. §4.1: "Clients can determine the storage
of a resource by moving up the URI path hierarchy until the response
includes a Link header field with rel=\"type\" targeting
http://www.w3.org/ns/pim/space#Storage." -/
def storageWalk (p : String) : List String := (ancestors p).reverse

/-- One step of the walk: given the responses gathered so far, in walk
order, either the storage was found or the next path to ask for.

The client host drives this: it asks for `storageWalk`'s head, calls this
with what came back, and repeats. Keeping the loop in the host is what keeps
this module free of I/O. -/
inductive WalkStep where
  | found (path : String)
  | ask (path : String)
  | exhausted
deriving Repr, DecidableEq

def walkStep (p : String) (answered : List (String × Bool)) : WalkStep :=
  match answered.find? (fun (_, isStore) => isStore) with
  | some (path, _) => .found path
  | none =>
      match (storageWalk p).find? (fun cand =>
              !(answered.map (·.1)).contains cand) with
      | some next => .ask next
      | none      => .exhausted

end L4Factoidal.Solid.Client
