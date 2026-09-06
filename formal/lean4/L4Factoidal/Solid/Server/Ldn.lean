/-
L4Factoidal.Solid.Server.Ldn — the Linked Data Notifications inbox.

Wraps: `L4Factoidal.LWS.Operations.step` (the inbox is an ordinary
container, and a notification is an ordinary POST to it).
Adds: the `ldp:inbox` advertisement and the acceptance rule.

Source: https://solidproject.org/TR/protocol §6 Linked Data Notifications,
verbatim:

  "A Solid server MUST conform to the LDN specification by implementing the
  Receiver parts to receive notifications, and MAY implement the Sender or
  Consumer parts."

  "A Solid client MUST conform to the LDN specification by implementing the
  Sender or Consumer parts to send or read notifications."

Linked Data Notifications (W3C Recommendation, 2017-05-02) §3, the Receiver
parts this module decides:

  the inbox is discovered "in the HTTP Link header with rel=\"http://www.w3.org/ns/ldp#inbox\"
  or, for RDF representations, an ldp:inbox triple";
  a receiver "MUST accept POST requests with a JSON-LD payload" and
  "MUST respond with a 201 Created status code and a Location header" on
  success.

The `ldp:inbox` triple in the resource's own representation is NOT written
by this module: a resource's representation is the bytes its author PUT, and
this server does not rewrite them. The link header field is the
advertisement.
-/
import L4Factoidal.LWS.Operations

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

/-- The LDN inbox link relation. -/
def ldpInbox : String := "http://www.w3.org/ns/ldp#inbox"

/-- The inbox container of a storage. One per storage, at the root, which is
the arrangement a client's storage walk can always find. -/
def inboxPath : String := "/inbox/"

/-- The `Link` header field value advertising the inbox. LDN §3: a receiver
advertises its inbox with `rel="http://www.w3.org/ns/ldp#inbox"`. -/
def inboxLink (baseIri : String) : LWS.Link :=
  { target := iriOfPath baseIri inboxPath, rel := ldpInbox }

/-- The media types a Receiver accepts. LDN requires JSON-LD; this server
also accepts the RDF syntaxes its own parser reads. -/
def acceptedNotificationTypes : List String :=
  ["application/ld+json", "text/turtle", "application/n-triples"]

/-- The inbox links a response carries. Only the storage root advertises the
inbox, which is what "A resource MUST advertise only one Inbox" allows and
what a client's storage walk can always reach. -/
def inboxLinks (baseIri : String) (isRoot : Bool) : List LWS.Link :=
  if isRoot then [inboxLink baseIri] else []

/-- The inbox container itself, as a storage holds it. A server that
advertises an inbox has to have one: LDN §3.3.1 requires a Receiver to
answer a POST to it with 201 and a `Location`, and a container that does not
exist answers 404 (Solid Protocol §5.3). -/
def inboxEntry (now : Nat) : Entry :=
  { path := inboxPath, kind := .container, contentType := "text/turtle",
    body := "", mtime := now }

/-- Is this a notification POST to the inbox? -/
def isNotificationPost (r : Request) : Bool :=
  r.method == "POST" && r.path == inboxPath

/-- Does the request carry a media type a Receiver accepts? A `Content-Type`
may carry parameters, so the comparison is on the type before `;`. -/
def acceptableNotification (r : Request) : Bool :=
  match r.header? "content-type" with
  | none => false
  | some ct =>
      let bare := (ct.splitOn ";").headD ""
      acceptedNotificationTypes.contains
        (String.ofList (bare.toList.filter (fun c => c != ' ')))

end L4Factoidal.Solid.Server
