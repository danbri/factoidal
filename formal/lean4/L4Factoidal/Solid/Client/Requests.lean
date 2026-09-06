/-
L4Factoidal.Solid.Client.Requests — build a conformant request for each
method.

Wraps: `L4Factoidal.HTTP.Server.Request`, the same record the server reads.
Adds: the client conformance rules of the Solid Protocol.

Source: https://solidproject.org/TR/protocol §2.2 HTTP Client, verbatim:

  "Clients MUST conform to HTTP Semantics [RFC9110]."
  "Clients MUST conform to HTTP/1.1 [RFC9112]."
  "Clients MUST use the Content-Type HTTP header field in PUT, POST, and
  PATCH requests that contain content [RFC9110]."
  "When a client receives a response with a 403 or 404 status code, the
  client MAY repeat the request with different credentials."

§5.3, Note: Conditional Update, verbatim:

  "Clients are encouraged to use the HTTP If-None-Match header field with a
  value of \"*\" to prevent an unsafe request method, e.g., PUT, PATCH, from
  inadvertently modifying an existing representation of the target resource
  when the client believes that the resource does not have a current
  representation."

§5.3.1: a PATCH body is `text/n3`.

Web Access Control §5.3.4, verbatim:

  "Clients MUST discover access privileges on a resource by making an HTTP
  GET or HEAD request on the target resource, and checking the WAC-Allow
  header value."

Every function here returns a `Request` record. Nothing is sent; the host
sends it.
-/
import L4Factoidal.Solid.Client.Discovery

namespace L4Factoidal.Solid.Client

open L4Factoidal.LWS
open L4Factoidal.HTTP (Request)

/-- What a client asks for. -/
inductive RequestKind where
  | read
  | create
  | replace
  | patch
  | delete
  | discoverStorage
  | readProfile
deriving Repr, DecidableEq, Inhabited

def RequestKind.ofString? (s : String) : Option RequestKind :=
  match s with
  | "read" => some .read
  | "create" => some .create
  | "replace" => some .replace
  | "patch" => some .patch
  | "delete" => some .delete
  | "discoverStorage" => some .discoverStorage
  | "readProfile" => some .readProfile
  | _ => none

def RequestKind.name : RequestKind → String
  | .read => "read" | .create => "create" | .replace => "replace"
  | .patch => "patch" | .delete => "delete"
  | .discoverStorage => "discoverStorage" | .readProfile => "readProfile"

/-- The arguments a request needs. -/
structure RequestArgs where
  target : String
  body : String := ""
  contentType : String := "text/turtle"
  /-- A `Slug` for a POST, which the server MAY use for the assigned name. -/
  slug : Option String := none
  /-- Ask the server to refuse if the resource already exists. -/
  ifNoneMatchStar : Bool := false
  /-- The state of a multi-step operation, carried from the previous
  interpretation. For `discoverStorage` it is the next resource of the
  storage walk of §4.1, which `storageStepOf` named; the request is then
  made on it rather than on `target`. -/
  state : Option String := none
deriving Repr, Inhabited

/-- The `Accept` field a client sends for an RDF source. §5.5 requires the
server to satisfy `text/turtle` or `application/ld+json`, so a client that
asks for both is always answerable. -/
def rdfAccept : String := "text/turtle, application/ld+json;q=0.9"

private def contentHeaders (a : RequestArgs) : List (String × String) :=
  if a.body == "" then [] else [("content-type", a.contentType)]

private def conditional (a : RequestArgs) : List (String × String) :=
  if a.ifNoneMatchStar then [("if-none-match", "*")] else []

/-- Build the request for a kind. `create` is a POST to a CONTAINER, which
is the form §5.3 requires for a server-assigned name ("Servers MUST allow
creation of new resources by a POST request to a URI path ending with /");
`replace` is a PUT, which assigns the URI from the client side. -/
def buildRequest (kind : RequestKind) (a : RequestArgs) : Request :=
  match kind with
  | .read =>
      { method := "GET", path := a.target, queryStr := "",
        headers := [("accept", rdfAccept)], body := "" }
  | .discoverStorage =>
      -- The walk asks about `state` once the first reply has named a
      -- parent to move up to; the first request has no state and asks
      -- about the target itself.
      { method := "HEAD", path := a.state.getD a.target, queryStr := "",
        headers := [], body := "" }
  | .readProfile =>
      { method := "GET", path := a.target, queryStr := "",
        headers := [("accept", rdfAccept)], body := "" }
  | .create =>
      { method := "POST", path := a.target, queryStr := "",
        headers := contentHeaders a ++
          (match a.slug with | some s => [("slug", s)] | none => []),
        body := a.body }
  | .replace =>
      { method := "PUT", path := a.target, queryStr := "",
        headers := contentHeaders a ++ conditional a, body := a.body }
  | .patch =>
      { method := "PATCH", path := a.target, queryStr := "",
        headers := [("content-type", "text/n3")], body := a.body }
  | .delete =>
      { method := "DELETE", path := a.target, queryStr := "",
        headers := [], body := "" }

/-- Does the request satisfy the client MUST of §2.2 — content implies a
`Content-Type` field? Checked here rather than assumed, so a host that
builds a request by hand can gate on it. -/
def contentTypePresent (r : Request) : Bool :=
  if (r.method == "PUT" || r.method == "POST" || r.method == "PATCH") && r.body != ""
  then r.headers.any (fun kv => kv.1 == "content-type")
  else true

/-- Every request this module builds satisfies that rule. -/
theorem buildRequest_contentTypePresent (kind : RequestKind) (a : RequestArgs) :
    contentTypePresent (buildRequest kind a) = true := by
  cases kind <;>
    simp [contentTypePresent, buildRequest, contentHeaders, conditional] <;>
    (try cases a.slug) <;> (try simp) <;>
    (try (by_cases hb : a.body = "" <;> simp [hb]))

end L4Factoidal.Solid.Client
