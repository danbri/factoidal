/-
L4Factoidal.LWS.Operations — the create, read, update and delete operations
of the Linked Web Storage Protocol 1.0 Core, as ONE total function

  step : Store σ → Config → Request → σ → Response × σ

Source: https://w3c.github.io/lws-protocol/lws10-core/ (editor's draft, read
2026-09-06), section "Resource Access":

  "An operation is any of the following actions that can be performed on a
  served resource: create resource, read resource, update resource, delete
  resource."

  "success - the operation is believed to have completed. This may be
  accompanied by a resource representation conveying the contents of a
  served resource. A success response is not defined for the create resource
  operation. See instead created."

and from the draft's CG-to-ED delta list:

  "HTTP Server MUST generate a Last-Modified header field in response to GET
  and HEAD requests."

**The draft has no HTTP binding.** Its `Operations`, `Containers` and
`Discovery` sections are headings with empty bodies, and it names no status
codes. Every status code below therefore comes from the Solid Protocol
v0.11.0 binding (https://solidproject.org/TR/protocol §5), which the LWS
draft's Acknowledgements name as its source, and the conformance registry
row for each one records both citations. The day the LWS draft fixes its own
binding, the rows are the difference.

Nothing here reads a clock, a socket or a file. The time comes from the
store's `now`, which the host sets; every mutation stamps `Last-Modified`
from it and then calls `tick`, so a sequence of writes has strictly
increasing modification times and the server-assigned names of POST are
distinct without a separate counter.
-/
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Discovery
import L4Factoidal.HTTP.Server

namespace L4Factoidal.LWS

open L4Factoidal.RDF
open L4Factoidal.HTTP (Request Response)

/-! ## The clock

`Last-Modified` is an HTTP-date (RFC 9110 §5.6.7), which is a civil date in
GMT. The conversion from a count of days to a civil date is Howard
Hinnant's era algorithm, in `Nat` throughout: the offset 719468 puts day
zero of the algorithm at 0000-03-01, and every intermediate subtraction is
between a value and a quotient of itself, so none of them underflows. -/

private def two (n : Nat) : String :=
  if n < 10 then "0" ++ toString n else toString n

private def monthName : Nat → String
  | 1 => "Jan" | 2 => "Feb" | 3 => "Mar" | 4 => "Apr"
  | 5 => "May" | 6 => "Jun" | 7 => "Jul" | 8 => "Aug"
  | 9 => "Sep" | 10 => "Oct" | 11 => "Nov" | _ => "Dec"

private def dayName : Nat → String
  | 0 => "Sun" | 1 => "Mon" | 2 => "Tue" | 3 => "Wed"
  | 4 => "Thu" | 5 => "Fri" | _ => "Sat"

/-- The civil year, month and day of a count of days since 1970-01-01. -/
def civilFromDays (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/-- An RFC 9110 §5.6.7 IMF-fixdate from seconds since the Unix epoch.
`httpDate 0 = "Thu, 01 Jan 1970 00:00:00 GMT"`. -/
def httpDate (unix : Nat) : String :=
  let days := unix / 86400
  let secs := unix % 86400
  let (y, m, d) := civilFromDays days
  dayName ((days + 4) % 7) ++ ", " ++ two d ++ " " ++ monthName m ++ " " ++
    toString y ++ " " ++ two (secs / 3600) ++ ":" ++ two (secs % 3600 / 60) ++
    ":" ++ two (secs % 60) ++ " GMT"

/-! ## Configuration -/

/-- What a storage knows about itself, and about the agent of the request
in flight. The agent is a WebID the HOST verified; the engine only decides
access from it (see `L4Factoidal.Solid.Server.WAC`). -/
structure Config where
  baseIri : String := "http://localhost/"
  owner   : Option String := none
  agent   : Option String := none
deriving Repr, Inhabited

/-! ## Helpers over the store -/

variable {σ : Type}

/-- The paths of the resources a container DIRECTLY contains, in the store's
own order. -/
def containedPaths (S : Store σ) (st : σ) (c : String) : List String :=
  (S.paths st).filter (fun p => contains c p)

/-- Create every missing ancestor container of `p`, newest clock first.

Solid Protocol §5.3: "Servers MUST create intermediate containers and
include corresponding containment triples in container representations
derived from the URI path component of PUT and PATCH requests." The
containment triples are derived from the path hierarchy rather than stored
(`L4Factoidal.Solid.Server.Containment`), so creating the container entry is
the whole of it. -/
def ensureAncestors (S : Store σ) : List String → σ → σ
  | [], st => st
  | a :: rest, st =>
      let st := match S.lookup st a with
        | some _ => st
        | none =>
            let kind := if a == rootPath then ResourceKind.storageRoot else .container
            S.tick (S.put st
              { path := a, kind, contentType := "text/turtle",
                body := "", mtime := S.now st })
      ensureAncestors S rest st

/-- Touch a container so its `Last-Modified` reflects a change to its
containment triples — Solid Protocol §4.2: "Servers can determine the field
value of the HTTP Last-Modified header field in response to HEAD and GET
requests targeting a container based on changes to containment triples." -/
def touchContainer (S : Store σ) (st : σ) (p : String) : σ :=
  match parent? p with
  | none => st
  | some c =>
      match S.lookup st c with
      | none => st
      | some e => S.tick (S.put st { e with mtime := S.now st })

/-! ## Responses -/

/-- The methods a target accepts. A storage root refuses DELETE, so the
`Allow` field it generates must not list it — Solid Protocol §5.4:
"Server MUST exclude the DELETE method in the field value of the Allow
header field, in response to requests to these resources." -/
def allowFor (kind : ResourceKind) (isRoot : Bool) : List String :=
  if isRoot then ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH"]
  else if kind.isContainer then ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH", "DELETE"]
  else ["GET", "HEAD", "OPTIONS", "PUT", "PATCH", "DELETE"]

/-- The header fields every successful response to a read carries. -/
def readHeaders (cfg : Config) (e : Entry) (isRoot : Bool) : List (String × String) :=
  [ ("content-type", e.contentType)
  , ("last-modified", httpDate e.mtime)
  , ("allow", String.intercalate ", " (allowFor e.kind isRoot))
  , ("accept-patch", "text/n3")
  , ("accept-put", "text/turtle")
  , ("link", renderLinks (discoveryLinks cfg.baseIri cfg.owner e.path e.kind isRoot)) ]
  ++ (if e.kind.isContainer then [("accept-post", "text/turtle")] else [])

/-! ## The step function -/

/-- The name a POST assigns. The store's clock is strictly increasing over
mutations (`StoreLaws.nowTick`), so two POSTs to one container never collide
and no counter is needed beside the clock. -/
def assignedName (S : Store σ) (st : σ) : String := "res" ++ toString (S.now st)

/-- One operation. Total: every request, well formed or not, has a response.

Read (GET, HEAD) — 200 with `Last-Modified`, or 404.
Create/Update (PUT) — 201 when the resource did not exist, 204 when it did.
Create (POST) — 201 with `Location`; 404 when the target has no
representation (Solid §5.3); 405 when the target is not a container.
Delete (DELETE) — 204; 405 on the storage root; 404 when absent; 409 when a
container is not empty.
OPTIONS — 204 with `Allow` and the `Accept-*` fields.
Anything else — 405 with `Allow` (Solid §5: "Servers MUST respond with the
405 status code to requests using HTTP methods that are not supported by the
target resource"). -/
def step (S : Store σ) (cfg : Config) (r : Request) (st : σ) : Response × σ :=
  let target := r.path
  let isRoot := target == rootPath
  let existing := S.lookup st target
  match r.method with
  | "GET" | "HEAD" =>
      match existing with
      | none => (⟨404, [("content-type", "text/plain")], "Not Found"⟩, st)
      | some e =>
          let hs := readHeaders cfg e isRoot
          (⟨200, hs, if r.method == "HEAD" then "" else e.body⟩, st)
  | "OPTIONS" =>
      let kind := (match existing with
                   | some e => e.kind
                   | none => if pathIsContainer target then ResourceKind.container else .dataResource)
      (⟨204, [ ("allow", String.intercalate ", " (allowFor kind isRoot))
             , ("accept-patch", "text/n3")
             , ("accept-put", "text/turtle")
             , ("accept-post", "text/turtle") ], ""⟩, st)
  | "PUT" =>
      match r.header? "content-type" with
      | none => (⟨400, [("content-type", "text/plain")],
                  "PUT with content requires a Content-Type header field"⟩, st)
      | some ct =>
          let st := ensureAncestors S (ancestors target) st
          let kind := if pathIsContainer target then
                        (if isRoot then ResourceKind.storageRoot else .container)
                      else .dataResource
          let e : Entry := { path := target, kind, contentType := ct,
                             body := r.body, mtime := S.now st }
          let st' := touchContainer S (S.tick (S.put st e)) target
          match existing with
          | none   => (⟨201, [("location", target), ("last-modified", httpDate e.mtime)], ""⟩, st')
          | some _ => (⟨204, [("last-modified", httpDate e.mtime)], ""⟩, st')
  | "POST" =>
      match existing with
      | none => (⟨404, [("content-type", "text/plain")],
                  "POST target has no representation"⟩, st)
      | some parentEntry =>
          if !parentEntry.kind.isContainer then
            (⟨405, [("allow", String.intercalate ", " (allowFor parentEntry.kind isRoot))], ""⟩, st)
          else
            match r.header? "content-type" with
            | none => (⟨400, [("content-type", "text/plain")],
                        "POST with content requires a Content-Type header field"⟩, st)
            | some ct =>
                let slug := match r.header? "slug" with
                  | some s => if s == "" then assignedName S st else s
                  | none   => assignedName S st
                let linkHdr := (r.header? "link").getD ""
                let asContainer := (linkHdr.splitOn "ldp#BasicContainer").length > 1
                let childPath := target ++ slug ++ (if asContainer then "/" else "")
                let kind := if asContainer then ResourceKind.container else .dataResource
                let e : Entry := { path := childPath, kind, contentType := ct,
                                   body := r.body, mtime := S.now st }
                let st' := touchContainer S (S.tick (S.put st e)) childPath
                (⟨201, [("location", childPath), ("last-modified", httpDate e.mtime)], ""⟩, st')
  | "DELETE" =>
      if isRoot then
        (⟨405, [("allow", String.intercalate ", " (allowFor .storageRoot true))], ""⟩, st)
      else
        match existing with
        | none => (⟨404, [("content-type", "text/plain")], "Not Found"⟩, st)
        | some e =>
            if e.kind.isContainer && !(containedPaths S st target).isEmpty then
              (⟨409, [("content-type", "text/plain")], "Container is not empty"⟩, st)
            else
              let st' := touchContainer S (S.tick (S.remove st target)) target
              (⟨204, [], ""⟩, st')
  | _ =>
      let kind := (match existing with
                   | some e => e.kind
                   | none => ResourceKind.dataResource)
      (⟨405, [("allow", String.intercalate ", " (allowFor kind isRoot))], ""⟩, st)

end L4Factoidal.LWS
