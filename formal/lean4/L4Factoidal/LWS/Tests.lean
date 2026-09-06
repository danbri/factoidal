/-
L4Factoidal.LWS.Tests — one build-time check per `guarded` row of
`L4Factoidal.LWS.Conformance.registry`, plus the theorems its `proved` rows
name.

Every `#guard` is evaluated during `lake build`: a wrong answer is a build
failure. Each check is a named `def` returning `Bool`, so the registry row
can name it and `Harness/LwsProbe.lean` can print the name beside the
statement it decides.
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.LWS.Patch
import L4Factoidal.LWS.Conformance

namespace L4Factoidal.LWS.Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.LWS

/-! ## Fixtures -/

def cfg : Config := { baseIri := "http://example.org/", owner := some "http://example.org/alice/card#me" }

/-- A storage holding only its root, at clock 0. -/
def emptyStorage : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := "", mtime := 0 }], clock := 1 }

def req (method target : String) (headers : List (String × String) := [])
    (body : String := "") : Request :=
  { method, path := target, queryStr := "", headers, body }

def run (r : Request) (st : MemState) : Response × MemState :=
  step MemStore cfg r st

/-- Run a list of requests in order, keeping every response. -/
def runAll : List Request → MemState → List Response × MemState
  | [], st => ([], st)
  | r :: rest, st =>
      let (resp, st') := run r st
      let (resps, st'') := runAll rest st'
      (resp :: resps, st'')

def hdr (resp : Response) (name : String) : Option String :=
  (resp.headers.find? (fun (k, _) => k == name)).map (·.2)

def turtle : List (String × String) := [("content-type", "text/turtle")]

/-! ## The clock -/

-- Day zero of the Unix epoch is a Thursday.
#guard httpDate 0 == "Thu, 01 Jan 1970 00:00:00 GMT"
#guard httpDate 1000000000 == "Sun, 09 Sep 2001 01:46:40 GMT"

/-! ## lws-core-03 — Last-Modified on GET and HEAD -/

/-- "HTTP Server MUST generate a Last-Modified header field in response to
GET and HEAD requests." -/
def lwsGuardLastModifiedOnGet : Bool :=
  let (_, st) := run (req "PUT" "/alice/card" turtle "<#me> <http://example.org/p> \"v\" .") emptyStorage
  let (resp, _) := run (req "GET" "/alice/card") st
  resp.status == 200 && (hdr resp "last-modified").isSome

def lwsGuardLastModifiedOnHead : Bool :=
  let (_, st) := run (req "PUT" "/alice/card" turtle "x") emptyStorage
  let (resp, _) := run (req "HEAD" "/alice/card") st
  resp.status == 200 && (hdr resp "last-modified").isSome && resp.body == ""

#guard lwsGuardLastModifiedOnGet
#guard lwsGuardLastModifiedOnHead

/-! ## lws-core-04 — the ?insertions blank-node refusal -/

def exP : WfIri := ⟨"http://example.org/p", by rfl⟩

/-- "The PATCH ?insertions formulae MUST NOT contain blank nodes." -/
def lwsGuardInsertionsRefuseBlankNodes : Bool :=
  let p : Patch := { insertions := [{ s := .bnode "b0", p := .iri exP, o := .var "x" }]
                   , conditions := [{ s := .var "s", p := .iri exP, o := .var "x" }] }
  match wellFormed p with
  | some e => e == PatchError.blankNodeInInsertions && e.status == 422
  | none   => false

/-- A patch whose insertions carry no blank node and whose variables are
bound by the conditions is well formed, so the guard above is not passing
because every patch is refused. -/
def lwsGuardInsertionsAcceptWithoutBlankNodes : Bool :=
  let p : Patch := { insertions := [{ s := .var "s", p := .iri exP, o := .var "x" }]
                   , conditions := [{ s := .var "s", p := .iri exP, o := .var "x" }] }
  (wellFormed p).isNone

#guard lwsGuardInsertionsRefuseBlankNodes
#guard lwsGuardInsertionsAcceptWithoutBlankNodes

-- An unbound variable in the insertions is refused with 422 too.
#guard (wellFormed { insertions := [{ s := .var "y", p := .iri exP, o := .var "y" }] }
          == some (PatchError.unboundVariable "y"))

/-! ## lws-core-05 — a container enumerates its members -/

def populated : MemState :=
  (runAll [ req "PUT" "/alice/card" turtle "a"
          , req "PUT" "/alice/notes/" turtle ""
          , req "PUT" "/alice/notes/one" turtle "b" ] emptyStorage).2

/-- "container — an LWS resource that is able to enumerate a collection of
LWS resources". Direct containment only: `/alice/notes/one` is contained by
`/alice/notes/`, not by `/alice/`. -/
def lwsGuardContainerEnumerates : Bool :=
  let alice := containedPaths MemStore populated "/alice/"
  let notes := containedPaths MemStore populated "/alice/notes/"
  alice.contains "/alice/card" && alice.contains "/alice/notes/" &&
  !alice.contains "/alice/notes/one" && notes == ["/alice/notes/one"]

#guard lwsGuardContainerEnumerates

-- PUT created the intermediate container /alice/ that no request named.
#guard (memLookup populated "/alice/").isSome

/-! ## lws-core-08 — auxiliary resources are advertised as web links -/

/-- "Auxiliary resources are discovered using web links [RFC8288] of a
specific type." -/
def lwsGuardAuxiliaryLinksAdvertised : Bool :=
  let (resp, _) := run (req "GET" "/alice/card") populated
  match hdr resp "link" with
  | none => false
  | some v =>
      (v.splitOn "rel=\"acl\"").length > 1 &&
      (v.splitOn "rel=\"describedby\"").length > 1 &&
      (v.splitOn "solid/terms#storageDescription").length > 1

#guard lwsGuardAuxiliaryLinksAdvertised

-- The storage root, and only the storage root, advertises pim:Storage.
#guard advertisesStorage (discoveryLinks "http://example.org/" none "/" .storageRoot true)
#guard !advertisesStorage (discoveryLinks "http://example.org/" none "/a" .dataResource false)

/-! ## lws-core-11 — create, read, update, delete -/

/-- "An operation is any of the following actions that can be performed on
a served resource: create resource, read resource, update resource, delete
resource." One sequence exercising all four. -/
def lwsGuardCreateReadUpdateDelete : Bool :=
  let (rs, st) := runAll
    [ req "PUT" "/alice/card" turtle "one"      -- create
    , req "GET" "/alice/card"                   -- read
    , req "PUT" "/alice/card" turtle "two"      -- update
    , req "GET" "/alice/card"                   -- read again
    , req "DELETE" "/alice/card"                -- delete
    , req "GET" "/alice/card" ] emptyStorage    -- gone
  (rs.map (·.status)) == [201, 200, 204, 200, 204, 404] &&
  (rs[1]?.map (·.body)) == some "one" &&
  (rs[3]?.map (·.body)) == some "two" &&
  (memLookup st "/alice/card").isNone

#guard lwsGuardCreateReadUpdateDelete

/-! ## lws-core-12 — created is not success -/

/-- "A success response is not defined for the create resource operation.
See instead created." A PUT that creates answers 201 with a `Location`; a
PUT that replaces answers 204 with none. -/
def lwsGuardCreatedIsNotSuccess : Bool :=
  let (created, st) := run (req "PUT" "/alice/card" turtle "one") emptyStorage
  let (replaced, _) := run (req "PUT" "/alice/card" turtle "two") st
  created.status == 201 && hdr created "location" == some "/alice/card" &&
  replaced.status == 204 && (hdr replaced "location").isNone

#guard lwsGuardCreatedIsNotSuccess

/-! ## POST assigns a name, and refuses a target with no representation -/

#guard (run (req "POST" "/alice/" turtle "x") populated).1.status == 201
#guard (run (req "POST" "/nowhere/" turtle "x") populated).1.status == 404
#guard (run (req "POST" "/alice/card" turtle "x") populated).1.status == 405

-- Two POSTs to one container get two different names, because the clock
-- advanced between them.
#guard
  let (rs, _) := runAll [ req "POST" "/alice/" turtle "x"
                        , req "POST" "/alice/" turtle "y" ] populated
  (rs[0]?.bind (fun r => hdr r "location")) !=
    (rs[1]?.bind (fun r => hdr r "location"))

/-! ## DELETE refuses the storage root, and a non-empty container -/

#guard (run (req "DELETE" "/") populated).1.status == 405
#guard (run (req "DELETE" "/alice/notes/") populated).1.status == 409
#guard
  let allow := hdr (run (req "DELETE" "/") populated).1 "allow"
  match allow with
  | some v => (v.splitOn "DELETE").length == 1
  | none   => false

/-! ## lws-core-06 — the storage root has no parent -/

/-- "The storage root is the only LWS resource that does not have a parent
in the LWS containment hierarchy". -/
theorem rootHasNoParent : parent? rootPath = none := by
  simp [parent?, rootPath]

/-! ## The registry's own arithmetic -/

#guard Conformance.registry.length == 18
#guard (Conformance.registry.map (·.id)).eraseDups.length == Conformance.registry.length

end L4Factoidal.LWS.Tests
