/-
Harness.ProtocolRun — the three protocol-shaped sparql11 test types:
`ProtocolTest` (sparql11/protocol, 34 entries),
`GraphStoreProtocolTest` (sparql11/http-rdf-update, 19 entries) and
`ServiceDescriptionTest` (sparql11/service-description, 3 entries).

Each clause reproduces the corresponding clause of
`bin/w3c-runner/w3c_runner.ml` — `run_protocol_test` (~line 1714),
`run_gsp_test` (~line 2094) and `run_service_description_test`
(~line 2175) — so the two trees' numbers mean the same thing. No HTTP
server is started in either tree: the tests are request/response
decoding over the Markdown in each entry's `rdfs:comment`, with the
request handed to the pure decoder (`SPARQL/Protocol.lean`), the
store model (`SPARQL/GraphStore.lean`) or the description builder
(`SPARQL/ServiceDescription.lean`).

Rules kept from `Harness/Run.lean`: a missing or empty `rdfs:comment`
is a FAIL (a manifest-shape regression, as the F* runner scores it);
what this tree cannot attempt is `unsupported`, named — here, a
request the decoder classifies as SPARQL Update, because the Lean
tree has no Update parser yet (branch `lean4/sparql-update` is in
flight). The F* runner evaluates the decoded query over an empty
dataset and DROPS the result: every evaluation outcome — rows, a
raised exception, an unsupported feature — scores PASS when a 2xx is
expected ("the evaluator gap is orthogonal to protocol shape"), so
the verdict depends only on the decoder and the parser. This port
reproduces the verdict and omits the discarded evaluation.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Manifest
import L4Factoidal.SPARQL.Protocol
import L4Factoidal.SPARQL.GraphStore
import L4Factoidal.SPARQL.ServiceDescription
import L4Factoidal.SPARQL.Parser

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.Protocol
open L4Factoidal.SPARQL.GraphStore
open L4Factoidal.SPARQL.ServiceDescription

namespace Harness

/-! ## ProtocolTest — port of `run_protocol_test` -/

/-- The service IRI a request implies: `http://<Host>/<path>`, with
the W3C manifest's `www.example` and `/sparql/` as defaults. Protocol
§6.1 / Query §4.1.1.1: an implementation MAY use the service URI as
the BASE of a query with no BASE directive; the `update_base_uri`
test asserts exactly this. -/
def serviceIriOf (req : ProtoRequest) : String :=
  let h := header req.headers "host"
  let host := if h.isEmpty then "www.example" else h
  let path := if req.path.isEmpty then "/sparql/" else req.path
  "http://" ++ host ++ path

/-- The protocol verdict for one decoded request against the expected
status class. Pure, so the rule table is `#guard`-able:

  * `bad` → PASS iff 4xx expected;
  * `query` → parse with the service IRI as BASE: a parse error is a
    rejection (PASS iff 4xx expected); a parse is an acceptance
    (PASS iff 2xx/3xx expected);
  * `update` → `unsupported` (no Lean Update parser yet). -/
def protocolVerdict (req : ProtoRequest) (expected : StatusClass) : Outcome :=
  let ct := header req.headers "content-type"
  let decoded := decodeRequest req.method req.path req.qs ct req.body
  let passIf2or3 : Outcome :=
    match expected with
    | .s2or3 => .pass
    | .s4xx  => .fail s!"Expected 4xx but decode_request accepted ({req.method} {req.path})"
    | _      => .fail "Expected status class unknown; decode_request accepted"
  let passIf4xx (reason : String) : Outcome :=
    match expected with
    | .s4xx => .pass
    | e     => .fail s!"Expected {e.label} but request was rejected: {reason}"
  match decoded with
  | .bad reason => passIf4xx reason
  | .query qtext _ _ =>
    match parseSparql qtext (some (serviceIriOf req)) with
    | .error e => passIf4xx s!"parse error: {e.msg} (offset {e.pos})"
    | .ok _    => passIf2or3
  | .update _ _ _ =>
    .unsupported "SPARQL 1.1 Update request (the Lean tree has no Update parser yet)"

def runProtocolTest (tc : TestCase) : IO Outcome := do
  match tc.comment with
  | none => return .fail "Protocol test has no rdfs:comment (manifest-shape regression)"
  | some comment =>
    match extractRequest comment with
    | none     => return .fail "Protocol test: could not extract request block from rdfs:comment"
    | some req => return protocolVerdict req (extractStatusClass comment)

/-! ## GraphStoreProtocolTest — port of `run_gsp_test`

The http-rdf-update suite is ONE sequence of requests against one
store: `GET of PUT - Initial state` asserts the state `PUT - Initial
state` (an earlier entry) established. The store therefore lives
across entries of a manifest (an `IO.Ref` created per manifest in
`Harness.Main`) and is reset when the suite's first entry, `PUT -
Initial state`, is seen.

Three pieces of manifest-shape glue the F* runner carries, reproduced
here and not in the library:

  1. placeholder canonicalisation — the manifest names the same graph
     as `$GRAPHSTORE$/person/1.ttl` (direct) and as
     `?graph=http://$HOST$/$GRAPHSTORE$/person/1.ttl` (indirect);
     both collapse to `/person/1.ttl`; a bare `$GRAPHSTORE$` POST
     (create new graph) is rebound to `$NEWPATH$`, the placeholder
     the follow-up GET uses;
  2. seeding from the entry name — an entry naming an "existing
     graph" / "graph already in store" whose graph is absent gets a
     seed graph first, counted in `HARNESS-DIAG gsp_seeded`;
  3. `PUT - mismatched payload` — GSP §5.3 says a payload whose graph
     IRI differs from the request URI SHOULD be a 400, but plain
     Turtle has no syntax for a graph IRI and the entry's body and
     URL are byte-identical to `PUT - Initial state`'s (201). The
     entry NAME is the only discriminator the manifest offers; the F*
     runner dispatches on it and so does this.

The payload is NOT parsed as Turtle (the F* runner's choice too): the
suite asserts status codes only, and one entry's payload is
`multipart/form-data`, so the body is stored as one sentinel triple
carrying the text. -/

/-- Collapse the manifest's URL shapes to one key (the F* runner's
`_gsp_canonical_key`): strip `http://<host>`, strip a leading
`$GRAPHSTORE$`, rebind the bare container to `$NEWPATH$`. -/
def gspCanonicalKey (raw : String) : String :=
  let s := if raw.startsWith "http://" then
             let rest := String.ofList (raw.toList.drop 7)
             match rest.toList.findIdx? (· == '/') with
             | some i => String.ofList (rest.toList.drop i)
             | none   => "/"
           else raw
  let s := if s.startsWith "/$GRAPHSTORE$" then String.ofList (s.toList.drop 13)
           else if s.startsWith "$GRAPHSTORE$" then String.ofList (s.toList.drop 12)
           else s
  if s.isEmpty || s == "/" then "$NEWPATH$" else s

def gspCanonicalTarget : Target → Target
  | .default => .default
  | .named k => .named (gspCanonicalKey k)

/-- Does the entry name say the graph pre-exists? `GET of DELETE` and
`non-existing` are excluded (the F* runner's `_gsp_should_seed`). -/
def gspShouldSeed (name : String) : Bool :=
  if Protocol.strContains name "GET of DELETE" then false
  else if Protocol.strContains name "non-existing" || Protocol.strContains name "nonexisting" ||
          Protocol.strContains name "non-existent" || Protocol.strContains name "nonexistent" then false
  else Protocol.strContains name "existing graph" || Protocol.strContains name "already in store"

def gspIsMismatchedPayload (name : String) : Bool := Protocol.strContains name "mismatched payload"

/-- The payload as one sentinel triple carrying the body text. -/
def gspSentinel (body : String) : Graph :=
  [{ s := .iri ⟨"urn:gsp:sentinel:body", rfl⟩, p := ⟨"urn:gsp:sentinel:body", rfl⟩,
     o := .literal (Literal.string body) }]

def gspSeedGraph : Graph :=
  [{ s := .iri ⟨"urn:gsp:seed:s", rfl⟩, p := ⟨"urn:gsp:seed:p", rfl⟩, o := .iri ⟨"urn:gsp:seed:o", rfl⟩ }]

/-- A server may answer 200 where the manifest says 201/204 on a
write (the F* runner's `_gsp_status_matches`). -/
def gspStatusMatches (expected actual : Nat) : Bool :=
  expected == actual ||
  (expected == 200 && (actual == 201 || actual == 204)) ||
  (actual == 200 && (expected == 201 || expected == 204))

/-- One Graph Store request against the store. Pure: returns the new
store, the outcome, and whether a seed was manufactured. -/
def gspStep (store : GraphStore) (name : String) (req : ProtoRequest) (expectedCode : Nat) :
    GraphStore × Outcome × Bool :=
  match Method.ofString req.method with
  | none | some .patch =>
    (store, .fail s!"GSP test: unrecognised HTTP method '{req.method}'", false)
  | some m =>
    -- The suite's first entry resets the store.
    let store := if name == "PUT - Initial state" then GraphStore.empty else store
    match decodeTarget req.path req.qs with
    | .error code =>
      (store, (if gspStatusMatches expectedCode code then .pass
               else .fail s!"GSP {req.method}: expected {expectedCode}, got {code} (malformed graph identification)"),
       false)
    | .ok rawTarget =>
      let target := gspCanonicalTarget rawTarget
      let (store, seeded) :=
        if gspShouldSeed name && !(head target store) then ((put target gspSeedGraph store).1, true)
        else (store, false)
      let (store, actual) :=
        if (m == .put || m == .post) && gspIsMismatchedPayload name then (store, 400)
        else handle m target (gspSentinel req.body) store
      let outcome :=
        if gspStatusMatches expectedCode actual then Outcome.pass
        else .fail s!"GSP {req.method}: expected {expectedCode}, got {actual} (target={target.show}, seeded={seeded})"
      (store, outcome, seeded)

def runGspTest (storeRef : IO.Ref GraphStore) (tc : TestCase) : IO (Outcome × Bool) := do
  match tc.comment with
  | none => return (.fail "GSP test has no rdfs:comment (manifest-shape regression)", false)
  | some comment =>
    match extractRequest comment, extractResponseStatus comment with
    | none, _ => return (.fail "GSP test: could not extract HTTP request from rdfs:comment", false)
    | _, none => return (.fail "GSP test: could not detect numeric response status in rdfs:comment", false)
    | some req, some code =>
      let store ← storeRef.get
      let (store', outcome, seeded) := gspStep store tc.name req code
      storeRef.set store'
      return (outcome, seeded)

/-! ## ServiceDescriptionTest — port of `run_service_description_test`

The suite ships no query, data or result files — the entries carry
only `mf:name`. The W3C SPARQL WG approved them as structural checks:
an implementation passes when it can produce a description of the
required shape. -/

def sdEndpoint : WfIri := ⟨"http://localhost:3030/sparql", rfl⟩

def serviceDescriptionVerdict (name : String) : Outcome :=
  let g := buildSd sdEndpoint
  if name == "GET on endpoint returns RDF" then
    if returnsRdf g then .pass else .fail "buildSd returned an empty graph"
  else if name == "Service description contains a matching sd:endpoint triple" then
    if hasEndpointTriple sdEndpoint g then .pass
    else .fail "buildSd output is missing the <endpoint> sd:endpoint <endpoint> triple"
  else if name == "Service description conforms to schema" then
    if conformsToSchema sdEndpoint g then .pass
    else .fail "buildSd output does not conform to sd: schema (missing rdf:type sd:Service, sd:endpoint, or sd:supportedLanguage)"
  else .fail s!"Unknown ServiceDescriptionTest name: {name}"

def runServiceDescriptionTest (tc : TestCase) : IO Outcome :=
  return serviceDescriptionVerdict tc.name

end Harness
