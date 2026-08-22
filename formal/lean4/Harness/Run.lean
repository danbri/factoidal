/-
Harness.Run — execute one `TestCase` with the Lean engine.

Every clause below reproduces the corresponding clause of
`bin/w3c-runner/w3c_runner.ml`'s `run_rdf_test` (~lines 2644–2850) and
of `Harness/CanonProbe.lean` for the rdf-canon types, so the two trees'
numbers mean the same thing. Where the F* runner has a lenient and a
strict parser and deliberately calls the STRICT one (issue #429 — the
lenient entry point skips bad lines, so a negative syntax test "passed"
whether the input was rejected or not), the Lean side has only the
strict behaviour: `parseTurtle` / `parseNTriples` / `parseNQuads` /
`parseTriG` return `Except ParseError _` and never recover.

Three rules this module keeps:

  * a comparison that gives up is NOT a pass. `IsoOutcome.budgetExceeded`
    scores `fail` and is counted separately in `HARNESS-DIAG`, so a
    silent give-up cannot be read as conformance;
  * a missing file is `skip`, with the path in the reason — the F*
    runner's `Skip "File missing"`;
  * a test type this tree cannot attempt is `unsupported <type>`, named.
    Every SPARQL type waits on a Lean SPARQL string parser, which
    does not exist yet. It is not silently passed, and it does not leave
    the denominator. (RDF/XML — `TestXMLEval`, `TestXMLNegativeSyntax` —
    runs through `parseRdfXml` since the RDF/XML port landed.)

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Manifest
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.Canonical

open L4Factoidal.RDF
open L4Factoidal.RDF.Canonical
open L4Factoidal.Syntax
open L4Factoidal.Crypto

namespace Harness

/-- What one run produced, plus whether a comparison budget tripped
(so `Main` can raise the `HARNESS-DIAG` counter). -/
structure RunResult where
  outcome        : Outcome
  budgetExceeded : Bool := false

def RunResult.ofOutcome (o : Outcome) : RunResult := { outcome := o }

/-- `budgetExceeded` is reported as its own kind of failure — never as
a pass, and never quietly folded into "not isomorphic". -/
def isoResult (label : String) (o : IsoOutcome) : RunResult :=
  match o with
  | .equal          => { outcome := .pass }
  | .notEqual       => { outcome := .fail label }
  | .budgetExceeded =>
      { outcome := .fail s!"isomorphism budget exceeded ({label})", budgetExceeded := true }

/-! ## rdf-canon helpers (shared with `Harness/CanonProbe.lean`) -/

/-- Every second entry of a split — the values between the quotes. -/
def oddIndexed : List String → List String
  | _ :: b :: rest => b :: oddIndexed rest
  | _              => []

/-- The double-quoted tokens of a string, in order. The suite's
`*-rdfc10map.json` files are flat `{"orig": "c14nN", …}` objects whose
keys and values are all blank-node labels, so pairing the quoted
tokens reconstructs the map without a JSON parser. -/
def quotedTokens (s : String) : List String := oddIndexed (s.splitOn "\"")

def pairUp : List String → List (String × String)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _              => []

/-- Budget for the negative (excessive-calls) rdf-canon test. Far below
`defaultHndqBudget` so the pathological input aborts promptly instead
of burning a million bounded-but-expensive Hash-N-Degree-Quads calls
first. Same value `CanonProbe` uses. -/
def negativeBudget : Nat := 1000

/-- `rdfc:hashAlgorithm "SHA384"` selects SHA-384; anything else (and
its absence) is the RDFC-1.0 §4.4 default, SHA-256. -/
def hashAlgOf (tc : TestCase) : HashAlgorithm :=
  match tc.hashAlgorithm with
  | some a => if a == "SHA384" then .sha384 else .sha256
  | none   => .sha256

/-! ## The dispatcher -/

/-- Run one test case. `assumedBase` is the suite's
`mf:assumedTestBase`; `manifestDir` the directory the manifest sits
in. -/
def runTest (assumedBase : Option String) (manifestDir : String) (tc : TestCase) :
    IO RunResult := do
  -- Every type handled here takes its input from `mf:action` as a file.
  let withAction (k : String → String → IO RunResult) : IO RunResult := do
    match tc.action with
    | none      => return .ofOutcome (.skip "mf:action is not a file IRI")
    | some path =>
      match ← readOpt path with
      | none      => return .ofOutcome (.skip s!"file missing: {path}")
      | some text => k path text
  -- …and additionally reads the expected `mf:result` file.
  let withActionAndResult (k : String → String → String → IO RunResult) : IO RunResult := do
    withAction fun path text => do
      match tc.resultFile with
      | none    => return .ofOutcome (.skip "no expected result file")
      | some rf =>
        match ← readOpt rf with
        | none          => return .ofOutcome (.skip s!"result file missing: {rf}")
        | some expected => k path text expected
  match tc.testType with

  /- ### N-Triples (RDF 1.1 N-Triples §4) -/
  | "TestNTriplesPositiveSyntax" =>
    withAction fun _ text => return .ofOutcome (
      match parseNTriples text .rdf11 with
      | .ok _    => .pass
      | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestNTriplesNegativeSyntax" =>
    withAction fun _ text => return .ofOutcome (
      match parseNTriples text .rdf11 with
      | .error _ => .pass
      | .ok g    => .fail s!"should reject but parsed OK ({g.length} triples)")

  /- ### N-Quads (RDF 1.1 N-Quads §4) -/
  | "TestNQuadsPositiveSyntax" =>
    withAction fun _ text => return .ofOutcome (
      match parseNQuads text .rdf11 with
      | .ok _    => .pass
      | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestNQuadsNegativeSyntax" =>
    withAction fun _ text => return .ofOutcome (
      match parseNQuads text .rdf11 with
      | .error _ => .pass
      | .ok _    => .fail "should reject but parsed OK")

  /- ### Turtle (RDF 1.1 Turtle §7) -/
  | "TestTurtlePositiveSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTurtle text (some base) .rdf11 with
        | .ok _    => .pass
        | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestTurtleNegativeSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTurtle text (some base) .rdf11 with
        | .error _ => .pass
        | .ok g    => .fail s!"should reject but parsed OK ({g.length} triples)")
  | "TestTurtleEval" =>
    withActionAndResult fun path text expectedText => do
      let base := fixtureBase assumedBase manifestDir path
      match parseTurtle text (some base) .rdf11 with
      | .error e => return .ofOutcome (.fail s!"Turtle parse error: {e.msg} (offset {e.pos})")
      | .ok g =>
        match parseNTriples expectedText .rdf11 with
        | .error e =>
            return .ofOutcome (.fail s!"expected-result N-Triples parse error: {e.msg} (offset {e.pos})")
        | .ok expected =>
            return isoResult
              s!"not isomorphic to the expected graph (got {g.length} triples, expected {expected.length})"
              (Graph.isomorphicOutcome g expected)
  /- Negative eval: the F* runner passes the test when the strict parser
     reports an error, and also when it succeeds with an empty graph. -/
  | "TestTurtleNegativeEval" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTurtle text (some base) .rdf11 with
        | .error _ => .pass
        | .ok g    => if g.isEmpty then .pass
                      else .fail s!"should produce an eval error but succeeded ({g.length} triples)")

  /- ### TriG (RDF 1.1 TriG §6) -/
  | "TestTrigPositiveSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTriG text (some base) .rdf11 with
        | .ok _    => .pass
        | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestTrigNegativeSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTriG text (some base) .rdf11 with
        | .error _ => .pass
        | .ok _    => .fail "should reject but parsed OK")
  | "TestTrigEval" =>
    withActionAndResult fun path text expectedText => do
      let base := fixtureBase assumedBase manifestDir path
      match parseTriG text (some base) .rdf11 with
      | .error e => return .ofOutcome (.fail s!"TriG parse error: {e.msg} (offset {e.pos})")
      | .ok ds =>
        match parseNQuads expectedText .rdf11 with
        | .error e =>
            return .ofOutcome (.fail s!"expected-result N-Quads parse error: {e.msg} (offset {e.pos})")
        | .ok expected =>
            let gotN := ds.default.length + (ds.named.map (fun ng => ng.graph.length)).sum
            let expN := expected.default.length + (expected.named.map (fun ng => ng.graph.length)).sum
            return isoResult
              s!"not isomorphic to the expected dataset (got {gotN} quads, expected {expN})"
              (Dataset.isomorphicOutcome ds expected)
  | "TestTrigNegativeEval" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTriG text (some base) .rdf11 with
        | .error _ => .pass
        | .ok ds   =>
          let n := ds.default.length + (ds.named.map (fun ng => ng.graph.length)).sum
          if n == 0 then .pass
          else .fail s!"should produce an eval error but succeeded ({n} quads)")

  /- ### RDF Dataset Canonicalization (RDFC-1.0) -/
  | "RDFC10EvalTest" =>
    withActionAndResult fun _ text expectedText => do
      match parseNQuads text .rdf11 with
      | .error e => return .ofOutcome (.fail s!"N-Quads parse error: {e.msg} (offset {e.pos})")
      | .ok ds =>
        let got := ds.canonicalNQuads (hashAlgOf tc)
        return .ofOutcome (
          if trimTrailingNewlines got == trimTrailingNewlines expectedText then .pass
          else .fail "canonical N-Quads output differs from the expected file")
  | "RDFC10MapTest" =>
    withActionAndResult fun _ text expectedText => do
      match parseNQuads text .rdf11 with
      | .error e => return .ofOutcome (.fail s!"N-Quads parse error: {e.msg} (offset {e.pos})")
      | .ok ds =>
        let expected := pairUp (quotedTokens expectedText)
        let got := (canonicalize ds (hashAlgOf tc)).issued
        return .ofOutcome (
          if got.length == expected.length && expected.all (fun p => got.contains p) then .pass
          else .fail s!"issued identifier map differs (got {got.length} entries, expected {expected.length})")
  /- Negative eval: the input is a poison graph; a conforming
     implementation must ABORT on excessive calls to Hash N-Degree
     Quads (RDFC-1.0 §4.4) rather than return a canonical form. -/
  | "RDFC10NegativeEvalTest" =>
    withAction fun _ text => do
      match parseNQuads text .rdf11 with
      | .error e => return .ofOutcome (.fail s!"N-Quads parse error: {e.msg} (offset {e.pos})")
      | .ok ds =>
        return .ofOutcome (
          if canonicalizeExceedsBudget .sha256 negativeBudget ds then .pass
          else .fail "expected an excessive-calls abort, got a result")

  /- ### RDF/XML (RDF 1.1 XML Syntax §7) — the F* runner's
     `TestXMLEval` compares against the sibling N-Triples file by
     isomorphism; `TestXMLNegativeSyntax` passes only on rejection. -/
  | "TestXMLEval" =>
    withActionAndResult fun path text expectedText => do
      let base := fixtureBase assumedBase manifestDir path
      match RdfXml.parseRdfXml text (some base) with
      | .error e => return .ofOutcome (.fail s!"RDF/XML parse error: {e}")
      | .ok g =>
        match parseNTriples expectedText .rdf11 with
        | .error e =>
            return .ofOutcome (.fail s!"expected-result N-Triples parse error: {e.msg} (offset {e.pos})")
        | .ok expected =>
            return isoResult
              s!"not isomorphic to the expected graph (got {g.length} triples, expected {expected.length})"
              (Graph.isomorphicOutcome g expected)
  | "TestXMLNegativeSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match RdfXml.parseRdfXml text (some base) with
        | .error _ => .pass
        | .ok g    => .fail s!"should reject but parsed OK ({g.length} triples)")

  /- ### Not attemptable yet — named, counted, never passed. -/
  | other => return .ofOutcome (.unsupported other)

end Harness
