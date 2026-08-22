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
    It is not silently passed, and it does not leave the denominator.
    The SPARQL 1.1 QUERY types (`QueryEvaluationTest`,
    `CSVResultFormatTest`, `PositiveSyntaxTest11`,
    `NegativeSyntaxTest11`) run through `SPARQL/Parser.lean` and
    `SPARQL/Query.lean` — see "SPARQL 1.1 Query" below, which
    reproduces `run_query_eval_test` (~lines 1174–1560). The SPARQL
    1.1 UPDATE types (`UpdateEvaluationTest`,
    `PositiveUpdateSyntaxTest11`, `NegativeUpdateSyntaxTest11`) run
    through `SPARQL/UpdateParser.lean` and `SPARQL/Update.lean` — see
    "SPARQL 1.1 Update" below. The protocol-shaped types
    (`ProtocolTest`, `GraphStoreProtocolTest`,
    `ServiceDescriptionTest`) run through `Harness/ProtocolRun.lean`
    (request/response decoding over `rdfs:comment`, no HTTP server);
    an entailment-regime evaluation test is
    `unsupported entailment regime <R>` (the Lean tree has the
    rdfs-core closure only, none of the regimes the suite names).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Manifest
import Harness.Compare
import Harness.ProtocolRun
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.Canonical
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsCsvTsv

open L4Factoidal.RDF
open L4Factoidal.RDF.Canonical
open L4Factoidal.Syntax
open L4Factoidal.Crypto
open L4Factoidal.SPARQL

namespace Harness

/-- What one run produced, plus whether a comparison budget tripped
(so `Main` can raise the `HARNESS-DIAG` counter) and how much was
actually compared (the measurement check). -/
structure RunResult where
  outcome         : Outcome
  budgetExceeded  : Bool := false
  rowsCompared    : Nat := 0
  triplesCompared : Nat := 0
  /-- A Graph Store test whose pre-state was manufactured from its
  name (`HARNESS-DIAG gsp_seeded`). -/
  gspSeeded       : Bool := false

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

/-! ## SPARQL 1.1 Query — port of `run_query_eval_test`

Rules, in the order the F* runner applies them:

  1. fixtures: every `qt:data` file is parsed by extension (`.nt`,
     `.nq`, `.trig`, `.rdf`, else Turtle) with base `file://<path>`,
     merged into the default graph (a `.trig`/`.nq` fixture's named
     graphs are kept); every `qt:graphData` file becomes a named graph
     whose name is the file's IRI; every `qt:serviceData` pair becomes
     an `EvalEnv.services` entry;
  2. the query is parsed with its own `file:` IRI as BASE;
  3. WHERE-clause blank nodes are query-scoped variables
     (`QueryPattern.rewriteBnodes`, applied inside `evalSelect` /
     `evalAsk` / `evalConstruct` as in the F* `eval_select_query`);
  4. SELECT: expected rows from `.srx` / `.srj` / `.tsv` / `.csv`, or
     an `rs:ResultSet` Turtle file; compared by `compareSelectRows`;
  5. ASK: the evaluated boolean against the expected one;
  6. CONSTRUCT: the expected Turtle graph, by isomorphism;
  7. parse failure → FAIL (named); missing file → SKIP (path);
     an entailment regime or DESCRIBE → `unsupported`, named. -/

/-- `NOW()` for the whole run: fixed, so a result is reproducible. -/
def fixedNow : String := "2026-08-22T00:00:00Z"

def fmtParseError (e : ParseError) : String := s!"{e.msg} (offset {e.pos})"

/-- Parse one data fixture by extension (port of `load_dataset`). -/
def parseDataFile (path text : String) : Except String Dataset :=
  let base := "file://" ++ path
  let ofGraph (r : Except ParseError Graph) : Except String Dataset :=
    match r with
    | .ok g    => .ok { default := g, named := [] }
    | .error e => .error (fmtParseError e)
  if path.endsWith ".nt" then ofGraph (parseNTriples text .rdf11)
  else if path.endsWith ".nq" then (parseNQuads text .rdf11).mapError fmtParseError
  else if path.endsWith ".trig" then (parseTriG text (some base) .rdf11).mapError fmtParseError
  else if path.endsWith ".rdf" then
    match RdfXml.parseRdfXml text (some base) with
    | .ok g    => .ok { default := g, named := [] }
    | .error e => .error s!"{e}"
  else ofGraph (parseTurtle text (some base) .rdf11)

/-- Merge two datasets: default graphs by union, named graphs
appended (a later `qt:graphData` binding wins a name collision by
coming after, as in the F* runner). -/
def mergeDatasets (a b : Dataset) : Dataset :=
  { default := Graph.union a.default b.default, named := a.named ++ b.named }

/-- Read and parse every fixture of a test. `.error o` carries the
outcome to report (skip for a missing file, fail for a parse error). -/
def loadFixtures (tc : TestCase) : IO (Except Outcome (Dataset × List (Iri × Graph))) := do
  let mut ds : Dataset := Dataset.empty
  for df in tc.dataFiles do
    match ← readOpt df with
    | none      => return .error (.skip s!"file missing: {df}")
    | some text =>
      match parseDataFile df text with
      | .error e => return .error (.fail s!"data parse error in {basename df}: {e}")
      | .ok d    => ds := mergeDatasets ds d
  for (iri, path) in tc.graphData do
    match ← readOpt path with
    | none      => return .error (.skip s!"file missing: {path}")
    | some text =>
      match parseDataFile path text with
      | .error e => return .error (.fail s!"graph data parse error in {basename path}: {e}")
      | .ok d    =>
        if h : isIri iri = true then
          ds := { ds with named := ds.named ++ [{ name := .iri ⟨iri, h⟩, graph := d.default }] }
        else return .error (.fail s!"qt:graphData name is not an IRI: {iri}")
  let mut services : List (Iri × Graph) := []
  for (endpoint, path) in tc.serviceData do
    match ← readOpt path with
    | none      => return .error (.skip s!"file missing: {path}")
    | some text =>
      match parseDataFile path text with
      | .error e => return .error (.fail s!"service data parse error in {basename path}: {e}")
      | .ok d    => services := services ++ [(endpoint, d.default)]
  return .ok (ds, services)

/-- What an expected-result file decodes to. -/
inductive Expected where
  | rows    (rows : List Binding) (csv : Bool)
  | boolean (b : Bool)
  | graph   (g : Graph)

/-- Decode the expected file by extension (the `.srx/.srj/.tsv/.csv`
and `.ttl` branches of `run_query_eval_test`). -/
def parseExpected (rf text : String) : Except String Expected :=
  let ofResult (label : String) (csv : Bool) (r : Except ResultsError QueryResult) :
      Except String Expected :=
    match r with
    | .ok (.bindings _ rows) => .ok (.rows rows csv)
    | .ok (.boolean b)       => .ok (.boolean b)
    | .error e               => .error s!"{label}: {e}"
  if rf.endsWith ".srx" then ofResult "SRX" false (parseSrx text)
  else if rf.endsWith ".srj" then ofResult "SRJ" false (parseSrj text)
  else if rf.endsWith ".tsv" then ofResult "TSV" false (parseTsv text)
  else if rf.endsWith ".csv" then ofResult "CSV" true (parseCsv text)
  else if rf.endsWith ".ttl" then
    match parseTurtle text (some ("file://" ++ rf)) .rdf11 with
    | .error e => .error s!"Turtle: {fmtParseError e}"
    | .ok g    =>
      if isRsResultSet g then
        match decodeRsResultSet g with
        | some (_, rows) => .ok (.rows rows false)
        | none           => .error "rs:ResultSet typed but no result-set subject"
      else .ok (.graph g)
  else .error s!"unknown result format: {basename rf}"

/-- The FAIL text for a SELECT mismatch: counts plus the expected rows
no actual row matches (the F* runner's `UNMATCHED` lines). -/
def selectMismatch (csv : Bool) (expected actual : List Binding) : String :=
  let cmp := if csv then termMatchCsv else termMatchStrict
  let unmatched := unmatchedRows cmp expected actual
  let extra := unmatchedRows (fun m a e => cmp m e a) actual expected
  let showRows (rs : List Binding) : String :=
    String.intercalate " | " (rs.take 5 |>.map (fun r => "[" ++ rowShow r ++ "]"))
  let base := s!"results mismatch: expected {expected.length} rows, got {actual.length}"
  (if unmatched.isEmpty then base else base ++ "; unmatched expected: " ++ showRows unmatched) ++
  (if extra.isEmpty then "" else "; unmatched actual: " ++ showRows extra)

/-- One `QueryEvaluationTest` / `CSVResultFormatTest`. -/
def runQueryEvaluation (tc : TestCase) : IO RunResult := do
  if !tc.entailmentRegimes.isEmpty then
    return .ofOutcome (.unsupported
      s!"entailment regime {String.intercalate "/" tc.entailmentRegimes}")
  let some qf := tc.queryFile
    | return .ofOutcome (.skip "mf:action carries no qt:query")
  let some qtext ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  match parseSparql qtext (some ("file://" ++ qf)) with
  | .error e => return .ofOutcome (.fail s!"SPARQL parse: {fmtParseError e}")
  | .ok q =>
  match ← loadFixtures tc with
  | .error o => return .ofOutcome o
  | .ok (ds, services) =>
  let some rf := tc.resultFile
    | return .ofOutcome (.skip "no mf:result")
  let some rtext ← readOpt rf
    | return .ofOutcome (.skip s!"result file missing: {rf}")
  match parseExpected rf rtext with
  | .error e => return .ofOutcome (.fail s!"expected-result parse error: {e}")
  | .ok expected =>
  -- EXISTS needs no hook: `evalSelect` / `evalAsk` / `evalConstruct`
  -- install the query's dataset in the environment themselves.
  let env : EvalEnv := { now := some fixedNow, services := services, base := q.base }
  let ordered := q.modifier.orderBy.isSome
  match q.form, expected with
  | .select _, .rows erows csv =>
      let arows := (evalSelect env ds q).2
      let n := erows.length + arows.length
      return (match compareSelectRows ordered csv erows arows with
        | .equal    => { outcome := .pass, rowsCompared := n }
        | .notEqual => { outcome := .fail (selectMismatch csv erows arows), rowsCompared := n }
        | .budgetExceeded =>
            { outcome := .fail s!"solution-bijection budget exceeded ({erows.length} expected rows, {arows.length} actual)",
              budgetExceeded := true, rowsCompared := n })
  | .ask, .boolean b =>
      let a := evalAsk env ds q
      return (if a == b then { outcome := .pass, rowsCompared := 1 }
              else { outcome := .fail s!"ASK boolean mismatch: expected {b}, got {a}", rowsCompared := 1 })
  | .construct _, .graph g =>
      let got := evalConstruct env ds q
      let r := isoResult
        s!"CONSTRUCT graph not isomorphic to the expected one (got {got.length} triples, expected {g.length})"
        (Graph.isomorphicOutcome got g)
      return { r with triplesCompared := got.length + g.length }
  | .describe _, _ =>
      return .ofOutcome (.unsupported "DESCRIBE (the Lean port fixes no description policy)")
  | .select _, .boolean _ => return .ofOutcome (.fail "expected file is a boolean result but the query is SELECT")
  | .select _, .graph _   => return .ofOutcome (.fail "expected file is a graph but the query is SELECT")
  | .ask, _               => return .ofOutcome (.fail "expected file is not a boolean result but the query is ASK")
  | .construct _, _       => return .ofOutcome (.fail "expected file is not a graph but the query is CONSTRUCT")

/-- `PositiveSyntaxTest11` / `NegativeSyntaxTest11`: the query file is
`mf:action` itself (a file IRI), parsed with its own `file:` IRI as
BASE. -/
def runSyntaxTest (positive : Bool) (tc : TestCase) : IO RunResult := do
  let some qf := (match tc.action with | some a => some a | none => tc.queryFile)
    | return .ofOutcome (.skip "no query file in mf:action")
  let some text ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  let res := parseSparql text (some ("file://" ++ qf))
  return .ofOutcome (
    if positive then
      match res with
      | .ok _    => .pass
      | .error e => .fail s!"should parse but was rejected: {fmtParseError e}"
    else
      match res with
      | .error _ => .pass
      | .ok _    => .fail "should reject but parsed OK")

/-! ## SPARQL 1.1 Update — port of the `UpdateEvaluationTest` /
`PositiveUpdateSyntaxTest11` / `NegativeUpdateSyntaxTest11` arms of
`w3c_runner.ml` (~lines 2217–2312). Rules, in the F* runner's order:

  1. the request is `ut:request`, parsed with its own `file:` IRI as
     BASE; a parse failure is a FAIL (named);
  2. a request containing a non-SILENT `LOAD` is a SKIP with that
     reason (no document fetch; `LOAD SILENT` is the §3.1.4 identity
     and runs);
  3. the input store is `ut:data` (default graph; a `.trig` / `.nq`
     fixture keeps its named graphs) plus `ut:graphData` as named
     graphs; the expected store is built the same way from
     `mf:result`; a missing file is a SKIP (path);
  4. `applyUpdateIn` runs the request; an `UpdateError` is a FAIL
     carrying the error;
  5. the two stores are compared by dataset isomorphism
     (`Dataset.isomorphicOutcome`) after dropping EMPTY named graphs
     on both sides — the F* comparison canonicalises to N-Quads, which
     cannot represent an empty graph, while the Lean isomorphism
     matches graph NAMES, so a slot left by `CLEAR` / `CREATE` would
     otherwise count as a difference the F* does not see. -/

/-- Read `data` files into the default graph and `graphData` files
into named graphs (the F* `load_dataset` + `load_triples` fold). -/
def loadUpdateStore (dataFiles : List String) (graphData : List (String × String)) :
    IO (Except Outcome Dataset) := do
  let mut ds : Dataset := Dataset.empty
  for df in dataFiles do
    match ← readOpt df with
    | none      => return .error (.skip s!"file missing: {df}")
    | some text =>
      match parseDataFile df text with
      | .error e => return .error (.fail s!"data parse error in {basename df}: {e}")
      | .ok d    => ds := mergeDatasets ds d
  for (iri, path) in graphData do
    match ← readOpt path with
    | none      => return .error (.skip s!"file missing: {path}")
    | some text =>
      match parseDataFile path text with
      | .error e => return .error (.fail s!"graph data parse error in {basename path}: {e}")
      | .ok d    =>
        if h : isIri iri = true then
          ds := { ds with named := ds.named ++ [{ name := .iri ⟨iri, h⟩, graph := d.default }] }
        else return .error (.fail s!"ut:graphData label is not an IRI: {iri}")
  return .ok ds

/-- Named-graph slots holding no triple are invisible to a quad-level
comparison (see the section banner). -/
def dropEmptyNamed (ds : Dataset) : Dataset :=
  { ds with named := ds.named.filter (fun ng => !ng.graph.isEmpty) }

def quadCount (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (fun ng => ng.graph.length)).sum

/-- One `UpdateEvaluationTest`. -/
def runUpdateEvaluation (tc : TestCase) : IO RunResult := do
  let some qf := tc.queryFile
    | return .ofOutcome (.skip "mf:action carries no ut:request")
  let some text ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  match parseSparqlUpdate text (some ("file://" ++ qf)) with
  | .error e => return .ofOutcome (.fail s!"Update parse: {fmtParseError e}")
  | .ok u =>
  if u.hasNonSilentLoad then
    return .ofOutcome (.skip "non-silent LOAD not yet implemented (no HTTP fetch)")
  match ← loadUpdateStore tc.dataFiles tc.graphData with
  | .error o => return .ofOutcome o
  | .ok input =>
  match ← loadUpdateStore tc.updateResultData tc.updateResultGraphData with
  | .error o => return .ofOutcome o
  | .ok expected =>
  let env : EvalEnv := { now := some fixedNow, base := u.base }
  match applyUpdateIn env input u with
  | .error e => return .ofOutcome (.fail s!"update raised an error: {e}")
  | .ok got =>
    let got' := dropEmptyNamed got
    let exp' := dropEmptyNamed expected
    let r := isoResult
      s!"UPDATE result mismatch: got {got.default.length} default-graph triples and {got'.named.length} non-empty named graphs, expected {expected.default.length} and {exp'.named.length}"
      (Dataset.isomorphicOutcome got' exp')
    return { r with triplesCompared := quadCount got' + quadCount exp' }

/-- `PositiveUpdateSyntaxTest11` / `NegativeUpdateSyntaxTest11`: the
request file is `mf:action` itself, parsed with its own `file:` IRI
as BASE. -/
def runUpdateSyntaxTest (positive : Bool) (tc : TestCase) : IO RunResult := do
  let some qf := (match tc.action with | some a => some a | none => tc.queryFile)
    | return .ofOutcome (.skip "no update file in mf:action")
  let some text ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  let res := parseSparqlUpdate text (some ("file://" ++ qf))
  return .ofOutcome (
    if positive then
      match res with
      | .ok _    => .pass
      | .error e => .fail s!"should parse but was rejected: {fmtParseError e}"
    else
      match res with
      | .error _ => .pass
      | .ok _    => .fail "should reject but parsed OK")

/-! ## The dispatcher -/

/-- Run one test case. `assumedBase` is the suite's
`mf:assumedTestBase`; `manifestDir` the directory the manifest sits
in; `gspStore` the Graph Store the http-rdf-update entries share
(one per manifest — see `Harness/ProtocolRun.lean`). -/
def runTest (assumedBase : Option String) (manifestDir : String)
    (gspStore : IO.Ref GraphStore.GraphStore) (tc : TestCase) :
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

  /- ### SPARQL 1.1 Query (sparql11 suites) — see the section above. -/
  | "QueryEvaluationTest" | "CSVResultFormatTest" => runQueryEvaluation tc
  | "PositiveSyntaxTest11" | "PositiveSyntaxTest" => runSyntaxTest true tc
  | "NegativeSyntaxTest11" | "NegativeSyntaxTest" => runSyntaxTest false tc

  /- ### SPARQL 1.1 Update (sparql11 suites) — see the section above. -/
  | "UpdateEvaluationTest"       => runUpdateEvaluation tc
  | "PositiveUpdateSyntaxTest11" => runUpdateSyntaxTest true tc
  | "NegativeUpdateSyntaxTest11" => runUpdateSyntaxTest false tc


  /- ### SPARQL 1.1 Protocol, Graph Store HTTP Protocol, Service
     Description — request/response decoding over the entry's
     `rdfs:comment`; see `Harness/ProtocolRun.lean`. -/
  | "ProtocolTest" => return .ofOutcome (← runProtocolTest tc)
  | "GraphStoreProtocolTest" => do
      let (o, seeded) ← runGspTest gspStore tc
      return { outcome := o, gspSeeded := seeded }
  | "ServiceDescriptionTest" => return .ofOutcome (← runServiceDescriptionTest tc)

  /- ### Any other type — named, counted, never passed. -/
  | other => return .ofOutcome (.unsupported other)

end Harness
