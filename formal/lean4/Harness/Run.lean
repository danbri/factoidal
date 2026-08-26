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
    (request/response decoding over `rdfs:comment`, no HTTP server).
    An entailment-regime evaluation test runs when the regime list
    names RDFS, RDF or D (the closure of `RDF/Entailment.lean` is
    applied to the data before evaluation — see "Entailment regimes"
    below), OWL-Direct / OWL-RDF-Based (OWL 2 RL closure + the OWL
    query path), or RIF (premise saturation); any other regime name
    is `unsupported entailment regime <R>`. The rdf-mt
    `PositiveEntailmentTest` / `NegativeEntailmentTest` types run
    through the same module (see "RDF 1.1 Semantics").

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
import L4Factoidal.RDF.Entailment
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsCsvTsv
import L4Factoidal.OWL.QueryEval
import L4Factoidal.RIF.Saturate

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

/-- Parse one data fixture by extension (port of `load_dataset`).
`mode` is the suite's RDF version: the sparql12 suites' fixtures carry
triple terms and reifiers, which `.rdf11` rejects. -/
def parseDataFile (path text : String) (mode : Mode := .rdf11) : Except String Dataset :=
  let base := "file://" ++ path
  let ofGraph (r : Except ParseError Graph) : Except String Dataset :=
    match r with
    | .ok g    => .ok { default := g, named := [] }
    | .error e => .error (fmtParseError e)
  if path.endsWith ".nt" then ofGraph (parseNTriples text mode)
  else if path.endsWith ".nq" then (parseNQuads text mode).mapError fmtParseError
  else if path.endsWith ".trig" then (parseTriG text (some base) mode).mapError fmtParseError
  else if path.endsWith ".rdf" then
    match RdfXml.parseRdfXml text (some base) with
    | .ok g    => .ok { default := g, named := [] }
    | .error e => .error s!"{e}"
  else ofGraph (parseTurtle text (some base) mode)

/-- Merge two datasets: default graphs by union, named graphs
appended (a later `qt:graphData` binding wins a name collision by
coming after, as in the F* runner). -/
def mergeDatasets (a b : Dataset) : Dataset :=
  { default := Graph.union a.default b.default, named := a.named ++ b.named }

/-- Read and parse every fixture of a test. `.error o` carries the
outcome to report (skip for a missing file, fail for a parse error). -/
def loadFixtures (tc : TestCase) (mode : Mode := .rdf11) :
    IO (Except Outcome (Dataset × List (Iri × Graph))) := do
  let mut ds : Dataset := Dataset.empty
  for df in tc.dataFiles do
    match ← readOpt df with
    | none      => return .error (.skip s!"file missing: {df}")
    | some text =>
      match parseDataFile df text mode with
      | .error e => return .error (.fail s!"data parse error in {basename df}: {e}")
      | .ok d    => ds := mergeDatasets ds d
  for (iri, path) in tc.graphData do
    match ← readOpt path with
    | none      => return .error (.skip s!"file missing: {path}")
    | some text =>
      match parseDataFile path text mode with
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
      match parseDataFile path text mode with
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
def parseExpected (rf text : String) (mode : Mode := .rdf11) : Except String Expected :=
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
    match parseTurtle text (some ("file://" ++ rf)) mode with
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

/-! ## Entailment regimes — shared by the sparql11 `entailment` suite
and the rdf-mt suite

The F* runner's `apply_entailment_regime` / `run_query_eval_test`
regime branch, reproduced with the regimes `RDF/Entailment.lean`
decides. Picking one regime from a manifest's list: the F* runner
prefers OWL-RDF-Based, then OWL-Direct, RDFS, RDF, D; this tree has no
OWL regime, so a list is read as RDFS > RDF > D and a list naming none
of those (OWL-only, RIF) is unsupported, with the names. -/

/-- The regime a `sd:entailmentRegime` list selects. -/
def pickRegime (names : List String) : Option Regime :=
  if names.contains "RDFS" then some .rdfs
  else if names.contains "RDF" then some .rdf
  else if names.contains "D" then some .d
  else none

/-- The `rdf:_n` slice for a graph: `rdf:_1` plus those it mentions. -/
def cmpSlice (g : Graph) : List WfIri :=
  (L4Factoidal.RDFS.containerMembershipIn g).foldl
    (fun acc i => if acc.contains i then acc else acc ++ [i]) [L4Factoidal.RDFS.rdf1]

/-- Close every graph of a dataset under the regime (the F* runner
closes the default graph and each `qt:graphData` graph alike). -/
def closeDataset (r : Regime) (D : List WfIri) (ds : Dataset) : Dataset :=
  { default := r.closure D (cmpSlice ds.default) ds.default,
    named := ds.named.map (fun ng => { ng with graph := r.closure D (cmpSlice ng.graph) ng.graph }) }

/-- The datatype map a test asks for, as well-formed IRIs, refused
(with the name) when it lists a datatype `RDF/Datatypes.lean` does not
model — a recognised-but-unmodelled datatype would make "well-formed"
a guess. The minimal `D` (`xsd:string`, `rdf:langString`) is added. -/
def recognizedDatatypesOf (names : List String) : Except String (List WfIri) := do
  let mut ds : List WfIri := []
  for n in names do
    if h : isIri n = true then
      let d : WfIri := ⟨n, h⟩
      if !modelledDatatypes.contains d then
        throw s!"recognized datatype {n} is not modelled by RDF/Datatypes.lean"
      ds := ds ++ [d]
    else throw s!"recognized datatype is not an IRI: {n}"
  return withMinimalD ds

/-! ## The RIF entailment regime (sparql11 entailment rif01/03/04/06)

Mirror of the F* runner's consumer-side glue
(`bin/w3c-runner/w3c_runner.ml`, `rif_rules_path_for` /
`rif_load_imports` / the `"RIF"` regime branch): the SPARQL test
suite does not bundle the RIF-XML rule documents, so they are
resolved by `mf:name` against the vendored mirror under
`third_party/testing/rif/tc/`. Saturation itself is library code
(`L4Factoidal.RIF.Saturate`). -/

/-- The vendored RIF Test Cases mirror, from any supported working
directory. -/
def rifTcBase : IO (Option String) := do
  let candidates := [
    "third_party/testing/rif/tc",
    "../../third_party/testing/rif/tc",
    "../../../third_party/testing/rif/tc" ]
  candidates.findM? (fun c => System.FilePath.isDir (System.FilePath.mk c))

/-- Test directory + premise filename by `mf:name` — the four-entry
table is exhaustive for the SPARQL 1.1 entailment manifest. -/
def rifPremiseFor (name : String) : Option (String × String) :=
  if name == "RIF Logical Entailment (referencing RIF XML)" then
    some ("Logical_entailment_referencing_RIF_XML", "rif01-premise.rif")
  else if name == "RIF Core WG tests: Frames" then
    some ("Frames", "Frames-premise.rif")
  else if name == "RIF Core WG tests: Modeling Brain Anatomy" then
    some ("Modeling_Brain_Anatomy", "Modeling_Brain_Anatomy-premise.rif")
  else if name == "RIF Core WG tests: RDF Combination Blank Node" then
    some ("RDF_Combination_Blank_Node", "RDF_Combination_Blank_Node-premise.rif")
  else none

/-- Drop the `<!DOCTYPE … ]>` block and inline the `<!ENTITY n "v">`
substitutions it declares (`&n;` → `v`). The vendored premises use
entity references for the RIF/XSD/RDF namespaces; the XML parser
takes the document without its DTD. -/
def rifXmlPreprocess (raw : String) : String :=
  let replaceAll (s pat rep : String) : String :=
    String.intercalate rep (s.splitOn pat)
  match raw.splitOn "<!DOCTYPE" with
  | [only] => only
  | before :: rest =>
      let restStr := String.intercalate "<!DOCTYPE" rest
      match restStr.splitOn "]>" with
      | inner :: after =>
          let doc := before ++ String.intercalate "]>" after
          let ents := ((inner.splitOn "<!ENTITY").drop 1).filterMap (fun e =>
            match e.splitOn "\"" with
            | namePart :: value :: _ => some (namePart.trim, value)
            | _ => none)
          ents.foldl (fun acc (n, v) => replaceAll acc ("&" ++ n ++ ";") v) doc
      | [] => raw
  | [] => raw

/-- Load one resolved import file by extension (`.rdf` RDF/XML,
otherwise Turtle) and close it under the profile its `Import` names —
the F* `materialise_import_graph` dispatch. -/
def rifLoadImport (path : String) (profile : Option String) : IO Graph := do
  let some text ← readOpt path | return []
  let g := if path.endsWith ".rdf"
           then (L4Factoidal.Syntax.RdfXml.parseRdfXml text (some ("file://" ++ path))).toOption.getD []
           else (parseTurtle text (some ("file://" ++ path))).toOption.getD []
  let entNs := "http://www.w3.org/ns/entailment/"
  return (match profile with
    | some p =>
        if p == entNs ++ "RDF" || p == entNs ++ "RDFS" then
          L4Factoidal.RDFS.closureFix g
        else if (p.splitOn "OWL").length > 1 then
          L4Factoidal.OWL.RL.closureFix g
        else g
    | none => g)

/-- Resolve one `Import` location URL to a local file in `dir`:
basename, tried bare, then `.rdf`, then `.ttl`. -/
def rifResolveImport (dir url : String) : IO (Option String) := do
  let bn := (url.splitOn "/").getLast?.getD url
  let candidates :=
    if bn.endsWith ".rdf" || bn.endsWith ".ttl" then [bn]
    else [bn ++ ".rdf", bn ++ ".ttl", bn]
  let found ← candidates.findM? (fun c =>
    System.FilePath.pathExists (System.FilePath.mk (dir ++ "/" ++ c)))
  return found.map (fun c => dir ++ "/" ++ c)

/-- The RIF regime's dataset: premise rules + imports + saturation.
`.error` carries the outcome when the premise cannot be used. -/
def rifSaturateDataset (tc : TestCase) (ds : Dataset) :
    IO (Except Outcome Dataset) := do
  let some base ← rifTcBase
    | return .error (.unsupported "RIF premise mirror not vendored (third_party/testing/rif/tc)")
  let some (sub, fname) := rifPremiseFor tc.name
    | return .error (.unsupported s!"no vendored RIF rules for test {tc.name}")
  let dir := base ++ "/" ++ sub
  let some raw ← readOpt (dir ++ "/" ++ fname)
    | return .error (.unsupported s!"RIF premise missing: {dir}/{fname}")
  let xml := rifXmlPreprocess raw
  let some doc := L4Factoidal.RIF.Xml.parseRifProgram xml
    | return .error (.fail "RIF-XML premise did not parse")
  let mut imported : Graph := []
  for (url, profile) in doc.imports do
    match ← rifResolveImport dir url with
    | some path => imported := imported ++ (← rifLoadImport path profile)
    | none => pure ()
  let merged := ds.default ++ imported
  let saturated := L4Factoidal.RIF.Saturate.saturateGraph "rules" doc.rules merged
  return .ok { ds with default := saturated }

/-- One `QueryEvaluationTest` / `CSVResultFormatTest`. `mode` is the
suite's RDF version; a `.rdf12` suite parses its queries with the
SPARQL 1.2 grammar. -/
def runQueryEvaluation (tc : TestCase) (mode : Mode := .rdf11) : IO RunResult := do
  -- Entailment-regime tests: pick the regime now; the closure is
  -- applied to the fixtures once they are loaded.
  -- The F* runner's preference order puts the OWL regimes first.
  -- OWL-Direct and OWL-RDF-Based both evaluate as: OWL 2 RL closure of
  -- every fixture graph, then the OWL query path (rewrite +
  -- query-time canonical materialisation, `OWL/QueryEval.lean`).
  let owlRegime : Bool :=
    tc.entailmentRegimes.contains "OWL-RDF-Based"
      || tc.entailmentRegimes.contains "OWL-Direct"
  let rifRegime : Bool := tc.entailmentRegimes.contains "RIF"
  let regime? : Option Regime ←
    if tc.entailmentRegimes.isEmpty || owlRegime || rifRegime
      then pure none
    else match pickRegime tc.entailmentRegimes with
      | some r => pure (some r)
      | none => return .ofOutcome (.unsupported
          s!"entailment regime {String.intercalate "/" tc.entailmentRegimes}")
  let some qf := tc.queryFile
    | return .ofOutcome (.skip "mf:action carries no qt:query")
  let some qtext ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  let sv : SparqlVersion := if mode == .rdf12 then .v12 else .v11
  match parseSparql qtext (some ("file://" ++ qf)) sv with
  | .error e => return .ofOutcome (.fail s!"SPARQL parse: {fmtParseError e}")
  | .ok q =>
  match ← loadFixtures tc mode with
  | .error o => return .ofOutcome o
  | .ok (ds0, services) =>
  -- SPARQL 1.1 Entailment Regimes: answers are simple-entailment
  -- answers over the regime's closure of the active graph, with the
  -- minimal datatype map (the suite names no recognised datatypes).
  let dsE : Except Outcome Dataset ←
    if rifRegime then rifSaturateDataset tc ds0
    else pure (.ok (
      if owlRegime then
        { default := L4Factoidal.OWL.RL.closureFix ds0.default,
          named := ds0.named.map (fun ng =>
            { ng with graph := L4Factoidal.OWL.RL.closureFix ng.graph }) }
      else match regime? with
      | some r => closeDataset r (withMinimalD []) ds0
      | none   => ds0))
  let ds ← match dsE with
    | .error o => return .ofOutcome o
    | .ok d => pure d
  -- SPARQL 1.1 Entailment Regimes: an answer may not bind a blank node
  -- the QUERIED graph does not contain (the closure mints witness
  -- nodes, and those are not legal answer terms). The original
  -- dataset's blank-node ids are the allowed set.
  let origBnodes : List BNodeId :=
    let ofGraph (g : Graph) : List BNodeId :=
      g.flatMap (fun t =>
        (match t.s with | .bnode b => [b] | _ => []) ++
        (match t.o with | .bnode b => [b] | _ => []))
    ofGraph ds0.default ++ ds0.named.flatMap (fun ng => ofGraph ng.graph)
  -- OWL Direct Semantics additionally restricts a variable standing in
  -- a CLASS position (object of rdf:type, either side of
  -- rdfs:subClassOf, object of rdfs:domain / rdfs:range /
  -- owl:equivalentClass) to CLASS NAMES: an anonymous class expression
  -- is not in the ontology's signature, so a blank node is not a legal
  -- binding there. Individual positions keep their blank nodes — the
  -- suite's own `owlds02` ("bnodes are not existentials with answer")
  -- expects one.
  let classPosVars : List VarName :=
    (L4Factoidal.OWL.QueryMaterialise.bgpsOf q.pattern).flatMap (fun b =>
      b.flatMap (fun tp =>
        match tp.p with
        | .iri pi =>
            (if pi == L4Factoidal.OWL.RL.rdfType
                || pi == L4Factoidal.OWL.RL.rdfsDomain
                || pi == L4Factoidal.OWL.RL.rdfsRange
                || pi == L4Factoidal.OWL.RL.owlEquivalentClass then
               match tp.o with | .var v => [v] | _ => []
             else []) ++
            (if pi == L4Factoidal.OWL.RL.rdfsSubClassOf then
               (match tp.s with | .var v => [v] | _ => []) ++
               (match tp.o with | .var v => [v] | _ => [])
             else [])
        | _ => []))
  let rowAllowed (row : List (VarName × Term)) : Bool :=
    row.all (fun vt => match vt.2 with
      | .bnode b => origBnodes.contains b && !classPosVars.contains vt.1
      | _ => true)
  let some rf := tc.resultFile
    | return .ofOutcome (.skip "no mf:result")
  let some rtext ← readOpt rf
    | return .ofOutcome (.skip s!"result file missing: {rf}")
  match parseExpected rf rtext mode with
  | .error e => return .ofOutcome (.fail s!"expected-result parse error: {e}")
  | .ok expected =>
  -- EXISTS needs no hook: `evalSelect` / `evalAsk` / `evalConstruct`
  -- install the query's dataset in the environment themselves.
  let env : EvalEnv := { now := some fixedNow, services := services, base := q.base }
  let ordered := q.modifier.orderBy.isSome
  match q.form, expected with
  | .select _, .rows erows csv =>
      let arows := if owlRegime then
                     (L4Factoidal.OWL.QueryEval.evalSelectOwl env ds q).filter rowAllowed
                   else (evalSelect env ds q).2
      let n := erows.length + arows.length
      return (match compareSelectRows ordered csv erows arows with
        | .equal    => { outcome := .pass, rowsCompared := n }
        | .notEqual => { outcome := .fail (selectMismatch csv erows arows), rowsCompared := n }
        | .budgetExceeded =>
            { outcome := .fail s!"solution-bijection budget exceeded ({erows.length} expected rows, {arows.length} actual)",
              budgetExceeded := true, rowsCompared := n })
  | .ask, .boolean b =>
      let a := if owlRegime then L4Factoidal.OWL.QueryEval.evalAskOwl env ds q
               else evalAsk env ds q
      return (if a == b then { outcome := .pass, rowsCompared := 1 }
              else { outcome := .fail s!"ASK boolean mismatch: expected {b}, got {a}", rowsCompared := 1 })
  | .construct _, .graph g =>
      let got := if owlRegime then L4Factoidal.OWL.QueryEval.evalConstructOwl env ds q
                 else evalConstruct env ds q
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
def runSyntaxTest (positive : Bool) (tc : TestCase) (mode : Mode := .rdf11) :
    IO RunResult := do
  let some qf := (match tc.action with | some a => some a | none => tc.queryFile)
    | return .ofOutcome (.skip "no query file in mf:action")
  let some text ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  let res := parseSparql text (some ("file://" ++ qf))
              (if mode == .rdf12 then .v12 else .v11)
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
def loadUpdateStore (dataFiles : List String) (graphData : List (String × String))
    (mode : Mode := .rdf11) : IO (Except Outcome Dataset) := do
  let mut ds : Dataset := Dataset.empty
  for df in dataFiles do
    match ← readOpt df with
    | none      => return .error (.skip s!"file missing: {df}")
    | some text =>
      match parseDataFile df text mode with
      | .error e => return .error (.fail s!"data parse error in {basename df}: {e}")
      | .ok d    => ds := mergeDatasets ds d
  for (iri, path) in graphData do
    match ← readOpt path with
    | none      => return .error (.skip s!"file missing: {path}")
    | some text =>
      match parseDataFile path text mode with
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
def runUpdateEvaluation (tc : TestCase) (mode : Mode := .rdf11) : IO RunResult := do
  let some qf := tc.queryFile
    | return .ofOutcome (.skip "mf:action carries no ut:request")
  let some text ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  match parseSparqlUpdate text (some ("file://" ++ qf))
          (if mode == .rdf12 then .v12 else .v11) with
  | .error e => return .ofOutcome (.fail s!"Update parse: {fmtParseError e}")
  | .ok u =>
  if u.hasNonSilentLoad then
    return .ofOutcome (.skip "non-silent LOAD not yet implemented (no HTTP fetch)")
  match ← loadUpdateStore tc.dataFiles tc.graphData mode with
  | .error o => return .ofOutcome o
  | .ok input =>
  match ← loadUpdateStore tc.updateResultData tc.updateResultGraphData mode with
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
def runUpdateSyntaxTest (positive : Bool) (tc : TestCase) (mode : Mode := .rdf11) :
    IO RunResult := do
  let some qf := (match tc.action with | some a => some a | none => tc.queryFile)
    | return .ofOutcome (.skip "no update file in mf:action")
  let some text ← readOpt qf
    | return .ofOutcome (.skip s!"file missing: {qf}")
  let res := parseSparqlUpdate text (some ("file://" ++ qf))
              (if mode == .rdf12 then .v12 else .v11)
  return .ofOutcome (
    if positive then
      match res with
      | .ok _    => .pass
      | .error e => .fail s!"should parse but was rejected: {fmtParseError e}"
    else
      match res with
      | .error _ => .pass
      | .ok _    => .fail "should reject but parsed OK")

/-! ## RDF 1.1 Semantics — the rdf-mt suite

Port of the F* runner's `PositiveEntailmentTest` /
`NegativeEntailmentTest` arms (`run_rdf_test`, ~lines 2853–2936):

  1. `mf:entailmentRegime` is `"simple"`, `"RDF"` or `"RDFS"` (the
     suite uses no other); `mf:recognizedDatatypes` is the datatype
     map, refused by name when it lists a datatype this tree does not
     model (the F* runner reports `rdf:XMLLiteral` as unsupported
     there; here it is modelled, via the XML parser);
  2. the action graph is parsed by extension (`.nt` N-Triples, else
     Turtle with the file's own `file:` IRI as base) and closed under
     the regime;
  3. `mf:result false`: a Positive test passes iff the closure is
     D-INCONSISTENT, a Negative test iff it is CONSISTENT (rdf-mt
     README: "for tests that have false as output …");
  4. otherwise the result graph is parsed the same way and
     `regimeEntails` decides: Positive passes iff it entails, Negative
     iff it does not. An inconsistent action graph entails everything
     (RDF 1.1 Semantics §5.1). -/

/-- Parse an rdf-mt fixture by extension. `mode` is the suite's RDF
version (see `runTest`): the rdf12 `rdf-semantics` fixtures carry
triple terms and reifier shorthand, which `.rdf11` rejects. -/
def parseEntailmentGraph (mode : Mode) (path text : String) : Except String Graph :=
  let r := if path.endsWith ".nt" then parseNTriples text mode
           else parseTurtle text (some ("file://" ++ path)) mode
  r.mapError fmtParseError

/-- One `PositiveEntailmentTest` (`positive = true`) or
`NegativeEntailmentTest`. -/
def runEntailmentTest (mode : Mode) (positive : Bool) (tc : TestCase) : IO RunResult := do
  let regimeName := tc.entailmentRegime.getD "simple"
  let some regime := Regime.ofName? regimeName
    | return .ofOutcome (.unsupported s!"entailment regime {regimeName}")
  let D ← match recognizedDatatypesOf tc.recognizedDatatypes with
    | .ok d => pure d
    | .error e => return .ofOutcome (.unsupported e)
  let some af := tc.action
    | return .ofOutcome (.skip "mf:action is not a file IRI")
  let some atext ← readOpt af
    | return .ofOutcome (.skip s!"file missing: {af}")
  match parseEntailmentGraph mode af atext with
  | .error e => return .ofOutcome (.fail s!"action parse error in {basename af}: {e}")
  | .ok action =>
  let kind := if positive then "Positive" else "Negative"
  if tc.resultFalse then
    -- Consistency: Positive expects an inconsistent action graph,
    -- Negative a consistent one.
    let inconsistent := regimeInconsistent regime D action
    let outcome :=
      if positive then
        (if inconsistent then Outcome.pass
         else .fail s!"expected a D-inconsistent action graph ({regimeName}, recognized {String.intercalate ", " tc.recognizedDatatypes}) but no clash was found")
      else
        (if inconsistent then Outcome.fail s!"action graph is D-inconsistent but the {kind} test expects it consistent"
         else .pass)
    return { outcome, triplesCompared := action.length }
  else
  let some rf := tc.resultFile
    | return .ofOutcome (.skip "no mf:result")
  let some rtext ← readOpt rf
    | return .ofOutcome (.skip s!"result file missing: {rf}")
  match parseEntailmentGraph mode rf rtext with
  | .error e => return .ofOutcome (.fail s!"result parse error in {basename rf}: {e}")
  | .ok expected =>
  let entails := regimeEntails regime D action expected
  let n := action.length + expected.length
  let outcome :=
    if positive then
      (if entails then Outcome.pass
       else .fail s!"should entail under {regimeName} but does not (action {action.length} triples, result {expected.length})")
    else
      (if entails then Outcome.fail s!"should NOT entail under {regimeName} but does"
       else .pass)
  return { outcome, triplesCompared := n }

/-! ## The dispatcher -/

/-! ## RDF version (`mode`)

The F* runner picks the RDF version with a CLI FLAG: `--rdf` runs the
`rdf11/` suites through `parse_*_strict`, `--rdf12` /`--rdf12c14n` /
`--rdf12entail` run the `rdf12/` suites through `parse_*_strict_12`
(`bin/w3c-runner/w3c_runner.ml`, the `run_rdf12_test` dispatch and the
`run_rdf12*_mode` branches of `main`). This tree takes manifest PATHS
rather than suite names, so a run may mix the two trees in one
invocation; the version therefore travels with the manifest —
`Harness.Main.modeOfManifest` reads it off `mf:assumedTestBase` (every
rdf12 leaf manifest declares one under `…/rdf/rdf12/…`) and falls back
to the manifest's own path. It is passed in here and used for every
fixture the suite's own format owns.

Under `.rdf12` the same parsers additionally admit the RDF 1.2
productions — triple terms `<<( s p o )>>`, reifiers `<< s p o >>` and
`~`, annotation blocks `{| … |}`, the `VERSION` directive, and base
direction (`"chat"@en--ltr`) — and reject nothing the 1.1 grammar
accepts. Fixtures a suite does NOT own stay at `.rdf11`: the sparql11
`qt:data` files and the rdf-canon `.nq` inputs are RDF 1.1 documents
whatever manifest names them. -/

/-- Run one test case. `mode` is the suite's RDF version (see above);
`assumedBase` is the suite's `mf:assumedTestBase`; `manifestDir` the
directory the manifest sits in; `gspStore` the Graph Store the
http-rdf-update entries share (one per manifest — see
`Harness/ProtocolRun.lean`). -/
def runTest (mode : Mode) (assumedBase : Option String) (manifestDir : String)
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
      match parseNTriples text mode with
      | .ok _    => .pass
      | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestNTriplesNegativeSyntax" =>
    withAction fun _ text => return .ofOutcome (
      match parseNTriples text mode with
      | .error _ => .pass
      | .ok g    => .fail s!"should reject but parsed OK ({g.length} triples)")

  /- ### N-Quads (RDF 1.1 N-Quads §4) -/
  | "TestNQuadsPositiveSyntax" =>
    withAction fun _ text => return .ofOutcome (
      match parseNQuads text mode with
      | .ok _    => .pass
      | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestNQuadsNegativeSyntax" =>
    withAction fun _ text => return .ofOutcome (
      match parseNQuads text mode with
      | .error _ => .pass
      | .ok _    => .fail "should reject but parsed OK")

  /- ### Turtle (RDF 1.1 Turtle §7) -/
  | "TestTurtlePositiveSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTurtle text (some base) mode with
        | .ok _    => .pass
        | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestTurtleNegativeSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTurtle text (some base) mode with
        | .error _ => .pass
        | .ok g    => .fail s!"should reject but parsed OK ({g.length} triples)")
  | "TestTurtleEval" =>
    withActionAndResult fun path text expectedText => do
      let base := fixtureBase assumedBase manifestDir path
      match parseTurtle text (some base) mode with
      | .error e => return .ofOutcome (.fail s!"Turtle parse error: {e.msg} (offset {e.pos})")
      | .ok g =>
        match parseNTriples expectedText mode with
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
        match parseTurtle text (some base) mode with
        | .error _ => .pass
        | .ok g    => if g.isEmpty then .pass
                      else .fail s!"should produce an eval error but succeeded ({g.length} triples)")

  /- ### TriG (RDF 1.1 TriG §6) -/
  | "TestTrigPositiveSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTriG text (some base) mode with
        | .ok _    => .pass
        | .error e => .fail s!"parser rejected input that should parse: {e.msg} (offset {e.pos})")
  | "TestTrigNegativeSyntax" =>
    withAction fun path text => do
      let base := fixtureBase assumedBase manifestDir path
      return .ofOutcome (
        match parseTriG text (some base) mode with
        | .error _ => .pass
        | .ok _    => .fail "should reject but parsed OK")
  | "TestTrigEval" =>
    withActionAndResult fun path text expectedText => do
      let base := fixtureBase assumedBase manifestDir path
      match parseTriG text (some base) mode with
      | .error e => return .ofOutcome (.fail s!"TriG parse error: {e.msg} (offset {e.pos})")
      | .ok ds =>
        match parseNQuads expectedText mode with
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
        match parseTriG text (some base) mode with
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
        match parseNTriples expectedText mode with
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

  /- ### RDF 1.2 canonical N-Triples / N-Quads — the two `rdf12/…/c14n`
     leaf manifests, and the only test types no rdf11 suite uses. Port
     of `run_rdf12_test`'s `TestNTriplesPositiveC14N` /
     `TestNQuadsPositiveC14N` arms (`w3c_runner.ml` ~lines 3246–3281):
     parse the input in RDF 1.2 mode, re-serialise with the canonical
     serialiser (`Graph.toCanonicalNTriples` /
     `Dataset.toCanonicalNQuads`, `Syntax/NTriples.lean` §"Canonical
     N-Triples"), and compare the result to the `-c14n.{nt,nq}` oracle
     BYTE FOR BYTE — no newline trimming, exactly as the F* runner's
     `actual = expected`. An input that does not parse is a FAIL, not a
     skip: the oracle says it is well-formed. -/
  | "TestNTriplesPositiveC14N" =>
    withActionAndResult fun _ text expectedText => do
      match parseNTriples text .rdf12 with
      | .error e =>
          return .ofOutcome (.fail s!"input failed to parse (RDF 1.2 N-Triples): {e.msg} (offset {e.pos})")
      | .ok g =>
        let got := Graph.toCanonicalNTriples g
        return { outcome :=
                   if got == expectedText then .pass
                   else .fail s!"canonical N-Triples output differs from the expected file ({got.length} chars, expected {expectedText.length})",
                 triplesCompared := g.length }
  | "TestNQuadsPositiveC14N" =>
    withActionAndResult fun _ text expectedText => do
      match parseNQuads text .rdf12 with
      | .error e =>
          return .ofOutcome (.fail s!"input failed to parse (RDF 1.2 N-Quads): {e.msg} (offset {e.pos})")
      | .ok ds =>
        let got := Dataset.toCanonicalNQuads ds
        return { outcome :=
                   if got == expectedText then .pass
                   else .fail s!"canonical N-Quads output differs from the expected file ({got.length} chars, expected {expectedText.length})",
                 triplesCompared := quadCount ds }

  /- ### SPARQL 1.1 Query (sparql11 suites) — see the section above. -/
  | "QueryEvaluationTest" | "CSVResultFormatTest" => runQueryEvaluation tc mode
  | "PositiveSyntaxTest11" | "PositiveSyntaxTest" => runSyntaxTest true tc mode
  | "NegativeSyntaxTest11" | "NegativeSyntaxTest" => runSyntaxTest false tc mode

  /- ### SPARQL 1.1 Update (sparql11 suites) — see the section above. -/
  | "UpdateEvaluationTest"       => runUpdateEvaluation tc mode
  | "PositiveUpdateSyntaxTest11" | "PositiveUpdateSyntaxTest" =>
      runUpdateSyntaxTest true tc mode
  | "NegativeUpdateSyntaxTest11" | "NegativeUpdateSyntaxTest" =>
      runUpdateSyntaxTest false tc mode

  /- ### RDF 1.1 Semantics (rdf-mt) — see "RDF 1.1 Semantics" above. -/
  | "PositiveEntailmentTest" => runEntailmentTest mode true tc
  | "NegativeEntailmentTest" => runEntailmentTest mode false tc


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
