/-
Harness.Manifest — read a W3C `manifest.ttl` with the Lean Turtle
parser and turn it into the `TestCase` records the runner dispatches
on.

Iron rule #6: the manifest is the REAL file off disk, parsed by the
engine under test. That is the point of this rung — the suites'
manifests are Turtle, so a Turtle parser is what makes them readable,
and the harness proves it by depending on nothing else.

The model of a test entry is the F* runner's
(`bin/w3c-runner/w3c_runner.ml`, `extract_test_cases` ~line 380 and
`read_manifest` ~line 602), reproduced clause for clause:

  * the manifest is parsed with base `file://<absolute manifest path>`,
    so relative entry references resolve to `file://` URIs that
    `iriToLocalPath` turns straight back into paths;
  * `mf:entries` heads an RDF COLLECTION — an `rdf:first`/`rdf:rest`
    chain ending in `rdf:nil` — walked in list order, so the printed
    per-test lines come out in the manifest's own order;
  * the test type is the local name of the FIRST `rdf:type`
    (namespace stripped at the last `#`);
  * `mf:action` is either a file IRI (every rdf11 syntax suite and the
    rdf-canon suite) or a blank node carrying `qt:query` / `qt:data` /
    `qt:graphData` (the SPARQL-shaped suites). Both shapes are
    recorded; which one a runner uses is its business;
  * `rdft:approval` is RECORDED, not filtered on. The F* runner runs
    Approved, Proposed and Rejected entries alike — it never consults
    approval — and its denominators (rdf-turtle 313, rdf-trig 356 …)
    are the full typed-entry counts. Matching those denominators means
    matching that treatment;
  * an entry whose type the runner cannot execute STILL produces a
    `TestCase`. It is scored `unsupported` and stays in the
    denominator; dropping it here would silently shrink the total.

No `sorry`, no `axiom`, no `native_decide`, no `partial`: the
collection walk is fuel-bounded by the triple count, which bounds any
`rdf:rest` chain the graph can contain.
-/
import L4Factoidal.Syntax.Turtle
import Harness.Common

open L4Factoidal.RDF
open L4Factoidal.Syntax

namespace Harness

/-! ## Vocabulary IRIs -/

def mfNs   : String := "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
def qtNs   : String := "http://www.w3.org/2001/sw/DataAccess/tests/test-query#"
def rdfNs  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def rdftNs : String := "http://www.w3.org/ns/rdftest#"
def rdfcNs : String := "https://w3c.github.io/rdf-canon/tests/vocab#"
/-- SPARQL 1.1 Service Description — `sd:entailmentRegime` on the
entailment suite's actions. -/
def sdNs   : String := "http://www.w3.org/ns/sparql-service-description#"
/-- SPARQL 1.1 Update test vocabulary — `ut:request`, `ut:data`,
`ut:graphData` / `ut:graph` on the action and on the result of an
`UpdateEvaluationTest`. -/
def utNs   : String := "http://www.w3.org/2009/sparql/tests/test-update#"
/-- `rdfs:label` names the graph of a `ut:graphData` node; `rdfs:comment`
carries the HTTP exchange of a Protocol / Graph Store test. -/
def rdfsNs : String := "http://www.w3.org/2000/01/rdf-schema#"

def rdfType  : String := rdfNs ++ "type"
def rdfFirst : String := rdfNs ++ "first"
def rdfRest  : String := rdfNs ++ "rest"
def rdfNil   : String := rdfNs ++ "nil"

/-! ## Graph lookup helpers

`Graph` is `List Triple`, so these are the same linear scans the F*
runner does — specification shape, not an index (the spec/pragmatics
split: no engine machinery in the Lean tree). -/

/-- A comparable key for a term: an IRI's text, a blank node's label,
a literal's lexical form. Port of the F* runner's `term_to_str`. -/
def termKey : Term → String
  | .iri i          => i.val
  | .bnode b        => b
  | .literal l      => l.val.lexicalForm
  | .tripleTerm _ _ _ => ""

def subjKey : Subject → String
  | .iri i   => i.val
  | .bnode b => b

/-- The subject position corresponding to a term, when the term can
occupy one (IRIs and blank nodes can; literals cannot). -/
def subjectOfTerm : Term → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

/-- Objects of `(s, p, ?)` in list order. -/
def findObjects (g : Graph) (s : Subject) (p : String) : List Term :=
  g.filterMap (fun t => if t.s == s && t.p.val == p then some t.o else none)

def findObject? (g : Graph) (s : Subject) (p : String) : Option Term :=
  (findObjects g s p).head?

/-- Walk an RDF collection (`rdf:first`/`rdf:rest`, terminated by
`rdf:nil`) rooted at `node`, returning its members in list order.

`fuel` bounds the walk; callers pass the graph's triple count, and no
chain can be longer than that because each link consumes an
`rdf:rest` triple. This is what keeps the function total — no
`partial`, no well-founded-recursion obligation. -/
def collectList (g : Graph) : Nat → Term → List Term
  | 0, _ => []
  | fuel + 1, node =>
    let sOpt : Option Subject :=
      match node with
      | .iri i   => if i.val == rdfNil then none else some (.iri i)
      | .bnode b => some (.bnode b)
      | _        => none
    match sOpt with
    | none   => []
    | some s =>
      let heads := match (findObjects g s rdfFirst).head? with
                   | some h => [h]
                   | none   => []
      match (findObjects g s rdfRest).head? with
      | some r => heads ++ collectList g fuel r
      | none   => heads

/-- The last path segment of an IRI: after the last `/`, then after the
last `#`. `http://www.w3.org/ns/entailment/RDFS` → `RDFS`. -/
def lastSegment (iri : String) : String := lastAfter (lastAfter iri "/") "#"

/-! ## The test case record -/

/-- One manifest entry, in the shape the F* runner models it.

`action` is the resolved local path when `mf:action` is a file IRI —
which is every entry in the rdf11 syntax suites and the rdf-canon
suite. `queryFile` / `dataFiles` / `graphData` carry the
SPARQL-shaped bnode action instead; they are STORED now and consumed
when the SPARQL rungs land (there is no Lean SPARQL string parser
yet). -/
structure TestCase where
  /-- `mf:name`, falling back to the entry node's own identifier. -/
  name       : String
  /-- The entry node's IRI text or blank-node label. -/
  entryId    : String
  /-- Local name of the first `rdf:type`, e.g. `TestTurtleEval`.
  `"Unknown"` when the entry carries no type. -/
  testType   : String
  /-- `mf:action` as a local path, when it is a plain file IRI. -/
  action     : Option String
  /-- `qt:query` as a local path (bnode-shaped action). -/
  queryFile  : Option String
  /-- `qt:data` as local paths (bnode-shaped action). -/
  dataFiles  : List String
  /-- `qt:graphData`: (graph IRI, local path) pairs. -/
  graphData  : List (String × String)
  /-- `mf:result` as a local path. -/
  resultFile : Option String
  /-- Local name of `rdft:approval` (`Approved` / `Proposed` /
  `Rejected` / …), `""` when the entry omits it. Recorded, never
  filtered on — see the module header. -/
  approval   : String
  /-- `rdfc:hashAlgorithm`, e.g. `"SHA384"` (rdf-canon only). -/
  hashAlgorithm : Option String
  /-- `sd:entailmentRegime` local names on the action (`RDFS`, `D`,
  `OWL-Direct`, …; sparql11-entailment only). Empty = simple
  entailment. -/
  entailmentRegimes : List String := []
  /-- `qt:serviceData`: (endpoint IRI, local data path) pairs for
  SERVICE tests. -/
  serviceData : List (String × String) := []
  /-- `UpdateEvaluationTest` only: the expected Graph Store after the
  update — `ut:data` files (default graph) under `mf:result`. The
  F* runner's `update_result_default_files`. -/
  updateResultData : List String := []
  /-- … and its `ut:graphData` (graph IRI, local path) pairs. The F*
  runner's `update_result_named_files`. -/
  updateResultGraphData : List (String × String) := []
  /-- `mf:entailmentRegime` — the rdf-mt suite's literal (`"simple"`,
  `"RDF"`, `"RDFS"`) on the entry itself (the F* runner's
  `test_type_detail`). -/
  entailmentRegime : Option String := none
  /-- `mf:recognizedDatatypes ( … )` — the datatype IRIs the test asks
  the implementation to recognise (rdf-mt only; empty otherwise). -/
  recognizedDatatypes : List String := []
  /-- `mf:result false` — the rdf-mt encoding of "the action graph is
  (Positive) / is not (Negative) inconsistent". Recorded as a flag;
  `resultFile` is `none` for such an entry. -/
  resultFalse : Bool := false
  /-- The first non-empty `rdfs:comment` literal on the entry: the
  HTTP request/response description of a `ProtocolTest` or
  `GraphStoreProtocolTest` (the F* runner's `protocol_comment`). -/
  comment : Option String := none
  deriving Repr

/-- `ut:data` / `qt:data` files and `ut:graphData` / `qt:graphData`
pairs under one node (an action, or an UPDATE result). Port of the F*
runner's `extract_data_and_graphdata`: a `qt:graphData` object is a
file IRI that is also the graph name; a `ut:graphData` object is
either such an IRI or a blank node carrying `ut:graph` (the file) and
`rdfs:label` (the graph IRI). -/
def dataAndGraphData (manifestDir : String) (g : Graph) (subj : Subject) :
    List String × List (String × String) :=
  let d := (findObjects g subj (qtNs ++ "data") ++ findObjects g subj (utNs ++ "data")).map
             (fun t => iriToLocalPath manifestDir (termKey t))
  let qtGd := (findObjects g subj (qtNs ++ "graphData")).map (fun t =>
                let iri := termKey t
                (iri, iriToLocalPath manifestDir iri))
  let utGd := (findObjects g subj (utNs ++ "graphData")).filterMap (fun t =>
                match t with
                | .iri i   => some (i.val, iriToLocalPath manifestDir i.val)
                | .bnode b =>
                    match findObject? g (.bnode b) (utNs ++ "graph"),
                          findObject? g (.bnode b) (rdfsNs ++ "label") with
                    | some file, some label =>
                        some (termKey label, iriToLocalPath manifestDir (termKey file))
                    | _, _ => none
                | _ => none)
  (d, qtGd ++ utGd)

/-- One entry → one `TestCase`. Total: never returns `none`, because
an entry the runner cannot execute must still occupy a slot in the
denominator. -/
def extractTestCase (manifestDir : String) (g : Graph) (entry : Term) : TestCase :=
  let entryId := termKey entry
  match subjectOfTerm entry with
  | none => { name := entryId, entryId, testType := "Unknown", action := none,
              queryFile := none, dataFiles := [], graphData := [],
              resultFile := none, approval := "", hashAlgorithm := none }
  | some subj =>
    let testType :=
      match findObject? g subj rdfType with
      | some t => localName (termKey t)
      | none   => "Unknown"
    let name :=
      match findObject? g subj (mfNs ++ "name") with
      | some t => termKey t
      | none   => entryId
    let approval :=
      match findObject? g subj (rdftNs ++ "approval") with
      | some t => localName (termKey t)
      | none   => ""
    let hashAlgorithm := (findObject? g subj (rdfcNs ++ "hashAlgorithm")).map termKey
    -- `mf:result`: a file IRI (query / rdf-mt entailment tests); the
    -- literal `false` (rdf-mt inconsistency tests); or a blank node
    -- carrying `ut:data` / `ut:graphData` — possibly none, for an
    -- expected EMPTY store (`mf:result []`, update-silent) — for UPDATE.
    let resultTerm := findObject? g subj (mfNs ++ "result")
    let resultFalse := match resultTerm with
                       | some (.literal l) => l.val.lexicalForm == "false"
                       | _ => false
    let (resultFile, updateResultData, updateResultGraphData) :=
      match resultTerm with
      | some (.bnode b) =>
          let (d, gd) := dataAndGraphData manifestDir g (.bnode b)
          (none, d, gd)
      | some (.literal _) => (none, [], [])
      | some t => (some (iriToLocalPath manifestDir (termKey t)), [], [])
      | none   => (none, [], [])
    -- rdf-mt: `mf:entailmentRegime "RDFS"` and `mf:recognizedDatatypes ( … )`
    -- on the entry itself (the F* runner's `test_type_detail` /
    -- `extract_iri_list`). `( )` and an absent triple both give `[]`.
    let entailmentRegime := (findObject? g subj (mfNs ++ "entailmentRegime")).map termKey
    let recognizedDatatypes :=
      match findObject? g subj (mfNs ++ "recognizedDatatypes") with
      | some t => (collectList g (g.length + 1) t).map termKey
      | none   => []
    -- `mf:action`: a file IRI, or a bnode carrying qt: predicates.
    let actionTerm := findObject? g subj (mfNs ++ "action")
    let noBnodeAction : Option String × List String × List (String × String) ×
                        List String × List (String × String) :=
      (none, [], [], [], [])
    let (action, (queryFile, dataFiles, graphData, entailmentRegimes, serviceData)) :=
      match actionTerm with
      | some (.iri i) => (some (iriToLocalPath manifestDir i.val), noBnodeAction)
      | some other =>
          match subjectOfTerm other with
          | none => (none, noBnodeAction)
          | some aSubj =>
            -- `qt:query` (query tests) or `ut:request` (UPDATE tests).
            let q := (match findObject? g aSubj (qtNs ++ "query") with
                      | some t => some t
                      | none   => findObject? g aSubj (utNs ++ "request")).map
                       (fun t => iriToLocalPath manifestDir (termKey t))
            let (d, gd) := dataAndGraphData manifestDir g aSubj
            -- `sd:entailmentRegime` is one IRI or an RDF collection of them.
            let regimes := (findObjects g aSubj (sdNs ++ "entailmentRegime")).flatMap (fun (t : Term) =>
                             match t with
                             | .iri i   => [lastSegment i.val]
                             | .bnode _ => (collectList g (g.length + 1) t).map
                                             (fun m => lastSegment (termKey m))
                             | _        => [])
            -- `qt:serviceData [ qt:endpoint <iri> ; qt:data <file> ]`.
            let sd := (findObjects g aSubj (qtNs ++ "serviceData")).filterMap (fun t =>
                        match subjectOfTerm t with
                        | none => none
                        | some s =>
                          match findObject? g s (qtNs ++ "endpoint"),
                                findObject? g s (qtNs ++ "data") with
                          | some ep, some df =>
                              some (termKey ep, iriToLocalPath manifestDir (termKey df))
                          | _, _ => none)
            (none, (q, d, gd, regimes, sd))
      | none => (none, noBnodeAction)
    -- `rdfs:comment`: the first literal with a non-empty lexical form.
    let comment : Option String :=
      (findObjects g subj (rdfsNs ++ "comment")).findSome? (fun (t : Term) =>
        match t with
        | .literal l => if l.val.lexicalForm.isEmpty then none else some l.val.lexicalForm
        | _          => none)
    { name, entryId, testType, action, queryFile, dataFiles, graphData,
      resultFile, approval, hashAlgorithm, entailmentRegimes, serviceData,
      updateResultData, updateResultGraphData,
      entailmentRegime, recognizedDatatypes, resultFalse, comment }

/-- `mf:assumedTestBase` — the base IRI the suite documents for its own
fixtures. Read out of the manifest rather than hardcoded, because the
rdf11 corpus MOVED: the suites once documented
`http://www.w3.org/2013/TurtleTests/` and now declare
`https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/`, with fixtures
regenerated against the new one. The F* runner reads it the same way
(`extract_assumed_test_base`), so both trees resolve relative IRIs
identically. -/
def assumedTestBase (g : Graph) : Option String :=
  match g.find? (fun t => t.p.val == mfNs ++ "assumedTestBase") with
  | some t => match t.o with
              | .iri i => some i.val
              | _      => none
  | none   => none

/-- All entries of a parsed manifest graph, in `mf:entries` order. -/
def extractTestCases (manifestDir : String) (g : Graph) : List TestCase :=
  let fuel := g.length + 1
  let heads := g.filterMap (fun t =>
    if t.p.val == mfNs ++ "entries" then some t.o else none)
  let nodes := match heads.head? with
               | some h => collectList g fuel h
               | none   => []
  nodes.map (extractTestCase manifestDir g)

/-- The whole job as one pure function: manifest text + its path →
(entries, assumed base). Separated from I/O so `#guard` can pin it on
an inline manifest. -/
def parseManifestText (manifestPath text : String) :
    Except String (List TestCase × Option String) :=
  let base := "file://" ++ manifestPath
  match parseTurtle text (some base) with
  | .error e => .error s!"manifest parse error at offset {e.pos}: {e.msg}"
  | .ok g    => .ok (extractTestCases (dirname manifestPath) g, assumedTestBase g)

/-! ## Lenient manifest parse — upstream-defect recovery, loudly

The rdf12 `rdf-semantics` manifest uses the prefix `test:` without
declaring it (upstream w3c/rdf-tests commit `2b35822`, 2025-06-28 —
`trs:literal-type`'s `test:approval test:NotClassified`). Under the
strict parse above the WHOLE suite reported 0 pass, 0 fail (out of 0),
`no_manifest=1`, in every umbrella run — the zero-test-pressure
mechanism of https://github.com/danbri/factoidal/issues/602. The F\*
runner's policy is lenient-with-report
(https://github.com/danbri/factoidal/issues/334); this is that policy
here: retry with the one undeclared prefix bound to a recovery
namespace, and RETURN the recovery as a warning line the runner must
print. The recovery namespace `urn:x-manifest-recovery:<pfx>#` cannot
collide with any vocabulary the extractor reads (those are all
absolute `http(s)` IRIs), so recovered statements are carried but
never mistaken for `mf:` / `rdft:` data. A recovered parse error's
offset refers to the AUGMENTED text (one prepended line per recovered
prefix). -/

/-- Bounded retry around `parseTurtle`: each round prepends a binding
for the one prefix the `undefined prefix:` error names. Any other
error, or fuel exhaustion, surfaces unchanged. -/
def parseTurtleRecover (base : String) :
    Nat → String → List String →
      Except L4Factoidal.Syntax.ParseError Graph × List String
  | 0, text, ws => (parseTurtle text (some base), ws)
  | fuel + 1, text, ws =>
      match parseTurtle text (some base) with
      | .ok g => (.ok g, ws)
      | .error e =>
          let tag := "undefined prefix: "
          if e.msg.startsWith tag then
            let pfx := e.msg.drop tag.length
            let ns := s!"urn:x-manifest-recovery:{pfx}#"
            let warn := s!"MANIFEST-RECOVERY: undeclared prefix '{pfx}:' bound to <{ns}> — upstream manifest defect, tolerated loudly (https://github.com/danbri/factoidal/issues/334 policy; suite pressure restored by https://github.com/danbri/factoidal/issues/602)"
            parseTurtleRecover base fuel
              (s!"@prefix {pfx}: <{ns}> .\n" ++ text) (ws ++ [warn])
          else (.error e, ws)

/-- Like `parseManifestText`, with undeclared-prefix recovery. The
second component is the warning lines (empty when the strict parse
succeeded); callers MUST surface them. -/
def parseManifestTextLenient (manifestPath text : String) :
    Except String (List TestCase × Option String) × List String :=
  let base := "file://" ++ manifestPath
  match parseTurtleRecover base 4 text [] with
  | (.error e, ws) =>
      (.error s!"manifest parse error at offset {e.pos}: {e.msg}", ws)
  | (.ok g, ws) =>
      (.ok (extractTestCases (dirname manifestPath) g, assumedTestBase g), ws)

/-- `mf:include` — the sub-manifests an umbrella manifest
(`sparql11/manifest-all.ttl`) points at, as local paths in collection
order. The F* runner follows these; so does `Harness.Main`. -/
def manifestIncludes (manifestDir : String) (g : Graph) : List String :=
  let fuel := g.length + 1
  let heads := g.filterMap (fun t =>
    if t.p.val == mfNs ++ "include" then some t.o else none)
  heads.flatMap (fun h => (collectList g fuel h).map (fun m => iriToLocalPath manifestDir (termKey m)))

/-- The includes of a manifest text (pure counterpart of
`parseManifestText`; an unparseable manifest has none). -/
def parseManifestIncludes (manifestPath text : String) : List String :=
  let base := "file://" ++ manifestPath
  match parseTurtle text (some base) with
  | .error _ => []
  | .ok g    => manifestIncludes (dirname manifestPath) g

/-- Load a manifest off disk. `none` when the file is absent
(the caller counts that as `no_manifest`). Uses the LENIENT parse and
prints each recovery warning — loud by design, `--quiet`
notwithstanding: a silently recovered manifest is how the rdf12
rdf-semantics suite ran at 0 tests for two months unnoticed. -/
def loadManifest (path : System.FilePath) :
    IO (Option (Except String (List TestCase × Option String))) := do
  match ← readOpt path with
  | none      => return none
  | some text =>
      let abs ← IO.FS.realPath path
      let (res, warns) := parseManifestTextLenient abs.toString text
      for w in warns do
        IO.println s!"  ({w} — in {abs})"
      return some res

end Harness
