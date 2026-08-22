/-
Harness.ShaclProbe — run the Lean SHACL Core validator over the real
W3C SHACL test suite (`third_party/testing/shacl/data-shapes-test-suite`).

Iron rule #6 applied to SHACL: the manifests and fixtures are read off
disk with the Lean Turtle parser; nothing is synthesised. Mirrors
`bin/shacl-runner/shacl_runner.ml` (the F* tree's runner) step for step,
so the two trees' numbers share denominators:

  * manifests are walked through `mf:include` (a repeated triple in this
    suite, not an RDF list) down to leaf files, each declaring one or
    more `sht:Validate` entries;
  * `sht:dataGraph` / `sht:shapesGraph` are resolved against the file's
    own base (`<>` = the file itself, the common case) or loaded from
    the sibling file they name;
  * the shapes graph is decoded (`SHACL.decodeShapesGraph`), the data
    graph validated (`SHACL.validate`), and the report serialised
    (`SHACL.reportToGraph`);
  * by default the FULL report is compared with the manifest's expected
    report under the suite's own "full compliance" rule
    (data-shapes-test-suite/index.html): the expected graph is the
    `mf:result` node's own triples plus each `sh:result` value's triples
    plus the blank-node structure of any `sh:resultPath`; the actual
    graph drops every `sh:resultMessage` whose object the expected graph
    does not also carry (the one asymmetric predicate); both are
    canonicalised with RDFC-1.0 (`RDF/Canonical.lean`, exactly what the
    F* runner does via `RDF_Canonical.canonicalize_to_nquads`) and the
    canonical N-Quads strings compared;
  * `--conforms-only` compares only the `sh:conforms` boolean (the F*
    runner's slice-1 floor).

A manifest entry whose shapes graph uses a SHACL-SPARQL predicate
(sh:sparql, sh:select, sh:ask, sh:validator, sh:parameter, …), or
whose `mf:result` is the bare IRI `sht:Failure`, is reported as
`UNSUPPORTED` — counted, named, in the denominator, never passed.

Scores are printed per sub-directory (core/node, core/property, …) and
in total, each with its denominator (anti-pattern #25), in the score-
line grammar of `Harness/Common.lean`. Not part of the verified
library: this file does I/O and prints scores.

Usage (from the repository root, paths resolve from the CWD):
  formal/lean4/.lake/build/bin/l4shacl \
    third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl
  … [--conforms-only] [-v]
-/

import L4Factoidal.SHACL.Report
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Canonical
import Harness.Common

open L4Factoidal.RDF
open L4Factoidal.SHACL
open L4Factoidal.Syntax
open Harness

namespace ShaclProbe

/-! ## Manifest vocabulary -/

def mfNs : String := "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
def shtNs : String := "http://www.w3.org/ns/shacl-test#"

def mfInclude : WfIri := ⟨"http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#include", rfl⟩
def mfAction  : WfIri := ⟨"http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#action", rfl⟩
def mfResult  : WfIri := ⟨"http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#result", rfl⟩
def mfName    : WfIri := ⟨"http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#name", rfl⟩
def rdfsLabel : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#label", rfl⟩
def shtValidate    : WfIri := ⟨"http://www.w3.org/ns/shacl-test#Validate", rfl⟩
def shtDataGraph   : WfIri := ⟨"http://www.w3.org/ns/shacl-test#dataGraph", rfl⟩
def shtShapesGraph : WfIri := ⟨"http://www.w3.org/ns/shacl-test#shapesGraph", rfl⟩
def shtFailure     : WfIri := ⟨"http://www.w3.org/ns/shacl-test#Failure", rfl⟩

/-! ## Files and IRIs -/

def fileUri (absPath : String) : String := "file://" ++ absPath

def pathOfFileIri (iri : String) : Option String :=
  if iri.startsWith "file://" then some (stripFileScheme iri) else none

/-- Parse a Turtle file against its own `file://` IRI as base. -/
def parseTtlFile (absPath : String) : IO (Option (Graph × String)) := do
  match ← readOpt absPath with
  | none => return none
  | some raw =>
    let base := fileUri absPath
    match parseTurtle raw (some base) with
    | .ok g => return some (g, base)
    | .error e =>
      IO.eprintln s!"l4shacl: {absPath}: Turtle parse error: {e}"
      return none

/-! ## Thin graph accessors -/

def iriStr : Term → Option String
  | .iri i => some i.val
  | _ => none

def literalLex : Option Term → Option String
  | some (.literal l) => some l.val.lexicalForm
  | _ => none

def boolOfLit : Option Term → Option Bool
  | some (.literal l) => some (l.val.lexicalForm == "true" || l.val.lexicalForm == "1")
  | _ => none

def obj1 (g : Graph) (t : Term) (p : WfIri) : Option Term :=
  (objectsOfTerm g t p).head?

def subjectsTyped (g : Graph) (ty : WfIri) : List Term :=
  g.filterMap fun (t : Triple) =>
    if t.p == L4Factoidal.SHACL.rdfType && t.o == .iri ty then some t.s.toTerm else none

def triplesWithSubject (g : Graph) (t : Term) : List Triple :=
  match t.toSubject? with
  | some s => g.filter (fun tr => tr.s == s)
  | none => []

/-! ## The expected report graph (port of `expected_report_graph`) -/

/-- The blank-node-only reachability closure from `frontier` — the
"triples needed to correctly represent the sh:resultPath". -/
def bnodePathClosure (g : Graph) : List Term → List Triple → Nat → List Triple
  | _, acc, 0 => acc
  | [], acc, _ + 1 => acc
  | t :: rest, acc, fuel + 1 =>
    match t with
    | .bnode _ =>
      let ts := triplesWithSubject g t
      bnodePathClosure g (rest ++ ts.map (·.o)) (acc ++ ts) fuel
    | _ => bnodePathClosure g rest acc fuel

/-- One expected `sh:result` value: its own triples, its resultPath
structure, and (recursively) any `sh:detail` sub-results. -/
def resultClosure (g : Graph) : Term → Nat → List Triple
  | _, 0 => []
  | rv, fuel + 1 =>
    let own := triplesWithSubject g rv
    let pathTs := bnodePathClosure g (objectsOfTerm g rv shResultPath) [] 50
    let detailTs := (objectsOfTerm g rv shDetail).flatMap fun d => resultClosure g d fuel
    own ++ pathTs ++ detailTs

def expectedReportGraph (g : Graph) (res : Term) : Graph :=
  triplesWithSubject g res ++
  (objectsOfTerm g res shResult).flatMap fun rv => resultClosure g rv 50

/-- The suite's sh:resultMessage carve-out: keep an actual
sh:resultMessage only when the expected graph carries the same
literal as a sh:resultMessage object. -/
def filterResultMessages (expected actual : Graph) : Graph :=
  let expectedMessages := expected.filterMap fun t =>
    if t.p == shResultMessage then
      match t.o with | .literal l => some l.val.lexicalForm | _ => none
    else none
  actual.filter fun t =>
    if t.p == shResultMessage then
      match t.o with
      | .literal l => expectedMessages.contains l.val.lexicalForm
      | _ => false
    else true

/-! ## Test cases -/

structure TestCase where
  name          : String
  file          : String
  group         : String
  data          : Option Graph
  shapes        : Option Graph
  expectConforms : Option Bool
  expectReport  : Option Graph
  expectFailure : Bool

/-- The sub-directory label of a test file: the two path components
after `/tests/` (`core/node`, `sparql/pre-binding`, …). -/
def groupOf (file : String) : String :=
  match (file.splitOn "/tests/").getLast? with
  | some tail =>
    let parts := tail.splitOn "/"
    if parts.length ≥ 3 then s!"{parts[0]!}/{parts[1]!}"
    else if parts.length = 2 then parts[0]!
    else tail
  | none => file

def resolveGraphRef (own : Graph) (ownBase : String) (t : Term) : IO (Option Graph) := do
  match iriStr t with
  | none => return none
  | some iri =>
    if iri == ownBase then return some own
    else
      match pathOfFileIri iri with
      | some p =>
        match ← parseTtlFile p with
        | some (g, _) => return some g
        | none => return none
      | none => return none

def testName (g : Graph) (t : Term) : String :=
  match literalLex (obj1 g t mfName) with
  | some n => n
  | none =>
    match literalLex (obj1 g t rdfsLabel) with
    | some n => n
    | none => match t with
      | .iri i => i.val
      | .bnode b => "_:" ++ b
      | _ => "<test>"

/-- A term for a runtime IRI string (a `file://` URI always has a colon). -/
def iriTerm (s : String) : Term :=
  if h : isIri s = true then .iri ⟨s, h⟩ else .bnode s

/-- Walk one manifest / test file: its `mf:include`s first (recursively),
then its own `sht:Validate` entries — the F* runner's order. -/
partial def collectFromFile (visited : IO.Ref (List String)) (path : String) :
    IO (List TestCase) := do
  if (← visited.get).contains path then return []
  visited.modify (path :: ·)
  match ← parseTtlFile path with
  | none =>
    IO.eprintln s!"l4shacl: cannot read {path}"
    return []
  | some (g, base) =>
    let root := iriTerm base
    let mut included : List TestCase := []
    for inc in objectsOfTerm g root mfInclude do
      match iriStr inc with
      | none => pure ()
      | some incIri =>
        match pathOfFileIri incIri with
        | some incPath => included := included ++ (← collectFromFile visited incPath)
        | none => pure ()
    let mut own : List TestCase := []
    for t in subjectsTyped g shtValidate do
      let name := testName g t
      let action := obj1 g t mfAction
      let result := obj1 g t mfResult
      let dgraph ← match action with
        | none => pure none
        | some act =>
          match obj1 g act shtDataGraph with
          | none => pure none
          | some dgt => resolveGraphRef g base dgt
      let sgraph ← match action with
        | none => pure none
        | some act =>
          match obj1 g act shtShapesGraph with
          | none => pure none
          | some sgt => resolveGraphRef g base sgt
      let expect := match result with
        | none => none
        | some res => boolOfLit (obj1 g res shConforms)
      let expectFailure := match result with
        | some (.iri i) => i == shtFailure
        | _ => false
      let expectReport :=
        if expectFailure then none
        else match result with
          | some res => if expect.isSome then some (expectedReportGraph g res) else none
          | none => none
      own := own ++ [{ name := name, file := path, group := groupOf path,
                       data := dgraph, shapes := sgraph,
                       expectConforms := expect, expectReport := expectReport,
                       expectFailure := expectFailure }]
    return included ++ own

/-! ## Running one test -/

structure Options where
  conformsOnly : Bool := false
  verbose      : Bool := false

def canonOf (g : Graph) : Canonical.CanonResult :=
  Canonical.canonicalize { default := g, named := [] }

def runTest (opts : Options) (tc : TestCase) : Outcome × Bool :=
  match tc.data, tc.shapes with
  | none, _ => (.skip "no dataGraph resolved from mf:action", false)
  | _, none => (.skip "no shapesGraph resolved from mf:action", false)
  | some data, some shapesG =>
    if tc.expectFailure then (.unsupported "mf:result sht:Failure (SHACL-SPARQL pre-binding)", false)
    else
      let sg := decodeShapesGraph shapesG
      if !sg.unsupported.isEmpty then
        (.unsupported ("SHACL-SPARQL: " ++ String.intercalate ", " sg.unsupported), false)
      else
        let report := validate data sg
        if opts.conformsOnly then
          match tc.expectConforms with
          | none => (.skip "mf:result has no sh:conforms boolean", false)
          | some expect =>
            if report.conforms == expect then (.pass, false)
            else (.fail s!"expected sh:conforms {expect}, got {report.conforms}", false)
        else
          match tc.expectReport with
          | none => (.skip "mf:result is not a full ValidationReport blob (no sh:conforms present)", false)
          | some expectedG =>
            let actualG := filterResultMessages expectedG (reportToGraph report)
            let ce := canonOf expectedG
            let ca := canonOf actualG
            let budget := ce.aborted || ca.aborted
            if !budget && ce.nquads == ca.nquads then (.pass, false)
            else
              let why := if budget then "canonicalisation budget exceeded" else "report not isomorphic to expected"
              (.fail s!"{why} ({report.results.length} results, conforms={report.conforms}; expected conforms={tc.expectConforms})\n    expected:\n{ce.nquads}    actual:\n{ca.nquads}", budget)

/-! ## Suite run -/

def bumpGroup (scores : List (String × Score)) (group : String) (o : Outcome) :
    List (String × Score) :=
  if scores.any (·.1 == group) then
    scores.map fun (g, s) => if g == group then (g, s.bump o) else (g, s)
  else scores ++ [(group, (Score.mk 0 0 0 0).bump o)]

def defaultManifest : String :=
  "third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl"

def main (args : List String) : IO UInt32 := do
  let opts : Options :=
    { conformsOnly := args.contains "--conforms-only",
      verbose := args.contains "-v" || args.contains "--verbose" }
  let manifestArg := (args.filter (fun a => !a.startsWith "-")).head?.getD defaultManifest
  let manifestPath := (← IO.FS.realPath manifestArg).toString
  let label := if (manifestPath.splitOn "/sparql/").length > 1 then "shacl-sparql" else "shacl-core"
  IO.println s!"=== SHACL W3C Test Runner (Lean) — {if opts.conformsOnly then "sh:conforms-only" else "full report comparison"} ==="
  IO.println s!"Manifest: {manifestPath}"
  let visited ← IO.mkRef ([] : List String)
  let tests ← collectFromFile visited manifestPath
  IO.println s!"Totals: {tests.length} test entries"
  IO.println ""
  let mut total : Score := {}
  let mut groups : List (String × Score) := []
  let mut diag : Diag := {}
  if tests.isEmpty then diag := { diag with zeroTests := 1 }
  for tc in tests do
    let (o, budget) := runTest opts tc
    if budget then diag := { diag with budgetExceeded := diag.budgetExceeded + 1 }
    match o with
    | .pass => IO.println s!"PASS {tc.name}"
    | .fail r =>
      if opts.verbose then IO.println s!"FAIL {tc.name} ({tc.file}): {r}"
      else IO.println s!"FAIL {tc.name} ({tc.file}): {(r.splitOn "\n").head?.getD r}"
    | .skip r => IO.println s!"SKIP {tc.name}: {r}"
    | .unsupported f => IO.println s!"UNSUPPORTED {tc.name}: {f}"
    total := total.bump o
    groups := bumpGroup groups tc.group o
  IO.println ""
  for (g, s) in groups do
    IO.println (Score.line s!"{label} {g}" s)
  IO.println (Score.line s!"{label} TOTAL" total)
  IO.println (Diag.line label diag)
  return (if total.fail > 0 then 1 else 0)

end ShaclProbe

def main (args : List String) : IO UInt32 := ShaclProbe.main args
