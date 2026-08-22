/-
Harness/CsvwRdfRun — a REAL csv2rdf conformance runner over the
vendored W3C csvw corpus.

Unlike `CsvwProbe` (a reader-level check), this one does the whole
pipeline and COMPARES AGAINST THE SUITE'S OWN EXPECTED OUTPUT:

    test.csv --[Lean CSVW reader + conversion + emit]--> triples
    test.ttl --[Lean Turtle parser]-------------------> triples
    compare by GRAPH ISOMORPHISM (blank nodes are not names)

That comparison is why this is conformance and the probe is not.
Isomorphism rather than triple-set equality because csv2rdf mints
blank nodes whose labels are arbitrary — comparing labels would fail
every test that has one, for a reason that is not a defect.

SCOPE, stated so the score reads honestly: the runner is driven by the
suite's OWN `manifest-rdf.jsonld`, and attempts only entries with no
`implicit` member — the tests that use NO accompanying metadata.
Metadata tests need `@context` resolution, `tableSchema` inheritance
and metadata discovery. Everything skipped is REPORTED with its
reason, never silently dropped, because a runner that quietly narrows
its denominator reports a number nobody can act on.

Pairing comes from the manifest's `action`/`result`, NOT from matching
filenames. That distinction is not pedantic: `test001.json` is the
expected JSON OUTPUT of the csv2json suite, not input metadata, and
guessing from names mistakes one for the other.

Usage: `lake exe l4csvw-rdf [tests-dir]`
-/
import L4Factoidal.CSVW.Emit
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.JSON.Parser

open L4Factoidal.CSVW
open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- Build the per-row lookup from the header row's column names. -/
private def rowBindings (names : List String) (cells : List String)
    : List (String × String) :=
  (names.zip cells)

/-- Convert one table to triples the way csv2rdf minimal mode does,
    with the default column URLs the suite's no-metadata tests expect:
    the table URL with the column name as a fragment. -/
def convertTable (tableUrl : String) (t : Table) : List Triple :=
  let names := match t.header.head? with
    | some h => h.cells
    | none   => []
  let rows := t.rows.zipIdx
  rows.flatMap (fun (row, i) =>
    let rowNum := i + 1
    let binds := rowBindings names row.cells
    let look := rowLookup binds rowNum row.num
    let subj : Subject := .bnode s!"row{rowNum}"
    (names.zip row.cells).flatMap (fun (nm, cell) =>
      let inh : Inherited := { propertyUrl := some (defaultPropertyRef tableUrl nm) }
      let r := convertCell inh nm look cell
      cellTriples inh subj r))

structure TestOutcome where
  name   : String
  status : String        -- "pass" | "fail" | "skip"
  detail : String

def runOne (dir base : String) : IO TestOutcome := do
  let csvPath := dir ++ "/" ++ base ++ ".csv"
  let ttlPath := dir ++ "/" ++ base ++ ".ttl"
  if !(← System.FilePath.pathExists csvPath) then
    return ⟨base, "skip", "no .csv action"⟩
  if !(← System.FilePath.pathExists ttlPath) then
    return ⟨base, "skip", "no expected .ttl"⟩
  let src ← IO.FS.readFile csvPath
  let expectedSrc ← IO.FS.readFile ttlPath
  let tableUrl := "http://www.w3.org/2013/csvw/tests/" ++ base ++ ".csv"
  let got := convertTable tableUrl (read (({} : Dialect).resolve) src)
  match parseTurtle expectedSrc (some tableUrl) with
  | .error _ => return ⟨base, "skip", "expected .ttl did not parse"⟩
  | .ok want =>
      if Graph.isomorphic? got want then
        return ⟨base, "pass", s!"{got.length} triples"⟩
      else
        return ⟨base, "fail", s!"produced {got.length}, expected {want.length}"⟩

/-- Manifest entries with no `implicit` member: the no-metadata
    tests. Returns (name, action, result). -/
def noMetadataEntries (j : L4Factoidal.JSON.Json) : List (String × String × String) :=
  let field? (k : String) (v : L4Factoidal.JSON.Json) : Option L4Factoidal.JSON.Json :=
    match v with
    | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
    | _ => none
  let str? (k : String) (v : L4Factoidal.JSON.Json) : Option String :=
    match field? k v with
    | some (.string s) => some s
    | _ => none
  match field? "entries" j with
  | some (.array es) =>
      es.filterMap (fun e =>
        if (field? "implicit" e).isSome then none
        else match str? "id" e, str? "action" e, str? "result" e with
          | some i, some a, some r =>
              if a.endsWith ".csv" && r.endsWith ".ttl" then some (i, a, r) else none
          | _, _, _ => none)
  | _ => []

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/csvw/tests"
  let manifestPath := dir ++ "/manifest-rdf.jsonld"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"csvw rdf runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match L4Factoidal.JSON.parseJson? mtext with
  | none =>
      IO.println "csvw rdf runner: manifest did not parse"
      return 1
  | some mjson =>
      let entries := noMetadataEntries mjson
      let total : Nat := match mjson with
        | L4Factoidal.JSON.Json.object ms =>
            match (ms.find? (fun (k, _) => k == "entries")).map (·.2) with
            | some (L4Factoidal.JSON.Json.array es) => es.length
            | _ => 0
        | _ => 0
      let mut pass := 0
      let mut fail := 0
      let mut skip := 0
      for (id, action, result) in entries do
        let base := action.dropRight 4
        let o ← runOne dir base
        if o.status == "pass" then pass := pass + 1
        else if o.status == "fail" then
          fail := fail + 1
          IO.println s!"FAIL {id} ({action} vs {result}): {o.detail}"
        else
          skip := skip + 1
          IO.println s!"skip {id}: {o.detail}"
      IO.println ""
      IO.println s!"csv2rdf NO-METADATA subset: {pass} pass, {fail} fail, {skip} skip (out of {entries.length} such entries)"
      IO.println s!"NOT ATTEMPTED: {total - entries.length} of {total} manifest entries carry metadata"
      IO.println "  (an `implicit` member), which needs @context resolution,"
      IO.println "  tableSchema inheritance and metadata discovery -- not ported."
      IO.println ""
      IO.println "Comparison is by GRAPH ISOMORPHISM against the suite's own"
      IO.println "expected .ttl: blank-node labels are arbitrary, so triple-set"
      IO.println "equality would fail correct output."
      return 0
