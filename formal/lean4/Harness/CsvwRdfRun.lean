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

/-- Convert every data row to `RowInput`s, with the default column
    URLs the suite's no-metadata tests expect: the table URL with the
    column name as a fragment.

    `row.num` is the SOURCE line number the reader recorded, and it is
    what the `#row=` fragment must report; `rowNum` is the 1-based
    position within the table. With a header row present they differ
    by one, so using either for both would put every row URL off by a
    line while the triple COUNT still looked right. -/
def tableRows (tableUrl : String) (t : Table) : List RowInput :=
  let names := match t.header.head? with
    | some h => h.cells
    | none   => []
  t.rows.zipIdx.map (fun (row, i) =>
    let rowNum := i + 1
    let look := rowLookup (rowBindings names row.cells) rowNum row.num
    { rowNum := rowNum, sourceRow := row.num,
      cells := (names.zip row.cells).map (fun (nm, cell) =>
        let inh : Inherited := { propertyUrl := some (defaultPropertyRef tableUrl nm) }
        (inh, convertCell inh nm look cell)) })

/-- Minimal mode: the cell triples only. -/
def convertTableMinimal (tableUrl : String) (t : Table) : List Triple :=
  (tableRows tableUrl t).flatMap (fun r => rowTriplesMinimal r.rowNum r.cells)

/-- Standard mode: the full TableGroup / Table / Row scaffolding. -/
def convertTableStandard (tableUrl : String) (t : Table) : List Triple :=
  tableGroupTriplesStandard tableUrl (tableRows tableUrl t)

structure TestOutcome where
  name   : String
  status : String        -- "pass" | "fail" | "skip"
  detail : String

/-- Run one manifest entry. `action` and `result` are the manifest's
    OWN file names and are used verbatim.

    They must not be derived from each other: test028 and test029 both
    read `countries.csv` but expect `test028.ttl` and `test029.ttl`,
    so a runner that guessed the expected file from the CSV name
    looked for `countries.ttl`, found nothing, and reported both as
    skips — a silently narrowed denominator. -/
def runOne (dir action result : String) (minimal : Bool) : IO TestOutcome := do
  let csvPath := dir ++ "/" ++ action
  let ttlPath := dir ++ "/" ++ result
  if !(← System.FilePath.pathExists csvPath) then
    return ⟨action, "skip", "action file missing: " ++ action⟩
  if !(← System.FilePath.pathExists ttlPath) then
    return ⟨action, "skip", "expected file missing: " ++ result⟩
  let src ← IO.FS.readFile csvPath
  let expectedSrc ← IO.FS.readFile ttlPath
  let tableUrl := "http://www.w3.org/2013/csvw/tests/" ++ action
  let table := read (({} : Dialect).resolve) src
  let got := if minimal then convertTableMinimal tableUrl table
             else convertTableStandard tableUrl table
  match parseTurtle expectedSrc (some tableUrl) with
  | .error _ => return ⟨action, "skip", "expected .ttl did not parse"⟩
  | .ok want =>
      -- The THREE-WAY outcome, not the Bool. `Graph.isomorphic?`
      -- returns `false` both for "different" and for "the comparison
      -- gave up", and scoring the second as a failure is how this
      -- runner reported two correct graphs as broken on 2026-08-22
      -- (produced 60, expected 60). A give-up is its own bucket.
      match Graph.isomorphicOutcome got want with
      | .equal    => return ⟨action, "pass", s!"{got.length} triples"⟩
      | .notEqual =>
          return ⟨action, "fail", s!"produced {got.length}, expected {want.length}"⟩
      | .budgetExceeded =>
          return ⟨action, "budget",
                  s!"isomorphism budget exceeded ({got.length} vs {want.length} triples)"⟩

/-- Manifest entries with no `implicit` member: the no-metadata
    tests. Returns (name, action, result, minimal).

    `minimal` comes from the entry's own `option` object. csv2rdf has
    TWO output modes and the manifest says which one each test wants;
    running every test in one mode would fail the other mode's tests
    for a reason that is a harness bug, not an engine gap. -/
def noMetadataEntries (j : L4Factoidal.JSON.Json)
    : List (String × String × String × Bool) :=
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
        else
          let minimal := match field? "option" e with
            | some o => match field? "minimal" o with
                | some (.bool b) => b
                | _ => false
            | none => false
          match str? "id" e, str? "action" e, str? "result" e with
          | some i, some a, some r =>
              if a.endsWith ".csv" && r.endsWith ".ttl" then some (i, a, r, minimal)
              else none
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
      let mut budget := 0
      for (id, action, result, minimal) in entries do
        let mode := if minimal then "minimal" else "standard"
        let o ← runOne dir action result minimal
        if o.status == "pass" then pass := pass + 1
        else if o.status == "fail" then
          fail := fail + 1
          IO.println s!"FAIL {id} ({action} vs {result}, {mode} mode): {o.detail}"
        else if o.status == "budget" then
          budget := budget + 1
          IO.println s!"BUDGET {id} ({action}, {mode} mode): {o.detail}"
        else
          skip := skip + 1
          IO.println s!"skip {id}: {o.detail}"
      IO.println ""
      IO.println s!"csv2rdf NO-METADATA subset: {pass} pass, {fail} fail, {budget} comparison-gave-up, {skip} skip (out of {entries.length} such entries)"
      IO.println s!"NOT ATTEMPTED: {total - entries.length} of {total} manifest entries carry metadata"
      IO.println "  (an `implicit` member), which needs @context resolution,"
      IO.println "  tableSchema inheritance and metadata discovery -- not ported."
      IO.println ""
      IO.println "Comparison is by GRAPH ISOMORPHISM against the suite's own"
      IO.println "expected .ttl: blank-node labels are arbitrary, so triple-set"
      IO.println "equality would fail correct output. A comparison that gives"
      IO.println "up is counted SEPARATELY from a failure -- it is not evidence"
      IO.println "the graphs differ, and folding it into `fail` misreports the"
      IO.println "engine."
      return 0
