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
suite's OWN `manifest-rdf.jsonld`. Entries with no `implicit` member
run with no metadata; entries that name a metadata file run through
`CSVW.MetadataParse` and `CSVW.Pipeline`. What is still NOT attempted:
entries whose metadata is only DISCOVERABLE (no `option.metadata` and
no usable `implicit` file), and negative tests, which assert an error
rather than a graph. Everything skipped is REPORTED with its reason,
never silently dropped, because a runner that quietly narrows its
denominator reports a number nobody can act on.

Pairing comes from the manifest's `action`/`result`, NOT from matching
filenames. That distinction is not pedantic: `test001.json` is the
expected JSON OUTPUT of the csv2json suite, not input metadata, and
guessing from names mistakes one for the other.

Usage: `lake exe l4csvw-rdf [tests-dir]`
-/
import L4Factoidal.CSVW.Pipeline
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.JSON.Parser

open L4Factoidal.CSVW
open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- The path a table `url` names, relative to the tests directory.
    Metadata `url` values in this corpus are relative already; an
    absolute one is reduced to its last path segment so a document
    that spells out the suite's own base still finds its file. -/
def relativeName (u : String) : String :=
  if u.startsWith "http://" || u.startsWith "https://" then
    (u.splitOn "/").getLast?.getD u
  else u

structure TestOutcome where
  name   : String
  status : String        -- "pass" | "fail" | "skip"
  detail : String

/-- One manifest entry, reduced to what the runner needs. -/
structure Entry where
  id      : String
  action  : String
  result  : String
  minimal : Bool
  /-- The metadata document to use, if the entry has one. -/
  metadata : Option String
  /-- The CSV file, when the entry starts from one. `none` means the
      tables come from the metadata document's own `url`/`tables`. -/
  csvAction : Option String
  negative : Bool

/-- Every entry the manifest lists, with its options. Nothing is
    filtered out here — the run loop decides what it can attempt, so
    the denominator stays the manifest's own.

    The `action` is NOT always a CSV file. 236 of the 270 entries name
    a METADATA document as their action: the test starts from the
    metadata and the CSV files come from its `url` / `tables`. A
    runner that assumed `action` was always the CSV attempted 30 of
    270 and reported the rest as nothing at all — which is how this
    runner first read the manifest. -/
def manifestEntries (j : L4Factoidal.JSON.Json) : List Entry :=
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
        let opt := field? "option" e
        let minimal := match opt.bind (field? "minimal") with
          | some (.bool b) => b
          | _ => false
        let implicits : List String := match field? "implicit" e with
          | some (L4Factoidal.JSON.Json.array a) =>
              a.filterMap (fun x => match x with
                | L4Factoidal.JSON.Json.string s => some s
                | _ => none)
          | some (L4Factoidal.JSON.Json.string s) => [s]
          | _ => []
        let metaOpt := opt.bind (fun o => match field? "metadata" o with
          | some (.string s) => some s
          | _ => none)
        let negative := match str? "type" e with
          | some t => t.endsWith "NegativeRdfTest"
          | none   => false
        match str? "id" e, str? "action" e with
        | some i, some a =>
            let isCsv := a.endsWith ".csv"
            let isJson := a.endsWith ".json"
            if !isCsv && !isJson then none
            else
              -- When the action is metadata, it IS the metadata
              -- document; `option.metadata` only names a USER metadata
              -- file that accompanies a CSV action.
              let metadata :=
                if isJson then some a
                else metaOpt.orElse (fun _ =>
                  (implicits.filter (fun f => f.endsWith ".json")).getLast?)
              some { id := i, action := a, result := (str? "result" e).getD "",
                     minimal := minimal, metadata := metadata,
                     csvAction := if isCsv then some a else none,
                     negative := negative }
        | _, _ => none)
  | _ => []

/-- Print both graphs as N-Triples for one entry. A diagnostic, not a
    gate: the score line never depends on it. -/
def dumpOne (dir : String) (e : Entry) (got want : Graph) : IO Unit := do
  let line (t : Triple) : String :=
    match L4Factoidal.Syntax.Graph.toNTriples [t] .rdf11 with
    | .ok s  => s.trim
    | .error _ => "<unserialisable>"
  IO.println s!"--- {e.id} ({dir}) PRODUCED {got.length} ---"
  for t in (got.map line).mergeSort (· ≤ ·) do IO.println t
  IO.println s!"--- {e.id} EXPECTED {want.length} ---"
  for t in (want.map line).mergeSort (· ≤ ·) do IO.println t

/-- The directory part of a manifest-relative path, with its trailing
    slash. A metadata document in `test011/` names its table as
    `tree-ops.csv`, which is `test011/tree-ops.csv` on disk; resolving
    it against the tests root instead finds the WRONG file of the same
    name at the top level, and the test then fails for a reason that
    has nothing to do with the engine. -/
def dirOf (p : String) : String :=
  match (p.splitOn "/").reverse with
  | _ :: rest => if rest.isEmpty then "" else String.intercalate "/" rest.reverse ++ "/"
  | []        => ""

/-- Run one manifest entry. `action` and `result` are the manifest's
    OWN file names and are used verbatim.

    They must not be derived from each other: test028 and test029 both
    read `countries.csv` but expect `test028.ttl` and `test029.ttl`,
    so a runner that guessed the expected file from the CSV name
    looked for `countries.ttl`, found nothing, and reported both as
    skips — a silently narrowed denominator. -/
def runOne (dir : String) (e : Entry) (dump : Bool := false) : IO TestOutcome := do
  let ttlPath := dir ++ "/" ++ e.result
  if e.result == "" then
    return ⟨e.action, "skip", "entry names no expected result"⟩
  if !(← System.FilePath.pathExists ttlPath) then
    return ⟨e.action, "skip", "expected file missing: " ++ e.result⟩
  let expectedSrc ← IO.FS.readFile ttlPath
  let suiteBase := "http://www.w3.org/2013/csvw/tests/"
  -- The base for the EXPECTED graph is the expected file's own
  -- location, which is what its relative IRIs resolve against.
  let expectedBase := suiteBase ++ e.result
  -- The metadata document's location is the base for everything the
  -- metadata says: a relative `url` inside it resolves against that
  -- file, not against the CSV. Getting this wrong moves every subject.
  let (mbase, mdir) := match e.metadata with
    | some mf => (suiteBase ++ mf, dirOf mf)
    | none    => (suiteBase ++ e.action, dirOf e.action)
  let (group, ctx) ← (do
    match e.metadata with
    | none =>
        pure (({ tables := [{ url := relativeName e.action }] } : TableGroup), ({} : Ctx))
    | some mf =>
        let mp := dir ++ "/" ++ mf
        if !(← System.FilePath.pathExists mp) then
          pure ((({ tables := [] } : TableGroup)), ({} : Ctx))
        else
          let msrc ← IO.FS.readFile mp
          match parseMetadataText msrc with
          | some (g, c) => pure (g, c)
          | none        => pure ((({ tables := [] } : TableGroup)), ({} : Ctx)))
  if group.tables.isEmpty then
    return ⟨e.action, "skip", "metadata did not parse into any table"⟩
  let mut pairs : List (TableDesc × Table) := []
  let mut missing : Option String := none
  for t in group.tables do
    let path := dir ++ "/" ++ mdir ++ relativeName t.url
    if ← System.FilePath.pathExists path then
      let src ← IO.FS.readFile path
      pairs := pairs ++ [(t, read (effectiveDialect group t).resolve src)]
    else
      missing := some t.url
  match missing with
  | some u => return ⟨e.action, "skip", "table file not found: " ++ u⟩
  | none => pure ()
  let got := convert mbase ctx group e.minimal pairs
  match parseTurtle expectedSrc (some expectedBase) with
  | .error _ => return ⟨e.action, "skip", "expected .ttl did not parse"⟩
  | .ok want =>
      if dump then dumpOne dir e got want
      -- The THREE-WAY outcome, not the Bool. `Graph.isomorphic?`
      -- returns `false` both for "different" and for "the comparison
      -- gave up", and scoring the second as a failure is how this
      -- runner reported two correct graphs as broken on 2026-08-22
      -- (produced 60, expected 60). A give-up is its own bucket.
      match Graph.isomorphicOutcome got want with
      | .equal    => return ⟨e.action, "pass", s!"{got.length} triples"⟩
      | .notEqual =>
          return ⟨e.action, "fail", s!"produced {got.length}, expected {want.length}"⟩
      | .budgetExceeded =>
          return ⟨e.action, "budget",
                  s!"isomorphism budget exceeded ({got.length} vs {want.length} triples)"⟩

def main (args : List String) : IO UInt32 := do
  let dir := (args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/csvw/tests"
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
      -- `--dump=<manifest id>` prints both graphs for one entry. A
      -- diagnostic switch; the score is computed the same either way.
      let dumpId := (args.find? (fun a => a.startsWith "--dump=")).map
        (fun a => String.ofList (a.toList.drop 7))
      let entries := manifestEntries mjson
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
      let mut negative := 0
      for e in entries do
        if e.negative then
          -- A negative test asserts an ERROR, not a graph. Scoring it
          -- against an expected `.ttl` it does not have would be a
          -- pass for the wrong reason; it needs the validator's
          -- outcome, which this runner does not drive.
          negative := negative + 1
        else
        let mode := if e.minimal then "minimal" else "standard"
        let o ← runOne dir e (dumpId == some e.id)
        if o.status == "pass" then pass := pass + 1
        else if o.status == "fail" then
          fail := fail + 1
          IO.println s!"FAIL {e.id} ({e.action} vs {e.result}, {mode} mode): {o.detail}"
        else if o.status == "budget" then
          budget := budget + 1
          IO.println s!"BUDGET {e.id} ({e.action}, {mode} mode): {o.detail}"
        else
          skip := skip + 1
          IO.println s!"skip {e.id}: {o.detail}"
      let attempted := pass + fail + budget + skip
      IO.println ""
      IO.println s!"csv2rdf: {pass} pass, {fail} fail, {budget} comparison-gave-up, {skip} skip (out of {attempted} attempted)"
      IO.println s!"NOT ATTEMPTED: {negative} negative tests (they assert an ERROR,"
      IO.println "  not a graph, and need the validator's outcome rather than an"
      IO.println s!"  expected .ttl) out of the manifest's {total} entries."
      IO.println ""
      IO.println "Comparison is by GRAPH ISOMORPHISM against the suite's own"
      IO.println "expected .ttl: blank-node labels are arbitrary, so triple-set"
      IO.println "equality would fail correct output. A comparison that gives"
      IO.println "up is counted SEPARATELY from a failure -- it is not evidence"
      IO.println "the graphs differ, and folding it into `fail` misreports the"
      IO.println "engine."
      return 0
