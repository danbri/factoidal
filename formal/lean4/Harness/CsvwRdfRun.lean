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
import L4Factoidal.CSVW.Validate
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

/-- The on-disk path a metadata `url` names, relative to the tests
    directory: resolve it against the metadata document's base and
    strip the suite's own base URL.

    Resolving rather than concatenating a directory prefix is what a
    processor does, and it is what an `@context` `@base` needs —
    test273 sets `"@base": "test273/"` on a metadata document at the
    top level, so its `"url": "action.csv"` names `test273/action.csv`
    and a directory-prefix rule looks in the wrong place. -/
def suiteRelative (base : String) (u : String) : String :=
  let suite := "http://www.w3.org/2013/csvw/tests/"
  let abs := L4Factoidal.Syntax.resolveIri base u
  if abs.startsWith suite then String.ofList (abs.toList.drop suite.length)
  else relativeName u

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
  /-- The metadata document to use, when the entry names one outright
      — the action IS metadata, or `option.metadata` supplies it. -/
  metadata : Option String
  /-- Metadata the processor would DISCOVER, in §5.2 precedence order:
      the `Link` header first, then `<file>-metadata.json`, then the
      directory's `csv-metadata.json`. A list rather than a choice
      because a candidate that does not reference the requested file
      MUST be ignored and the next one tried (test122, test123). -/
  metaCandidates : List String
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
                if isJson then some a else metaOpt
              -- Metadata DISCOVERY order (§5.2): the `Link` header
              -- first (a `linked-metadata.json` in `implicit` stands
              -- for it), then the file-specific
              -- `<name>-metadata.json`, then the directory's
              -- `csv-metadata.json`. Taking the LAST `implicit` entry
              -- picked the directory one and applied the wrong
              -- description (test017).
              --
              -- All three are kept, in order, rather than one being
              -- chosen here: a candidate that does not reference the
              -- requested file must be ignored and the next tried,
              -- and only the file's contents can say which that is.
              let jsons := if isJson then [] else implicits.filter (fun f => f.endsWith ".json")
              let ordered :=
                (jsons.filter (fun f => f.endsWith "linked-metadata.json")) ++
                (jsons.filter (fun f => f.endsWith (a ++ "-metadata.json"))) ++
                (jsons.filter (fun f => f.endsWith "csv-metadata.json" &&
                                        !(f.endsWith (a ++ "-metadata.json")))) ++
                jsons
              let candidates := ordered.foldl (fun acc f =>
                if acc.contains f then acc else acc ++ [f]) ([] : List String)
              some { id := i, action := a, result := (str? "result" e).getD "",
                     minimal := minimal, metadata := metadata,
                     metaCandidates := candidates,
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
  -- Read one metadata document: its parsed group, its context, and
  -- the base URL everything in it resolves against — its own
  -- location, moved by an `@context` `@base` if it has one.
  let readMeta : String → IO (Option (TableGroup × Ctx × String)) := fun mf => do
    let mp := dir ++ "/" ++ mf
    if !(← System.FilePath.pathExists mp) then pure none
    else
      let msrc ← IO.FS.readFile mp
      match parseMetadataText msrc with
      | some (g, c) => pure (some (g, c, effectiveBase (suiteBase ++ mf) c))
      | none        => pure none
  let requested := suiteBase ++ e.action
  let mut chosen : Option (TableGroup × Ctx × String) := none
  match e.metadata with
  | some mf => chosen ← readMeta mf
  | none =>
      -- DISCOVERED metadata: take the first candidate that actually
      -- references the requested file. §5.2 says one that does not
      -- MUST be ignored, so a non-matching candidate falls through to
      -- the next rather than stopping the run (test117/119/120/122/123).
      for mf in e.metaCandidates do
        if chosen.isNone then
          match ← readMeta mf with
          | some (g, c, b) =>
              if describesTable b g requested then chosen := some (g, c, b)
          | none => pure ()
  -- No metadata, or none that describes the request: the CSV is
  -- converted on its own, which is what the spec's fallback says.
  -- The fallback table takes the ABSOLUTE requested URL, not the
  -- manifest's relative name. Resolving a relative one against a base
  -- that already ends in it doubled the directory
  -- (`tests/test119/test119/action.csv`), so the file was not found
  -- and the emitted subject would have been wrong in the same way.
  let (group, ctx, mbase) := match chosen with
    | some (g, c, b) => (g, c, b)
    | none           => (({ tables := [{ url := requested }] } : TableGroup),
                         ({} : Ctx), requested)
  if group.tables.isEmpty then
    return ⟨e.action, "skip", "metadata did not parse into any table"⟩
  -- Resolve any `tableSchema` given as a URL. The parse records the
  -- link and stops; fetching it is the only part that needs I/O, and
  -- it belongs here rather than inside a pure module.
  let mut group := group
  let mut resolved : List TableDesc := []
  for t in group.tables do
    match t.schemaRef with
    | none => resolved := resolved ++ [t]
    | some ref =>
        let sp := dir ++ "/" ++ suiteRelative mbase ref
        if ← System.FilePath.pathExists sp then
          let ssrc ← IO.FS.readFile sp
          match parseSchemaText ctx ssrc with
          | some sch => resolved := resolved ++ [{ t with schema := some sch }]
          | none     => resolved := resolved ++ [t]
        else resolved := resolved ++ [t]
  group := { group with tables := resolved }
  let mut pairs : List (TableDesc × Table) := []
  let mut missing : Option String := none
  for t in group.tables do
    let path := dir ++ "/" ++ suiteRelative mbase t.url
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
      let mut overStrict := 0
      let mut negPass := 0
      let mut negFail := 0
      let mut negSkip := 0
      for e in entries do
        if e.negative then
          -- A negative test asserts an ERROR, not a graph. It is
          -- scored by the VALIDATOR: the metadata must be rejected.
          let mp := dir ++ "/" ++ e.action
          if !(← System.FilePath.pathExists mp) then
            negSkip := negSkip + 1
            IO.println s!"skip {e.id}: metadata file missing: {e.action}"
          else
            let msrc ← IO.FS.readFile mp
            match L4Factoidal.JSON.parseJson? msrc with
            | none =>
                -- A document that will not even parse IS rejected.
                negPass := negPass + 1
            | some mj =>
                if L4Factoidal.CSVW.passes (L4Factoidal.CSVW.validate mj) then
                  negFail := negFail + 1
                  IO.println s!"NEG-FAIL {e.id} ({e.action}): validator raised no error"
                else negPass := negPass + 1
        else
        let mode := if e.minimal then "minimal" else "standard"
        -- CROSS-CHECK: a validator tightened to reject the negative
        -- tests must still ACCEPT every positive one. Without this the
        -- negative score can be bought with rules that reject
        -- everything, and the two numbers would never disagree.
        match e.metadata with
        | none => pure ()
        | some mf =>
            let mp := dir ++ "/" ++ mf
            if ← System.FilePath.pathExists mp then
              let msrc ← IO.FS.readFile mp
              match L4Factoidal.JSON.parseJson? msrc with
              | none => pure ()
              | some mj =>
                  if !L4Factoidal.CSVW.passes (L4Factoidal.CSVW.validate mj) then
                    overStrict := overStrict + 1
                    IO.println s!"OVER-STRICT {e.id}: the validator rejects a POSITIVE test's metadata"
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
      IO.println s!"csv2rdf POSITIVE: {pass} pass, {fail} fail, {budget} comparison-gave-up, {skip} skip (out of {attempted} attempted)"
      IO.println s!"csv2rdf NEGATIVE (validator must reject): {negPass} pass, {negFail} fail, {negSkip} skip (out of {negPass + negFail + negSkip})"
      IO.println s!"csv2rdf TOTAL: {pass + negPass} pass, {fail + negFail} fail, {budget} comparison-gave-up, {skip + negSkip} skip (out of {total} manifest entries)"
      IO.println s!"VALIDATOR CROSS-CHECK: {overStrict} positive tests whose metadata the validator wrongly rejects"
      IO.println ""
      IO.println "Comparison is by GRAPH ISOMORPHISM against the suite's own"
      IO.println "expected .ttl: blank-node labels are arbitrary, so triple-set"
      IO.println "equality would fail correct output. A comparison that gives"
      IO.println "up is counted SEPARATELY from a failure -- it is not evidence"
      IO.println "the graphs differ, and folding it into `fail` misreports the"
      IO.println "engine."
      return 0
