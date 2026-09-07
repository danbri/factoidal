/-
Harness/CsvwValidateRun — the W3C csvw VALIDATION manifest, run end to
end (`lake exe l4csvw-validate`).

Spec: https://www.w3.org/TR/tabular-data-model/ (structural rules) and
https://www.w3.org/TR/tabular-metadata/ §5.11.2/§6.4.9 (cell format,
`required`, `primaryKey`) — the same split `CSVW.Validate` documents.

A document CONFORMS iff its metadata JSON parses, decodes into a
`TableGroup`, the raw-JSON structural checks
(`CSVW.Validate.checkTableGroup`/`checkTable`) find no violation, and
the data-level checks (`CSVW.Validate.checkData`) find no violation.
A `PositiveValidationTest` / `WarningValidationTest` PASSES iff the
document conforms (a warning does not fail it); a
`NegativeValidationTest` PASSES iff it does NOT conform.

Manifest entries are read the same way `Harness/CsvwRdfRun.lean` reads
`manifest-rdf.jsonld` (same suite, same `action`/`option.metadata`/
`implicit` shape) — reproduced here rather than imported, because that
file is itself an executable's root module (its own top-level `main`)
and importing it would collide with this one's. Every Lean W3C harness
in this tree follows the same pattern: manifest reading lives with the
runner that needs it (see `Harness/JsonLdFrameRun.lean`,
`Harness/JsonLdProbe.lean`).

Usage: `lake exe l4csvw-validate [tests-dir]`

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Fixtures
import Harness.Common
import L4Factoidal.CSVW.Pipeline
import L4Factoidal.CSVW.Validate
import L4Factoidal.JSON.Parser

open L4Factoidal.CSVW
open L4Factoidal.JSON (Json)

/-- The three manifest test kinds. -/
inductive VKind where
  | positive | warning | negative
deriving DecidableEq, Repr

def VKind.label : VKind → String
  | .positive => "positive" | .warning => "warning" | .negative => "negative"

/-- One manifest entry, reduced to what the runner needs. -/
structure VEntry where
  id       : String
  kind     : VKind
  action   : String
  /-- The metadata document to use, when the entry names one outright
      — the action IS metadata, or `option.metadata` supplies it. -/
  metadata : Option String
  /-- Metadata the processor would DISCOVER, in §5.2 precedence order
      (see `CsvwRdfRun.lean`'s `manifestEntries` for why all three
      candidates are kept rather than one chosen here). -/
  metaCandidates : List String

/-- Every entry the manifest lists. Nothing is filtered out here — the
    run loop decides what it can attempt, so the denominator stays the
    manifest's own. -/
def manifestEntries (j : Json) : List VEntry :=
  let field? (k : String) (v : Json) : Option Json :=
    match v with
    | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
    | _ => none
  let str? (k : String) (v : Json) : Option String :=
    match field? k v with
    | some (.string s) => some s
    | _ => none
  match field? "entries" j with
  | some (.array es) =>
      es.filterMap (fun e =>
        let typeStr := (str? "type" e).getD ""
        let kind : VKind :=
          if typeStr.endsWith "NegativeValidationTest" then .negative
          else if typeStr.endsWith "WarningValidationTest" then .warning
          else .positive
        let opt := field? "option" e
        let implicits : List String := match field? "implicit" e with
          | some (Json.array a) =>
              a.filterMap (fun x => match x with
                | Json.string s => some s
                | _ => none)
          | some (Json.string s) => [s]
          | _ => []
        let metaOpt := opt.bind (fun o => match field? "metadata" o with
          | some (.string s) => some s
          | _ => none)
        match str? "id" e, str? "action" e with
        | some i, some a =>
            let stem := match a.splitOn "?" with
              | b :: _ => b
              | []     => a
            let isJson := stem.endsWith ".json"
            -- When the action is metadata, it IS the metadata
            -- document; `option.metadata` only names a USER metadata
            -- file that accompanies a CSV action.
            let metadata := if isJson then some a else metaOpt
            let jsons := if isJson then [] else implicits.filter (fun f => f.endsWith ".json")
            let ordered :=
              (jsons.filter (fun f => f.endsWith "linked-metadata.json")) ++
              (jsons.filter (fun f => f.endsWith (a ++ "-metadata.json"))) ++
              (jsons.filter (fun f => f.endsWith "csv-metadata.json" &&
                                      !(f.endsWith (a ++ "-metadata.json")))) ++
              jsons
            let candidates := ordered.foldl (fun acc f =>
              if acc.contains f then acc else acc ++ [f]) ([] : List String)
            some { id := i, kind := kind, action := a, metadata := metadata,
                   metaCandidates := candidates }
        | _, _ => none)
  | _ => []

/-- The on-disk path a metadata `url` names, relative to the tests
    directory: resolve it against the metadata document's own base and
    strip the suite's own base URL (see `CsvwRdfRun.lean`'s
    `suiteRelative`, reproduced identically). -/
def suiteRelative (base : String) (u : String) : String :=
  let suite := "http://www.w3.org/2013/csvw/tests/"
  let abs := L4Factoidal.Syntax.resolveIri base u
  let noQuery := match abs.splitOn "?" with
    | b :: _ => b
    | []     => abs
  if noQuery.startsWith suite then String.ofList (noQuery.toList.drop suite.length)
  else if u.startsWith "http://" || u.startsWith "https://" then
    (u.splitOn "/").getLast?.getD u
  else u

/-- One entry's verdict: does the described document conform, and why
    not when it doesn't. `none` means the entry could not be attempted
    at all (a file the manifest names is missing) — reported as a
    SKIP, never silently dropped from the denominator. -/
def runOne (dir : String) (e : VEntry) : IO (Option (Bool × List String)) := do
  let suiteBase := "http://www.w3.org/2013/csvw/tests/"
  -- Read one metadata document: its raw JSON tree (for the structural
  -- checks), its decoded group + context (for the data-level checks,
  -- when decoding succeeds), and the base URL everything in it
  -- resolves against.
  let readMeta : String → IO (Option (Json × Option (TableGroup × Ctx) × String)) := fun mf => do
    let mp := dir ++ "/" ++ mf
    if !(← System.FilePath.pathExists mp) then pure none
    else
      let msrc ← IO.FS.readFile mp
      match L4Factoidal.JSON.parseJson? msrc with
      | none    => pure none
      | some rj =>
          let decoded := parseMetadata rj
          let base := match decoded with
            | some (_, c) => effectiveBase (suiteBase ++ mf) c
            | none        => suiteBase ++ mf
          pure (some (rj, decoded, base))
  let requested := suiteBase ++ e.action
  let mut chosen : Option (Json × Option (TableGroup × Ctx) × String) := none
  let mut metaMissing := false
  match e.metadata with
  | some mf =>
      match ← readMeta mf with
      | some c => chosen := some c
      | none   => metaMissing := true
  | none =>
      for mf in e.metaCandidates do
        if chosen.isNone then
          match ← readMeta mf with
          | some (rj, some (g, c), b) =>
              if describesTable b g requested then chosen := some (rj, some (g, c), b)
          | _ => pure ()
  if metaMissing then
    -- A named metadata file that is not on disk: the entry cannot be
    -- attempted (this suite ships every fixture it references, so
    -- this is a missing-fixture report, not a verdict).
    return none
  match chosen with
  | none =>
      -- No metadata at all (a bare-CSV positive test) or none of the
      -- discovered candidates described the request: the CSV converts
      -- on its own, per the spec's fallback. Nothing structural or
      -- data-level to check against — such a document always
      -- conforms.
      let path := dir ++ "/" ++ suiteRelative requested e.action
      if !(← System.FilePath.pathExists path) then return none
      return some (true, [])
  | some (rawJson, none, _) =>
      -- The JSON parsed but the lenient decoder could not build ANY
      -- table or table group from it (`parseMetadata` returned
      -- `none`) — a genuine decode failure. The raw-JSON structural
      -- checks still run: they are what catches most of these anyway
      -- (a root with neither `tables` nor `url`, for instance).
      let structural := validate rawJson
      let findings := (err "metadata failed to decode") :: structural
      return some (passes findings, (findings.filter (·.severity == .error)).map (·.message))
  | some (rawJson, some (group, ctx), mbase) =>
      let structural := validate rawJson
      -- Resolve any `tableSchema` given as a URL, exactly as
      -- `CsvwRdfRun.lean` does: the parse records the link and stops,
      -- and fetching it is the only part that needs I/O.
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
      let group := { group with tables := resolved }
      let mut pairs : List (TableDesc × Table) := []
      for t in group.tables do
        let path := dir ++ "/" ++ suiteRelative mbase t.url
        if ← System.FilePath.pathExists path then
          let src ← IO.FS.readFile path
          pairs := pairs ++ [(t, read (effectiveDialect group t).resolve src)]
        else
          -- The table's file is not on disk: read it as empty rather
          -- than skip the whole entry. Several validation fixtures
          -- test only the metadata SHAPE and ship no accompanying CSV
          -- at all; an empty table contributes no data-level finding
          -- of its own, and the structural findings above are
          -- unaffected.
          pairs := pairs ++ [(t, ({ header := [], rows := [] } : Table))]
      let dataFindings := checkData group pairs
      let findings := structural ++ dataFindings
      return some (passes findings, (findings.filter (·.severity == .error)).map (·.message))

def main (args : List String) : IO UInt32 := do
  let argDir := (args.filter (fun a => !a.startsWith "--")).head?
  let dir ← Harness.fixtureArgOr argDir "third_party/testing/csvw/tests"
  let manifestPath := dir ++ "/manifest-validation.jsonld"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"csvw-validation: manifest not found: {manifestPath}"
    IO.println (Harness.Diag.line "csvw-validation" { noManifest := 1 })
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match L4Factoidal.JSON.parseJson? mtext with
  | none =>
      IO.println "csvw-validation: manifest did not parse"
      IO.println (Harness.Diag.line "csvw-validation" { noManifest := 1 })
      return 1
  | some mjson =>
      let entries := manifestEntries mjson
      let total := entries.length
      if total == 0 then
        IO.println "csvw-validation: manifest parsed but named no entries"
        IO.println (Harness.Diag.line "csvw-validation" { zeroTests := 1 })
        return 1
      let mut posScore : Harness.Score := {}
      let mut warnScore : Harness.Score := {}
      let mut negScore : Harness.Score := {}
      for e in entries do
        let bucket := e.kind.label
        match ← runOne dir e with
        | none =>
            IO.println s!"SKIP {e.id} ({bucket}): a file the entry names is not on disk"
            match e.kind with
            | .positive => posScore := posScore.bump (.skip "missing fixture")
            | .warning  => warnScore := warnScore.bump (.skip "missing fixture")
            | .negative => negScore := negScore.bump (.skip "missing fixture")
        | some (conforms, reasons) =>
            let ok := match e.kind with
              | .negative => !conforms
              | _         => conforms
            if ok then
              IO.println s!"PASS {e.id} ({bucket})"
              match e.kind with
              | .positive => posScore := posScore.bump .pass
              | .warning  => warnScore := warnScore.bump .pass
              | .negative => negScore := negScore.bump .pass
            else
              let why := if e.kind == VKind.negative then
                           "the document conforms; expected a violation"
                         else String.intercalate "; " reasons
              IO.println s!"FAIL {e.id} ({bucket}): {why}"
              match e.kind with
              | .positive => posScore := posScore.bump (.fail why)
              | .warning  => warnScore := warnScore.bump (.fail why)
              | .negative => negScore := negScore.bump (.fail why)
      let total3 := (posScore.add warnScore).add negScore
      IO.println ""
      IO.println (Harness.Score.line "csvw-validation positive" posScore)
      IO.println (Harness.Score.line "csvw-validation warning" warnScore)
      IO.println (Harness.Score.line "csvw-validation negative" negScore)
      IO.println (Harness.Score.line "csvw-validation" total3)
      IO.println (Harness.Diag.line "csvw-validation" ({} : Harness.Diag))
      IO.println ""
      IO.println "A PositiveValidationTest / WarningValidationTest passes iff the"
      IO.println "document CONFORMS (a warning does not fail it); a"
      IO.println "NegativeValidationTest passes iff it does NOT."
      return if total3.fail > 0 then 1 else 0
