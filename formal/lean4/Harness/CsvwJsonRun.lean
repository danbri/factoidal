/-
Harness/CsvwJsonRun — a REAL csv2json conformance runner over the
vendored W3C csvw corpus.

Same shape as `CsvwRdfRun`, and deliberately so: the manifest is the
suite's own `manifest-json.jsonld`, the pairing comes from each
entry's `action` / `result`, and everything not attempted is REPORTED
with its reason.

The comparison is STRUCTURAL JSON equality that ignores the order of
an object's members and respects the order of an array's items. That
distinction is the whole point: csv2json fixes the order of `row` and
`describes` (which is why `"ordered"` columns exist at all), while
JSON object member order carries no meaning. Comparing raw text would
fail correct output on whitespace, and comparing with array order
ignored would pass output that had lost the ordering the specification
requires.

Usage: `lake exe l4csvw-json [tests-dir]`
-/
import L4Factoidal.CSVW.JsonDoc
import L4Factoidal.CSVW.Validate
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

open L4Factoidal.CSVW
open L4Factoidal.JSON
open L4Factoidal.Syntax

/-- Structural JSON equality: object members are a SET of pairs, array
    items are a SEQUENCE. `fuel` bounds the nesting; a document deeper
    than that compares unequal rather than looping. -/
def jsonEquiv : Nat → Json → Json → Bool
  | 0,        _, _ => false
  | _ + 1,    .null, .null => true
  | _ + 1,    .bool a, .bool b => a == b
  | _ + 1,    .string a, .string b => a == b
  | _ + 1,    .number a, .number b => normNum a == normNum b
  | fuel + 1, .array as, .array bs =>
      as.length == bs.length && (as.zip bs).all (fun (x, y) => jsonEquiv fuel x y)
  | fuel + 1, .object as, .object bs =>
      as.length == bs.length &&
      as.all (fun (k, v) =>
        match (bs.find? (fun (k2, _) => k2 == k)).map (·.2) with
        | some w => jsonEquiv fuel v w
        | none   => false)
  | _ + 1,    _, _ => false
where
  /-- Two JSON numbers are the same number even when written
      differently. The parser keeps the SOURCE TEXT, so `1.0`, `1` and
      `0.0e0` arrive as different strings while denoting one value;
      comparing the text would fail correct output for a reason that is
      not a defect. The EXPONENT is expanded here rather than
      approximated through a float, so the comparison stays exact. -/
  normNum (s : String) : String :=
    let cs := s.toList
    let (mantChars, expChars) :=
      match cs.findIdx? (fun c => c == 'e' || c == 'E') with
      | some i => (cs.take i, cs.drop (i + 1))
      | none   => (cs, [])
    let exp : Int :=
      if expChars.isEmpty then 0
      else
        let neg := expChars.head? == some '-'
        let ds := expChars.filter Char.isDigit
        let v : Int := (String.ofList ds).toNat!
        if neg then -v else v
    let neg := mantChars.head? == some '-'
    let body := if neg || mantChars.head? == some '+' then mantChars.drop 1 else mantChars
    let (ip, fp) := match body.findIdx? (· == '.') with
      | some i => (body.take i, body.drop (i + 1))
      | none   => (body, [])
    let digits := ip ++ fp
    -- The decimal point sits `ip.length + exp` places from the left.
    let pointPos : Int := (ip.length : Int) + exp
    let (digits, pointPos) :=
      if pointPos ≤ 0 then
        (List.replicate (1 - pointPos).toNat '0' ++ digits, (1 : Int))
      else (digits, pointPos)
    let digits :=
      if pointPos > digits.length then
        digits ++ List.replicate (pointPos.toNat - digits.length) '0'
      else digits
    let cut := pointPos.toNat
    let ipOut := (digits.take cut).dropWhile (· == '0')
    let fpOut := (digits.drop cut).reverse.dropWhile (· == '0') |>.reverse
    let ipStr := if ipOut.isEmpty then "0" else String.ofList ipOut
    let fpStr := String.ofList fpOut
    (if neg && !(ipStr == "0" && fpStr == "") then "-" else "")
      ++ ipStr ++ (if fpStr == "" then "" else "." ++ fpStr)

structure JsonOutcome where
  name   : String
  status : String        -- "pass" | "fail" | "skip"
  detail : String

def dirOfJ (p : String) : String :=
  match (p.splitOn "/").reverse with
  | _ :: rest => if rest.isEmpty then "" else String.intercalate "/" rest.reverse ++ "/"
  | []        => ""

def relativeNameJ (u : String) : String :=
  if u.startsWith "http://" || u.startsWith "https://" then
    (u.splitOn "/").getLast?.getD u
  else u

/-- The on-disk path a metadata `url` names: resolve it against the
    metadata document's base and strip the suite's own base URL. This
    is what an `@context` `@base` needs — test273 puts `"@base":
    "test273/"` on a top-level metadata document, so its `"url":
    "action.csv"` names `test273/action.csv`. -/
def suiteRelativeJ (base : String) (u : String) : String :=
  let suite := "http://www.w3.org/2013/csvw/tests/"
  let abs := L4Factoidal.Syntax.resolveIri base u
  if abs.startsWith suite then String.ofList (abs.toList.drop suite.length)
  else relativeNameJ u

structure JEntry where
  id        : String
  action    : String
  result    : String
  minimal   : Bool
  metadata  : Option String
  /-- Metadata the processor would DISCOVER, in §5.2 precedence order.
      A list rather than a choice because a candidate that does not
      reference the requested file MUST be ignored and the next one
      tried. Same rule, same reason, as `CsvwRdfRun`. -/
  metaCandidates : List String
  negative  : Bool

def jsonManifestEntries (j : Json) : List JEntry :=
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
        let opt := field? "option" e
        let minimal := match opt.bind (field? "minimal") with
          | some (.bool b) => b
          | _ => false
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
        let negative := match str? "type" e with
          | some t => t.endsWith "NegativeJsonTest"
          | none   => false
        match str? "id" e, str? "action" e with
        | some i, some a =>
            let isCsv := a.endsWith ".csv"
            let isJson := a.endsWith ".json"
            if !isCsv && !isJson then none
            else
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
              some { id := i, action := a, result := (str? "result" e).getD "",
                     minimal := minimal, metadata := metadata,
                     metaCandidates := candidates, negative := negative }
        | _, _ => none)
  | _ => []

/-- `--dump=<manifest id>` prints both documents. A diagnostic; the
    score is computed the same either way. -/
def runOneJson (dir : String) (e : JEntry) (dump : Bool := false) : IO JsonOutcome := do
  if e.result == "" then
    return ⟨e.action, "skip", "entry names no expected result"⟩
  let rp := dir ++ "/" ++ e.result
  if !(← System.FilePath.pathExists rp) then
    return ⟨e.action, "skip", "expected file missing: " ++ e.result⟩
  let expectedSrc ← IO.FS.readFile rp
  let suiteBase := "http://www.w3.org/2013/csvw/tests/"
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
      -- §5.2: DISCOVERED metadata that does not reference the
      -- requested file MUST be ignored, so a non-matching candidate
      -- falls through to the next.
      for mf in e.metaCandidates do
        if chosen.isNone then
          match ← readMeta mf with
          | some (g, c, b) =>
              if describesTable b g requested then chosen := some (g, c, b)
          | none => pure ()
  -- The fallback table takes the ABSOLUTE requested URL: resolving a
  -- relative one against a base that already ends in it doubles the
  -- directory.
  let (group, ctx, mbase) := match chosen with
    | some (g, c, b) => (g, c, b)
    | none           => (({ tables := [{ url := requested }] } : TableGroup),
                         ({} : Ctx), requested)
  if group.tables.isEmpty then
    return ⟨e.action, "skip", "metadata did not parse into any table"⟩
  let mut group := group
  let mut resolved : List TableDesc := []
  for t in group.tables do
    match t.schemaRef with
    | none => resolved := resolved ++ [t]
    | some ref =>
        let sp := dir ++ "/" ++ suiteRelativeJ mbase ref
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
    let path := dir ++ "/" ++ suiteRelativeJ mbase t.url
    if ← System.FilePath.pathExists path then
      let src ← IO.FS.readFile path
      pairs := pairs ++ [(t, read (effectiveDialect group t).resolve src)]
    else
      missing := some t.url
  match missing with
  | some u => return ⟨e.action, "skip", "table file not found: " ++ u⟩
  | none => pure ()
  let got := convertJson mbase ctx group e.minimal pairs
  match parseJson? expectedSrc with
  | none => return ⟨e.action, "skip", "expected .json did not parse"⟩
  | some want =>
      if dump then do
        IO.println s!"--- {e.id} PRODUCED ---"
        IO.println (Json.toStringPretty got)
        IO.println s!"--- {e.id} EXPECTED ---"
        IO.println (Json.toStringPretty want)
      if jsonEquiv 64 got want then return ⟨e.action, "pass", ""⟩
      else return ⟨e.action, "fail", "structural JSON mismatch"⟩

def main (args : List String) : IO UInt32 := do
  let dir := (args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/csvw/tests"
  let manifestPath := dir ++ "/manifest-json.jsonld"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"csvw json runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match parseJson? mtext with
  | none =>
      IO.println "csvw json runner: manifest did not parse"
      return 1
  | some mjson =>
      let dumpId := (args.find? (fun a => a.startsWith "--dump=")).map
        (fun a => String.ofList (a.toList.drop 7))
      let entries := jsonManifestEntries mjson
      let total : Nat := match mjson with
        | Json.object ms =>
            match (ms.find? (fun (k, _) => k == "entries")).map (·.2) with
            | some (Json.array es) => es.length
            | _ => 0
        | _ => 0
      let mut pass := 0
      let mut fail := 0
      let mut skip := 0
      let mut overStrict := 0
      let mut negPass := 0
      let mut negFail := 0
      let mut negSkip := 0
      for e in entries do
        if e.negative then
          -- A negative test asserts an ERROR, not a document. It is
          -- scored by the VALIDATOR: the metadata must be rejected.
          let mp := dir ++ "/" ++ e.action
          if !(← System.FilePath.pathExists mp) then
            negSkip := negSkip + 1
            IO.println s!"skip {e.id}: metadata file missing: {e.action}"
          else
            let msrc ← IO.FS.readFile mp
            match parseJson? msrc with
            | none => negPass := negPass + 1
            | some mj =>
                if L4Factoidal.CSVW.passes (L4Factoidal.CSVW.validate mj) then
                  negFail := negFail + 1
                  IO.println s!"NEG-FAIL {e.id} ({e.action}): validator raised no error"
                else negPass := negPass + 1
        else
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
              match parseJson? msrc with
              | none => pure ()
              | some mj =>
                  if !L4Factoidal.CSVW.passes (L4Factoidal.CSVW.validate mj) then
                    overStrict := overStrict + 1
                    IO.println s!"OVER-STRICT {e.id}: the validator rejects a POSITIVE test's metadata"
        let o ← runOneJson dir e (dumpId == some e.id)
        if o.status == "pass" then pass := pass + 1
        else if o.status == "fail" then
          fail := fail + 1
          IO.println s!"FAIL {e.id} ({e.action} vs {e.result}): {o.detail}"
        else
          skip := skip + 1
          IO.println s!"skip {e.id}: {o.detail}"
      let attempted := pass + fail + skip
      IO.println ""
      IO.println s!"csv2json POSITIVE: {pass} pass, {fail} fail, {skip} skip (out of {attempted} attempted)"
      IO.println s!"csv2json NEGATIVE (validator must reject): {negPass} pass, {negFail} fail, {negSkip} skip (out of {negPass + negFail + negSkip})"
      IO.println s!"csv2json TOTAL: {pass + negPass} pass, {fail + negFail} fail, {skip + negSkip} skip (out of {total} manifest entries)"
      IO.println s!"VALIDATOR CROSS-CHECK: {overStrict} positive tests whose metadata the validator wrongly rejects"
      IO.println ""
      IO.println "Comparison is STRUCTURAL: object members are a set, array items"
      IO.println "a sequence. csv2json fixes the order of `row` and `describes`,"
      IO.println "so ignoring array order would pass output that lost it."
      return 0
