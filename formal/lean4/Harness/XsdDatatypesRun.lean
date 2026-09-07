/-
Harness/XsdDatatypesRun — the W3C XML Schema Test Suite (`w3c/xsdtests`),
DATATYPE tests only, run against `L4Factoidal.XSD`.

The suite's own manifests decide the denominator: `suite.xml` names the
`*Meta/*.testSet` files, each of those carries `testGroup`s with a
`schemaTest` and its `instanceTest`s, and every one names the expected
`validity`. The manifests are XML and are read by the project's own XML
parser, so no second reader of the syntax under test exists.

## What is scored, and what is only counted

Part 2 Datatypes is this run; Part 1 Structures is not
(https://github.com/danbri/factoidal/issues/666). So each test group is
CLASSIFIED from its schema document:

  * `datatype`   — the schema has only simple type definitions and
    element declarations of simple type. Its instance tests are SCORED.
  * `structures` — complex types, attributes, groups, identity
    constraints. Counted, never scored.
  * `mixed`      — both, or `include`/`import`/`redefine`/`override`,
    which this reader does not follow.

Four further buckets keep a test out of the score for a stated reason
rather than counting as a failure:

  * `schema-invalid` — the group's `schemaTest` expects the SCHEMA to be
    rejected, so the instance outcome is not defined.
  * `version-1.0` — the group applies to XSD 1.0 only; this engine
    implements 1.1, in which the answer may differ.
  * `unreadable` — the instance or schema document does not parse, or
    the element declaration is not found.
  * `not-simple` — the instance's document element has element
    children, so it is not a datatype instance.

Usage:
  lake -d formal/lean4 exe l4xsd-datatypes [suite-dir] [--verbose]
                                           [--set NAME] [--limit N]
-/
import L4Factoidal.XSD.SchemaReader

open L4Factoidal.XML
open L4Factoidal.XSD

/-! ## Manifest reading -/

structure Counts where
  scored     : Nat := 0
  pass       : Nat := 0
  fail       : Nat := 0
  structures : Nat := 0
  mixed      : Nat := 0
  schemaInvalid : Nat := 0
  version10  : Nat := 0
  unreadable : Nat := 0
  notSimple  : Nat := 0
  schemaTests : Nat := 0
deriving Repr, Inhabited

def Counts.add (a b : Counts) : Counts :=
  { scored := a.scored + b.scored, pass := a.pass + b.pass,
    fail := a.fail + b.fail, structures := a.structures + b.structures,
    mixed := a.mixed + b.mixed, schemaInvalid := a.schemaInvalid + b.schemaInvalid,
    version10 := a.version10 + b.version10, unreadable := a.unreadable + b.unreadable,
    notSimple := a.notSimple + b.notSimple,
    schemaTests := a.schemaTests + b.schemaTests }

/-- Per-datatype tally, keyed by the built-in's local name (or
`«list»` / `«union»` for the two non-atomic varieties). -/
abbrev Tally := List (String × Nat × Nat)

def Tally.bump (t : Tally) (k : String) (ok : Bool) : Tally :=
  if t.any (fun e => e.1 == k) then
    t.map (fun e => if e.1 == k then (e.1, e.2.1 + (if ok then 1 else 0),
                                      e.2.2 + (if ok then 0 else 1)) else e)
  else (k, (if ok then 1 else 0), (if ok then 0 else 1)) :: t

def Tally.merge (a b : Tally) : Tally :=
  b.foldl (fun acc e =>
    if acc.any (fun x => x.1 == e.1)
    then acc.map (fun x => if x.1 == e.1 then (x.1, x.2.1 + e.2.1, x.2.2 + e.2.2) else x)
    else e :: acc) a

def dirOf (p : String) : String :=
  match (p.splitOn "/").reverse with
  | _ :: rest => if rest.isEmpty then "" else String.intercalate "/" rest.reverse ++ "/"
  | []        => ""

/-- Resolve `..` and `.` in a path built by concatenation. -/
def normalizePath (p : String) : String :=
  let segs := p.splitOn "/"
  let out := segs.foldl (fun acc s =>
    if s == ".." then (match acc with | _ :: rest => rest | [] => [])
    else if s == "." || s == "" then acc
    else s :: acc) []
  (if p.startsWith "/" then "/" else "") ++ String.intercalate "/" out.reverse

def hrefOf (n : Node) : Option String :=
  (attrOf "xlink:href" n).orElse (fun _ => attrOf "href" n)

/-- The `<expected>` child that applies to XSD 1.1: the one with no
`version`, or one whose `version` names 1.1. -/
def expectedValidity (group : Node) (test : Node) : Option String :=
  let exps := (elementChildren test).filter (fun c => localOf (tagOf c) == "expected")
  let pick := exps.find? (fun e =>
    match attrOf "version" e with
    | none => true
    | some v => (v.splitOn " ").contains "1.1")
  match pick.bind (attrOf "validity") with
  | some v => some v
  | none => (exps.head?.bind (attrOf "validity")).orElse (fun _ =>
              (attrOf "validity") group)

/-- Does the group apply only to XSD 1.0? -/
def isVersion10Only (group : Node) : Bool :=
  match attrOf "version" group with
  | some v => v == "1.0"
  | none   => false

/-- The concatenated character data of an element, one level deep. -/
def textOf : Node → String
  | .element _ _ cs => String.join (cs.map (fun c =>
      match c with
      | .text s  => s
      | .cdata s => s
      | _        => ""))
  | _ => ""

def hasElementChild : Node → Bool
  | .element _ _ cs => cs.any (fun c => match c with | .element _ _ _ => true | _ => false)
  | _ => false

/-- The datatype label a simple type is attributed to. -/
def labelOf : SimpleType → String
  | .atomic b _ => b.localName
  | .list _ _   => "«list»"
  | .union _ _  => "«union»"

structure GroupResult where
  counts : Counts := {}
  tally  : Tally := []
  fails  : List String := []

/-- Read and parse a document. A file the parser cannot even decode as
UTF-8 (the suite carries a few UTF-16 and Latin-1 schema documents) is
`none`, and lands in the `unreadable` bucket rather than aborting the
run — the parser reads UTF-8 only, which its own header states. -/
def readDoc (path : String) : IO (Option Document) := do
  if !(← System.FilePath.pathExists path) then return none
  let bytes ← IO.FS.readBinFile path
  match String.fromUTF8? bytes with
  | none => return none
  | some src =>
    match parseXML src with
    | .ok d    => return some d
    | .error _ => return none

def runGroup (base : String) (group : Node) (verbose : Bool) : IO GroupResult := do
  let kids := elementChildren group
  let schemaTests := kids.filter (fun c => localOf (tagOf c) == "schemaTest")
  let instTests := kids.filter (fun c => localOf (tagOf c) == "instanceTest")
  let mut r : GroupResult := { counts := { schemaTests := schemaTests.length } }
  -- The schema document of the group.
  let schemaHref := schemaTests.head?.bind (fun st =>
    ((elementChildren st).find? (fun c => localOf (tagOf c) == "schemaDocument")).bind hrefOf)
  match schemaHref with
  | none => return { r with counts := { r.counts with
                       unreadable := r.counts.unreadable + instTests.length } }
  | some href =>
    let schemaPath := normalizePath (base ++ href)
    match ← readDoc schemaPath with
    | none => return { r with counts := { r.counts with
                         unreadable := r.counts.unreadable + instTests.length } }
    | some sdoc =>
      match readSchema sdoc with
      | none => return { r with counts := { r.counts with
                           unreadable := r.counts.unreadable + instTests.length } }
      | some schema =>
        if schema.klass == .structures then
          return { r with counts := { r.counts with
                     structures := r.counts.structures + instTests.length } }
        if schema.klass == .mixed then
          return { r with counts := { r.counts with
                     mixed := r.counts.mixed + instTests.length } }
        -- The schema is a datatype schema. If the suite expects it to
        -- be REJECTED, its instances have no defined outcome here.
        let schemaExpected := schemaTests.head?.bind (fun st => expectedValidity group st)
        if schemaExpected == some "invalid" then
          return { r with counts := { r.counts with
                     schemaInvalid := r.counts.schemaInvalid + instTests.length } }
        if isVersion10Only group then
          return { r with counts := { r.counts with
                     version10 := r.counts.version10 + instTests.length } }
        for it in instTests do
          let ihref := ((elementChildren it).find? (fun c =>
            localOf (tagOf c) == "instanceDocument")).bind hrefOf
          match ihref with
          | none => r := { r with counts := { r.counts with
                             unreadable := r.counts.unreadable + 1 } }
          | some ih =>
            match ← readDoc (normalizePath (base ++ ih)) with
            | none => r := { r with counts := { r.counts with
                               unreadable := r.counts.unreadable + 1 } }
            | some idoc =>
              let root := idoc.root
              if hasElementChild root then
                r := { r with counts := { r.counts with
                         notSimple := r.counts.notSimple + 1 } }
              else
                match elementType? schema (localOf (tagOf root)) with
                | none => r := { r with counts := { r.counts with
                                   unreadable := r.counts.unreadable + 1 } }
                | some ty =>
                  let expected := (expectedValidity group it).getD "valid"
                  let got := validate ty (textOf root)
                  let ok := (got && expected == "valid") || (!got && expected == "invalid")
                  let nm := (attrOf "name" it).getD "?"
                  if verbose && !ok then
                    IO.println s!"  FAIL {nm}  type={labelOf ty} expected={expected} got={got} lex={repr (textOf root)}"
                  r := { r with
                    counts := { r.counts with
                      scored := r.counts.scored + 1,
                      pass := r.counts.pass + (if ok then 1 else 0),
                      fail := r.counts.fail + (if ok then 0 else 1) },
                    tally := r.tally.bump (labelOf ty) ok,
                    fails := if ok then r.fails else nm :: r.fails }
        return r

def runTestSet (root : String) (rel : String) (verbose : Bool) : IO GroupResult := do
  let path := normalizePath (root ++ "/" ++ rel)
  match ← readDoc path with
  | none =>
      IO.println s!"  test set unreadable: {rel}"
      return {}
  | some doc =>
    let base := dirOf path
    let groups := (elementChildren doc.root).filter (fun c => localOf (tagOf c) == "testGroup")
    let mut acc : GroupResult := {}
    for g in groups do
      let r ← runGroup base g verbose
      acc := { counts := acc.counts.add r.counts,
               tally := acc.tally.merge r.tally,
               fails := acc.fails ++ r.fails }
    return acc

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let positional := args.filter (fun a => !a.startsWith "--")
  let suiteDir := positional.head?.getD "third_party/testing/xsd"
  let setFilter :=
    match args.dropWhile (fun a => a != "--set") with
    | _ :: v :: _ => some v
    | _ => none
  match ← readDoc (suiteDir ++ "/suite.xml") with
  | none =>
      IO.println s!"xsd-datatypes: cannot read {suiteDir}/suite.xml"
      IO.println "Run tools/ensure-test-env.sh first."
      return 1
  | some suite =>
    let refs := (elementChildren suite.root).filterMap (fun c =>
      if localOf (tagOf c) == "testSetRef" then hrefOf c else none)
    let refs := match setFilter with
      | none => refs
      | some f => refs.filter (fun rf => (rf.splitOn f).length > 1)
    let mut total : Counts := {}
    let mut tally : Tally := []
    for rel in refs do
      let r ← runTestSet suiteDir rel verbose
      if r.counts.scored > 0 || r.counts.structures > 0 then
        IO.println s!"{rel}: {r.counts.pass} pass, {r.counts.fail} fail (of {r.counts.scored} scored); structures {r.counts.structures}, mixed {r.counts.mixed}, schema-invalid {r.counts.schemaInvalid}, version-1.0 {r.counts.version10}, unreadable {r.counts.unreadable}, not-simple {r.counts.notSimple}"
      total := total.add r.counts
      tally := tally.merge r.tally
    IO.println ""
    IO.println "per-datatype (scored instance tests):"
    for (k, p, f) in (tally.toArray.qsort (fun a b => a.2.2 > b.2.2)).toList do
      IO.println s!"  {k}: {p} pass, {f} fail (of {p + f})"
    IO.println ""
    IO.println s!"XSD datatype instance tests: {total.pass} pass, {total.fail} fail (out of {total.scored} scored)"
    IO.println s!"not scored: structures {total.structures}, mixed {total.mixed}, schema-invalid {total.schemaInvalid}, version-1.0 {total.version10}, unreadable {total.unreadable}, not-simple {total.notSimple}"
    IO.println s!"schema tests seen (not scored in this run): {total.schemaTests}"
    return 0
