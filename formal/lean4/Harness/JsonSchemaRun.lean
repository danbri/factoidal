/-
Harness/JsonSchemaRun — a REAL JSON Schema conformance runner over the
vendored draft-07 suite.

The suite's own `manifest.json` lists every vendored file and its test
count, and each file holds a list of `{description, schema, tests:
[{description, data, valid}]}` groups. This runner reads them from
disk and asks `JSONSchema.Validate.validate` for a verdict.

## Three outcomes, not two

`validate` is THREE-valued — pass, fail, or UNSUPPORTED — and the
score keeps that distinction:

  * **pass** — the verdict matched `valid`;
  * **fail** — the verdict was definite and WRONG. This is the number
    that means something is broken;
  * **unsupported** — a keyword outside the ported slice made the
    verdict undetermined. NOT counted as either, and reported with the
    keywords responsible, so the gap is named instead of buried.

Folding `unsupported` into `pass` would inflate the score with tests
the validator never decided; folding it into `fail` would deflate it
with tests it never claimed to decide. The module header of
`JSONSchema/Validate.lean` makes the same point about `vand`/`vor`.

Usage: `lake exe l4jsonschema [tests-dir]`
-/
import L4Factoidal.JSONSchema.Validate
import L4Factoidal.JSON.Parser

open L4Factoidal.JSON
open L4Factoidal.JSONSchema

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match field? k v with
  | some (.string s) => some s
  | _                => none

/-- The draft-07 keyword vocabulary. Needed because a schema object's
    members are NOT all keywords: inside `properties` they are
    PROPERTY NAMES, and reporting `foo` and `tilde~field` as
    unimplemented keywords is noise that hides the real gap. -/
def draft7Keywords : List String :=
  ["$id", "$schema", "$ref", "$comment", "title", "description", "default",
   "readOnly", "writeOnly", "examples", "multipleOf", "maximum",
   "exclusiveMaximum", "minimum", "exclusiveMinimum", "maxLength",
   "minLength", "pattern", "additionalItems", "items", "maxItems",
   "minItems", "uniqueItems", "contains", "maxProperties", "minProperties",
   "required", "additionalProperties", "definitions", "properties",
   "patternProperties", "dependencies", "propertyNames", "const", "enum",
   "type", "format", "if", "then", "else", "allOf", "anyOf", "oneOf", "not",
   "contentMediaType", "contentEncoding"]

/-- Every KEYWORD a schema mentions, at any depth — only names that
    appear in keyword POSITION. `properties` / `patternProperties` /
    `dependencies` / `definitions` map property names to sub-schemas,
    so their keys are skipped and their values recursed into. -/
partial def schemaKeywords : Json → List String
  | .object ms =>
      ms.flatMap (fun (k, v) =>
        if ["properties", "patternProperties", "dependencies", "definitions"].contains k then
          k :: (match v with
                | .object subs => subs.flatMap (fun (_, sub) => schemaKeywords sub)
                | other        => schemaKeywords other)
        else if draft7Keywords.contains k then k :: schemaKeywords v
        else schemaKeywords v)
  | .array vs  => vs.flatMap schemaKeywords
  | _          => []

structure Tally where
  pass        : Nat := 0
  fail        : Nat := 0
  unsupported : Nat := 0
deriving Repr, Inhabited

def Tally.add (a b : Tally) : Tally :=
  { pass := a.pass + b.pass, fail := a.fail + b.fail,
    unsupported := a.unsupported + b.unsupported }

/-- Run one file's groups. Returns the tally, the keywords that left
    something undetermined, and the DESCRIPTION of each group that did
    — naming the undetermined cases, not just counting them, so the
    remaining gap can be read off the run instead of guessed at. -/
def runFile (reg : Registry) (src : String) : Tally × List String × List String :=
  match parseJson? src with
  | none => ({ unsupported := 1 }, ["<file did not parse>"], [])
  | some (.array groups) =>
      groups.foldl (fun (acc, kws, undec) g =>
        match field? "schema" g, field? "tests" g with
        | some schema, some (.array ts) =>
            let (t, k) := ts.foldl (fun (acc2, kws2) tc =>
              match field? "data" tc, field? "valid" tc with
              | some d, some (.bool want) =>
                  match validateWith reg schema d with
                  | .pass => (Tally.add acc2 (if want then {pass := 1} else {fail := 1}), kws2)
                  | .fail => (Tally.add acc2 (if want then {fail := 1} else {pass := 1}), kws2)
                  | .unsupported =>
                      (Tally.add acc2 {unsupported := 1},
                       kws2 ++ (schemaKeywords schema).filter (fun s => !kws2.contains s))
              | some _, some _ => (Tally.add acc2 {unsupported := 1}, kws2)
              | _, _ => (acc2, kws2)) (({} : Tally), kws)
            (Tally.add acc t, k,
             if t.unsupported > 0 then
               undec ++ [s!"{(str? "description" g).getD "<no description>"} ({t.unsupported})"]
             else undec)
        | _, _ => (acc, kws, undec)) (({} : Tally), [], [])
  | some _ => ({ unsupported := 1 }, ["<file is not an array of groups>"], [])

/-- The keywords this slice implements. Every draft-07 assertion is on
    the list, so an undetermined verdict is no longer a MISSING
    keyword — it is a `$ref` whose target this slice does not resolve
    (a remote document rather than a pointer into this one). -/
def portedKeywords : List String :=
  ["type", "const", "enum", "minimum", "maximum", "exclusiveMinimum",
   "exclusiveMaximum", "multipleOf", "minLength", "maxLength", "pattern",
   "minItems", "maxItems", "uniqueItems", "contains", "items",
   "additionalItems", "required", "minProperties", "maxProperties",
   "properties", "patternProperties", "additionalProperties",
   "propertyNames", "dependencies", "allOf", "anyOf", "oneOf", "not",
   "if", "then", "else", "$ref",
   "title", "description", "default", "$comment", "examples", "$schema",
   "$id", "definitions", "readOnly", "writeOnly", "format",
   "contentMediaType", "contentEncoding"]

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/jsonschema"
  let manifestPath := dir ++ "/manifest.json"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"json schema runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match parseJson? mtext with
  | none =>
      IO.println "json schema runner: manifest did not parse"
      return 1
  | some mj =>
      let files := match field? "files" mj with
        | some (.array fs) => fs.filterMap (str? "path")
        | _ => []
      let declared := match field? "total_tests_vendored" mj with
        | some (.number n) => n
        | _ => "?"
      -- The suite's `remotes/` directory holds the documents its
      -- absolute `$ref`s name. Registering them by their own `$id` is
      -- what a document loader would do; without it every remote ref
      -- is undetermined, which is honest but leaves 52 tests
      -- unanswered.
      let remotesDir := dir ++ "/remotes"
      let mut reg : Registry := []
      if ← System.FilePath.isDir remotesDir then
        for entry in (← System.FilePath.readDir remotesDir) do
          let ep := entry.path.toString
          if ep.endsWith ".json" then
            let rsrc ← IO.FS.readFile ep
            match parseJson? rsrc with
            | none => pure ()
            | some rj =>
                match field? "$id" rj with
                | some (.string i) =>
                    let base := match i.splitOn "#" with
                      | b :: _ => b
                      | []     => i
                    reg := reg ++ [(base, rj)]
                | _ => pure ()
      let mut total : Tally := {}
      let mut gaps : List String := []
      let mut undecided : List String := []
      let mut missing := 0
      for f in files do
        let p := dir ++ "/" ++ f
        if !(← System.FilePath.pathExists p) then
          missing := missing + 1
          IO.println s!"missing vendored file: {f}"
        else
          let src ← IO.FS.readFile p
          let (t, kws, un) := runFile reg src
          if t.fail > 0 then
            IO.println s!"{t.fail} decided-and-wrong in {f}"
          total := Tally.add total t
          gaps := gaps ++ kws.filter (fun k => !gaps.contains k)
          undecided := undecided ++ un.map (fun d => f ++ ": " ++ d)
      let attempted := total.pass + total.fail
      IO.println ""
      IO.println s!"json-schema draft-07 DECIDED: {total.pass} pass, {total.fail} fail (out of {attempted} decided)"
      IO.println s!"UNDETERMINED: {total.unsupported} tests used a keyword outside the ported slice"
      IO.println s!"  (out of {total.pass + total.fail + total.unsupported} run; the suite declares {declared} vendored)"
      if missing > 0 then
        IO.println s!"  {missing} vendored files were not on disk"
      let unported := gaps.filter (fun k =>
        !portedKeywords.contains k && !k.startsWith "<")
      IO.println ""
      if total.unsupported == 0 then
        IO.println "Every vendored test was DECIDED: no keyword, no `$ref`, and no"
        IO.println "bound in this suite left the validator without a verdict."
      else if !unported.isEmpty then
        IO.println "Keywords the undetermined tests mention that this slice does not implement:"
        IO.println ("  " ++ String.intercalate ", " (unported.take 40))
      else
        IO.println "Every draft-07 ASSERTION keyword is implemented, so an undetermined"
        IO.println "test is not a missing keyword. The groups are named below."
      if !undecided.isEmpty then
        IO.println "The groups left undetermined, with how many of their tests:"
        for d in undecided do
          IO.println s!"  {d}"
        IO.println ""
      IO.println "An UNDETERMINED verdict is counted separately, never as a pass"
      IO.println "and never as a failure: folding it into pass would inflate the"
      IO.println "score with tests the validator did not decide, and into fail"
      IO.println "would deflate it with tests it never claimed to decide."
      return 0
