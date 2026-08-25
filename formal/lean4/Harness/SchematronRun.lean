/-
Harness/SchematronRun — a REAL Schematron conformance runner.

It reads `third_party/testing/schematron/manifest.json`, parses each
case's `.sch` with `Schematron.FromXml`, parses its instance with the
project's own XML parser, and validates with
`Schematron.Validate.validate` — supplying the two parameters that
module deliberately leaves open (`select` and `evalTest`) from
`XPath.Mini`.

## What the score means

Each case declares its EXPECTED findings as `{type, context, test}`
triples. A case passes when the findings produced are the SAME
MULTISET as the expected ones. Order is not compared: within a pattern
`Validate` emits rule by rule, while the manifest lists findings in
document order, and those differ for `first-matching-rule` without
either being wrong.

Three outcomes, not two:

  * **pass** — the finding multiset matched;
  * **fail** — it did not. This is the number that means something is
    broken;
  * **undecided** — at least one `@test` was outside the XPath subset,
    so `Validate` produced an `indeterminate` finding. Counted apart,
    with the reason printed, because a test the evaluator could not
    read is neither a violation nor a clean bill of health.

Usage: `lake exe l4schematron [tests-dir]`
-/
import L4Factoidal.Schematron.FromXml
import L4Factoidal.XPath.Mini
import L4Factoidal.JSON.Parser

open L4Factoidal.JSON
open L4Factoidal.Schematron
open L4Factoidal.XPath
open L4Factoidal.XML

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match field? k v with
  | some (.string s) => some s
  | _                => none

/-- One expected finding, as the manifest writes it. The MESSAGE is not
    compared: the manifest does not carry it, and inventing a
    comparison against an absent field would score nothing. -/
structure Want where
  type    : String
  context : String
  test    : String
deriving BEq, Repr

def wantOf (j : Json) : Option Want :=
  match str? "type" j, str? "context" j, str? "test" j with
  | some t, some c, some x => some { type := t, context := c, test := x }
  | _, _, _ => none

def gotOf (f : Finding) : Want :=
  { type := f.kind, context := f.context, test := f.test }

/-- Multiset equality: same length, and every element of each list
    occurs the same number of times in the other. -/
def sameMultiset (a b : List Want) : Bool :=
  a.length == b.length &&
  a.all (fun x => (a.filter (· == x)).length == (b.filter (· == x)).length)

/-- The `select` parameter: does this rule's `@context` claim the node
    at `path`? -/
def selectOf (root : Node) : String → String → Bool := contextSelects root

/-- The `evalTest` parameter, bridging `XPath.Mini`'s refusal into
    `Schematron.TestResult`. The `undecided` case carries the reason
    the evaluator gave, unchanged — a runner that replaced it with its
    own wording would hide which construct is missing. -/
def evalOf (root : Node) (test path : String) : TestResult :=
  match evalTestAt root test path with
  | Sum.inl (some true)  => .true'
  | Sum.inl (some false) => .false'
  | Sum.inl none         => .undecided "the evaluator returned no value"
  | Sum.inr why          => .undecided why

structure Tally where
  pass      : Nat := 0
  fail      : Nat := 0
  undecided : Nat := 0
deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/schematron"
  let manifestPath := dir ++ "/manifest.json"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"schematron runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match parseJson? mtext with
  | none =>
      IO.println "schematron runner: manifest did not parse"
      return 1
  | some (.array cases) =>
      let mut t : Tally := {}
      let mut errors := 0
      for c in cases do
        let name := (str? "name" c).getD "<unnamed>"
        match str? "schema" c, str? "instance" c with
        | some sp, some ip => do
            let schemaSrc ← IO.FS.readFile (dir ++ "/" ++ sp)
            let instSrc ← IO.FS.readFile (dir ++ "/" ++ ip)
            match parseSchematron schemaSrc, parseXML instSrc with
            | .error e, _ =>
                IO.println s!"ERROR {name}: {e}"
                errors := errors + 1
            | _, .error e =>
                IO.println s!"ERROR {name}: the instance is not well-formed XML: {e.message} at {e.position}"
                errors := errors + 1
            | .ok sch, .ok doc =>
                let root := doc.root
                let nodes := documentPaths root
                let findings := validate sch nodes (selectOf root) (evalOf root)
                let want := match field? "expect" c with
                  | some (.array ws) => ws.filterMap wantOf
                  | _                => []
                if hasIndeterminate findings then
                  t := { t with undecided := t.undecided + 1 }
                  IO.println s!"UNDECIDED {name}:"
                  for f in findings do
                    match f with
                    | .indeterminate _ tst _ _ why =>
                        IO.println s!"    test {tst} -- {why}"
                    | _ => pure ()
                else
                  let got := findings.map gotOf
                  if sameMultiset got want then
                    t := { t with pass := t.pass + 1 }
                  else
                    t := { t with fail := t.fail + 1 }
                    IO.println s!"FAIL {name}"
                    IO.println s!"    expected {want.length}: {repr want}"
                    IO.println s!"    produced {got.length}: {repr got}"
        | _, _ =>
            IO.println s!"ERROR {name}: the manifest entry has no schema or instance"
            errors := errors + 1
      let attempted := t.pass + t.fail
      IO.println ""
      IO.println s!"schematron DECIDED: {t.pass} pass, {t.fail} fail (out of {attempted} decided)"
      IO.println s!"UNDECIDED: {t.undecided} cases used an expression outside the XPath subset"
      if errors > 0 then
        IO.println s!"ERRORS: {errors} cases could not be read at all"
      IO.println s!"  (out of {cases.length} cases in the manifest)"
      IO.println ""
      IO.println "An UNDECIDED case is counted apart, never as a pass and never"
      IO.println "as a failure: a `@test` the evaluator cannot read is neither a"
      IO.println "violation nor a clean bill of health."
      return (if t.fail > 0 || errors > 0 then 1 else 0)
  | some _ =>
      IO.println "schematron runner: the manifest is not an array of cases"
      return 1
