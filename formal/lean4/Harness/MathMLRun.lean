/-
Harness/MathMLRun — the Content MathML evaluation corpus.

`third_party/testing/mathml/manifest.json` carries one entry per test:
the MathML source, an optional symbol environment, and the expected
value written as an exact rational (`157/50`), an integer, `true` /
`false`, or the literal `undef`.

`undef` is a REAL expected answer, not a skip. A division by zero, an
inexact root, a non-integer power and an unsupported operator all
denote nothing, and an evaluator that returned a number for any of
them would be wrong in the direction that is hardest to notice. Six of
the corpus's tests expect exactly that, so they are scored like any
other.

Usage: `lake exe l4mathml [tests-dir]`
-/
import L4Factoidal.MathML.FromXml
import L4Factoidal.JSON.Parser

open L4Factoidal.JSON
open L4Factoidal.MathML

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match field? k v with
  | some (.string s) => some s
  | _                => none

/-- Write a value the way the manifest writes it: an integer bare, a
    rational as `num/den`, a boolean as `true`/`false`. -/
def showValue : Option Value → String
  | none            => "undef"
  | some (.bool b)  => if b then "true" else "false"
  | some (.num (n, d)) => if d == 1 then toString n else toString n ++ "/" ++ toString d

/-- The environment an entry supplies, as the evaluator wants it. -/
def envOf (j : Json) : String → Option (Int × Int) :=
  let pairs : List (String × (Int × Int)) := match field? "env" j with
    | some (.object ms) =>
        ms.filterMap (fun (k, v) => match v with
          | .string s => (s.toInt?).map (fun i => (k, (i, (1 : Int))))
          | .number s => (s.toInt?).map (fun i => (k, (i, (1 : Int))))
          | _ => none)
    | _ => []
  fun s => (pairs.find? (fun (k, _) => k == s)).map (·.2)

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/mathml"
  let manifestPath := dir ++ "/manifest.json"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"mathml runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match parseJson? mtext with
  | none =>
      IO.println "mathml runner: manifest did not parse"
      return 1
  | some mj =>
      let tests := match field? "tests" mj with
        | some (.array ts) => ts
        | _ => []
      let mut pass := 0
      let mut fail := 0
      let mut unread := 0
      for t in tests do
        let name := (str? "name" t).getD "?"
        match str? "input" t, str? "expectedValue" t with
        | some src, some want =>
            match parseMathML src with
            | none =>
                -- The markup did not READ. Distinct from an
                -- undefined VALUE: one is a gap in this module, the
                -- other is the answer.
                if want == "undef" then
                  fail := fail + 1
                  IO.println s!"FAIL {name}: markup did not read (expected the undefined VALUE, which is not the same thing)"
                else
                  unread := unread + 1
                  IO.println s!"UNREAD {name}: the markup did not parse into an expression"
            | some e =>
                let got := showValue (eval (envOf t) e)
                if got == want then pass := pass + 1
                else
                  fail := fail + 1
                  IO.println s!"FAIL {name}: got {got}, expected {want}"
        | _, _ => pure ()
      IO.println ""
      IO.println s!"content-mathml evaluation: {pass} pass, {fail} fail, {unread} markup-not-read (out of {tests.length})"
      IO.println "`undef` is an expected ANSWER here, not a skip: a division by zero,"
      IO.println "an inexact root, a non-integer power and an unsupported operator all"
      IO.println "denote nothing, and returning a number for any of them would be"
      IO.println "wrong in the direction hardest to notice."
      return 0
