/-
Harness/XPathRun — the ported F* XPath 1.0 Stage-1 unit battery.

`tests/unit/xpath_cases.json` carries the 100 cases from
`tests/unit/xpath_tests.ml` (the F* XPath 1.0 Stage-1 regression
battery, scored 100 pass 0 fail there), itself spec-cited against
XPath 1.0 (https://www.w3.org/TR/1999/REC-xpath-19991116/). Each case
names a fixture key ("a"/"b"/"c"/"d"/"ns"), an XPath 1.0 expression,
an expected kind ("string" — go through `string()`/`Value.toStr`,
"bool" — go through `boolean()`/`Value.toBool`, or "parsefails" —
the expression must fail to parse) and the expected answer. One case
binds a variable (`$x` to the number 5) via a "vars" object.

Usage: `lake -d formal/lean4 exe l4xpath [cases-file]` — run from the
repository root, so the process's own working directory IS the
repository root and the default path resolves directly. Also:
`cd formal/lean4 && lake exe l4xpath [cases-file]` — run from inside
`formal/lean4`, where the default path does not exist directly but
`"../../" ++ path` does. Both invocations work: a relative
`cases-file` (default `tests/unit/xpath_cases.json`) is tried first
against the process's own working directory, then against
`"../../" ++ path`.

This harness only reads JSON, builds a document and a context, calls
the evaluator, and compares strings. No XPath semantics live here —
that is `L4Factoidal/XPath/Eval.lean` and `Expr.lean`.
-/
import L4Factoidal.XPath.Eval
import L4Factoidal.XML.Parser
import L4Factoidal.JSON.Parser

open L4Factoidal.XPath L4Factoidal.XPath.Full L4Factoidal.XML
open L4Factoidal.JSON

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match field? k v with
  | some (.string s) => some s
  | _                => none

/-- Read the cases file, trying `path` first against the process's own
    working directory (repository root, when run as
    `lake -d formal/lean4 exe l4xpath`) and then against
    `"../../" ++ path` (the working directory when run as
    `lake exe l4xpath` from inside `formal/lean4`). -/
def readCasesFile (path : String) : IO (Option String) := do
  if ← System.FilePath.pathExists path then
    some <$> IO.FS.readFile path
  else
    let alt := "../../" ++ path
    if ← System.FilePath.pathExists alt then
      some <$> IO.FS.readFile alt
    else
      pure none

/-- The document named by a case's `fixture` key, read out of the
    manifest's top-level `fixtures` object and parsed once per case
    (the corpus is small; a cache buys nothing here). An unknown key
    or an unparseable fixture is the empty document, which every case
    that reaches it is expected NOT to do. -/
def fixtureDoc (fixtures : Json) (key : String) : Doc :=
  match str? key fixtures with
  | none => []
  | some xml =>
      match parseXML xml with
      | .ok d    => d.prolog ++ (d.root :: d.epilog)
      | .error _ => []

/-- The `vars` object a case may carry, as integer-valued bindings
    (the one case that needs this binds `$x` to the number 5). -/
def varsOf (c : Json) : List (String × Value) :=
  match field? "vars" c with
  | some (.object ms) =>
      ms.filterMap (fun (k, v) => match v with
        | .number s => (s.toInt?).map (fun i => (k, Value.num (Num.finite i 0)))
        | _         => none)
  | _ => []

/-- Score one case against its expected answer. -/
def scoreCase (fixtures : Json) (c : Json) : String × Bool :=
  let name := (str? "name" c).getD "?"
  let fixtureKey := (str? "fixture" c).getD "a"
  let expr := (str? "expr" c).getD ""
  let kind := (str? "kind" c).getD "string"
  let expected := (str? "expected" c).getD ""
  if kind == "parsefails" then
    let got := if (parseExpr expr).isNone then "true" else "false"
    (s!"FAIL {name}: got \"{got}\", expected \"{expected}\"", got == expected)
  else
    let theDoc := fixtureDoc fixtures fixtureKey
    let ctx : Ctx := { doc := theDoc, item := .doc theDoc, vars := varsOf c }
    match evalText ctx expr with
    | none =>
        (s!"FAIL {name}: got \"<unreadable>\", expected \"{expected}\"", false)
    | some v =>
        let got := if kind == "bool" then (if v.toBool then "true" else "false") else v.toStr
        (s!"FAIL {name}: got \"{got}\", expected \"{expected}\"", got == expected)

def main (args : List String) : IO UInt32 := do
  let path := args.head? |>.getD "tests/unit/xpath_cases.json"
  match ← readCasesFile path with
  | none =>
      IO.println s!"xpath runner: cases file not found: {path}"
      return 1
  | some text =>
      match parseJson? text with
      | none =>
          IO.println "xpath runner: cases file did not parse"
          return 1
      | some j =>
          let fixtures := (field? "fixtures" j).getD (.object [])
          let cases := match field? "cases" j with
            | some (.array cs) => cs
            | _                => []
          let mut pass := 0
          let mut fail := 0
          for c in cases do
            let (msg, ok) := scoreCase fixtures c
            if ok then pass := pass + 1
            else
              fail := fail + 1
              IO.println msg
          IO.println s!"xpath 1.0 unit battery: {pass} pass, {fail} fail (out of {cases.length})"
          return (if fail > 0 then 1 else 0)
