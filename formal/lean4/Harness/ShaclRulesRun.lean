/-
Harness.ShaclRulesRun — the SHACL 1.2 `rules` suite runner (`l4shacl-rules`).

The Lean SHACL probe (`l4shacl`) does not recognise the `srt:` test
types, and the rules manifests link their entries with `mf:entries`
rather than `mf:include`, so the probe walked in and reported "out of
0" — the UNREAD row of `tools/lean-shacl-scores.sh` and of
<https://github.com/danbri/factoidal/issues/553>. This runner reads
them.

Four sub-suites, mirroring `bin/shacl-runner/shacl_runner.ml`:

| Sub-suite | Test types | Checked by |
|---|---|---|
| `eval` | `srt:RulesEvalTest` | `runRules`, compared with RDFC-1.0 |
| `syntax` | `srt:Rules{Positive,Negative}SyntaxTest` | `srlValidSyntax` |
| `wellformed` | `srt:Rules{Positive,Negative}WellFormednessTest` | `srlWellFormed` |
| `stratification` | `srt:Rules{Positive,Negative}StratificationTest` | `srlStratifiable` |

An eval test's `mf:action` is a blank node carrying `srt:ruleset` and
`srt:data`; a syntax-family test's `mf:action` is the `.srl` IRI
directly.

Not part of the verified library: this file does I/O and prints scores.

Usage, from the repository root:

    lake exe l4shacl-rules [manifest-dir]

defaulting to `third_party/testing/shacl/shacl12-test-suite/tests/rules`.
-/
import Harness.Manifest
import L4Factoidal.SHACL.Rules
import L4Factoidal.RDF.Canonical
import L4Factoidal.Syntax.Turtle

open L4Factoidal.RDF
open L4Factoidal.SHACL
open Harness

namespace Harness.ShaclRules

def srtNs : String := "http://www.w3.org/ns/shacl-rules-test#"

/-- Which checker a syntax-family type calls, and what it should say. -/
structure SyntaxKind where
  typeIri : String
  expect  : Bool
  check   : String → Bool

def syntaxKinds : List SyntaxKind :=
  [ { typeIri := srtNs ++ "RulesPositiveSyntaxTest", expect := true,  check := srlValidSyntax }
  , { typeIri := srtNs ++ "RulesNegativeSyntaxTest", expect := false, check := srlValidSyntax }
  , { typeIri := srtNs ++ "RulesPositiveWellFormednessTest", expect := true,  check := srlWellFormed }
  , { typeIri := srtNs ++ "RulesNegativeWellFormednessTest", expect := false, check := srlWellFormed }
  , { typeIri := srtNs ++ "RulesPositiveStratificationTest", expect := true,  check := srlStratifiable }
  , { typeIri := srtNs ++ "RulesNegativeStratificationTest", expect := false, check := srlStratifiable } ]

/-- The canonical N-Quads of a graph, which is what two graphs are
    compared by — the same comparison `bin/shacl-runner` makes with
    `RDF_Canonical.canonicalize_to_nquads`. -/
def canonOf (g : Graph) : String :=
  (Canonical.canonicalize { default := g, named := [] }).nquads

def entriesOf (g : Graph) : List Term :=
  let fuel := g.length + 1
  let heads := g.filterMap (fun t =>
    if t.p.val == mfNs ++ "entries" then some t.o else none)
  heads.flatMap (fun h => collectList g fuel h)

def typeOf (g : Graph) (s : Subject) : Option String :=
  (findObject? g s rdfType).map termKey

def nameOf (g : Graph) (s : Subject) : String :=
  match findObject? g s (mfNs ++ "name") with
  | some (.literal l) => l.val.lexicalForm
  | _ => lastAfter (subjKey s) "#"

/-- `mf:action`'s object as a local file path, for the syntax family
    where it is the `.srl` IRI itself. -/
def actionPath (dir : String) (g : Graph) (s : Subject) : Option String :=
  match findObject? g s (mfNs ++ "action") with
  | some (.iri i) => some (iriToLocalPath dir i.val)
  | _ => none

/-- The `(ruleset, data, result)` paths of an eval test. -/
def evalPaths (dir : String) (g : Graph) (s : Subject) :
    Option (String × String × String) := do
  let act ← findObject? g s (mfNs ++ "action")
  let actS ← subjectOfTerm act
  let rs ← findObject? g actS (srtNs ++ "ruleset")
  let da ← findObject? g actS (srtNs ++ "data")
  let re ← findObject? g s (mfNs ++ "result")
  match rs, da, re with
  | .iri r, .iri d, .iri x =>
      some (iriToLocalPath dir r.val, iriToLocalPath dir d.val, iriToLocalPath dir x.val)
  | _, _, _ => none

def readTurtleGraph (path : String) : IO (Option Graph) := do
  match ← readOpt path with
  | none => return none
  | some text =>
      match L4Factoidal.Syntax.parseTurtle text (some ("file://" ++ path)) with
      | .error _ => return none
      | .ok g => return some g

def runEvalTest (dir : String) (g : Graph) (s : Subject) : IO Outcome := do
  match evalPaths dir g s with
  | none => return .skip "mf:action lacks srt:ruleset / srt:data, or mf:result is not an IRI"
  | some (srlPath, dataPath, resPath) =>
      match ← readOpt srlPath with
      | none => return .skip s!"missing ruleset {srlPath}"
      | some srl =>
          match ← readTurtleGraph dataPath, ← readTurtleGraph resPath with
          | some data, some expected =>
              let inferred := runRules data srl
              if canonOf inferred == canonOf expected then return .pass
              else return .fail s!"inferred graph differs from expected\n    expected: {canonOf expected}\n    actual:   {canonOf inferred}"
          | none, _ => return .skip s!"unparsed data {dataPath}"
          | _, none => return .skip s!"unparsed result {resPath}"

def runSyntaxTest (dir : String) (g : Graph) (s : Subject) (k : SyntaxKind) :
    IO Outcome := do
  match actionPath dir g s with
  | none => return .skip "mf:action is not an IRI"
  | some p =>
      match ← readOpt p with
      | none => return .skip s!"missing ruleset {p}"
      | some srl =>
          let got := k.check srl
          if got == k.expect then return .pass
          else return .fail s!"expected {if k.expect then "valid" else "invalid"}, got {if got then "valid" else "invalid"}"

def runOne (dir : String) (g : Graph) (entry : Term) : IO (String × Outcome) := do
  match subjectOfTerm entry with
  | none => return ("<non-subject entry>", .skip "entry is not a subject term")
  | some s =>
      let name := nameOf g s
      match typeOf g s with
      | none => return (name, .skip "entry has no rdf:type")
      | some ty =>
          if ty == srtNs ++ "RulesEvalTest" then
            return (name, ← runEvalTest dir g s)
          else
            match syntaxKinds.find? (fun k => k.typeIri == ty) with
            | some k => return (name, ← runSyntaxTest dir g s k)
            | none => return (name, .unsupported s!"unrecognised test type {ty}")

def runManifest (path : String) : IO Score := do
  match ← readOpt path with
  | none =>
      IO.println s!"  MISSING {path}"
      return {}
  | some text =>
      match L4Factoidal.Syntax.parseTurtle text (some ("file://" ++ path)) with
      | .error e =>
          IO.println s!"  UNPARSED {path}: {e.msg} at {e.pos}"
          return {}
      | .ok g =>
          let dir := dirname path
          let entries := entriesOf g
          let mut score : Score := {}
          for e in entries do
            let (name, out) := ← runOne dir g e
            if out.isFail then IO.println ("  " ++ out.line name)
            score := score.bump out
          IO.println (Score.line (suiteLabel path) score)
          return score

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD
    "third_party/testing/shacl/shacl12-test-suite/tests/rules"
  IO.println "SHACL 1.2 rules suite, Lean 4 (L4Factoidal.SHACL.Rules)"
  IO.println ""
  let mut total : Score := {}
  for sub in ["syntax", "wellformed", "stratification", "eval"] do
    let m := root ++ "/" ++ sub ++ "/manifest.ttl"
    total := total.add (← runManifest m)
  IO.println ""
  IO.println (Score.line "shacl 1.2 rules TOTAL" total)
  return (if total.fail > 0 then 1 else 0)

end Harness.ShaclRules

def main (args : List String) : IO UInt32 := Harness.ShaclRules.main args
