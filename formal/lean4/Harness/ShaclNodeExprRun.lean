/-
Harness.ShaclNodeExprRun — the SHACL 1.2 `node-expr` suite runner
(`l4shacl-nodeexpr`).

The `l4shacl` probe does not recognise `sht:EvalNodeExpr`, so this
suite reported "out of 2" and was the second unread row of
<https://github.com/danbri/factoidal/issues/553>. This runner reads it,
mirroring `bin/shacl-runner/shacl_runner.ml`'s extraction:

* every subject typed `sht:EvalNodeExpr` in a leaf manifest file;
* `mf:action`'s `sht:nodeExpr` is the expression node, and the leaf
  file's whole graph is the data graph;
* `sht:focusNode` sets the focus, `sht:scope-<name>` properties become
  variable bindings, `sht:ignoreOrder true` compares as a multiset;
* `mf:result` is an `rdf:List` of the expected terms.

Not part of the verified library: this file does I/O and prints scores.

Usage, from the repository root:

    lake exe l4shacl-nodeexpr [manifest]

defaulting to
`third_party/testing/shacl/shacl12-test-suite/tests/node-expr/manifest.ttl`.
-/
import Harness.Manifest
import L4Factoidal.SHACL.NodeExpr
import L4Factoidal.Syntax.Turtle

open L4Factoidal.RDF
open L4Factoidal.SHACL
open Harness

namespace Harness.ShaclNodeExpr

def shtNs : String := "http://www.w3.org/ns/shacl-test#"
def shtScopePrefix : String := shtNs ++ "scope-"

/-- A term key that separates literals differing only in datatype or
    language, so the multiset comparison cannot collapse them. -/
def keyOf : Term → String
  | .iri i => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .literal l =>
      "\"" ++ l.val.lexicalForm ++ "\"^^" ++ l.val.datatype.val ++
      (match l.val.langTag with | some t => "@" ++ t | none => "") ++
      (match l.val.direction with
       | some .ltr => "--ltr" | some .rtl => "--rtl" | none => "")
  | .tripleTerm _ _ _ => "<<triple>>"

def insertStr (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertStr x ys

def sortStrs : List String → List String
  | [] => []
  | x :: xs => insertStr x (sortStrs xs)

structure NeSpec where
  name         : String
  graph        : Graph
  expr         : Term
  focus        : Option Term
  scope        : List (String × Term)
  expected     : List Term
  ignoreOrder  : Bool

def labelOf (g : Graph) (s : Subject) : String :=
  match findObject? g s (mfNs ++ "name") with
  | some (.literal l) => l.val.lexicalForm
  | _ => match findObject? g s (rdfsNs ++ "label") with
         | some (.literal l) => l.val.lexicalForm
         | _ => subjKey s

def specOf (g : Graph) (s : Subject) : Option NeSpec := do
  let act ← findObject? g s (mfNs ++ "action")
  let actS ← subjectOfTerm act
  let expr ← findObject? g actS (shtNs ++ "nodeExpr")
  let focus := findObject? g actS (shtNs ++ "focusNode")
  let ignoreOrder :=
    match findObject? g actS (shtNs ++ "ignoreOrder") with
    | some (.literal l) => l.val.lexicalForm == "true"
    | _ => false
  let scope := g.filterMap (fun tr =>
    if tr.s == actS && tr.p.val.startsWith shtScopePrefix
       && tr.p.val.length > shtScopePrefix.length
    then some (String.ofList (tr.p.val.toList.drop shtScopePrefix.length), tr.o)
    else none)
  let expected :=
    match findObject? g s (mfNs ++ "result") with
    | some rl => collectList g (g.length + 1000) rl
    | none => []
  some { name := labelOf g s, graph := g, expr := expr, focus := focus,
         scope := scope, expected := expected, ignoreOrder := ignoreOrder }

def runSpec (ne : NeSpec) : Outcome :=
  let actual := evalNodeExprTop ne.graph ne.focus ne.scope ne.expr
  let ok :=
    if ne.ignoreOrder then
      sortStrs (actual.map keyOf) == sortStrs (ne.expected.map keyOf)
    else actual.map keyOf == ne.expected.map keyOf
  if ok then .pass
  else .fail s!"expected [{String.intercalate "; " (ne.expected.map keyOf)}], got [{String.intercalate "; " (actual.map keyOf)}]"

/-- Every subject in `g` typed `sht:EvalNodeExpr`. -/
def evalSubjects (g : Graph) : List Subject :=
  (g.filterMap (fun t =>
    if t.p.val == rdfType && termKey t.o == shtNs ++ "EvalNodeExpr"
    then some t.s else none))

/-- Subjects typed `sht:Validate`. The `constraints/` sub-directory
    holds two of these — ordinary SHACL validation tests that happen to
    use a node expression in a shape. They belong to `l4shacl`, not
    here, and are counted as UNSUPPORTED so this runner's denominator
    is the suite's own and the two are visible rather than missing.
    F\*'s 142 is these two plus the 140 `EvalNodeExpr` entries. -/
def validateSubjects (g : Graph) : List Subject :=
  (g.filterMap (fun t =>
    if t.p.val == rdfType && termKey t.o == shtNs ++ "Validate"
    then some t.s else none))

/-- `mf:include` in BOTH shapes the suite uses: an `rdf:List` of
    manifests (`manifest-rules.ttl`) and one statement per manifest
    (`node-expr/manifest.ttl`). `Harness.Manifest.manifestIncludes`
    handles only the list form, so a bare-IRI include walked in as
    zero sub-manifests and the whole suite read as "out of 0". -/
def includesOf (dir : String) (g : Graph) : List String :=
  let fuel := g.length + 1
  let heads := g.filterMap (fun t =>
    if t.p.val == mfNs ++ "include" then some t.o else none)
  heads.flatMap (fun h =>
    match collectList g fuel h with
    | [] => [iriToLocalPath dir (termKey h)]          -- a bare IRI include
    | ms => ms.map (fun m => iriToLocalPath dir (termKey m)))

partial def collectManifests (path : String) : IO (List String) := do
  match ← readOpt path with
  | none => return []
  | some text =>
      match L4Factoidal.Syntax.parseTurtle text (some ("file://" ++ path)) .rdf12 with
      | .error _ => return [path]
      | .ok g =>
          let incs := includesOf (dirname path) g
          if incs.isEmpty then return [path]
          else return (← incs.foldlM (fun acc m => do
            return acc ++ (← collectManifests m)) ([] : List String))

def runFile (path : String) : IO Score := do
  match ← readOpt path with
  | none => return {}
  | some text =>
      match L4Factoidal.Syntax.parseTurtle text (some ("file://" ++ path)) .rdf12 with
      | .error e =>
          IO.println s!"  UNPARSED {path}: {e.msg} at {e.pos}"
          return { fail := 1 }
      | .ok g =>
          let mut score : Score := {}
          for _ in validateSubjects g do
            score := score.bump (.unsupported "sht:Validate — a validation test, run by l4shacl")
          for s in evalSubjects g do
            match specOf g s with
            | none =>
                IO.println s!"  SKIP {basename path}: entry {subjKey s} has no sht:nodeExpr"
                score := score.bump (.skip "no sht:nodeExpr")
            | some ne =>
                let out := runSpec ne
                if out.isFail then IO.println ("  " ++ out.line (basename path ++ " / " ++ ne.name))
                score := score.bump out
          return score

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD
    "third_party/testing/shacl/shacl12-test-suite/tests/node-expr/manifest.ttl"
  IO.println "SHACL 1.2 node-expr suite, Lean 4 (L4Factoidal.SHACL.NodeExpr)"
  IO.println ""
  let files ← collectManifests root
  let mut total : Score := {}
  for f in files do
    total := total.add (← runFile f)
  IO.println ""
  IO.println s!"({files.length} leaf files read)"
  IO.println (Score.line "shacl 1.2 node-expr TOTAL" total)
  return (if total.fail > 0 then 1 else 0)

end Harness.ShaclNodeExpr

def main (args : List String) : IO UInt32 := Harness.ShaclNodeExpr.main args
