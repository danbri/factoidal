/-
Harness/ShExRun — the ShEx validation suite, run end to end.

`third_party/testing/shex/validation/manifest.jsonld` lists 1182
entries: `sht:ValidationTest` (the focus node MUST satisfy the shape)
and `sht:ValidationFailure` (it must NOT). Each names a schema, a data
graph, a shape label and a focus node.

The schema is read from the ShExJ (`.json`) beside each `.shex`. A
ShExC parser is separate work; ShExJ is the specification's own
abstract syntax written down, and reading it is what lets the
validator be MEASURED today.

## Three outcomes

  * **pass / fail** — the verdict matched, or it did not;
  * **not read** — the schema JSON, the data graph, or the focus node
    could not be read. That is a gap in the READER, not a validation
    result, and folding it into either column would report a parser
    gap as an engine verdict.

Usage: `lake exe l4shex [validation-dir]`
-/
import L4Factoidal.ShEx.FromJson
import L4Factoidal.ShEx.Satisfies
import L4Factoidal.Syntax.Turtle
import L4Factoidal.JSON.Parser

open L4Factoidal.JSON
open L4Factoidal.ShEx
open L4Factoidal.RDF
open L4Factoidal.Syntax

private def fld? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match fld? k v with
  | some (.string s) => some s
  | _                => none

/-- The manifest's entries, whatever wrapper it uses. -/
def entriesOf (j : Json) : List Json :=
  let direct := match fld? "entries" j with
    | some (.array es) => es
    | _ => []
  if !direct.isEmpty then direct
  else match fld? "@graph" j with
    | some (.array gs) => gs.flatMap (fun g => match fld? "entries" g with
        | some (.array es) => es
        | _ => [])
    | _ => []

/-- A focus node, written as an IRI or as a Turtle literal. The suite
    writes a bare string for an IRI and an object for a literal. -/
def focusOf (j : Json) : Option Term :=
  match j with
  | .string s => if h : isIri s then some (.iri ⟨s, h⟩) else none
  | .object _ =>
      match str? "@value" j with
      | some v => some (.literal (Literal.string v))
      | none   => (str? "@id" j).bind (fun s =>
          if h : isIri s then some (Term.iri ⟨s, h⟩) else none)
  | _ => none

/-- The ShExJ file beside a `.shex`. -/
def jsonBeside (p : String) : String :=
  if p.endsWith ".shex" then String.ofList (p.toList.take (p.length - 5)) ++ ".json" else p

/-- Resolve a manifest-relative path, collapsing one `../`. -/
def resolveRel (dir rel : String) : String :=
  if rel.startsWith "../" then
    let up := match (dir.splitOn "/").reverse with
      | _ :: rest => String.intercalate "/" rest.reverse
      | []        => dir
    up ++ "/" ++ String.ofList (rel.toList.drop 3)
  else dir ++ "/" ++ rel

structure Tally where
  pass    : Nat := 0
  fail    : Nat := 0
  notRead : Nat := 0
deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let dir := (args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/shex/validation"
  let verbose := args.contains "--verbose"
  let manifestPath := dir ++ "/manifest.jsonld"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"shex runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match parseJson? mtext with
  | none =>
      IO.println "shex runner: manifest did not parse"
      return 1
  | some mj =>
      let entries := entriesOf mj
      let mut t : Tally := {}
      let mut readGaps : List String := []
      let mut seen := 0
      let _ := seen
      for e in entries do
        seen := seen + 1
        let ty := (str? "@type" e).getD ""
        let name := (str? "name" e).getD "?"
        match fld? "action" e with
        | none => t := { t with notRead := t.notRead + 1 }
        | some act =>
            let schemaRel := (str? "schema" act).getD ""
            let dataRel := (str? "data" act).getD ""
            let label := (str? "shape" act).getD ""
            let focus := (fld? "focus" act).bind focusOf
            let sp := jsonBeside (resolveRel dir schemaRel)
            let dp := resolveRel dir dataRel
            if !(← System.FilePath.pathExists sp) then
              t := { t with notRead := t.notRead + 1 }
              if !readGaps.contains "schema json missing" then
                readGaps := readGaps ++ ["schema json missing"]
            else if !(← System.FilePath.pathExists dp) then
              t := { t with notRead := t.notRead + 1 }
              if !readGaps.contains "data graph missing" then
                readGaps := readGaps ++ ["data graph missing"]
            else
              let ssrc ← IO.FS.readFile sp
              let dsrc ← IO.FS.readFile dp
              match (parseJson? ssrc).bind schemaOf, parseTurtle dsrc none, focus with
              | some sch, .ok g, some n =>
                  let got := validateNode sch g label n
                  let want := ty == "sht:ValidationTest"
                  if got == want then t := { t with pass := t.pass + 1 }
                  else
                    t := { t with fail := t.fail + 1 }
                    if verbose then
                      IO.println s!"FAIL {name} ({ty}): got {got}"
              | none, _, _ =>
                  t := { t with notRead := t.notRead + 1 }
                  if !readGaps.contains "schema JSON not read" then
                    readGaps := readGaps ++ ["schema JSON not read"]
              | _, .error _, _ =>
                  t := { t with notRead := t.notRead + 1 }
                  if !readGaps.contains "data Turtle not read" then
                    readGaps := readGaps ++ ["data Turtle not read"]
              | _, _, none =>
                  t := { t with notRead := t.notRead + 1 }
                  if !readGaps.contains "focus node not read" then
                    readGaps := readGaps ++ ["focus node not read"]
      IO.println ""
      IO.println s!"shex validation: {t.pass} pass, {t.fail} fail (out of {t.pass + t.fail} decided)"
      IO.println s!"NOT READ: {t.notRead} entries (out of {entries.length})"
      if !readGaps.isEmpty then
        IO.println ("  reasons: " ++ String.intercalate ", " readGaps)
      IO.println ""
      IO.println "A NOT-READ entry is a gap in the reader, not a validation"
      IO.println "result: folding it into either column would report a parser"
      IO.println "gap as an engine verdict."
      return 0
