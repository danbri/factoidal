/-
Harness/ShExCRun — a DIFFERENTIAL runner for the ShExC parser.

Every fixture under `third_party/testing/shex/schemas/` ships a
compact-syntax `.shex` and a ShExJ `.json` twin of the SAME schema.
This runner reads both and compares the trees.

## Why a differential and not an expectation file

A ShExC parser has no separate ground truth to check against: the
schema IS the answer. Comparing the two front doors turns the corpus
itself into the oracle, and a disagreement points at one of them
without either having to be blessed.

Four outcomes:

  * **match** — the two readers built the same tree;
  * **mismatch** — they did not, and the first differing declaration
    label is named. This is the number that means something is
    broken;
  * **declined** — the ShExC parser refused, with its message. A
    refusal is NOT a mismatch: a construct outside the implemented
    grammar is visibly unparsed, never a schema that validates the
    wrong graphs;
  * **no reference** — the JSON twin is missing or does not read, so
    there is nothing to compare against.

Usage: `lake exe l4shexc [schemas-dir]`
-/
import L4Factoidal.ShEx.Compact
import L4Factoidal.ShEx.SchemaEq
import L4Factoidal.ShEx.FromJson
import L4Factoidal.JSON.Parser

open L4Factoidal.ShEx
open L4Factoidal.JSON

structure Tally where
  match'   : Nat := 0
  mismatch : Nat := 0
  declined : Nat := 0
  noRef    : Nat := 0
deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/shex/schemas"
  if !(← System.FilePath.pathExists dir) then
    IO.println s!"shexc runner: directory not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let entries ← System.FilePath.readDir dir
  let names := ((entries.toList.map (fun e => e.fileName)).filter
    (fun n => n.endsWith ".shex")).toArray.qsort (· < ·) |>.toList
  let mut t : Tally := {}
  let mut reasons : List String := []
  for n in names do
    let stem := String.ofList (n.toList.take (n.length - 5))
    let jsonPath := dir ++ "/" ++ stem ++ ".json"
    let shexText ← IO.FS.readFile (dir ++ "/" ++ n)
    if !(← System.FilePath.pathExists jsonPath) then
      t := { t with noRef := t.noRef + 1 }
    else
      let jsonText ← IO.FS.readFile jsonPath
      match (parseJson? jsonText).bind schemaOf with
      | none =>
          t := { t with noRef := t.noRef + 1 }
      | some ref =>
        match Compact.parseShExC shexText with
        | .error e =>
            t := { t with declined := t.declined + 1 }
            reasons := reasons ++ [e]
            IO.println s!"DECLINED {stem}: {e}"
        | .ok got =>
            if schemaEq got ref then t := { t with match' := t.match' + 1 }
            else
              t := { t with mismatch := t.mismatch + 1 }
              let where' := (firstDiff got ref).getD "<unknown>"
              IO.println s!"MISMATCH {stem}: first difference at {where'} \
(ShExC has {got.shapes.length} shape(s), ShExJ has {ref.shapes.length})"
              -- `SHEXC_DUMP=<stem>` prints both trees. A label alone
              -- says WHICH declaration differs, never HOW, and the
              -- difference is usually one field deep inside it.
              if (← IO.getEnv "SHEXC_DUMP") == some stem then
                IO.println s!"  ShExC: {repr got.shapes}"
                IO.println s!"  ShExJ: {repr ref.shapes}"
  let compared := t.match' + t.mismatch
  IO.println ""
  IO.println s!"ShExC DIFFERENTIAL: {t.match'} match, {t.mismatch} mismatch \
(out of {compared} compared)"
  IO.println s!"DECLINED: {t.declined} schemas the parser refused"
  IO.println s!"NO REFERENCE: {t.noRef} schemas whose ShExJ twin is missing or unreadable"
  IO.println s!"  (out of {names.length} .shex files)"
  -- Which refusals, and how many of each: one reason repeated a
  -- hundred times and a hundred one-off reasons call for very
  -- different next pieces of work.
  let uniq := reasons.eraseDups
  if !uniq.isEmpty then
    IO.println ""
    IO.println "Refusal reasons, by frequency:"
    let counted := (uniq.map (fun r => ((reasons.filter (· == r)).length, r))).toArray.qsort
      (fun a b => a.1 > b.1) |>.toList
    for (k, r) in counted.take 25 do
      IO.println s!"  {k}x  {r}"
    if counted.length > 25 then
      IO.println s!"  … and {counted.length - 25} more reasons"
  IO.println ""
  IO.println "A DECLINED schema is counted apart, never as a mismatch: a"
  IO.println "construct outside the implemented grammar is visibly unparsed,"
  IO.println "never a schema that validates the wrong graphs."
  return (if t.mismatch > 0 then 1 else 0)
