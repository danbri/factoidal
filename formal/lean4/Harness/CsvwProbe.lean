/-
Harness/CsvwProbe — run `L4Factoidal.CSVW` against the REAL W3C csvw
corpus vendored at `third_party/testing/csvw/tests/`.

This is a HARNESS, not part of the verified library: it does file I/O
and prints. It reads the suite's own `.csv` files off disk — never
synthetic input "inspired by" the suite.

WHAT IT MEASURES, stated precisely so the number cannot be read as
more than it is: for every `ToRdfTest` in the manifest whose action is
a plain `.csv` file, it reads that file with the Lean dialect reader
and reports whether the read produced a table with at least one row
and a UNIFORM column count. That is a READER-LEVEL check, not
conformance: it does not compare against the expected `.ttl`, which
needs metadata resolution and an isomorphism check.

Reported as its own metric with its own name for exactly that reason.
Calling it "csvw: N pass" would be a lie by naming.

Usage: `lake exe l4csvw-probe [tests-dir]`
-/
import L4Factoidal.CSVW.Dialect

open L4Factoidal.CSVW

/-- Every column count in the table, header rows included. -/
private def widths (t : Table) : List Nat :=
  (t.header ++ t.rows).map (fun r => r.cells.length)

private def uniform (ws : List Nat) : Bool :=
  match ws with
  | []      => false
  | w :: rest => rest.all (· == w)

structure Outcome where
  name    : String
  ok      : Bool
  detail  : String

def probeFile (dir name : String) : IO Outcome := do
  let path := dir ++ "/" ++ name
  if !(← System.FilePath.pathExists path) then
    return ⟨name, false, "missing"⟩
  let src ← IO.FS.readFile path
  let d : ResolvedDialect := ({} : Dialect).resolve
  let t := read d src
  let ws := widths t
  let rowCount := t.rows.length
  if ws.isEmpty then
    return ⟨name, false, "no rows read"⟩
  else if !(uniform ws) then
    -- RAGGED IS NOT A READER FAILURE. CSVW treats a row with the
    -- wrong cell count as a VALIDATION error, not a parse error, and
    -- the suite ships such files deliberately (test058, test091).
    -- The reader is right to return them; reporting them as failures
    -- would penalise correct behaviour.
    return ⟨name, true, s!"ragged (validation-level): widths {ws.take 5}"⟩
  else
    return ⟨name, true, s!"{rowCount} data rows x {ws.head!} columns"⟩

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/csvw/tests"
  if !(← System.FilePath.isDir dir) then
    IO.println s!"csvw probe: corpus directory not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let entries ← System.FilePath.readDir dir
  let csvs := entries.toList.filterMap (fun e =>
    let n := e.fileName
    if n.endsWith ".csv" then some n else none)
  let csvs := csvs.toArray.qsort (· < ·) |>.toList
  let mut uniformCount := 0
  let mut raggedCount := 0
  let mut fail := 0
  for name in csvs do
    let o ← probeFile dir name
    if !o.ok then
      fail := fail + 1
      IO.println s!"FAIL {o.name}: {o.detail}"
    else if o.detail.startsWith "ragged" then
      raggedCount := raggedCount + 1
      IO.println s!"ragged {o.name}: {o.detail}"
    else uniformCount := uniformCount + 1
  IO.println ""
  IO.println s!"csvw READER probe: {uniformCount} read with uniform width, {raggedCount} read ragged (a VALIDATION-level condition, not a read failure), {fail} failed to read (out of {csvs.length} .csv files)"
  IO.println "NOTE: this is a reader-level check only. It does NOT compare"
  IO.println "against the suite's expected .ttl output, so it is not a"
  IO.println "csvw conformance score and must not be reported as one."
  return 0
