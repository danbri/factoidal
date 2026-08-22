/-
Harness.RdfXmlProbe — run the Lean RDF/XML parser over the real W3C
test files on disk.

Iron rule #6 ("run the real W3C test files") applied to the RDF/XML
port, one rung BELOW the manifest-driven harness: this probe uses the
suite's DIRECTORY layout and file-naming convention rather than reading
`manifest.ttl`, so it measures the RDF/XML parser without depending on
the Turtle parser at the same time.

The convention, which the manifest agrees with:
  * `<dir>/error*.rdf` — a negative syntax test (`rdft:TestXMLNegativeSyntax`);
    the parser MUST reject it. A parse that succeeds is a probe failure.
  * every other `<dir>/*.rdf` — must parse.
  * where `<dir>/X.rdf` has a sibling `<dir>/X.nt`, the graph must be
    isomorphic to it (RDF 1.1 Concepts §3.6) — `RDF.Graph.isomorphic?`.

Base IRI: the suite's `manifest.ttl` declares
`mf:assumedTestBase <https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-xml/>`
and every `mf:action` is the relative reference `<dir>/<file>.rdf`, so
each file's base is `<assumedTestBase><dir>/<file>.rdf`. That string is
what the expected `.nt` files contain, so the probe reads the base out
of `manifest.ttl` with a two-line scan (NOT a Turtle parse — keeping
this probe's dependency on the Turtle port at zero) and falls back to
the literal above.

Every count is printed with its DENOMINATOR and every failure is named,
per the project's score-reporting rule (anti-pattern #25). This probe
reports what it measured; it does not claim conformance — that claim
waits for the manifest-driven runner.
-/
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDF.Isomorphism

open L4Factoidal.Syntax
open L4Factoidal.RDF

/-- Counters for one run. -/
structure Tally where
  parsePosOk    : Nat := 0
  parsePosTotal : Nat := 0
  rejectNegOk   : Nat := 0
  rejectNegTotal: Nat := 0
  evalIsoOk     : Nat := 0
  evalIsoTotal  : Nat := 0
  /-- Positive files with no sibling `.nt` — parsed but not compared. -/
  noExpected    : Nat := 0
  failures      : List String := []

def Tally.note (t : Tally) (msg : String) : Tally :=
  { t with failures := t.failures ++ [msg] }

/-- The suite's negative-test naming convention. -/
def isErrorName (name : String) : Bool := name.startsWith "error"

/-- List a directory's entries with a given extension, sorted. -/
def filesWithExt (dir : System.FilePath) (ext : String) : IO (List String) := do
  if !(← dir.pathExists) then return []
  let entries ← dir.readDir
  let names := entries.toList.map (fun e => e.fileName)
  let matching := names.filter (fun n => n.endsWith ("." ++ ext))
  return (matching.toArray.qsort (· < ·)).toList

/-- Immediate subdirectories, sorted. -/
def subdirs (dir : System.FilePath) : IO (List String) := do
  if !(← dir.pathExists) then return []
  let entries ← dir.readDir
  let mut out : List String := []
  for e in entries do
    if ← e.path.isDir then out := e.fileName :: out
  return (out.toArray.qsort (· < ·)).toList

def readOpt (p : System.FilePath) : IO (Option String) := do
  try
    let s ← IO.FS.readFile p
    return some s
  catch _ =>
    return none

/-- The base IRI the suite documents, scanned out of `manifest.ttl`'s
`mf:assumedTestBase <…>` line. -/
def assumedTestBase (root : System.FilePath) (fallback : String) : IO String := do
  match ← readOpt (root / "manifest.ttl") with
  | none => return fallback
  | some text =>
    let lines := text.splitOn "\n"
    match lines.find? (fun l => (l.splitOn "mf:assumedTestBase").length > 1) with
    | none => return fallback
    | some l =>
      match (l.splitOn "<").getLast? with
      | none => return fallback
      | some tail =>
        match (tail.splitOn ">").head? with
        | none => return fallback
        | some iri => return iri

/-- Run every `*.rdf` in one test directory. -/
def runDir (root : System.FilePath) (baseRoot : String) (dirName : String)
    (t0 : Tally) : IO Tally := do
  let dir := root / dirName
  let mut t := t0
  for name in (← filesWithExt dir "rdf") do
    let path := dir / name
    let some text ← readOpt path | do
      t := t.note s!"{dirName}/{name}: unreadable"
      continue
    let base := baseRoot ++ dirName ++ "/" ++ name
    let res := RdfXml.parseRdfXml text (some base)
    if isErrorName name then
      t := { t with rejectNegTotal := t.rejectNegTotal + 1 }
      match res with
      | .error _ => t := { t with rejectNegOk := t.rejectNegOk + 1 }
      | .ok g    => t := t.note s!"{dirName}/{name}: ACCEPTED a negative test ({g.length} triples)"
    else
      t := { t with parsePosTotal := t.parsePosTotal + 1 }
      match res with
      | .error e => t := t.note s!"{dirName}/{name}: parse failed — {e}"
      | .ok g =>
        t := { t with parsePosOk := t.parsePosOk + 1 }
        let ntName := String.ofList (name.toList.take (name.length - 4)) ++ ".nt"
        let ntPath := dir / ntName
        if ← ntPath.pathExists then
          t := { t with evalIsoTotal := t.evalIsoTotal + 1 }
          match ← readOpt ntPath with
          | none => t := t.note s!"{dirName}/{name}: sibling {ntName} unreadable"
          | some ntText =>
            match parseNTriples ntText with
            | .error e =>
                t := t.note s!"{dirName}/{name}: sibling {ntName} failed N-Triples parse — {e}"
            | .ok expected =>
              if Graph.isomorphic? g expected then
                t := { t with evalIsoOk := t.evalIsoOk + 1 }
              else
                t := t.note
                  s!"{dirName}/{name}: not isomorphic to {ntName} ({g.length} produced vs {expected.length} expected)"
        else
          t := { t with noExpected := t.noExpected + 1 }
  return t

def report (label : String) (t : Tally) (verbose : Bool) : IO Unit := do
  IO.println ""
  IO.println s!"=== {label} ==="
  IO.println s!"parse-positive: {t.parsePosOk} pass, {t.parsePosTotal - t.parsePosOk} fail (out of {t.parsePosTotal})"
  IO.println s!"reject-negative: {t.rejectNegOk} pass, {t.rejectNegTotal - t.rejectNegOk} fail (out of {t.rejectNegTotal})"
  IO.println s!"eval-isomorphic: {t.evalIsoOk} pass, {t.evalIsoTotal - t.evalIsoOk} fail (out of {t.evalIsoTotal})"
  IO.println s!"positive files with no sibling .nt (parsed, not compared): {t.noExpected}"
  IO.println s!"failures listed: {t.failures.length}"
  if verbose then
    for f in t.failures do
      IO.println s!"  FAIL {f}"

def main (args : List String) : IO Unit := do
  let root : System.FilePath :=
    match args.head? with
    | some a => if a == "--quiet" then "../../third_party/testing/w3c/rdf/rdf11/rdf-xml" else a
    | none   => "../../third_party/testing/w3c/rdf/rdf11/rdf-xml"
  let verbose := !(args.contains "--quiet")
  if !(← root.pathExists) then
    IO.println s!"rdf-xml: directory not present at {root} — no numbers reported"
    return
  let base ← assumedTestBase root "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-xml/"
  IO.println s!"rdf-xml base IRI (from manifest.ttl): {base}"
  let dirs ← subdirs root
  IO.println s!"test directories walked: {dirs.length}"
  let mut t : Tally := {}
  for d in dirs do
    t ← runDir root base d t
  report "rdf-xml (RDF 1.1 XML Syntax)" t verbose
