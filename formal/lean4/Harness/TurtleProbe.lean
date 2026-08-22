/-
Harness.TurtleProbe — run the Lean Turtle and TriG parsers over the real
W3C test files on disk.

Iron rule #6 ("run the real W3C test files") applied to the Lean tree,
one rung BELOW the full manifest-driven harness described in
`docs/designissues/2026-08-22-lean4-w3c-harness.md`: reading a manifest
needs a Turtle parser, so the FIRST measurement of a Turtle parser
cannot come from a manifest. This probe therefore uses the suites' file
NAMING convention instead, which the manifests agree with:

  * `*-bad-*.ttl` / `*-bad-*.trig` — a negative syntax test; the parser
    MUST reject it. A parse that succeeds is a failure of this probe.
  * every other `*.ttl` / `*.trig` — must parse.
  * where `X.ttl` has a sibling `X.nt` (or `X.trig` a sibling `X.nq`),
    the two must denote the same graph / dataset up to blank-node
    renaming — `RDF.Graph.isomorphic?` / `RDF.Dataset.isomorphic?`.

Base IRI is the suites' documented one,
`<mf:assumedTestBase><file>`, READ OUT OF EACH SUITE'S `manifest.ttl`
by this same Turtle parser, so relative references in the fixtures
resolve exactly as the manifests intend — and so the run also
demonstrates the point of the rung, that the manifests are now
readable.

Every count is printed with its DENOMINATOR and every failure is named,
per the project's score-reporting rule (anti-pattern #25). This probe
reports what it measured; it does not claim conformance — that claim
waits for the manifest-driven `l4w3c` runner.
-/

import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism

open L4Factoidal.Syntax
open L4Factoidal.RDF

/-- Counters for one suite run. -/
structure Tally where
  parsePosOk    : Nat := 0
  parsePosTotal : Nat := 0
  rejectNegOk   : Nat := 0
  rejectNegTotal: Nat := 0
  evalIsoOk     : Nat := 0
  evalIsoTotal  : Nat := 0
  /-- Files walked that the suite's `manifest.ttl` does NOT list as an
  `mf:action` — present in the directory but not part of the suite. -/
  notInManifest : Nat := 0
  failures      : List String := []

def Tally.note (t : Tally) (msg : String) : Tally :=
  { t with failures := t.failures ++ [msg] }

/-- Files whose name marks them as a NEGATIVE syntax test. -/
def isBadName (name : String) : Bool :=
  ((name.splitOn "-bad-").length > 1)

/-- List a directory's entries with a given extension, sorted. -/
def filesWithExt (dir : System.FilePath) (ext : String) : IO (List String) := do
  if !(← dir.pathExists) then return []
  let entries ← dir.readDir
  let names := entries.toList.map (fun e => e.fileName)
  let matching := names.filter (fun n => n.endsWith ("." ++ ext))
  return (matching.toArray.qsort (· < ·)).toList

/-- Read a file, returning `none` when it cannot be decoded/read. -/
def readOpt (p : System.FilePath) : IO (Option String) := do
  try
    let s ← IO.FS.readFile p
    return some s
  catch _ =>
    return none

/-- The suite's own declared base IRI, read out of its `manifest.ttl`
with THIS parser: `<> mf:assumedTestBase <…>`. Reading it here rather
than hardcoding it does two jobs at once — it uses the base the suite
actually documents (the corpus moved from
`http://www.w3.org/2013/TurtleTests/` to a `w3c.github.io` base, and
some fixtures were regenerated against the new one), and it exercises
the gating claim of this whole rung: the W3C manifests are Turtle, so a
Turtle parser is what makes them readable. Falls back to `fallback`
when the manifest is absent or carries no such triple. -/
def lastSegment (iri : String) : String :=
  match (iri.splitOn "/").getLast? with
  | some s => s
  | none   => iri

def manifestInfo (dir : System.FilePath) (fallback : String) : IO (String × List String) := do
  match ← readOpt (dir / "manifest.ttl") with
  | none => return (fallback, [])
  | some text =>
    match parseTurtle text (some fallback) with
    | .error e =>
        IO.println s!"  (manifest.ttl did NOT parse — {e}; using fallback base, no entry list)"
        return (fallback, [])
    | .ok g =>
      let mfBase := "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#assumedTestBase"
      let mfAction := "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#action"
      let base :=
        match g.find? (fun t => t.p.val == mfBase) with
        | some t => (match t.o with | .iri i => i.val | _ => fallback)
        | none   => fallback
      let actions := (g.filter (fun t => t.p.val == mfAction)).filterMap (fun t =>
        match t.o with | .iri i => some (lastSegment i.val) | _ => none)
      IO.println s!"  manifest.ttl parsed: {g.length} triples, {actions.length} mf:action entries"
      return (base, actions)

/-- One suite of Turtle files. -/
def runTurtleSuite (dir : System.FilePath) (baseRoot : String) (actions : List String) :
    IO Tally := do
  let mut t : Tally := {}
  for name in (← filesWithExt dir "ttl") do
    let path := dir / name
    let some text ← readOpt path | do
      t := t.note s!"{name}: unreadable"
      continue
    let base := baseRoot ++ name
    let listed := actions.isEmpty || actions.contains name
    if !listed then t := { t with notInManifest := t.notInManifest + 1 }
    let res := parseTurtle text (some base)
    if isBadName name then
      t := { t with rejectNegTotal := t.rejectNegTotal + 1 }
      match res with
      | .error _ => t := { t with rejectNegOk := t.rejectNegOk + 1 }
      | .ok g    => t := t.note s!"{name}: ACCEPTED a -bad- file ({g.length} triples)"
    else
      t := { t with parsePosTotal := t.parsePosTotal + 1 }
      match res with
      | .error e =>
          t := t.note s!"{name}: parse failed{if listed then "" else " [NOT a manifest entry]"} — {e}"
      | .ok g =>
        t := { t with parsePosOk := t.parsePosOk + 1 }
        -- eval comparison when a sibling .nt exists
        let ntName := String.ofList (name.toList.take (name.length - 4)) ++ ".nt"
        let ntPath := dir / ntName
        if ← ntPath.pathExists then
          t := { t with evalIsoTotal := t.evalIsoTotal + 1 }
          match ← readOpt ntPath with
          | none => t := t.note s!"{name}: sibling {ntName} unreadable"
          | some ntText =>
            match parseNTriples ntText with
            | .error e => t := t.note s!"{name}: sibling {ntName} failed N-Triples parse — {e}"
            | .ok expected =>
              if Graph.isomorphic? g expected then
                t := { t with evalIsoOk := t.evalIsoOk + 1 }
              else
                t := t.note
                  s!"{name}: not isomorphic to {ntName} ({g.length} vs {expected.length} triples)"
  return t

/-- One suite of TriG files. -/
def runTriGSuite (dir : System.FilePath) (baseRoot : String) (actions : List String) :
    IO Tally := do
  let mut t : Tally := {}
  for name in (← filesWithExt dir "trig") do
    let path := dir / name
    let some text ← readOpt path | do
      t := t.note s!"{name}: unreadable"
      continue
    let base := baseRoot ++ name
    let listed := actions.isEmpty || actions.contains name
    if !listed then t := { t with notInManifest := t.notInManifest + 1 }
    let res := parseTriG text (some base)
    if isBadName name then
      t := { t with rejectNegTotal := t.rejectNegTotal + 1 }
      match res with
      | .error _ => t := { t with rejectNegOk := t.rejectNegOk + 1 }
      | .ok _    => t := t.note s!"{name}: ACCEPTED a -bad- file"
    else
      t := { t with parsePosTotal := t.parsePosTotal + 1 }
      match res with
      | .error e =>
          t := t.note s!"{name}: parse failed{if listed then "" else " [NOT a manifest entry]"} — {e}"
      | .ok ds =>
        t := { t with parsePosOk := t.parsePosOk + 1 }
        let nqName := String.ofList (name.toList.take (name.length - 5)) ++ ".nq"
        let nqPath := dir / nqName
        if ← nqPath.pathExists then
          t := { t with evalIsoTotal := t.evalIsoTotal + 1 }
          match ← readOpt nqPath with
          | none => t := t.note s!"{name}: sibling {nqName} unreadable"
          | some nqText =>
            match parseNQuads nqText with
            | .error e => t := t.note s!"{name}: sibling {nqName} failed N-Quads parse — {e}"
            | .ok expected =>
              if Dataset.isomorphic? ds expected then
                t := { t with evalIsoOk := t.evalIsoOk + 1 }
              else
                t := t.note s!"{name}: not isomorphic to {nqName}"
  return t

def report (label : String) (t : Tally) (verbose : Bool) : IO Unit := do
  IO.println ""
  IO.println s!"=== {label} ==="
  IO.println s!"parse-positive: {t.parsePosOk} of {t.parsePosTotal}"
  IO.println s!"reject-negative: {t.rejectNegOk} of {t.rejectNegTotal}"
  IO.println s!"eval-iso: {t.evalIsoOk} of {t.evalIsoTotal}"
  IO.println s!"walked but not listed in manifest.ttl: {t.notInManifest}"
  IO.println s!"failures listed: {t.failures.length}"
  if verbose then
    for f in t.failures do
      IO.println s!"  FAIL {f}"

def main (args : List String) : IO Unit := do
  let root : System.FilePath :=
    match args.head? with
    | some a => a
    | none   => "../../third_party/testing/w3c/rdf/rdf11"
  let verbose := !(args.contains "--quiet")
  let ttlDir := root / "rdf-turtle"
  let trigDir := root / "rdf-trig"
  if ← ttlDir.pathExists then
    let (base, actions) ← manifestInfo ttlDir "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/"
    IO.println s!"rdf-turtle base IRI (from manifest.ttl): {base}"
    let t ← runTurtleSuite ttlDir base actions
    report "rdf-turtle (Turtle 1.1)" t verbose
  else
    IO.println s!"rdf-turtle: directory not present at {ttlDir} — no numbers reported"
  if ← trigDir.pathExists then
    let (base, actions) ← manifestInfo trigDir "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-trig/"
    IO.println s!"rdf-trig base IRI (from manifest.ttl): {base}"
    let t ← runTriGSuite trigDir base actions
    report "rdf-trig (TriG 1.1)" t verbose
  else
    IO.println s!"rdf-trig: directory not present at {trigDir} — no numbers reported"
