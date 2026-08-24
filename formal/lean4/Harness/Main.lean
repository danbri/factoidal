/-
Harness.Main — `lake exe l4w3c <manifest.ttl>…`

The Lean tree's W3C conformance runner. It reads the REAL manifests
and the real fixture files off disk (iron rule #6) and scores them
with the Lean engine, printing the score-line grammar
`bin/w3c-runner/w3c_runner.ml` prints so the two trees' numbers are
directly comparable:

    <suite>: N pass, M fail, K skip, U unsupported (out of T)

Every numerator is labelled and the denominator is always present
(anti-pattern #25), and the `HARNESS-DIAG` line follows each score
line so that a run which measured NOTHING — missing manifest, empty
entry list, a comparison that gave up — cannot be mistaken for a green
one. Exit code is 1 when any test fails.

Usage:

    lake exe l4w3c ../../third_party/testing/w3c/rdf/rdf11/rdf-turtle/manifest.ttl \
                   ../../third_party/testing/rdf-canon/tests/manifest.ttl

    lake exe l4w3c --quiet <manifest…>   # score lines + failures only

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Run
-- Imported so the harness's `#guard`s evaluate during THIS build: a
-- wrong answer in the manifest walk or the score-line formatter is a
-- build error, not a surprise at run time.
import Harness.HarnessTests

namespace Harness

/-- How deep an `mf:include` chain may go. `manifest-all.ttl` →
`<suite>/manifest.ttl` is one level; the bound only stops a cycle. -/
def includeDepth : Nat := 4

/-- The RDF version a manifest's fixtures are written in — this
tree's answer to the F* runner's `--rdf` / `--rdf12` CLI flags (see
`Harness/Run.lean` §"RDF version"). A manifest is RDF 1.2 when its
`mf:assumedTestBase` sits under `…/rdf/rdf12/` (every rdf12 leaf
manifest declares one) or, failing that, when its own path does. A
manifest that says neither is RDF 1.1, which keeps every existing
suite exactly where it was. -/
def modeOfManifest (assumedBase : Option String) (path : String) :
    L4Factoidal.Syntax.Mode :=
  let says (s : String) : Bool :=
    (s.splitOn "/rdf12/").length > 1 || (s.splitOn "/sparql12/").length > 1
  match assumedBase with
  | some b => if says b then .rdf12 else .rdf11
  | none   => if says path then .rdf12 else .rdf11

/-- Run every entry of one manifest. A manifest with NO entries but an
`mf:include` list (`sparql11/manifest-all.ttl`) runs each included
manifest in turn, printing one score line per sub-suite, and returns
their sum — the F* runner follows includes the same way. -/
def runManifest : Nat → System.FilePath → Bool → IO (Score × Diag)
  | 0, path, _ => do
      let label := suiteLabel path.toString
      IO.println (Score.line label {})
      IO.println (Diag.line label { noManifest := 1 })
      IO.println s!"  (mf:include nesting deeper than {includeDepth}: {path})"
      return ({}, { noManifest := 1 })
  | depth + 1, path, verbose => do
  let label := suiteLabel path.toString
  match ← loadManifest path with
  | none =>
      IO.println (Score.line label {})
      IO.println (Diag.line label { noManifest := 1 })
      IO.println s!"  (manifest not found: {path} — run tools/ensure-test-env.sh)"
      return ({}, { noManifest := 1 })
  | some (.error e) =>
      IO.println (Score.line label {})
      IO.println (Diag.line label { noManifest := 1 })
      IO.println s!"  (manifest did NOT parse: {e})"
      return ({}, { noManifest := 1 })
  | some (.ok (tests, assumedBase)) =>
      let abs := (← IO.FS.realPath path).toString
      let manifestDir := dirname abs
      -- An umbrella manifest: no entries of its own, only includes.
      let includes ← if tests.isEmpty then
          (match ← readOpt path with
           | some text => pure (parseManifestIncludes abs text)
           | none      => pure [])
        else pure []
      if tests.isEmpty && !includes.isEmpty then
        if verbose then
          IO.println s!"# {label}: {includes.length} included manifests"
        let mut total : Score := {}
        let mut totalDiag : Diag := {}
        for inc in includes do
          let (s, d) ← runManifest depth (System.FilePath.mk inc) verbose
          total := total.add s
          totalDiag := totalDiag.add d
          IO.println ""
        return (total, totalDiag)
      else
      let mode := modeOfManifest assumedBase abs
      if verbose then
        let v := match mode with | .rdf11 => "RDF 1.1" | .rdf12 => "RDF 1.2"
        match assumedBase with
        | some b => IO.println s!"# {label}: {tests.length} entries, {v}, mf:assumedTestBase {b}"
        | none   => IO.println s!"# {label}: {tests.length} entries, {v}, no mf:assumedTestBase"
      let mut score : Score := {}
      let mut diag : Diag := { zeroTests := if tests.isEmpty then 1 else 0 }
      -- The Graph Store the http-rdf-update entries share, in manifest order.
      let gspStore ← IO.mkRef L4Factoidal.SPARQL.GraphStore.GraphStore.empty
      for tc in tests do
        let r ← runTest mode assumedBase manifestDir gspStore tc
        score := score.bump r.outcome
        diag := { diag with
                  budgetExceeded := diag.budgetExceeded + (if r.budgetExceeded then 1 else 0),
                  rowsCompared := diag.rowsCompared + r.rowsCompared,
                  triplesCompared := diag.triplesCompared + r.triplesCompared,
                  gspSeeded := diag.gspSeeded + (if r.gspSeeded then 1 else 0) }
        if verbose || r.outcome.isFail then
          IO.println (Outcome.line tc.name r.outcome)
      IO.println (Score.line label score)
      IO.println (Diag.line label diag)
      return (score, diag)

def main (args : List String) : IO UInt32 := do
  let verbose := !(args.contains "--quiet")
  let manifests := args.filter (fun a => !a.startsWith "--")
  if manifests.isEmpty then
    IO.eprintln "usage: l4w3c [--quiet] <manifest.ttl>..."
    IO.eprintln "  e.g. lake exe l4w3c ../../third_party/testing/w3c/rdf/rdf11/rdf-turtle/manifest.ttl"
    IO.eprintln "       lake exe l4w3c ../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl"
    return 2
  let mut total : Score := {}
  let mut totalDiag : Diag := {}
  for m in manifests do
    let (s, d) ← runManifest includeDepth (System.FilePath.mk m) verbose
    total := total.add s
    totalDiag := totalDiag.add d
    IO.println ""
  IO.println (Score.line "TOTAL" total)
  IO.println (Diag.line "TOTAL" totalDiag)
  return (if total.fail == 0 then 0 else 1)

end Harness

def main (args : List String) : IO UInt32 := Harness.main args
