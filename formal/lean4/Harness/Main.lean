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

/-- Run every entry of one manifest. -/
def runManifest (path : System.FilePath) (verbose : Bool) : IO (Score × Diag) := do
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
      let manifestDir := dirname (← IO.FS.realPath path).toString
      if verbose then
        match assumedBase with
        | some b => IO.println s!"# {label}: {tests.length} entries, mf:assumedTestBase {b}"
        | none   => IO.println s!"# {label}: {tests.length} entries, no mf:assumedTestBase"
      let mut score : Score := {}
      let mut diag : Diag := { zeroTests := if tests.isEmpty then 1 else 0 }
      for tc in tests do
        let r ← runTest assumedBase manifestDir tc
        score := score.bump r.outcome
        if r.budgetExceeded then diag := { diag with budgetExceeded := diag.budgetExceeded + 1 }
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
    return 2
  let mut total : Score := {}
  let mut totalDiag : Diag := {}
  for m in manifests do
    let (s, d) ← runManifest (System.FilePath.mk m) verbose
    total := total.add s
    totalDiag := totalDiag.add d
    IO.println ""
  IO.println (Score.line "TOTAL" total)
  IO.println (Diag.line "TOTAL" totalDiag)
  return (if total.fail == 0 then 0 else 1)

end Harness

def main (args : List String) : IO UInt32 := Harness.main args
