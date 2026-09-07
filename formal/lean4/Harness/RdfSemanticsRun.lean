/-
Harness.RdfSemanticsRun — the W3C RDF 1.2 Semantics entailment
manifest (`lake exe l4rdf-semantics`).

`third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl` — 47
entries, 32 `mf:PositiveEntailmentTest` + 15 `mf:NegativeEntailmentTest`.

This file reuses the general W3C manifest walk
(`Harness.Manifest.loadManifest`) and the general per-test dispatcher
(`Harness.runTest`, `Harness/Run.lean`), which already routes
`PositiveEntailmentTest` / `NegativeEntailmentTest` to
`Harness.runEntailmentTest` — see that file's "RDF 1.1 Semantics"
section, whose `parseEntailmentGraph` docstring names this very
manifest ("the rdf12 `rdf-semantics` fixtures carry triple terms and
reifier shorthand, which `.rdf11` rejects"). No new manifest reader,
no new entailment logic lives here: this module is I/O and score
bookkeeping only — the harness reads files, calls the library, counts
and prints.

## `mf:recognizedDatatypes` / `mf:unrecognizedDatatypes`

Every entry carries `mf:entailmentRegime` ("simple" / "RDF" / "RDFS" /
"RDFS-Plus"), `mf:recognizedDatatypes` and `mf:unrecognizedDatatypes`.
`mf:recognizedDatatypes` IS load-bearing and IS read, via
`TestCase.recognizedDatatypes` → `Harness.recognizedDatatypesOf` → the
`D` argument of every `RDF.Entailment.Regime` call inside
`runEntailmentTest`. `mf:unrecognizedDatatypes` is `()` (empty) on
ALL 47 entries in this manifest — checked by inspection
(`grep -c 'mf:unrecognizedDatatypes' manifest.ttl` = 47, every one
`();`) — so for this particular manifest it never discriminates a
verdict; `bin/w3c-runner/w3c_runner.ml` does not read it either (its
one mention of the predicate is a comment about the empty-list
encoding, not a dispatch). A future manifest revision that populates
it would need a real reader, not assumed to stay empty.

## RDF version

The manifest declares `mf:assumedTestBase
<https://w3c.github.io/rdf-tests/rdf/rdf12/rdf-semantics/>`, which
`Harness.Main.modeOfManifest` (not imported here — see below) would
resolve to `Mode.rdf12` by its own `/rdf12/`-in-the-base rule. This
runner is dedicated to that one manifest and passes `Mode.rdf12`
directly, matching `bin/w3c-runner/w3c_runner.ml`'s own dedicated
`--rdf12entail` CLI mode for the same suite.

## Why this file does not `import Harness.Main`

`Harness.Main` ends with an UNNAMESPACED `def main`, which would
collide with this file's own `def main` (both resolve to `_root_.main`
— the `lean_exe` entry point). So the small amount of manifest-walk
glue `Harness.Main.runManifest` provides (mode selection, the
score/diag accumulation loop, the per-test print) is reproduced here
directly against `Harness.loadManifest` / `Harness.runTest` /
`Harness.Score` / `Harness.Diag` — a dozen lines, all bookkeeping, no
semantic logic.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.

Usage: `lake exe l4rdf-semantics [manifest.ttl]`
-/
import Harness.Run
import Harness.Fixtures

open L4Factoidal.Syntax (Mode)

namespace Harness

/-- Root-relative default, resolved via `Harness.Fixtures.fixtureArgOr`
so the same binary runs from the repository root or from
`formal/lean4` (this task's two required invocation directories). -/
def rdfSemanticsDefaultManifest : String :=
  "third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl"

/-- Run the rdf-semantics manifest end to end: load it, dispatch every
entry through `Harness.runTest` under `Mode.rdf12`, print one outcome
line per test (`Outcome.line`), the score-line grammar (`Score.line`)
and the `HARNESS-DIAG` line (`Diag.line`) so a silently-empty walk
cannot read as green, and return the process exit code. -/
def runRdfSemantics (path : System.FilePath) : IO UInt32 := do
  let label := "rdf-semantics"
  match ← loadManifest path with
  | none =>
      IO.println (Score.line label {})
      IO.println (Diag.line label { noManifest := 1 })
      IO.println s!"  (manifest not found: {path} — run tools/ensure-test-env.sh)"
      return 1
  | some (.error e) =>
      IO.println (Score.line label {})
      IO.println (Diag.line label { noManifest := 1 })
      IO.println s!"  (manifest did NOT parse: {e})"
      return 1
  | some (.ok (tests, assumedBase)) =>
      let abs := (← IO.FS.realPath path).toString
      let manifestDir := dirname abs
      IO.println s!"# {label}: {tests.length} entries, RDF 1.2, mf:assumedTestBase {assumedBase}"
      let mut score : Score := {}
      let mut diag : Diag := { zeroTests := if tests.isEmpty then 1 else 0 }
      let gspStore ← IO.mkRef L4Factoidal.SPARQL.GraphStore.GraphStore.empty
      for tc in tests do
        let r ← runTest Mode.rdf12 assumedBase manifestDir gspStore tc
        score := score.bump r.outcome
        diag := { diag with
                  budgetExceeded := diag.budgetExceeded + (if r.budgetExceeded then 1 else 0),
                  rowsCompared := diag.rowsCompared + r.rowsCompared,
                  triplesCompared := diag.triplesCompared + r.triplesCompared,
                  gspSeeded := diag.gspSeeded + (if r.gspSeeded then 1 else 0) }
        IO.println (Outcome.line tc.name r.outcome)
      IO.println (Score.line label score)
      IO.println (Diag.line label diag)
      return (if score.fail == 0 then 0 else 1)

end Harness

def main (args : List String) : IO UInt32 := do
  let path ← Harness.fixtureArgOr args.head? Harness.rdfSemanticsDefaultManifest
  Harness.runRdfSemantics (System.FilePath.mk path)
