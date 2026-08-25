/-
Bench/SparqlJoinBench.lean — the measurement fixture for the indexed
SPARQL join (issue #466 performance work, 2026-08-25).

Reproduces the workload of the 2026-08-22 npm packaging benchmark
(`docs/designissues/2026-08-22-npm-l4-module-packaging.md`): N people,
each with a `:name` and an `:age` triple (so 2N triples in the graph),
queried with the two-pattern join

    SELECT * WHERE { ?s <http://ex/name> ?n . ?s <http://ex/age> ?a }

Three timings per graph size:

  * `evalBgp`     — the specification evaluator (per-row graph scans);
                    this is what `GraphPattern.evalIn` ran before
                    2026-08-25, so it is the BEFORE column.
  * `evalBgpIdx`  — the indexed twin (`evalBgpIdx_eq_evalBgp` proves
                    it returns the same list).
  * `evalSelect`  — the full shipped path (parse once, evaluate
                    through `GraphPattern.evalIn`, post-process), which
                    now runs the indexed twin: the AFTER column.

Run from `formal/lean4/` with the library built:

    lake env lean --run Bench/SparqlJoinBench.lean

TIMING MODE: `lean --run` executes through the Lean interpreter over
the compiled library, so absolute numbers are NOT comparable to the
wasm numbers in the design doc; before/after ratios under the SAME
command are what this fixture measures.
-/
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser

open L4Factoidal.RDF L4Factoidal.SPARQL

private def mkIri (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def nameIri : WfIri := mkIri "http://ex/name"
private def ageIri  : WfIri := mkIri "http://ex/age"

/-- Runtime IRI constructor: the strings this bench builds always pass
`isIri`; the fallback arm keeps the function total without a proof
about interpolated strings. -/
private def dynIri (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else nameIri

/-- N people → 2N triples: `<http://ex/pI> :name "personI"`,
`<http://ex/pI> :age "I"`. -/
private def mkGraph (people : Nat) : Graph := Id.run do
  let mut g : Graph := []
  for i in [0:people] do
    let s : Subject := .iri (dynIri s!"http://ex/p{i}")
    g := { s := s, p := nameIri, o := .literal (Literal.string s!"person{i}") } :: g
    g := { s := s, p := ageIri, o := .literal (Literal.string s!"{i}") } :: g
  return g

private def queryText : String :=
  "SELECT * WHERE { ?s <http://ex/name> ?n . ?s <http://ex/age> ?a }"

/-- The same two-pattern BGP, as the algebra AST. -/
private def benchBgp : Bgp :=
  [ { s := .var "s", p := .iri nameIri, o := .var "n" },
    { s := .var "s", p := .iri ageIri,  o := .var "a" } ]

private def median (xs : List Nat) : Nat :=
  match (xs.toArray.qsort (· < ·)).toList.drop (xs.length / 2) with
  | x :: _ => x
  | []     => 0

/-- Median-of-`runs` wall time. `IO.lazyPure` is what forces the pure
computation BETWEEN the two clock reads — a plain `let x := act ()`
in a `do` block is deferred by the compiler into `x`'s first use
site, which sits after the second read, and every timing then
reports 0 ms (measured here first, 2026-08-25). -/
private def timeMedian (runs : Nat) (act : Unit → Nat) :
    IO (Nat × Nat) := do
  if runs > 1 then
    let _ ← IO.lazyPure act   -- warmup; skipped for single-run timings
  let mut times : List Nat := []
  let mut out := 0
  for _ in [0:runs] do
    let t0 ← IO.monoMsNow
    out ← IO.lazyPure act
    let t1 ← IO.monoMsNow
    times := (t1 - t0) :: times
  return (out, median times)

def main : IO Unit := do
  let q ← match parseSparql queryText with
    | .ok q => pure q
    | .error e => throw (IO.userError s!"query parse failed: {e}")
  let out ← IO.getStdout
  out.putStrLn "people | triples | rows | evalBgp(spec) ms | evalBgpIdx ms | evalSelect ms"
  out.putStrLn "(spec column: median of 5 runs up to 2,000 triples, 1 run above — the quadratic scan is minutes-per-run in the interpreter at 20,000 triples; other columns: median of 5 after 1 warmup)"
  out.flush
  for people in [100, 1000, 4000, 10000] do
    let g := mkGraph people
    let ds : Dataset := { default := g, named := [] }
    let env : EvalEnv := {}
    let specRuns := if people ≤ 1000 then 5 else 1
    let (rowsSpec, tSpec) ← timeMedian specRuns (fun _ => (evalBgp benchBgp g).length)
    let (rowsIdx, tIdx) ← timeMedian 5 (fun _ => (evalBgpIdx benchBgp g).length)
    let (rowsSel, tSel) ← timeMedian 5 (fun _ => (evalSelect env ds q).2.length)
    let rowsNote := if rowsSpec == rowsIdx && rowsIdx == rowsSel
                    then s!"{rowsSel}" else s!"MISMATCH {rowsSpec}/{rowsIdx}/{rowsSel}"
    out.putStrLn s!"{people} | {2 * people} | {rowsNote} | {tSpec} | {tIdx} | {tSel}"
    out.flush
