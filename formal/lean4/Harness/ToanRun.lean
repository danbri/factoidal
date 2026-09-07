/-
Harness/ToanRun — the "Think of a Number" (TOAN) parity battery.

Runs every case in `L4Factoidal.Math.ToanCases` — the checks
transcribed from the F* consumer test `tests/unit/toan_tests.ml` —
against the Lean `Math/*` and `MathML/Core` functions and prints a
labelled score.

A case whose F* function has no Lean counterpart prints MISSING with
the function named and counts as a FAILURE. There is no skip: a suite
that skips the unported functions scores the port it wishes it had.

Usage: `lake exe l4toan` (no arguments; the battery is a Lean table,
not a file corpus, so it needs no fixtures).
-/
import L4Factoidal.Math.ToanCases

open L4Factoidal.Math.Toan

/-- Per-category tallies, in first-appearance order. -/
def tally (cs : List Case) : List (String × Nat × Nat) :=
  cs.foldl (fun acc c =>
    let hit := acc.any (fun t => t.1 == c.cat)
    if hit then
      acc.map (fun t =>
        if t.1 == c.cat then
          (t.1, t.2.1 + (if c.ok then 1 else 0), t.2.2 + (if c.ok then 0 else 1))
        else t)
    else acc ++ [(c.cat, (if c.ok then 1 else 0), (if c.ok then 0 else 1))]) []

def main : IO UInt32 := do
  let cs := allCases
  for c in cs do
    match c.outcome with
    | .pass        => IO.println s!"  PASS  {c.name}"
    | .fail d      => IO.println s!"  FAIL  [{c.cat}] {c.name} (toan_tests.ml:{c.ml}): {d}"
    | .missing fn  =>
        IO.println s!"  MISSING  [{c.cat}] {c.name} (toan_tests.ml:{c.ml}): no Lean {fn}"
  let pass := (cs.filter Case.ok).length
  let fail := cs.length - pass
  IO.println ""
  IO.println "by category:"
  for (cat, p, f) in tally cs do
    IO.println s!"  {cat}: {p} pass, {f} fail (out of {p + f})"
  IO.println ""
  IO.println s!"TOAN (Lean): {pass} pass, {fail} fail (out of {cs.length})"
  return (if fail > 0 then 1 else 0)
