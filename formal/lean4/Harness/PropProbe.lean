/-
Harness.PropProbe — `lake exe l4prop [--cases N] [--seed S] [--verbose]`

Runs `L4Factoidal.Testing.allProps` over N seeded cases (default 500,
seeds S .. S+N-1) and prints, per invariant, `N pass, M fail (out of
T)`. Every failure is printed as a minimal repro: the seed, the graph
as N-Triples, the query text, and the invariant's own message. Exit
code 1 on any failure.

The measurement check (`skills/measuring-inference`): the probe also
prints how many solution rows and triples the cases actually produced,
so a 100%-green run over empty inputs is visible as such.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Testing.Props

open L4Factoidal.Testing

namespace Harness.Prop

structure Tally where
  pass : Nat := 0
  fail : Nat := 0

def findFlag : List String → String → Option String
  | [], _ => none
  | a :: rest, flag => if a == flag then rest.head? else findFlag rest flag

def parseNatArg (args : List String) (flag : String) (dflt : Nat) : Nat :=
  match findFlag args flag with
  | some v => v.toNat?.getD dflt
  | none   => dflt

def repro (c : Case) : String :=
  s!"  seed: {c.seed}\n  graph (N-Triples):\n{c.graphText}  query: {c.queryText}"

def main (args : List String) : IO UInt32 := do
  let n := parseNatArg args "--cases" 500
  let seed0 := parseNatArg args "--seed" 0
  let verbose := args.contains "--verbose"
  let mut tallies : List (String × Tally) := allProps.map (fun (name, _) => (name, {}))
  let mut rows : Nat := 0
  let mut triples : Nat := 0
  let mut failures : Nat := 0
  for i in List.range n do
    let c := genCase (seed0 + i)
    rows := rows + c.omegaA.length + c.omegaB.length
    triples := triples + c.graph.length
    if verbose then
      IO.println s!"# seed {c.seed}: {c.graph.length} triples, A {c.omegaA.length} rows, B {c.omegaB.length} rows: {c.queryText}"
    let mut newTallies : List (String × Tally) := []
    for ((name, p), (_, t)) in allProps.zip tallies do
      match p c with
      | none   => newTallies := newTallies ++ [(name, { t with pass := t.pass + 1 })]
      | some m =>
          failures := failures + 1
          IO.println s!"FAIL {name} (seed {c.seed}): {m}"
          IO.println (repro c)
          newTallies := newTallies ++ [(name, { t with fail := t.fail + 1 })]
    tallies := newTallies
  for (name, t) in tallies do
    IO.println s!"PROP {name}: {t.pass} pass, {t.fail} fail (out of {t.pass + t.fail})"
  IO.println s!"PROP TOTAL: {n} cases, {failures} failures; measurement: {triples} triples generated, {rows} BGP rows evaluated"
  return (if failures == 0 then 0 else 1)

end Harness.Prop

def main (args : List String) : IO UInt32 := Harness.Prop.main args
