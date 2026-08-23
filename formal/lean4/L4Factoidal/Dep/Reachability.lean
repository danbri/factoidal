/-
L4Factoidal.Dep.Reachability — verified graph reachability for
module-liveness analysis.

Port of `formal/fstar/Dep.Reachability.fst` (170 lines).

## Why the module exists

`tools/module-liveness.py` v2 rooted its dead-module search in
`ocamlobjinfo` output, read by an unverified Python breadth-first
search. That search is exhaustive relative to the edges it is given,
but nothing checked that its OUTPUT is closed under those edges: an
off-by-one queue drain or a flipped edge direction would silently
under- or over-report DEAD modules, and the `.cmx` dependency meant the
tool could not run before a build existed.

This is the reachability core the v3 tool calls instead. It carries one
theorem, `closedSetCatchesAll`, whose premises — `isClosed` and
`contains` — are DECIDABLE, and the driver re-checks them on the
algorithm's actual output at run time. That is what makes the fuel
bound and the closure implementation irrelevant to soundness: if
`closureFuel` ran out of fuel, or had a bug, and returned a non-closed
set, the driver's run-time `isClosed` check catches it and refuses
before any DEAD verdict is trusted.

The theorem's job is narrower and stronger than "the algorithm is
right": IF the set the driver holds really is closed and really does
contain the roots, THEN no root reaches anything outside it. That is a
fact about ALL closed supersets of the roots, not only the one
`closureFuel` happens to compute.

## Differences from the F\*

1. `reaches` is a `Type`-valued `noeq` GADT in F\* because the proof
   recurses structurally on the derivation term. In Lean it is a
   `Prop`-valued inductive and the proof uses `induction`, which is the
   same argument written the way Lean writes it.
2. `no_root_reaches` needs `FStar.Classical.impl_intro` and an explicit
   `introduce ... with` block to get from `Reaches → False` to a
   negation. In Lean `¬P` IS `P → False`, so the corollary is direct.
3. No `--fuel` / `--ifuel` pragmas. The F\* module sets them per lemma
   where z3's default budget was not enough; `induction` needs none.
-/

namespace L4Factoidal.Dep

/-! ## The graph

`Node` is an opaque, decidably-equal label — in practice an F\* module
name or an OCaml unit name. `(s, d)` reads "s's compiled unit
references d's". Issue #453 applies: no proof here computes on string
CONTENTS; every step is list membership or structural induction, never
parsing. -/

abbrev Node := String
abbrev Edge := Node × Node

/-- An edge is closed with respect to `acc` when its source is absent
    from `acc` or its target is present. Vacuously closed when the
    source is absent. -/
def edgeClosed (acc : List Node) (e : Edge) : Bool :=
  !(acc.contains e.1) || acc.contains e.2

/-- Every edge whose source is in `acc` has its target in `acc`.
    Decidable — this is the premise the driver re-checks on the
    algorithm's real output. -/
def isClosed (edges : List Edge) (acc : List Node) : Bool :=
  edges.all (edgeClosed acc)

/-- Every element of `xs` is in `acc`. The roots-are-included premise,
    also re-checked by the driver. -/
def allMem (xs acc : List Node) : Bool := xs.all (fun x => acc.contains x)

/-! ## The algorithm

Not trusted for soundness. It only has to be plausible enough that
`closureFuel`'s output usually IS closed, because the driver refuses
otherwise. `stepEdge` and `step` only ever ADD nodes, so `closureFuel`
is monotone in `acc`, and `edges.length + 1` rounds are enough for a
correct implementation to reach a fixed point — each round that does
not reach one has added at least one node, and there are at most
`edges.length` distinct targets worth adding. That adequacy argument is
exactly the kind of reasoning issue #448 does not want load-bearing,
which is why the theorem below does not depend on it. -/

def stepEdge (acc : List Node) (e : Edge) : List Node :=
  if acc.contains e.1 && !(acc.contains e.2) then e.2 :: acc else acc

def step (edges : List Edge) (acc : List Node) : List Node :=
  edges.foldl stepEdge acc

def closureFuel (edges : List Edge) (acc : List Node) : Nat → List Node
  | 0      => acc
  | f + 1  =>
      let acc' := step edges acc
      if acc'.length == acc.length then acc else closureFuel edges acc' f

def reachable (edges : List Edge) (roots : List Node) : List Node :=
  closureFuel edges roots (edges.length + 1)

/-! ## The specification

Inductive reachability, independent of the algorithm above.
`Reaches edges r n` says `n` is reachable from `r` by following zero or
more edges. -/

inductive Reaches (edges : List Edge) : Node → Node → Prop where
  | refl (n : Node) : Reaches edges n n
  | step {a b c : Node} : Reaches edges a b → (b, c) ∈ edges → Reaches edges a c

/-! ## The deletion-safety theorem

Both premises are the decidable booleans the driver re-checks on the
algorithm's real output, so neither `closureFuel`'s fuel bound nor its
implementation is trusted — only this proof, and the run-time re-checks
that make its hypotheses true of the actual data. -/

theorem closedSetCatchesAll {edges : List Edge} {acc : List Node} {r n : Node}
    (hc : isClosed edges acc = true) (hr : acc.contains r = true)
    (h : Reaches edges r n) : acc.contains n = true := by
  induction h with
  | refl => exact hr
  | step _hab hmem ih =>
      rename_i b c
      have hEdge : edgeClosed acc (b, c) = true :=
        List.all_eq_true.mp hc (b, c) hmem
      have ihm : b ∈ acc := by simpa using ih
      have hc' : c ∈ acc := by simpa [edgeClosed, ihm] using hEdge
      simpa using hc'

/-- The form the driver's report uses, the contrapositive of the above:
    if every root is in a closed set that does not contain `n`, then no
    root reaches `n`. -/
theorem noRootReaches {edges : List Edge} {acc roots : List Node} {n : Node}
    (hc : isClosed edges acc = true) (hr : allMem roots acc = true)
    (hn : acc.contains n = false) :
    ∀ r ∈ roots, ¬ Reaches edges r n := by
  intro r hrMem h
  have hrAcc : acc.contains r = true := List.all_eq_true.mp hr r hrMem
  have hcn := closedSetCatchesAll hc hrAcc h
  rw [hn] at hcn
  exact Bool.noConfusion hcn

/-! ## Build-time checks

The theorems are about ALL closed supersets, so they say nothing about
whether `reachable` computes one. These check that it does on small
graphs — which is what the driver's run-time `isClosed` re-check exists
to catch when it does not. -/

def g1 : List Edge := [("a", "b"), ("b", "c"), ("d", "e")]

#guard (reachable g1 ["a"]).contains "c"
#guard (reachable g1 ["a"]).contains "b"
#guard !(reachable g1 ["a"]).contains "d"
#guard !(reachable g1 ["a"]).contains "e"
#guard isClosed g1 (reachable g1 ["a"])
#guard isClosed g1 (reachable g1 ["d"])
#guard isClosed g1 (reachable g1 [])

/-! A cycle must not stop the fixed point from being reached. -/

def g2 : List Edge := [("a", "b"), ("b", "a"), ("b", "c"), ("c", "b")]

#guard isClosed g2 (reachable g2 ["a"])
#guard (reachable g2 ["a"]).contains "c"
#guard (reachable g2 ["c"]).contains "a"

/-! An unreachable node stays out, which is the DEAD verdict the driver
    reports. -/

def g3 : List Edge := [("root", "x"), ("x", "y"), ("dead1", "dead2")]

#guard !(reachable g3 ["root"]).contains "dead1"
#guard !(reachable g3 ["root"]).contains "dead2"
#guard isClosed g3 (reachable g3 ["root"])
#guard allMem ["root"] (reachable g3 ["root"])

/-! The premises the driver re-checks are decidable and DO reject a set
    that is not closed — checked here so the re-check is known to have
    teeth rather than being assumed to. -/

#guard !isClosed g1 ["a"]
#guard !isClosed g1 ["a", "b"]
#guard isClosed g1 ["a", "b", "c"]
#guard isClosed g1 []

/-! Axiom audit — no `sorry`, no `axiom`, no `native_decide`. -/

#print axioms closedSetCatchesAll
#print axioms noRootReaches

end L4Factoidal.Dep
