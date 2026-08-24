/-
L4Factoidal.RDF.ListHelpers — port of `RDF.List.Helpers`.

The F* module gives tail-recursive replacements for `append`,
`concatMap` and `assoc`, with equivalence proofs against the standard
library. Its header records why: the structural recursions in
`FStar.List.Tot.Base` overflow the OCaml stack on long lists, and two
incidents paid for the module — the Turtle parser path
(<https://github.com/danbri/factoidal/issues/94>) and the BGP
filter-map path, 2026-04-26.

## What the port found

The Lean core library already ships both of the interesting two, and
the toolchain substitutes them without a call-site change:

* `List.appendTR as bs = as.reverse.reverseAux bs`, tagged with the
  `@[csimp]` lemma `List.append_eq_appendTR`.
* `List.flatMapTR`, tagged with `List.flatMap_eq_flatMapTR`.

A `@[csimp]` lemma rewrites the definition at CODE GENERATION time, so
the compiled program calls the tail-recursive version while every proof
still sees the structural one. The F* tree has no such mechanism, which
is why the same work there is a module of hand-written functions plus
hand-written equivalence lemmas, and why every call site had to be
edited to use the `_tr` names.

`appendTr_eq_core` records the sharper part: the F* accumulator
strategy and `List.appendTR` are the SAME algorithm — reverse the left
list, then `reverseAux` it onto the right. Two independent
implementations reached one function.

`concatMapTr` and `List.flatMapTR` are NOT the same algorithm. The F*
version accumulates a reversed list and reverses once at the end; the
Lean core version accumulates into an `Array`. Both are tail-recursive
and both equal `flatMap`, which is what the equivalence theorems below
state; the difference is in allocation, not in result.

## Port fidelity

The three functions are transcribed arm for arm from the F* source, so
the differential comparison is between the two trees' own definitions,
not between this file and the Lean core library. The core-library
theorems are additional checks the port buys, not substitutes for the
transcription.

`assocTr` is stated over `BEq` with `LawfulBEq` where a proof needs the
equality to be real, because Lean's `List.lookup` is `BEq`-based while
F*'s `assoc` takes an `eqtype`. The F* header says `assoc_tr` exists
for naming symmetry rather than for stack safety; that reading carries
over, since `List.lookup` is already tail-recursive.

No `sorry`, no user `axiom`, no `native_decide`.
-/

namespace L4Factoidal.RDF.ListHelpers

/-! ## 1. Tail-recursive append

Walk `xs` into a reverse accumulator, then splice `ys` on with
`reverseAux`, which is itself tail-recursive. -/

def appendAux {α : Type u} (acc xs ys : List α) : List α :=
  match xs with
  | [] => acc.reverseAux ys
  | x :: rest => appendAux (x :: acc) rest ys

def appendTr {α : Type u} (xs ys : List α) : List α :=
  appendAux [] xs ys

/-- The accumulator invariant. Stated with `acc` general so the
induction step lines up with the recursive call, exactly as the F*
proof does. -/
theorem appendAux_eq {α : Type u} (acc xs ys : List α) :
    appendAux acc xs ys = acc.reverse ++ (xs ++ ys) := by
  induction xs generalizing acc with
  | nil => simp [appendAux, List.reverseAux_eq]
  | cons x rest ih =>
      simp [appendAux, ih, List.reverse_cons, List.append_assoc]

theorem appendTr_eq {α : Type u} (xs ys : List α) :
    appendTr xs ys = xs ++ ys := by
  simp [appendTr, appendAux_eq]

/-- The two trees reached the same function. `List.appendTR` is Lean
core's compiler substitute for `List.append`; `appendTr` is the F*
tree's hand-written one. -/
theorem appendTr_eq_core {α : Type u} (xs ys : List α) :
    appendTr xs ys = List.appendTR xs ys := by
  simp [appendTr_eq, List.appendTR, List.reverseAux_eq]

/-! ## 2. Tail-recursive concatMap

Walk the outer list with an accumulator holding the reversed
concatenation so far, reversing `f x` onto it at each step, and reverse
once at the end. -/

def concatMapAux {α : Type u} {β : Type v}
    (f : α → List β) (xs : List α) (acc : List β) : List β :=
  match xs with
  | [] => acc.reverse
  | x :: rest => concatMapAux f rest ((f x).reverseAux acc)

def concatMapTr {α : Type u} {β : Type v}
    (f : α → List β) (xs : List α) : List β :=
  concatMapAux f xs []

theorem concatMapAux_eq {α : Type u} {β : Type v}
    (f : α → List β) (xs : List α) (acc : List β) :
    concatMapAux f xs acc = acc.reverse ++ xs.flatMap f := by
  induction xs generalizing acc with
  | nil => simp [concatMapAux]
  | cons x rest ih =>
      simp [concatMapAux, ih, List.reverseAux_eq, List.reverse_append,
            List.flatMap_cons, List.append_assoc]

theorem concatMapTr_eq {α : Type u} {β : Type v}
    (f : α → List β) (xs : List α) :
    concatMapTr f xs = xs.flatMap f := by
  simp [concatMapTr, concatMapAux_eq]

/-- Agreement with Lean core's tail-recursive `flatMap`, which uses a
different accumulator. The results agree; the allocation does not. -/
theorem concatMapTr_eq_core {α : Type u} {β : Type v}
    (f : α → List β) (xs : List α) :
    concatMapTr f xs = List.flatMapTR f xs := by
  rw [concatMapTr_eq, ← List.flatMap_eq_flatMapTR]

/-! ## 3. assoc

Already tail-position recursive in both trees. Kept for naming
symmetry with the other two, which is the reason the F* header gives. -/

def assocTr {α : Type u} {β : Type v} [BEq α]
    (x : α) (xs : List (α × β)) : Option β :=
  match xs with
  | [] => none
  | (k, v) :: rest => if x == k then some v else assocTr x rest

theorem assocTr_eq {α : Type u} {β : Type v} [BEq α]
    (x : α) (xs : List (α × β)) :
    assocTr x xs = xs.lookup x := by
  induction xs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      cases hx : x == k <;> simp [assocTr, List.lookup, hx, ih]

/-! ## Build-time checks -/

/-! Append: the result, and that the accumulator does not leak. -/
#guard appendTr [1, 2, 3] [4, 5] == [1, 2, 3, 4, 5]
#guard appendTr ([] : List Nat) [4, 5] == [4, 5]
#guard appendTr [1, 2, 3] ([] : List Nat) == [1, 2, 3]

/-! concatMap: order is preserved, and an empty inner list drops out. -/
#guard concatMapTr (fun n => [n, n * 10]) [1, 2, 3] == [1, 10, 2, 20, 3, 30]
#guard concatMapTr (fun n => if n == 2 then [] else [n]) [1, 2, 3] == [1, 3]
#guard concatMapTr (fun n => [n]) ([] : List Nat) == ([] : List Nat)

/-! assoc: first match wins, absent key gives `none`. -/
#guard assocTr "b" [("a", 1), ("b", 2), ("b", 3)] == some 2
#guard assocTr "z" [("a", 1), ("b", 2)] == (none : Option Nat)

/-! The two trees' append agrees with Lean core's on a real input. -/
#guard appendTr [1, 2, 3] [4, 5] == List.appendTR [1, 2, 3] [4, 5]
#guard concatMapTr (fun n => [n, n]) [1, 2] == List.flatMapTR (fun n => [n, n]) [1, 2]

/-! ## Axiom audit -/

#print axioms appendTr_eq
#print axioms appendTr_eq_core
#print axioms concatMapTr_eq
#print axioms concatMapTr_eq_core
#print axioms assocTr_eq

end L4Factoidal.RDF.ListHelpers
