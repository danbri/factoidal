/-
L4Factoidal.SPARQL.EvalLimits — the row-cap circuit breaker.

Port of `formal/fstar/SPARQL.Eval.Limits.fst` (128 lines). Recovery-plan
phase 5: it retires the `--max-rows N` breaker that lived in
`factoidal_http.ml` as an `exceeds_cap` / `result_cap_response` pair.
The rendering decision "should this oversized result become a 413?" is
glue; the policy "stop after N rows" is not.

`maxRows = 0` is the unlimited sentinel, matching the OCaml `cap <= 0`
test it replaces.

The combinator takes a materialised list because that is what the
evaluator returns today. A streaming version is a later extension, not
a difference between the trees.
-/

namespace L4Factoidal.SPARQL

structure RowCap where
  maxRows : Nat
  deriving Repr, DecidableEq, Inhabited

def noCap : RowCap := { maxRows := 0 }

def mkCap (n : Nat) : RowCap := { maxRows := n }

def RowCap.isEnabled (c : RowCap) : Bool := c.maxRows != 0

/-- The predicate the caller polls between rows. -/
def capReached (c : RowCap) (nRows : Nat) : Bool :=
  c.isEnabled && nRows ≥ c.maxRows

/-- Keep the first `c.maxRows` elements, or all of them when the cap is
    disabled. The accumulator threads how many have been kept, so no
    step recomputes `length`. -/
def takeCappedAux {α : Type} (c : RowCap) : List α → Nat → List α
  | [],      _     => []
  | x :: rest, taken =>
      if c.isEnabled && taken ≥ c.maxRows then []
      else x :: takeCappedAux c rest (taken + 1)

def takeCapped {α : Type} (c : RowCap) (rows : List α) : List α :=
  takeCappedAux c rows 0

/-! ## The two properties

The F\* module proves both. Here they are proved too, rather than
demoted to `#guard`s: `takeCappedLengthLeCap` is what makes the breaker
a breaker, and `takeCappedUnlimitedId` is what makes a disabled cap
free. -/

/-- Called at or past the cap with the cap enabled, the walk returns
    nothing. Both list shapes evaluate the guard the same way, so this
    needs no induction. -/
theorem takeCappedAux_at_cap {α : Type} (c : RowCap) (rows : List α) (taken : Nat)
    (hen : c.isEnabled = true) (hge : taken ≥ c.maxRows) :
    takeCappedAux c rows taken = [] := by
  cases rows with
  | nil => rfl
  | cons _ _ => simp [takeCappedAux, hen, hge]

/-- What the walk returns, plus what was already taken, cannot exceed
    the cap. Stated with `taken < c.maxRows` as a hypothesis rather than
    as an `if` inside the conclusion; the at-cap case is
    `takeCappedAux_at_cap` above. -/
theorem takeCappedAux_length_le {α : Type} (c : RowCap) (rows : List α) (taken : Nat)
    (hen : c.isEnabled = true) (h : taken < c.maxRows) :
    (takeCappedAux c rows taken).length + taken ≤ c.maxRows := by
  induction rows generalizing taken with
  | nil => simp [takeCappedAux]; omega
  | cons _ rest ih =>
      have hguard : ¬ (taken ≥ c.maxRows) := by omega
      simp [takeCappedAux, hen, hguard]
      by_cases h2 : taken + 1 < c.maxRows
      · have := ih (taken + 1) h2
        omega
      · have hcap : taken + 1 ≥ c.maxRows := by omega
        rw [takeCappedAux_at_cap c rest (taken + 1) hen hcap]
        simp
        omega

/-- The bound the breaker exists for. -/
theorem takeCapped_length_le_cap {α : Type} (c : RowCap) (rows : List α)
    (hen : c.isEnabled = true) : (takeCapped c rows).length ≤ c.maxRows := by
  have hpos : 0 < c.maxRows := by
    simp [RowCap.isEnabled] at hen
    omega
  have h := takeCappedAux_length_le c rows 0 hen hpos
  simpa [takeCapped] using h

/-- A disabled cap is the identity, so paying for it costs nothing. -/
theorem takeCappedAux_unlimited {α : Type} (rows : List α) (taken : Nat) :
    takeCappedAux noCap rows taken = rows := by
  induction rows generalizing taken with
  | nil => rfl
  | cons _ rest ih => simp [takeCappedAux, noCap, RowCap.isEnabled]; exact ih (taken + 1)

theorem takeCapped_unlimited_id {α : Type} (rows : List α) :
    takeCapped noCap rows = rows := takeCappedAux_unlimited rows 0

/-! ## Build-time checks

The theorems say what holds in general; these say the numbers come out
right on a concrete list, which is what a caller sees. -/

#guard takeCapped (mkCap 3) [1, 2, 3, 4, 5] == [1, 2, 3]
#guard takeCapped (mkCap 5) [1, 2, 3] == [1, 2, 3]
#guard takeCapped noCap [1, 2, 3, 4, 5] == [1, 2, 3, 4, 5]
#guard takeCapped (mkCap 1) [1, 2, 3] == [1]

/-! A cap of 0 is UNLIMITED, not "keep nothing" — the sentinel that
    would be easiest to get backwards. -/

#guard takeCapped (mkCap 0) [1, 2, 3] == [1, 2, 3]
#guard !(mkCap 0).isEnabled
#guard (mkCap 1).isEnabled

#guard !capReached noCap 1000
#guard !capReached (mkCap 3) 2
#guard capReached (mkCap 3) 3
#guard capReached (mkCap 3) 4

/-! The empty list is a fixed point under every cap. -/

#guard takeCapped (mkCap 3) ([] : List Nat) == []
#guard takeCapped noCap ([] : List Nat) == []

/-! Axiom audit. -/

#print axioms takeCapped_length_le_cap
#print axioms takeCapped_unlimited_id

end L4Factoidal.SPARQL
