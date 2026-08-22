/-
L4Factoidal.SPARQL.ExprTheorems — proved properties of the SPARQL 1.1
expression language.

The F* source states its expression properties as SMT `Lemma`s
discharged by Z3; here they are ordinary Lean theorems with explicit
tactic proofs, kernel-rechecked on every `lake build`. No `sorry`, no
user `axiom`, no `native_decide`.

Contents:
  * §17.2.2 — `ebv` on the rows of the operand-mapping table it
    decides, including the language-tagged row the F* source carries as
    a finding;
  * §17.4.1.1 — BOUND is exactly "the variable is in dom(μ)", the one
    form that never errors;
  * §17.3 — the error-tolerant / error-preserving truth tables, stated
    on `boolAnd`/`boolOr`/`boolNot` AND on the evaluator arms that use
    them (it is the second form a future edit could break);
  * the scaled-decimal order — reflexivity, the exchange law
    `cmp b a = -cmp a b` (hence antisymmetry), the cross-multiplied
    characterisation that reconciles the two scale-normalisation
    branches, and TRANSITIVITY of the strict order;
  * §17.4.1.7 — reflexivity of `=` on IRI, literal, Boolean and numeric
    values, and its NON-reflexivity on blank nodes (a fact about the
    operator mapping, not an omission);
  * §18.5 — the FILTER bridge collapses a type error to `false`.

Each theorem pins down behaviour a plausible-looking simplification
could silently change — which is the test for whether it earns its
place.
-/
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## §17.2.2 — effective boolean value -/

/-- A Boolean value's EBV is that Boolean. -/
@[simp] theorem ebv_bool (b : Bool) : ebv (.bool b) = some b := rfl

/-- A type error has no effective boolean value — it is not `false`.
This is the distinction §17.3 needs, and the one §18.5 is allowed to
forget. -/
@[simp] theorem ebv_error : ebv .error = none := rfl

/-- The numeric row of the table: zero is false, everything else true. -/
@[simp] theorem ebv_num (n : Int) : ebv (.num n) = some (decide (n ≠ 0)) := rfl

theorem ebv_num_zero : ebv (.num 0) = some false := by decide

theorem ebv_num_nonzero {n : Int} (h : n ≠ 0) : ebv (.num n) = some true := by
  simp [h]

/-- An IRI is "any other argument": a type error, never a Boolean. -/
@[simp] theorem ebv_iri (i : WfIri) : ebv (.term (.iri i)) = none := rfl

/-- A blank node is a type error too. -/
@[simp] theorem ebv_bnode (b : BNodeId) : ebv (.term (.bnode b)) = none := rfl

/-- §17.2.2's String row covers the UN-tagged case only, so a
language-tagged literal is a TYPE ERROR — not `true` because it happens
to be non-empty. -/
theorem ebv_langString (lex tag : String) :
    ebv (.term (.literal (Literal.langString lex tag))) = none := rfl

/-- A plain `xsd:string` literal, by contrast, does have an EBV. -/
theorem ebv_string (lex : String) :
    ebv (.term (.literal (Literal.string lex))) = some (decide (lex.length > 0)) := rfl

/-! ## §17.4.1.1 — BOUND -/

/-- BOUND(?v) reports exactly whether `?v` is in the domain of the
solution mapping. -/
@[simp] theorem eval_bound (mu : Binding) (v : VarName) :
    (Expr.bound v).eval mu = .bool (mu.lookup v).isSome := by
  simp [Expr.eval, Expr.evalIn]

/-- BOUND(?v) is `true` precisely when the lookup succeeds. -/
theorem eval_bound_true_iff (mu : Binding) (v : VarName) :
    (Expr.bound v).eval mu = .bool true ↔ (mu.lookup v).isSome := by
  simp

/-- BOUND never produces a type error — the only §17 form of which that
is true, because it inspects the DOMAIN rather than a value. -/
theorem eval_bound_ne_error (mu : Binding) (v : VarName) :
    (Expr.bound v).eval mu ≠ .error := by
  simp

/-- An unbound variable used as a VALUE, by contrast, is a type error. -/
theorem eval_var_unbound (mu : Binding) (v : VarName)
    (h : mu.lookup v = none) : (Expr.var v).eval mu = .error := by
  simp [Expr.eval, Expr.evalIn, h]

/-! ## §17.3 — the connective truth tables -/

@[simp] theorem boolAnd_false_left (b : Option Bool) :
    boolAnd (some false) b = some false := by
  cases b with
  | none => rfl
  | some x => cases x <;> rfl

@[simp] theorem boolAnd_false_right (a : Option Bool) :
    boolAnd a (some false) = some false := by
  cases a with
  | none => rfl
  | some x => cases x <;> rfl

/-- Error-TOLERANT: a determinate `false` beats a type error. -/
theorem boolAnd_false_error : boolAnd (some false) none = some false := rfl

/-- Error-PRESERVING: `true && error` stays an error rather than
collapsing to a Boolean. -/
theorem boolAnd_true_error : boolAnd (some true) none = none := rfl

theorem boolAnd_error_error : boolAnd none none = none := rfl

@[simp] theorem boolOr_true_left (b : Option Bool) :
    boolOr (some true) b = some true := by
  cases b with
  | none => rfl
  | some x => cases x <;> rfl

@[simp] theorem boolOr_true_right (a : Option Bool) :
    boolOr a (some true) = some true := by
  cases a with
  | none => rfl
  | some x => cases x <;> rfl

theorem boolOr_true_error : boolOr (some true) none = some true := rfl
theorem boolOr_false_error : boolOr (some false) none = none := rfl

@[simp] theorem boolNot_error : boolNot none = none := rfl
@[simp] theorem boolNot_some (b : Bool) : boolNot (some b) = some (!b) := rfl

/-- The evaluator arm honours the table: a sub-expression with a
determinate `false` makes `&&` false whatever the other side does —
including when the other side is a type error. -/
theorem eval_and_false_left (env : EvalEnv) (mu : Binding) (e1 e2 : Expr)
    (h : ebv (Expr.evalIn env mu e1) = some false) :
    Expr.evalIn env mu (.and e1 e2) = .bool false := by
  simp [Expr.evalIn, h]

theorem eval_and_false_right (env : EvalEnv) (mu : Binding) (e1 e2 : Expr)
    (h : ebv (Expr.evalIn env mu e2) = some false) :
    Expr.evalIn env mu (.and e1 e2) = .bool false := by
  simp [Expr.evalIn, h]

/-- ...and a `true` beside a type error does NOT collapse: the error
propagates. -/
theorem eval_and_true_error (env : EvalEnv) (mu : Binding) (e1 e2 : Expr)
    (h1 : ebv (Expr.evalIn env mu e1) = some true)
    (h2 : ebv (Expr.evalIn env mu e2) = none) :
    Expr.evalIn env mu (.and e1 e2) = .error := by
  simp [Expr.evalIn, h1, h2, boolAnd]

theorem eval_or_true_left (env : EvalEnv) (mu : Binding) (e1 e2 : Expr)
    (h : ebv (Expr.evalIn env mu e1) = some true) :
    Expr.evalIn env mu (.or e1 e2) = .bool true := by
  simp [Expr.evalIn, h]

theorem eval_or_false_error (env : EvalEnv) (mu : Binding) (e1 e2 : Expr)
    (h1 : ebv (Expr.evalIn env mu e1) = some false)
    (h2 : ebv (Expr.evalIn env mu e2) = none) :
    Expr.evalIn env mu (.or e1 e2) = .error := by
  simp [Expr.evalIn, h1, h2, boolOr]

/-- NOT of a type error is a type error. -/
theorem eval_not_error (env : EvalEnv) (mu : Binding) (e : Expr)
    (h : ebv (Expr.evalIn env mu e) = none) :
    Expr.evalIn env mu (.not e) = .error := by
  simp [Expr.evalIn, h]

/-! ## Integer groundwork for the numeric order

Core Lean has no `ring` tactic and no ordered-ring API, so the two
multiplication facts the order proofs need are established here from
`Int.mul_pos` / `Int.mul_nonneg` and `omega`. -/

theorem int_mul_lt_mul_right {a b k : Int} (h : a < b) (hk : 0 < k) :
    a * k < b * k := by
  have hpos : 0 < (b - a) * k := Int.mul_pos (by omega) hk
  have hexp : (b - a) * k = b * k - a * k := by simp [Int.sub_mul]
  omega

theorem int_mul_le_mul_right {a b k : Int} (h : a ≤ b) (hk : 0 ≤ k) :
    a * k ≤ b * k := by
  have hpos : 0 ≤ (b - a) * k := Int.mul_nonneg (by omega) hk
  have hexp : (b - a) * k = b * k - a * k := by simp [Int.sub_mul]
  omega

/-- `x * p * q = x * q * p` — the one rearrangement the order proofs
need, spelled out because core Lean has no `ring`. -/
theorem int_mul_swap_right (x p q : Int) : x * p * q = x * q * p := by
  rw [Int.mul_assoc, Int.mul_comm p q, ← Int.mul_assoc]

/-! ## The scaled-decimal order — SPARQL 1.1 §17.1

`Scaled.cmp` decides the order of two exact decimal values. An
inconsistent order here silently reorders ORDER BY and changes which
rows a range FILTER keeps, so the laws below are worth their proofs. -/

theorem pow10_pos (n : Nat) : 0 < pow10 n := by
  induction n with
  | zero => decide
  | succ k ih =>
      simp only [pow10]
      exact Int.mul_pos (by decide) ih

@[simp] theorem pow10_zero : pow10 0 = 1 := rfl

/-- `10 ^ (a + b) = 10 ^ a * 10 ^ b`. -/
theorem pow10_add (a b : Nat) : pow10 (a + b) = pow10 a * pow10 b := by
  induction a with
  | zero => simp [pow10]
  | succ k ih =>
      have h : k + 1 + b = (k + b) + 1 := by omega
      rw [h]
      simp only [pow10]
      rw [ih, Int.mul_assoc]

@[simp] theorem intCompare_self (a : Int) : intCompare a a = 0 := by
  unfold intCompare
  have h : ¬ (a < a) := by omega
  simp [h]

/-- The three-way comparison exchanges under swapping. -/
theorem intCompare_swap (a b : Int) : intCompare b a = -intCompare a b := by
  unfold intCompare
  by_cases h1 : a < b
  · have h2 : ¬ (b < a) := by omega
    have h3 : ¬ (b = a) := by omega
    simp [h1, h2, h3]
  · by_cases h2 : a = b
    · subst h2; simp
    · have h3 : b < a := by omega
      simp [h1, h2, h3]

/-- Multiplying both sides by a POSITIVE factor does not change the
comparison. This is what lets the two branches of `Scaled.cmp`'s
scale-normalisation be reconciled. -/
theorem intCompare_mul_pos (a b k : Int) (hk : 0 < k) :
    intCompare (a * k) (b * k) = intCompare a b := by
  have hlt : a * k < b * k ↔ a < b := by
    constructor
    · intro h
      by_cases hc : a < b
      · exact hc
      · have : b * k ≤ a * k :=
          int_mul_le_mul_right (by omega) (by omega)
        omega
    · intro h; exact int_mul_lt_mul_right h hk
  have heq : a * k = b * k ↔ a = b := by
    constructor
    · intro h
      by_cases hc : a = b
      · exact hc
      · have hsplit : a < b ∨ b < a := by omega
        cases hsplit with
        | inl h' => have := int_mul_lt_mul_right h' hk; omega
        | inr h' => have := int_mul_lt_mul_right h' hk; omega
    · intro h; rw [h]
  unfold intCompare
  by_cases h1 : a < b
  · simp [h1, hlt.mpr h1]
  · by_cases h2 : a = b
    · subst h2; simp
    · have hnl : ¬ (a * k < b * k) := fun hc => h1 (hlt.mp hc)
      have hne : ¬ (a * k = b * k) := fun hc => h2 (heq.mp hc)
      simp [h1, h2, hnl, hne]

/-- The cross-multiplied characterisation of the scaled order: `a` and
`b` compare exactly as `a.mantissa · 10^b.scale` compares with
`b.mantissa · 10^a.scale`. Both branches of `Scaled.cmp` reduce to this
one expression. -/
theorem Scaled.cmp_cross (a b : Scaled) :
    a.cmp b = intCompare (a.mantissa * pow10 b.scale) (b.mantissa * pow10 a.scale) := by
  unfold Scaled.cmp
  by_cases h : a.scale ≥ b.scale
  · rw [if_pos h]
    have hs : a.scale - b.scale + b.scale = a.scale := by omega
    have key : b.mantissa * pow10 (a.scale - b.scale) * pow10 b.scale
             = b.mantissa * pow10 a.scale := by
      rw [Int.mul_assoc, ← pow10_add, hs]
    rw [← intCompare_mul_pos a.mantissa (b.mantissa * pow10 (a.scale - b.scale))
      (pow10 b.scale) (pow10_pos _), key]
  · rw [if_neg h]
    have hs : b.scale - a.scale + a.scale = b.scale := by omega
    have key : a.mantissa * pow10 (b.scale - a.scale) * pow10 a.scale
             = a.mantissa * pow10 b.scale := by
      rw [Int.mul_assoc, ← pow10_add, hs]
    rw [← intCompare_mul_pos (a.mantissa * pow10 (b.scale - a.scale)) b.mantissa
      (pow10 a.scale) (pow10_pos _), key]

/-- The order is reflexive: every value compares equal to itself. -/
@[simp] theorem Scaled.cmp_refl (a : Scaled) : a.cmp a = 0 := by
  rw [Scaled.cmp_cross]; simp

/-- The order exchanges: comparing the other way negates the result.
With reflexivity this gives antisymmetry. -/
theorem Scaled.cmp_swap (a b : Scaled) : b.cmp a = -a.cmp b := by
  rw [Scaled.cmp_cross, Scaled.cmp_cross, intCompare_swap]

/-- Antisymmetry: `a` compares equal to `b` exactly when `b` compares
equal to `a`. -/
theorem Scaled.cmp_eq_zero_symm {a b : Scaled} (h : a.cmp b = 0) : b.cmp a = 0 := by
  rw [Scaled.cmp_swap, h]; rfl

/-- `a < b` in the scaled model, spelled through the cross product. -/
theorem Scaled.cmp_neg_iff (a b : Scaled) :
    a.cmp b < 0 ↔ a.mantissa * pow10 b.scale < b.mantissa * pow10 a.scale := by
  rw [Scaled.cmp_cross]
  unfold intCompare
  by_cases h : a.mantissa * pow10 b.scale < b.mantissa * pow10 a.scale
  · simp [h]
  · by_cases h2 : a.mantissa * pow10 b.scale = b.mantissa * pow10 a.scale <;>
      simp [h, h2]

/-- TRANSITIVITY of the strict order. From `a·10^sb < b·10^sa` and
`b·10^sc < c·10^sb`, scaling the first by `10^sc` and the second by
`10^sa` chains them through a common middle term; cancelling the
positive factor `10^sb` gives the result. -/
theorem Scaled.cmp_trans {a b c : Scaled}
    (h1 : a.cmp b < 0) (h2 : b.cmp c < 0) : a.cmp c < 0 := by
  rw [Scaled.cmp_neg_iff] at h1 h2 ⊢
  have pa : (0 : Int) < pow10 a.scale := pow10_pos _
  have pb : (0 : Int) < pow10 b.scale := pow10_pos _
  have pc : (0 : Int) < pow10 c.scale := pow10_pos _
  have s1 : a.mantissa * pow10 b.scale * pow10 c.scale
          < b.mantissa * pow10 a.scale * pow10 c.scale :=
    int_mul_lt_mul_right h1 pc
  have s2 : b.mantissa * pow10 c.scale * pow10 a.scale
          < c.mantissa * pow10 b.scale * pow10 a.scale :=
    int_mul_lt_mul_right h2 pa
  have hmid : b.mantissa * pow10 a.scale * pow10 c.scale
            = b.mantissa * pow10 c.scale * pow10 a.scale :=
    int_mul_swap_right _ _ _
  have chain : a.mantissa * pow10 b.scale * pow10 c.scale
             < c.mantissa * pow10 b.scale * pow10 a.scale := by omega
  have hl : a.mantissa * pow10 b.scale * pow10 c.scale
          = a.mantissa * pow10 c.scale * pow10 b.scale :=
    int_mul_swap_right _ _ _
  have hr : c.mantissa * pow10 b.scale * pow10 a.scale
          = c.mantissa * pow10 a.scale * pow10 b.scale :=
    int_mul_swap_right _ _ _
  rw [hl, hr] at chain
  by_cases hc : a.mantissa * pow10 c.scale < c.mantissa * pow10 a.scale
  · exact hc
  · exfalso
    have hge : c.mantissa * pow10 a.scale ≤ a.mantissa * pow10 c.scale := by omega
    have := int_mul_le_mul_right hge (by omega : (0:Int) ≤ pow10 b.scale)
    omega

/-! ## §17.4.1.7 — reflexivity of `=`

`=` is reflexive on the term kinds its operator mapping covers. It is
NOT reflexive on blank nodes: §17.4.1.7 gives no `op:` mapping for
them, so `?b = ?b` on a blank node is a type error. That is the
specification, and pinning it down here stops a future "obvious"
catch-all arm from quietly changing FILTER results. -/

theorem listCharCompare_refl (cs : List Char) : listCharCompare cs cs = 0 := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [listCharCompare, ih]

@[simp] theorem strCompare_refl (s : String) : strCompare s s = 0 := by
  simp [strCompare, listCharCompare_refl]

/-- `=` holds between an IRI term and itself. -/
theorem valueCompare_eq_refl_iri (i : WfIri) :
    valueCompare (.term (.iri i)) (.term (.iri i)) .eq = some true := by
  simp [valueCompare, applyCompOp]

/-- `=` holds between a literal term and itself, whatever its datatype
and language tag. -/
theorem valueCompare_eq_refl_literal (l : WfLiteral) :
    valueCompare (.term (.literal l)) (.term (.literal l)) .eq = some true := by
  simp [valueCompare, applyCompOp]

/-- `=` holds between a Boolean value and itself. -/
theorem valueCompare_eq_refl_bool (b : Bool) :
    valueCompare (.bool b) (.bool b) .eq = some true := by
  cases b <;> simp [valueCompare, applyCompOp]

/-- `=` holds between an integer value and itself. -/
theorem valueCompare_eq_refl_num (n : Int) :
    valueCompare (.num n) (.num n) .eq = some true := by
  simp [valueCompare, numericCompare, EvalResult.toNumeric?, applyCompOp]

/-- A blank node has no `op:` mapping under `=`, so comparing one with
ITSELF is a type error. Not an omission — §17.4.1.7's operator table
does not cover blank nodes, which is why SPARQL has `sameTerm`. -/
theorem valueCompare_eq_bnode_error (b : BNodeId) :
    valueCompare (.term (.bnode b)) (.term (.bnode b)) .eq = none := rfl

/-- `sameTerm`, by contrast, IS reflexive on every RDF term — it is
term identity, and `Term.eqb` is proved reflexive in `RDF.Core`. -/
theorem eval_sameTerm_refl (env : EvalEnv) (mu : Binding) (l : WfLiteral) :
    Expr.evalIn env mu (.sameTerm (.lit l) (.lit l)) = .bool true := by
  simp [Expr.evalIn]

/-! ## §18.5 — the FILTER bridge -/

/-- FILTER keeps a row exactly when the expression's EBV is `true`; a
type error and a definite `false` both drop it. -/
@[simp] theorem toCond_eq (e : Expr) (mu : Binding) :
    e.toCond mu = (ebv (e.eval mu)).getD false := rfl

/-- A type error drops the row. -/
theorem toCond_error (e : Expr) (mu : Binding)
    (h : ebv (e.eval mu) = none) : e.toCond mu = false := by
  simp [h]

/-- BOUND(?v) as a filter keeps exactly the rows that bind `?v` — the
smallest end-to-end statement joining §17.4.1.1 to §18.5. -/
theorem toCond_bound (v : VarName) (mu : Binding) :
    (Expr.bound v).toCond mu = (mu.lookup v).isSome := by
  simp

/-! ## Axiom audit

`#print axioms` lists everything a proof depends on. The acceptable
base is exactly Lean's own foundations — `propext`, `Classical.choice`,
`Quot.sound` — with no `sorryAx` and nothing declared in this project.
The lines below put that in every build log. -/

#print axioms ebv_langString
#print axioms eval_bound
#print axioms eval_and_false_left
#print axioms eval_and_true_error
#print axioms Scaled.cmp_refl
#print axioms Scaled.cmp_swap
#print axioms Scaled.cmp_trans
#print axioms valueCompare_eq_refl_literal
#print axioms valueCompare_eq_bnode_error
#print axioms toCond_bound

end L4Factoidal.SPARQL
