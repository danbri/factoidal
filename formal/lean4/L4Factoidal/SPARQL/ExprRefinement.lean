/-
L4Factoidal.SPARQL.ExprRefinement — port of `SPARQL11.Expression.Refinement`.

The F* module does one thing per operator: it writes an INDEPENDENT
transcription of the W3C table, then proves the engine's arm equal to
it. `L4Factoidal.SPARQL.ExprTheorems` states row facts about the engine
directly; it does not carry a second transcription, so it does not do
this module's job. The two are complementary and both are kept.

Scope, same as the F* source:
  * §17.2.2 — `ebvSpec`, a transcription of the effective-boolean-value
    operand-mapping table, and its agreement with the engine's `ebv`
    and with the `ebvOrFalse` fold that FILTER uses;
  * §17.3 — `specAnd`/`specOr`/`specNot`, the error-tolerant and
    error-preserving truth tables, their agreement with the engine's
    `boolAnd`/`boolOr`/`boolNot`, and UNCONDITIONAL statements of what
    the `.and`/`.or`/`.not` arms of `Expr.evalIn` compute;
  * §17.4.1.7 — `eqSpecNum` and `eqSpecPlainString` for the same-kind
    integer and plain-string classes, their agreement with
    `valueCompare`, and the two documented type-error / definite-false
    rows for literals.

F* issue #365 recorded two divergences here (a language-tagged literal
read as truthy, and the connectives folding an error to a definite
Boolean) and then aligned the engine. The Lean port was made from the
aligned engine, so every agreement below holds with no carve-out; the
`ebvSpec_langString` and `eval_and_true_error_agrees` theorems pin the
two former divergence witnesses so a later edit cannot reopen them.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.Expr
import L4Factoidal.SPARQL.ExprTheorems

namespace L4Factoidal.SPARQL.ExprRefinement

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## §17.2.2 — an independent transcription of the EBV table

Written from the specification text, over the vocabulary constants,
without reading the engine's `ebv` match arms. `none` is the table's
"type error" row. The String row is the un-language-tagged case only,
so `rdf:langString` and `rdf:dirLangString` fall to "any other
argument". -/
def ebvSpec : EvalResult → Option Bool
  | .bool b => some b
  | .num n  => some (n ≠ 0)
  | .dec s  => some (s ≠ "0" && s ≠ "0.0" && s ≠ "")
  | .dbl s  => some (s ≠ "0" && s ≠ "0.0" && s ≠ "NaN" && s ≠ "")
  | .term (.literal l) =>
      if l.val.datatype == xsdBoolean then
        -- SPARQL 1.2 §17.2: valid boolean lexical forms only
        -- (XSD 1.1 §3.3.2). SPARQL 1.1 additionally sent an
        -- ill-formed boolean to `false`; 1.2 removed that row, so it
        -- falls to "any other argument" — a type error.
        match l.val.lexicalForm with
        | "true" | "1" => some true
        | "false" | "0" => some false
        | _ => none
      else if l.val.datatype == xsdString then
        some (l.val.lexicalForm.length > 0)
      else if isNumericDatatype l.val.datatype then
        some (l.val.lexicalForm ≠ "0" && l.val.lexicalForm ≠ "0.0" &&
              l.val.lexicalForm ≠ "")
      else none
  | .term (.iri _) => none
  | .term (.bnode _) => none
  | .term (.tripleTerm _ _ _) => none
  | .error => none

/-- AGREEMENT: the engine computes the transcribed table, for every
argument, with no fragment excluded. -/
theorem ebvSpec_agrees (v : EvalResult) : ebvSpec v = ebv v := by
  cases v with
  | term t => cases t <;> rfl
  | _ => rfl

/-- AGREEMENT, determinate rows: where the table gives a Boolean, the
FILTER fold gives that Boolean. -/
theorem ebvOrFalse_of_spec_some {v : EvalResult} {b : Bool}
    (h : ebvSpec v = some b) : ebvOrFalse v = b := by
  simp [ebvOrFalse, ← ebvSpec_agrees, h]

/-- AGREEMENT, type-error rows: every type-error class the table names
folds to `false` at a FILTER, so the "drops the row" behaviour is
uniform across those classes with no exception to name. -/
theorem ebvOrFalse_of_spec_none {v : EvalResult}
    (h : ebvSpec v = none) : ebvOrFalse v = false := by
  simp [ebvOrFalse, ← ebvSpec_agrees, h]

/-- The first of the two F* issue #365 divergence witnesses, pinned. A
non-empty language-tagged literal is a type error under the table, the
engine agrees, and the FILTER fold reports `false`. -/
theorem ebvSpec_langString (lex tag : String) :
    ebvSpec (.term (.literal (Literal.langString lex tag))) = none ∧
    ebv (.term (.literal (Literal.langString lex tag))) = none ∧
    ebvOrFalse (.term (.literal (Literal.langString lex tag))) = false :=
  ⟨rfl, rfl, rfl⟩

/-- A plain `xsd:string` literal does have an effective Boolean value:
the String row of the table is reached only without a tag. -/
theorem ebvSpec_string (lex : String) :
    ebvSpec (.term (.literal (Literal.string lex))) = some (decide (lex.length > 0)) := rfl

/-! ## §17.3 — an independent transcription of the connective tables

logical-and: a determinate `false` on either side dominates; two
determinate `true`s give `true`; every remaining row is an error.
logical-or is the dual with `true` dominating. fn:not carries an error
argument through to an error result. -/

def specAnd : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

def specOr : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

def specNot : Option Bool → Option Bool
  | some b => some (!b)
  | none => none

theorem specAnd_agrees (a b : Option Bool) : specAnd a b = boolAnd a b := by
  cases a <;> cases b <;> rfl

theorem specOr_agrees (a b : Option Bool) : specOr a b = boolOr a b := by
  cases a <;> cases b <;> rfl

theorem specNot_agrees (a : Option Bool) : specNot a = boolNot a := by
  cases a <;> rfl

/-! ### What the evaluator arms compute

These are unconditional: no hypothesis about the operands, so no row of
the table can be lost by a hypothesis that never holds. -/

theorem eval_and_matches_spec (env : EvalEnv) (mu : Binding) (e1 e2 : Expr) :
    Expr.evalIn env mu (.and e1 e2) =
      (match specAnd (ebvSpec (Expr.evalIn env mu e1))
                     (ebvSpec (Expr.evalIn env mu e2)) with
       | some b => .bool b
       | none => .error) := by
  simp only [Expr.evalIn, ebvSpec_agrees, specAnd_agrees]
  rfl

theorem eval_or_matches_spec (env : EvalEnv) (mu : Binding) (e1 e2 : Expr) :
    Expr.evalIn env mu (.or e1 e2) =
      (match specOr (ebvSpec (Expr.evalIn env mu e1))
                    (ebvSpec (Expr.evalIn env mu e2)) with
       | some b => .bool b
       | none => .error) := by
  simp only [Expr.evalIn, ebvSpec_agrees, specOr_agrees]
  rfl

theorem eval_not_matches_spec (env : EvalEnv) (mu : Binding) (e1 : Expr) :
    Expr.evalIn env mu (.not e1) =
      (match specNot (ebvSpec (Expr.evalIn env mu e1)) with
       | some b => .bool b
       | none => .error) := by
  simp only [Expr.evalIn, ebvSpec_agrees, specNot_agrees]
  rfl

/-- The second F* issue #365 divergence witness, pinned: `true AND
error` is an error, and the engine signals it rather than folding it to
a definite Boolean. The second operand is a bare IRI, a type-error EBV
class. -/
theorem eval_and_true_error_agrees (env : EvalEnv) (mu : Binding) (i : WfIri) :
    ebvSpec (Expr.evalIn env mu (.iri i)) = none ∧
    specAnd (some true) (ebvSpec (Expr.evalIn env mu (.iri i))) = none ∧
    Expr.evalIn env mu (.and (.boolLit true) (.iri i)) = .error :=
  ⟨rfl, rfl, rfl⟩

/-- `false OR error` is an error, by the same reading of the table. -/
theorem eval_or_false_error_agrees (env : EvalEnv) (mu : Binding) (i : WfIri) :
    ebvSpec (Expr.evalIn env mu (.iri i)) = none ∧
    specOr (some false) (ebvSpec (Expr.evalIn env mu (.iri i))) = none ∧
    Expr.evalIn env mu (.or (.boolLit false) (.iri i)) = .error :=
  ⟨rfl, rfl, rfl⟩

/-- `fn:not` of an error is an error, not `true`. -/
theorem eval_not_error_agrees (env : EvalEnv) (mu : Binding) (i : WfIri) :
    ebvSpec (Expr.evalIn env mu (.iri i)) = none ∧
    specNot (ebvSpec (Expr.evalIn env mu (.iri i))) = none ∧
    Expr.evalIn env mu (.not (.iri i)) = .error :=
  ⟨rfl, rfl, rfl⟩

/-! ## §17.4.1.7 — the value-comparison path

Two same-kind classes get an independent spec here: `op:numeric-equal`
on two `xsd:integer`-denoting operands, and `op:equal` on two plain
(un-language-tagged) `xsd:string` literals. General cross-lexical value
equality over decimals and doubles needs a spec for the scaled-value
parse and is not stated here; the two reflexivity theorems below need
no such spec, because the parse is a total function of the lexical form
and is applied to the same string twice. -/

/-- `op:numeric-equal` on two integer-denoting operands: mathematical
integer equality. -/
def eqSpecNum (a b : Int) : Bool := a == b

/-- `op:equal` on two plain `xsd:string` literals: the same codepoint
sequence. -/
def eqSpecPlainString (l1 l2 : WfLiteral) : Bool :=
  l1.val.lexicalForm == l2.val.lexicalForm

/-! ### Groundwork: the three-way comparison is zero exactly on equals -/

theorem intCompare_eq_zero_iff (a b : Int) : intCompare a b = 0 ↔ a = b := by
  unfold intCompare
  constructor
  · intro h
    split at h
    · omega
    · next hne => split at h <;> omega
  · intro h; subst h; simp

theorem listCharCompare_eq_zero_iff (cs ds : List Char) :
    listCharCompare cs ds = 0 ↔ cs = ds := by
  induction cs generalizing ds with
  | nil => cases ds <;> simp [listCharCompare]
  | cons a as ih =>
      cases ds with
      | nil => simp [listCharCompare]
      | cons b bs =>
          simp only [listCharCompare]
          by_cases hc : intCompare (a.toNat : Int) (b.toNat : Int) = 0
          · have hn : a.toNat = b.toNat :=
              Int.ofNat.inj ((intCompare_eq_zero_iff (a.toNat : Int) (b.toNat : Int)).mp hc)
            have hab : a = b := Char.ext (UInt32.toNat.inj hn)
            subst hab
            simp [ih]
          · simp only [hc, beq_iff_eq]
            constructor
            · intro h; exact absurd h hc
            · intro h
              cases h
              exact absurd (((intCompare_eq_zero_iff _ _).mpr rfl)) hc

/-- The Boolean form the operator mapping actually uses. -/
theorem intCompare_beq_zero (a b : Int) : (intCompare a b == 0) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact intCompare_eq_zero_iff a b

theorem strCompare_eq_zero_iff (a b : String) : strCompare a b = 0 ↔ a = b := by
  unfold strCompare
  rw [listCharCompare_eq_zero_iff]
  constructor
  · intro h
    have : String.ofList a.toList = String.ofList b.toList := by rw [h]
    rwa [String.ofList_toList, String.ofList_toList] at this
  · intro h; rw [h]

theorem strCompare_beq_zero (a b : String) : (strCompare a b == 0) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact strCompare_eq_zero_iff a b

/-! ### Agreement -/

theorem eq_num_matches_spec (a b : Int) :
    valueCompare (.num a) (.num b) .eq = some (eqSpecNum a b) ∧
    valueCompare (.num a) (.num b) .ne = some (!eqSpecNum a b) := by
  have hz : Scaled.cmp ⟨a, 0⟩ ⟨b, 0⟩ = intCompare a b := by
    simp [Scaled.cmp, pow10_zero]
  constructor <;>
    simp [valueCompare, numericCompare, EvalResult.toNumeric?, hz,
          applyCompOp, eqSpecNum, intCompare_beq_zero, bne]

theorem eq_plain_string_matches_spec (l1 l2 : WfLiteral)
    (h1 : l1.val.datatype = xsdString) (h2 : l2.val.datatype = xsdString)
    (t1 : l1.val.langTag = none) (t2 : l2.val.langTag = none) :
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .eq
        = some (eqSpecPlainString l1 l2) ∧
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .ne
        = some (!eqSpecPlainString l1 l2) := by
  constructor <;>
    simp [valueCompare, h1, h2, t1, t2, applyCompOp, eqSpecPlainString,
          strCompare_beq_zero, bne]

/-- Same-kind decimal reflexivity. The scaled-value parse is a total
function of the lexical form, so calling it twice on one string returns
one value; no knowledge of what it computes is needed. -/
theorem eq_dec_reflexive (s : String) (h : (parseToScaled s).isSome) :
    valueCompare (.dec s) (.dec s) .eq = some true := by
  cases hp : parseToScaled s with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some v =>
      simp [valueCompare, numericCompare, EvalResult.toNumeric?, hp,
            applyCompOp, Scaled.cmp_refl]

theorem eq_dbl_reflexive (s : String) (h : (parseDoubleToScaled s).isSome) :
    valueCompare (.dbl s) (.dbl s) .eq = some true := by
  cases hp : parseDoubleToScaled s with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some v =>
      simp [valueCompare, numericCompare, EvalResult.toNumeric?, hp,
            applyCompOp, Scaled.cmp_refl]

/-- Two literals of DIFFERENT datatypes are a type error under `=`, not
a `false`. This is what keeps `=` open-world on datatypes the engine
does not know. -/
theorem eq_literal_different_datatype_typeerror (l1 l2 : WfLiteral)
    (h : l1.val.datatype ≠ l2.val.datatype) :
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .eq = none := by
  have hne : (l1.val.datatype == l2.val.datatype) = false :=
    beq_eq_false_iff_ne.mpr h
  simp [valueCompare, hne]

/-- Two literals of the SAME datatype whose language tags are in DIFFERENT
SPARQL language-tag equivalence classes are unequal — a definite `false`, not
a type error.  This deliberately uses `langTagOptionEq` rather than structural
`Option String` inequality: language tags compare case-insensitively. -/
theorem eq_literal_same_datatype_diff_lang (l1 l2 : WfLiteral)
    (hd : l1.val.datatype = l2.val.datatype)
    (ht : langTagOptionEq l1.val.langTag l2.val.langTag = false) :
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .eq = some false ∧
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .ne = some true := by
  constructor <;> simp [valueCompare, hd, ht]

/-- The expression-level corollary: the `.compare .eq` arm over two
integer-denoting sub-expressions computes the transcribed spec. -/
theorem eval_eq_num_matches_spec (env : EvalEnv) (mu : Binding)
    (e1 e2 : Expr) (a b : Int)
    (h1 : Expr.evalIn env mu e1 = .num a)
    (h2 : Expr.evalIn env mu e2 = .num b) :
    Expr.evalIn env mu (.compare .eq e1 e2) = .bool (eqSpecNum a b) := by
  simp only [Expr.evalIn, h1, h2, (eq_num_matches_spec a b).1]

/-! ## Build-time checks -/

#guard ebvSpec (.num 0) == some false
#guard ebvSpec (.num 7) == some true
#guard ebvSpec (.term (.literal (Literal.langString "yes" "en"))) == none
#guard specAnd (some true) none == none
#guard specAnd (some false) none == some false
#guard specOr (some false) none == none
#guard specNot none == none
#guard eqSpecNum 3 3 == true
#guard eqSpecPlainString (Literal.string "a") (Literal.string "a") == true

/-! ## Axiom audit -/

#print axioms ebvSpec_agrees
#print axioms ebvOrFalse_of_spec_none
#print axioms eval_and_matches_spec
#print axioms eval_and_true_error_agrees
#print axioms strCompare_beq_zero
#print axioms eq_num_matches_spec
#print axioms eq_plain_string_matches_spec
#print axioms eq_literal_same_datatype_diff_lang
#print axioms eval_eq_num_matches_spec

end L4Factoidal.SPARQL.ExprRefinement
