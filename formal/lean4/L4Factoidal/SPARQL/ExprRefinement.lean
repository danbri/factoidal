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
private def decimalEbvSpec (s : String) : Option Bool :=
  if s.toList.contains 'e' || s.toList.contains 'E' then some false else
  match L4Factoidal.XSD.parseLexical s with
  | some (.num _ m _) => some (m != 0)
  | _ => some false

private def integerEbvSpec (dt : WfIri) (s : String) : Option Bool :=
  match parseIntString s with
  | some n => if integerValueFitsDatatype dt n then some (n != 0) else some false
  | none => some false

private def floatingEbvSpec (isFloat : Bool) (s : String) : Option Bool :=
  match L4Factoidal.XSD.parseLexical s with
  | none => some false
  | some .nan => some false
  | some (.inf _) => some true
  | some parsed@(.num _ m e) =>
      if m == 0 then some false else
      let k10 : Int := ((toString m).length : Int) - 1 + e
      let boundary : Int := if isFloat then -46 else -324
      if k10 < boundary then some false
      else if k10 > boundary then some true
      else
        let value := if isFloat then L4Factoidal.XSD.canon 24 (-126) 127 parsed
                     else L4Factoidal.XSD.canonDouble parsed
        match value.cls with
        | .zero | .nan => some false
        | .finite _ _ | .inf => some true

def ebvSpec : EvalResult → Option Bool
  | .bool b => some b
  | .num n  => some (n ≠ 0)
  | .dec s  => decimalEbvSpec s
  | .flt s  => floatingEbvSpec true s
  | .dbl s  => floatingEbvSpec false s
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
      else if isIntegerDatatype l.val.datatype then
        integerEbvSpec l.val.datatype l.val.lexicalForm
      else if l.val.datatype == xsdDecimal then decimalEbvSpec l.val.lexicalForm
      else if l.val.datatype == xsdFloat then floatingEbvSpec true l.val.lexicalForm
      else if l.val.datatype == xsdDouble then floatingEbvSpec false l.val.lexicalForm
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

theorem dateDatatype_eqs_false (dt : WfIri) (h : isDateDatatype dt = false) :
    (dt == xsdDate) = false ∧ (dt == xsdDateTime) = false := by
  constructor
  · cases hd : (dt == xsdDate) with
    | false => rfl
    | true => simp [isDateDatatype, hd] at h
  · cases hdt : (dt == xsdDateTime) with
    | false => rfl
    | true => simp [isDateDatatype, hdt] at h

/-! ### Agreement -/

theorem eq_num_matches_spec (a b : Int) :
    valueCompare (.num a) (.num b) .eq = some (eqSpecNum a b) ∧
    valueCompare (.num a) (.num b) .ne = some (!eqSpecNum a b) := by
  have hz : Scaled.cmp ⟨a, 0⟩ ⟨b, 0⟩ = intCompare a b := by
    simp [Scaled.cmp, pow10_zero]
  constructor <;>
    simp [valueCompare, valueCompareCore, numericValueCompare, numericKind?, numericCompare,
          EvalResult.toNumeric?, hz,
          promoteKind, roundScaledToKind?, applyCompOp, eqSpecNum,
          intCompare_beq_zero, bne]

theorem eq_plain_string_matches_spec (l1 l2 : WfLiteral)
    (h1 : l1.val.datatype = xsdString) (h2 : l2.val.datatype = xsdString)
    (t1 : l1.val.langTag = none) (t2 : l2.val.langTag = none)
    (d1 : l1.val.direction = none) (d2 : l2.val.direction = none) :
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .eq
        = some (eqSpecPlainString l1 l2) ∧
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .ne
        = some (!eqSpecPlainString l1 l2) := by
  have hn : isNumericDatatype xsdString = false := by decide
  have hi : isIntegerDatatype xsdString = false := by decide
  have hdec : (xsdString == xsdDecimal) = false := by decide
  have hflt : (xsdString == xsdFloat) = false := by decide
  have hdbl : (xsdString == xsdDouble) = false := by decide
  have hb : (xsdString == xsdBoolean) = false := by decide
  have hd : isDateDatatype xsdString = false := by decide
  have hp1 : literalPromote l1 = .term (.literal l1) := by
    simp [literalPromote, h1, hi, hdec, hflt, hdbl, hb]
  have hp2 : literalPromote l2 = .term (.literal l2) := by
    simp [literalPromote, h2, hi, hdec, hflt, hdbl, hb]
  have hdate1 : (xsdString == xsdDate) = false := by decide
  have hdate2 : (xsdString == xsdDateTime) = false := by decide
  have hvd1 : validDateLiteral l1 = false := by
    simp [validDateLiteral, dateKind?, h1, hdate1, hdate2]
  have hvd2 : validDateLiteral l2 = false := by
    simp [validDateLiteral, dateKind?, h2, hdate1, hdate2]
  have hm : hasSpecificEqualityMapping (.literal l1) (.literal l2) = false := by
    simp [hasSpecificEqualityMapping, validNumericLiteral, validBooleanLiteral,
          hp1, hp2, h1, h2, hb, hvd1, hvd2]
  have hs : sameTermEq (.literal l1) (.literal l2) =
      (l1.val.lexicalForm == l2.val.lexicalForm) := by
    simp [sameTermEq, h1, h2, t1, t2, d1, d2]
  constructor <;>
    simp [valueCompare, valueCompareCore, hp1, hp2, h1, h2, t1, t2,
          hm, hs, hn, hb, hd, applyCompOp, eqSpecPlainString,
          strCompare_beq_zero, bne]

/-- Same-kind decimal reflexivity. The scaled-value parse is a total
function of the lexical form, so calling it twice on one string returns
one value; no knowledge of what it computes is needed. -/
theorem eq_dec_reflexive (s : String) (h : (parseToScaled s).isSome) :
    valueCompare (.dec s) (.dec s) .eq = some true := by
  cases hp : parseToScaled s with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some v =>
      simp [valueCompare, valueCompareCore, numericValueCompare, numericKind?, numericCompare,
            EvalResult.toNumeric?, hp,
            promoteKind, roundScaledToKind?, applyCompOp, Scaled.cmp_refl]

/-- Same-kind double reflexivity whenever the lexical denotes a non-NaN
IEEE value. Signed zero and infinity are included. -/
theorem eq_dbl_reflexive (s : String) (p : L4Factoidal.XSD.Parsed)
    (hp : L4Factoidal.XSD.parseLexical s = some p)
    (hn : (L4Factoidal.XSD.canonDouble p).cls ≠ .nan) :
    valueCompare (.dbl s) (.dbl s) .eq = some true := by
  generalize hc : L4Factoidal.XSD.canonDouble p = c at hn
  cases c with
  | mk neg cls =>
      cases cls <;>
        simp_all [valueCompare, valueCompareCore, numericValueCompare, numericKind?,
          canonicalNumericAt?, canonicalNumericCompare, promoteKind, applyCompOp,
          finiteDyadicCompare, intCompare]

/-- Distinct lexical forms in one unsupported datatype have no value-space
operator mapping. Under equality they therefore produce a type error. The
hypotheses classify the datatype explicitly rather than assuming the result of
the executable comparison. -/
theorem eq_unsupported_same_datatype_diff_lexical_typeerror (l1 l2 : WfLiteral)
    (hd : l1.val.datatype = l2.val.datatype)
    (ht1 : l1.val.langTag = none) (ht2 : l2.val.langTag = none)
    (hdir1 : l1.val.direction = none) (hdir2 : l2.val.direction = none)
    (hi : isIntegerDatatype l1.val.datatype = false)
    (hdec : (l1.val.datatype == xsdDecimal) = false)
    (hflt : (l1.val.datatype == xsdFloat) = false)
    (hdbl : (l1.val.datatype == xsdDouble) = false)
    (hbool : (l1.val.datatype == xsdBoolean) = false)
    (hdate : isDateDatatype l1.val.datatype = false)
    (hstr : (l1.val.datatype == xsdString) = false)
    (hlex : l1.val.lexicalForm ≠ l2.val.lexicalForm) :
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .eq = none := by
  have hi2 : isIntegerDatatype l2.val.datatype = false := by simpa [← hd] using hi
  have hdec2 : (l2.val.datatype == xsdDecimal) = false := by simpa [← hd] using hdec
  have hflt2 : (l2.val.datatype == xsdFloat) = false := by simpa [← hd] using hflt
  have hdbl2 : (l2.val.datatype == xsdDouble) = false := by simpa [← hd] using hdbl
  have hbool2 : (l2.val.datatype == xsdBoolean) = false := by simpa [← hd] using hbool
  have hdate2 : isDateDatatype l2.val.datatype = false := by simpa [← hd] using hdate
  have hstr2 : (l2.val.datatype == xsdString) = false := by simpa [← hd] using hstr
  have hn1 : isNumericDatatype l1.val.datatype = false := by
    simp [isNumericDatatype, hi, hdec, hflt, hdbl]
  have hn2 : isNumericDatatype l2.val.datatype = false := by
    simp [isNumericDatatype, hi2, hdec2, hflt2, hdbl2]
  have hp1 : literalPromote l1 = .term (.literal l1) := by
    simp [literalPromote, hi, hdec, hflt, hdbl, hbool]
  have hp2 : literalPromote l2 = .term (.literal l2) := by
    simp [literalPromote, hi2, hdec2, hflt2, hdbl2, hbool2]
  have hvn1 : validNumericLiteral l1 = false := by simp [validNumericLiteral, hp1]
  have hvn2 : validNumericLiteral l2 = false := by simp [validNumericLiteral, hp2]
  have hvb1 : validBooleanLiteral l1 = false := by
    simp [validBooleanLiteral, hbool]
  have hvb2 : validBooleanLiteral l2 = false := by
    simp [validBooleanLiteral, hbool2]
  have hdateParts1 := dateDatatype_eqs_false l1.val.datatype hdate
  have hdateParts2 := dateDatatype_eqs_false l2.val.datatype hdate2
  have hvd1 : validDateLiteral l1 = false := by
    simp [validDateLiteral, dateKind?, hdateParts1.1, hdateParts1.2]
  have hvd2 : validDateLiteral l2 = false := by
    simp [validDateLiteral, dateKind?, hdateParts2.1, hdateParts2.2]
  have hm : hasSpecificEqualityMapping (.literal l1) (.literal l2) = false := by
    simp [hasSpecificEqualityMapping, hvn1, hvn2, hvb1, hvb2, hvd1, hvd2]
  have hs : sameTermEq (.literal l1) (.literal l2) = false := by
    have hlexb : (l1.val.lexicalForm == l2.val.lexicalForm) = false :=
      beq_eq_false_iff_ne.mpr hlex
    simp [sameTermEq, hd, ht1, ht2, hdir1, hdir2, hlexb]
  simp [valueCompare, hp1, hp2, hm, hs, valueCompareCore, ht1, ht2,
        hn1, hn2, hbool, hbool2, hdate, hdate2, hstr, hstr2]

/-- Well-formed language strings in different language-tag equivalence
classes are definitely unequal. The constructor supplies the datatype,
language tag, and direction invariants used by the operator mapping. -/
theorem eq_langString_diff_lang (s1 s2 tag1 tag2 : String)
    (ht : langTagOptionEq (some tag1) (some tag2) = false) :
    valueCompare (.term (.literal (Literal.langString s1 tag1)))
        (.term (.literal (Literal.langString s2 tag2))) .eq = some false ∧
    valueCompare (.term (.literal (Literal.langString s1 tag1)))
        (.term (.literal (Literal.langString s2 tag2))) .ne = some true := by
  let l1 := Literal.langString s1 tag1
  let l2 := Literal.langString s2 tag2
  change valueCompare (.term (.literal l1)) (.term (.literal l2)) .eq = some false ∧
    valueCompare (.term (.literal l1)) (.term (.literal l2)) .ne = some true
  have hi : isIntegerDatatype l1.val.datatype = false := by
    simpa [l1, Literal.langString] using
      (show isIntegerDatatype rdfLangString = false by decide)
  have hdec : (l1.val.datatype == xsdDecimal) = false := by
    simpa [l1, Literal.langString] using
      (show (rdfLangString == xsdDecimal) = false by decide)
  have hflt : (l1.val.datatype == xsdFloat) = false := by
    simpa [l1, Literal.langString] using
      (show (rdfLangString == xsdFloat) = false by decide)
  have hdbl : (l1.val.datatype == xsdDouble) = false := by
    simpa [l1, Literal.langString] using
      (show (rdfLangString == xsdDouble) = false by decide)
  have hbool : (l1.val.datatype == xsdBoolean) = false := by
    simpa [l1, Literal.langString] using
      (show (rdfLangString == xsdBoolean) = false by decide)
  have hdate : isDateDatatype l1.val.datatype = false := by
    simpa [l1, Literal.langString] using
      (show isDateDatatype rdfLangString = false by decide)
  have hi2 : isIntegerDatatype l2.val.datatype = false := by
    simpa [l2, Literal.langString] using
      (show isIntegerDatatype rdfLangString = false by decide)
  have hdec2 : (l2.val.datatype == xsdDecimal) = false := by
    simpa [l2, Literal.langString] using
      (show (rdfLangString == xsdDecimal) = false by decide)
  have hflt2 : (l2.val.datatype == xsdFloat) = false := by
    simpa [l2, Literal.langString] using
      (show (rdfLangString == xsdFloat) = false by decide)
  have hdbl2 : (l2.val.datatype == xsdDouble) = false := by
    simpa [l2, Literal.langString] using
      (show (rdfLangString == xsdDouble) = false by decide)
  have hbool2 : (l2.val.datatype == xsdBoolean) = false := by
    simpa [l2, Literal.langString] using
      (show (rdfLangString == xsdBoolean) = false by decide)
  have hdate2 : isDateDatatype l2.val.datatype = false := by
    simpa [l2, Literal.langString] using
      (show isDateDatatype rdfLangString = false by decide)
  have hp1 : literalPromote l1 = .term (.literal l1) := by
    simp [literalPromote, hi, hdec, hflt, hdbl, hbool]
  have hp2 : literalPromote l2 = .term (.literal l2) := by
    simp [literalPromote, hi2, hdec2, hflt2, hdbl2, hbool2]
  have hvn1 : validNumericLiteral l1 = false := by simp [validNumericLiteral, hp1]
  have hvn2 : validNumericLiteral l2 = false := by simp [validNumericLiteral, hp2]
  have hvb1 : validBooleanLiteral l1 = false := by
    simp [validBooleanLiteral, hbool]
  have hvb2 : validBooleanLiteral l2 = false := by
    simp [validBooleanLiteral, hbool2]
  have hdateParts1 := dateDatatype_eqs_false l1.val.datatype hdate
  have hdateParts2 := dateDatatype_eqs_false l2.val.datatype hdate2
  have hvd1 : validDateLiteral l1 = false := by
    simp [validDateLiteral, dateKind?, hdateParts1.1, hdateParts1.2]
  have hvd2 : validDateLiteral l2 = false := by
    simp [validDateLiteral, dateKind?, hdateParts2.1, hdateParts2.2]
  have hm : hasSpecificEqualityMapping (.literal l1) (.literal l2) = false := by
    simp [hasSpecificEqualityMapping, hvn1, hvn2, hvb1, hvb2, hvd1, hvd2]
  have htag1 : l1.val.langTag = some tag1 := by simp [l1, Literal.langString]
  have htag2 : l2.val.langTag = some tag2 := by simp [l2, Literal.langString]
  have hs : sameTermEq (.literal l1) (.literal l2) = false := by
    simp [sameTermEq, htag1, htag2, ht]
  constructor <;>
    simp [valueCompare, hp1, hp2, hm, hs, valueCompareCore,
          htag1, htag2, ht, unequalRdfTerms]


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
#print axioms eq_langString_diff_lang
#print axioms eq_unsupported_same_datatype_diff_lexical_typeerror
#print axioms eval_eq_num_matches_spec

end L4Factoidal.SPARQL.ExprRefinement
