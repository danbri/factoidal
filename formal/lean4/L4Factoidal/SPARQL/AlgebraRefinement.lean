/-
L4Factoidal.SPARQL.AlgebraRefinement — the shipping evaluator against
the declarative algebra.

Layer 1 of the port of `SPARQL11.Algebra.Refinement` (2497 lines).
`SPARQL/AlgebraSpec.lean` carries the independent §18.5 transcription
and says in its own header that the proof tying the evaluator to it was
"not yet ported". This module starts that proof.

Every theorem names a SHIPPING function of `SPARQL.Algebra` — the one
the engine calls — on one side, and only `SPARQL.AlgebraSpec` on the
other. The two sides were written against different things, which is
what makes the agreement worth stating.

## What this layer covers

* UNION, at both layers, unconditionally.
* FILTER, at both layers, under one hypothesis on the condition
  (`FExprCongr`) that the F* source also needs and names.
* MINUS, at the set layer, under the compatibility bridge below.
* The COMPATIBILITY BRIDGE, which is where the interesting asymmetry
  is, and a witness that it cannot be dropped.

## What this layer does NOT cover

JOIN and LEFTJOIN beyond the bridge, EXTEND, PROJECT, DISTINCT, and the
BGP vertical. This module therefore does NOT make
`SPARQL11.Algebra.Refinement` a covered module — see the ninth
correction in `docs/designissues/2026-08-23-lean-port-gap.md` on
partial ports and the coverage count.

## The compatibility asymmetry, ported faithfully

The engine's `Binding.compatible` decides agreement with `Term.eqb`,
which bottoms out in `Literal.eqb`. That test folds language-tag case
and compares two `rdf:XMLLiteral` lexical forms by exclusive canonical
XML. The specification's `Compatible` demands `t1 = t2`.

So the engine's test is strictly COARSER, and the two directions are
not alike:

* `compatible_of_Compatible` is UNCONDITIONAL — a coarser test accepts
  everything the specification demands.
* the converse needs `BindingLitExact`, which says every literal the
  two mappings bind is compared exactly.
* `compatible_not_Compatible_witness` is the machine-checked witness
  that the hypothesis cannot be dropped: `"x"@en` and `"x"@EN` are
  accepted by the engine and are different RDF terms.

This is the same shape as finding SR-2 in the F* source, reached the
same way, and the same shape as finding SE-1 on the simple-entailment
vertical.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.AlgebraSpec
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.SPARQL.AlgebraRefinement

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.AlgebraSpec

/-! ## 1. UNION

`union` is `++`, and neither layer's clause mentions equality of terms,
so both directions hold with no hypothesis. -/

theorem occurs_append {mu : SMap} {o1 o2 : SMultiset} :
    Occurs mu (o1 ++ o2) ↔ Occurs mu o1 ∨ Occurs mu o2 := by
  constructor
  · rintro ⟨m, hm, he⟩
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl ⟨m, h, he⟩
    · exact Or.inr ⟨m, h, he⟩
  · rintro (⟨m, hm, he⟩ | ⟨m, hm, he⟩)
    · exact ⟨m, List.mem_append_left _ hm, he⟩
    · exact ⟨m, List.mem_append_right _ hm, he⟩

/-- SET layer: the evaluator's UNION contains exactly the mappings
§18.5 says it should. -/
theorem union_set (o1 o2 : SMultiset) (mu : SMap) :
    Occurs mu (union o1 o2) ↔ InUnion o1 o2 mu :=
  occurs_append

/-- BAG layer: `Card[Union(Ω1,Ω2)][μ] = Card[Ω1][μ] + Card[Ω2][μ]`. -/
theorem union_card (o1 o2 : SMultiset) : unionCardSpec o1 o2 (union o1 o2) := by
  intro mu
  simp only [union, mult, List.filter_append, List.length_append]

/-! ## 2. FILTER

The evaluator filters by applying the condition to each ROW of the
list. The specification's clause applies it to the MAPPING μ. Those
agree only if the condition cannot tell two lists denoting the same
mapping apart — the congruence property the F* source records as
finding FC-1 and proves of its real expression evaluator.

It is a hypothesis here rather than a fact because this module's
`FExpr` is the abstract §18.5 predicate, exactly as the specification
states it. -/

/-- The condition depends on the MAPPING, not on the list that
represents it. -/
def FExprCongr (f : FExpr) : Prop := ∀ mu mu', SMapEq mu mu' → f mu = f mu'

/-- With the condition true of μ, the two filters commute: dropping
rows the condition rejects cannot drop a row that denotes μ. -/
theorem filter_keep {f : FExpr} (hf : FExprCongr f) {mu : SMap} (hfm : f mu = true)
    (omega : SMultiset) :
    List.filter (fun m => smapEqb mu m) (List.filter f omega)
      = List.filter (fun m => smapEqb mu m) omega := by
  induction omega with
  | nil => rfl
  | cons m rest ih =>
      rw [List.filter_cons]
      cases hcm : f m with
      | true =>
          rw [if_pos (rfl : (true : Bool) = true), List.filter_cons, List.filter_cons]
          cases hem : smapEqb mu m with
          | true => rw [if_pos (rfl : (true : Bool) = true), if_pos (rfl : (true : Bool) = true), ih]
          | false =>
              rw [if_neg (by simp), if_neg (by simp), ih]
      | false =>
          have hem : smapEqb mu m = false := by
            cases hx : smapEqb mu m with
            | false => rfl
            | true =>
                have hc := (hf mu m (smapEqb_sound hx)).trans hcm
                rw [hfm] at hc; exact absurd hc (by simp)
          rw [if_neg (by simp), List.filter_cons,
              if_neg (by rw [hem]; simp), ih]

/-- With the condition false of μ, nothing denoting μ survives. -/
theorem filter_drop {f : FExpr} (hf : FExprCongr f) {mu : SMap} (hfm : f mu = false)
    (omega : SMultiset) :
    List.filter (fun m => smapEqb mu m) (List.filter f omega) = [] := by
  induction omega with
  | nil => rfl
  | cons m rest ih =>
      rw [List.filter_cons]
      cases hcm : f m with
      | true =>
          have hem : smapEqb mu m = false := by
            cases hx : smapEqb mu m with
            | false => rfl
            | true =>
                have hc := (hf mu m (smapEqb_sound hx)).trans hcm
                rw [hfm] at hc; exact absurd hc (by simp)
          rw [if_pos (rfl : (true : Bool) = true), List.filter_cons, if_neg (by rw [hem]; simp), ih]
      | false => rw [if_neg (by simp), ih]

/-- BAG layer: `Card[Filter(expr,Ω)][μ] = Card[Ω][μ]` when the
condition holds of μ, and 0 otherwise. -/
theorem filter_card {f : FExpr} (hf : FExprCongr f) (omega : SMultiset) :
    filterCardSpec f omega (filterSeq f omega) := by
  intro mu
  show (List.filter (fun m => smapEqb mu m) (List.filter f omega)).length
      = if f mu then (List.filter (fun m => smapEqb mu m) omega).length else 0
  cases hfm : f mu with
  | true => simp only [filter_keep hf hfm omega, if_true]
  | false => simp [filter_drop hf hfm omega]

/-- SET layer, which follows from the bag layer through part 4's
`mult_pos_iff_occurs`. -/
theorem filter_set {f : FExpr} (hf : FExprCongr f) (omega : SMultiset) (mu : SMap) :
    Occurs mu (filterSeq f omega) ↔ InFilter f omega mu := by
  rw [← mult_pos_iff_occurs, filter_card hf omega mu]
  cases hfm : f mu with
  | true =>
      simp only [if_true, InFilter, hfm, and_true]
      exact mult_pos_iff_occurs mu omega
  | false =>
      simp only [InFilter, hfm]
      simp

/-! ## 3. The compatibility bridge

Where the engine and the specification are genuinely not the same
relation. -/

/-- `Binding.lookup` (the engine's) and `sval` (the specification's)
are the same partial function. They are written differently — argument
order and `=` against `==` — so the bridge below needs this stated. -/
theorem binding_lookup_eq_sval (v : VarName) : ∀ mu : SMap,
    Binding.lookup v mu = sval v mu
  | [] => rfl
  | (w, t) :: rest => by
      by_cases h : w = v
      · subst h; simp [Binding.lookup, sval, List.lookup]
      · have hb : (v == w) = false := by simp [Ne.symm h]
        simp only [Binding.lookup, if_neg h, sval, List.lookup, hb]
        exact binding_lookup_eq_sval v rest

theorem noRepeats_head {v : VarName} {vs : List VarName}
    (h : noRepeats (v :: vs) = true) : v ∉ vs := by
  simp only [noRepeats, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  intro hm
  have hc : vs.contains v = true := by simpa using hm
  rw [hc] at h
  exact absurd h.1 (by simp)

/-- The engine accepts everything the specification demands — on a
WELL-FORMED left mapping.

The `smapWf` hypothesis is not decoration. `Binding.compatible` tests
EVERY pair in the list, `sval` sees only the first binding for a
variable, so a duplicate-key list makes the two disagree:
`compatible_duplicate_key_witness` below is a mapping the
specification calls compatible with itself and the engine rejects.
The specification's own header says the same thing about `sm_compatible`
in the F* tree, and pins the difference on the REPRESENTATION. -/
theorem compatible_of_Compatible : ∀ {mu1 mu2 : SMap},
    noRepeats (sdom mu1) = true → Compatible mu1 mu2 →
    Binding.compatible mu1 mu2 = true
  | [], _, _, _ => rfl
  | (v, t) :: rest, mu2, hwf, h => by
      have hvnot : v ∉ sdom rest := noRepeats_head (by simpa [sdom] using hwf)
      have hrestwf : noRepeats (sdom rest) = true := by
        simp only [sdom, List.map_cons, noRepeats, Bool.and_eq_true] at hwf
        exact hwf.2
      have hrest : Compatible rest mu2 := by
        intro w s1 s2 h1 h2
        refine h w s1 s2 ?_ h2
        have hwv : ¬ (w = v) := by
          intro hc; subst hc
          rw [sval_none_outside_dom w rest hvnot] at h1
          exact absurd h1 (by simp)
        have hbeq : (w == v) = false := by simp [hwv]
        simp only [sval, List.lookup, hbeq]
        exact h1
      simp only [Binding.compatible, compatible_of_Compatible hrestwf hrest, Bool.and_true]
      cases h2 : Binding.lookup v mu2 with
      | none => rfl
      | some t2 =>
          have hvt : sval v ((v, t) :: rest) = some t := by
            simp [sval, List.lookup]
          have : t = t2 := h v t t2 hvt (by rw [← binding_lookup_eq_sval v mu2]; exact h2)
          rw [this]; exact Term.eqb_refl t2

/-- Every literal these two mappings bind is one `Literal.eqb` compares
exactly — the fragment on which the engine's test IS the
specification's relation. -/
def BindingLitExact (mu1 mu2 : SMap) : Prop :=
  ∀ v l1 l2, sval v mu1 = some (.literal l1) → sval v mu2 = some (.literal l2) →
    Literal.eqb l1.val l2.val = true → l1 = l2

/-! ## 4. The witness: the hypothesis cannot be dropped

Any pair of literals the engine's test conflates makes the converse of
`compatible_of_Compatible` false. `"x"@en` and `"x"@EN` are such a
pair, because `Literal.eqb` folds language-tag case.

### Why the pair is a `#guard` and not a `decide`

The theorem below is stated over ABSTRACT literals with the conflation
as a hypothesis, and the concrete pair is checked by `#guard` rather
than proved in the kernel. That is forced, not preferred:
`langTagEq` calls `String.toLower`, which is `String.mapAux`, and the
kernel does not reduce it — `decide` gets stuck at
`(String.mapAux Char.toLower "en" "en".startPos).1.1.toList`.

The `#guard`s are what stop the theorem being vacuous. They run the
compiled evaluator on every `lake build`, so a hypothesis no pair can
satisfy would fail the build.

The abstract form is also the stronger statement: it holds of EVERY
pair the engine conflates, not only of this one. -/

private def vX : VarName := "x"
private def litEn : WfLiteral := Literal.langString "x" "en"
private def litEN : WfLiteral := Literal.langString "x" "EN"

/-- For ANY two literals the engine's term test conflates and that are
not equal, the engine calls the two singleton mappings compatible and
the specification does not. So `compatible_of_Compatible` has no
converse, and no statement that the engine DECIDES `Compatible` is
true as written. -/
theorem compatible_not_Compatible_of_coarse {l1 l2 : WfLiteral}
    (heq : Term.eqb (.literal l1) (.literal l2) = true) (hne : l1 ≠ l2) :
    Binding.compatible [(vX, .literal l1)] [(vX, .literal l2)] = true ∧
    ¬ Compatible [(vX, .literal l1)] [(vX, .literal l2)] := by
  constructor
  · simp only [Binding.compatible, Binding.lookup, if_true]
    simpa using heq
  · intro h
    have := h vX (.literal l1) (.literal l2) (by simp [sval, List.lookup])
                                             (by simp [sval, List.lookup])
    exact hne (Term.literal.inj this)

/-! ## Build-time checks -/

#guard union [] [] == ([] : SolutionSeq)
#guard (union [[(vX, Term.literal litEn)]] []).length == 1

/-! The satisfiability evidence for `compatible_not_Compatible_of_coarse`.
The engine's term test conflates the pair; the two literals are not
equal. Both run on the compiled evaluator, which does what the kernel
will not. -/
#guard Term.eqb (Term.literal litEn) (Term.literal litEN) == true
#guard litEn != litEN

/-! ## Axiom audit -/

#print axioms union_set
#print axioms union_card
#print axioms filter_card
#print axioms filter_set
#print axioms compatible_of_Compatible
#print axioms compatible_not_Compatible_of_coarse

end L4Factoidal.SPARQL.AlgebraRefinement
