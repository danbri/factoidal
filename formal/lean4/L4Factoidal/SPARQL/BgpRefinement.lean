/-
L4Factoidal.SPARQL.BgpRefinement — what an answer of `evalBgp` MEANS.

Layer 2 of the query-rung reduction. The F\* counterpart is
`formal/fstar/SPARQL11.Algebra.BGPRefinement.fst` (2,234 lines); this
port carries its central theorem,
`theorem_eval_bgp_instantiates_into_graph`.

## The statement

`evalBgp b g` returns solution mappings. The theorem says what one MEANS:
substitute it back into the basic graph pattern and every triple you get
is a triple of `g`.

    theorem evalBgp_instantiates_into_graph (b : Bgp) (g : Graph)
        {mu : Binding} (h : mu ∈ evalBgp b g) :
        ∀ t ∈ instBgp b mu, Graph.mem t g = true

That is the SPARQL 1.1 §18.3.1 reading of BGP matching — a solution is a
substitution whose image is a subgraph — proved against the shipping
evaluator rather than assumed of it.

## The substitution is the UPDATE template instantiator, reused

The F\* `instantiate_tp` / `instantiate_bgp` live in
`SPARQL11.Algebra.fst`. The Lean tree already had them, under the names
`instSubject` / `instObject` / `instTriple` in `SPARQL.Update`, where
they instantiate an INSERT template, and `constructPredicate` in
`SPARQL.Query`. They are the same functions: `instTriple fresh mu tp`
with `fresh := id` is `instantiate_tp tp mu` exactly.

So this module defines no substitution of its own. `instBgp` is one
line over `instTriple id`, and every lemma below is stated about the
shipping template instantiator. A second copy would have let the two
drift, and the theorem would then be about the copy.

`fresh` exists because SPARQL 1.1 Update §4.1.3 makes a blank node
WRITTEN IN a template a fresh node per solution. A basic graph pattern
being matched has no such rule — its blank nodes are the ones that
matched — so `id` is the right instance here, not a convenience.

## Why the conclusion is `Graph.mem` and not `t ∈ g`

`Graph.mem` compares with `Triple.eqb`, the engine's RDF term equality.
List membership compares structurally. The stronger form is FALSE, and
the counterexample is in `tryBindTerm`'s var case:

    | .var v, t, mu =>
        match mu.lookup v with
        | some existing => if existing.eqb t then some mu else none

When `v` is already bound, the mapping is NOT updated to hold the graph's
own term — the already-bound term stays, and matching succeeds on
`Term.eqb`. So substituting the solution back yields the FIRST term
bound to `v`, which need not be structurally identical to the one this
triple carries.

The same effect appears in `tryBindTerm`'s LITERAL case, where the
pattern's own literal is kept and only compared to the graph's:

    | .literal l, t, mu =>
        match t with
        | .literal l' => if l.val.eqb l'.val then some mu else none

Two language-tagged literals differing only in the CASE of the tag are
`Term.eqb`-equal and structurally distinct, so a pattern spelling the
tag `en` against a graph spelling it `EN` matches, and the instantiated
triple is not a member of the graph list. The `#guard` block below pins
that concrete case, in both directions.

The F\* module handles this by scoping to a fragment — `bgp_frag`
demands exact literal constants, so the two literals coincide. This port
takes the other route and proves the theorem for EVERY basic graph
pattern, with the conclusion stated at `Graph.mem`. Nothing is assumed
about the pattern and no fragment predicate is needed. The two agree
where both apply; this one also covers patterns the F\* fragment
excludes.

## Triple terms

RDF 1.2 triple terms are IN, in both pattern and data positions, and the
`tripleTerm` arms of every lemma below are proved rather than excluded.

## What layer 2 is FOR

`SPARQL11.EntailmentRegime.RDFS` composes this with the ρdf closure to
get the RDFS entailment regime theorem. That module is not ported yet;
this is the half of its input that does not mention entailment.
-/
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- μ applied to a basic graph pattern; a pattern position that does not
instantiate drops out. Port of `instantiate_bgp`, over the shipping
template instantiator at `fresh := id`. -/
def instBgp (b : Bgp) (mu : Binding) : List Triple :=
  b.filterMap (instTriple id mu)

/-! ## Extension: a match only ADDS bindings

Every `tryBind*` either leaves μ alone or conses one new variable onto
it, and it only conses when that variable was unbound. So the mapping
grows monotonically along a BGP walk, and a term instantiated early
stays instantiated the same way at the end. -/

/-- μ' agrees with μ everywhere μ is defined. -/
def Extends (mu mu' : Binding) : Prop :=
  ∀ v t, mu.lookup v = some t → mu'.lookup v = some t

theorem Extends.refl (mu : Binding) : Extends mu mu := fun _ _ h => h

theorem Extends.trans {a b c : Binding} (h1 : Extends a b) (h2 : Extends b c) :
    Extends a c := fun v t h => h2 v t (h1 v t h)

theorem Extends.bind {mu : Binding} {v : VarName} {t : Term}
    (hfresh : mu.lookup v = none) : Extends mu (mu.bind v t) := by
  intro w u hw
  simp only [Binding.bind, Binding.lookup]
  by_cases hvw : v = w
  · subst hvw; rw [hfresh] at hw; exact absurd hw (by simp)
  · simp [hvw, hw]

theorem tryBindSubject_extends {ps : PatternSubject} {s : Subject}
    {mu mu' : Binding} (h : tryBindSubject ps s mu = some mu') :
    Extends mu mu' := by
  cases ps with
  | iri i =>
      cases s with
      | iri i' =>
          simp only [tryBindSubject] at h
          split at h
          · obtain rfl : mu = mu' := by simpa using h
            exact Extends.refl _
          · simp at h
      | bnode _ => simp [tryBindSubject] at h
  | bnode b =>
      cases s with
      | bnode b' =>
          simp only [tryBindSubject] at h
          split at h
          · obtain rfl : mu = mu' := by simpa using h
            exact Extends.refl _
          · simp at h
      | iri _ => simp [tryBindSubject] at h
  | tripleTerm _ _ _ => simp [tryBindSubject] at h
  | var v =>
      simp only [tryBindSubject] at h
      cases hl : mu.lookup v with
      | none =>
          simp only [hl, Option.some.injEq] at h
          subst h; exact Extends.bind hl
      | some existing =>
          simp only [hl] at h
          split at h
          · obtain rfl : mu = mu' := by simpa using h
            exact Extends.refl _
          · simp at h

theorem tryBindTerm_extends : ∀ {pt : PatternTerm} {t : Term} {mu mu' : Binding},
    tryBindTerm pt t mu = some mu' → Extends mu mu' := by
  intro pt
  induction pt with
  | iri i =>
      intro t mu mu' h
      cases t with
      | iri i' =>
          simp only [tryBindTerm] at h
          split at h
          · obtain rfl : mu = mu' := by simpa using h
            exact Extends.refl _
          · simp at h
      | bnode _ => simp [tryBindTerm] at h
      | literal _ => simp [tryBindTerm] at h
      | tripleTerm _ _ _ => simp [tryBindTerm] at h
  | bnode b =>
      intro t mu mu' h
      cases t with
      | bnode b' =>
          simp only [tryBindTerm] at h
          split at h
          · obtain rfl : mu = mu' := by simpa using h
            exact Extends.refl _
          · simp at h
      | iri _ => simp [tryBindTerm] at h
      | literal _ => simp [tryBindTerm] at h
      | tripleTerm _ _ _ => simp [tryBindTerm] at h
  | literal l =>
      intro t mu mu' h
      cases t with
      | literal l' =>
          simp only [tryBindTerm] at h
          split at h
          · obtain rfl : mu = mu' := by simpa using h
            exact Extends.refl _
          · simp at h
      | iri _ => simp [tryBindTerm] at h
      | bnode _ => simp [tryBindTerm] at h
      | tripleTerm _ _ _ => simp [tryBindTerm] at h
  | var v =>
      intro t mu mu' h
      simp only [tryBindTerm] at h
      cases hl : mu.lookup v with
      | none =>
          simp only [hl, Option.some.injEq] at h
          subst h; exact Extends.bind hl
      | some existing =>
          simp only [hl] at h
          split at h
          · obtain rfl : mu = mu' := by simpa using h
            exact Extends.refl _
          · simp at h
  | tripleTerm ps pp po ihs ihp iho =>
      intro t mu mu' h
      cases t with
      | tripleTerm s p o =>
          simp only [tryBindTerm] at h
          cases h1 : tryBindTerm ps s.toTerm mu with
          | none => simp [h1] at h
          | some mu1 =>
              simp only [h1] at h
              cases h2 : tryBindTerm pp (.iri p) mu1 with
              | none => simp [h2] at h
              | some mu2 =>
                  simp only [h2] at h
                  exact ((ihs h1).trans (ihp h2)).trans (iho h)
      | iri _ => simp [tryBindTerm] at h
      | bnode _ => simp [tryBindTerm] at h
      | literal _ => simp [tryBindTerm] at h

theorem tpMatch_extends {tp : TriplePattern} {t : Triple} {mu mu' : Binding}
    (h : tpMatch tp t mu = some mu') : Extends mu mu' := by
  simp only [tpMatch] at h
  cases h1 : tryBindSubject tp.s t.s mu with
  | none => simp [h1] at h
  | some mu1 =>
      simp only [h1] at h
      cases h2 : tryBindTerm tp.p (.iri t.p) mu1 with
      | none => simp [h2] at h
      | some mu2 =>
          simp only [h2] at h
          exact ((tryBindSubject_extends h1).trans
                 (tryBindTerm_extends h2)).trans (tryBindTerm_extends h)

theorem evalBgpFrom_extends {g : Graph} : ∀ (b : Bgp) {mu mu' : Binding},
    mu' ∈ evalBgpFrom g b mu → Extends mu mu' := by
  intro b
  induction b with
  | nil => intro mu mu' h
           simp only [evalBgpFrom, List.mem_singleton] at h
           subst h; exact Extends.refl _
  | cons tp rest ih =>
      intro mu mu' h
      simp only [evalBgpFrom, List.mem_flatMap] at h
      obtain ⟨mu1, hmu1, hrest⟩ := h
      simp only [evalTP, List.mem_filterMap] at hmu1
      obtain ⟨t, _, hmatch⟩ := hmu1
      exact (tpMatch_extends hmatch).trans (ih hrest)

/-! ## Instantiation is monotone in the mapping

Stated at `fresh := id`, which is all this module needs; the `fresh`
argument plays no part in any of these proofs, so a general version
would carry a parameter no caller here varies. -/

theorem instSubject_mono {ps : PatternSubject} {mu mu' : Binding} {s : Subject}
    (he : Extends mu mu') (h : instSubject id mu ps = some s) :
    instSubject id mu' ps = some s := by
  cases ps with
  | iri i => simpa [instSubject] using h
  | bnode b => simpa [instSubject] using h
  | tripleTerm _ _ _ => simp [instSubject] at h
  | var v =>
      simp only [instSubject] at h ⊢
      cases hl : mu.lookup v with
      | none => simp [hl] at h
      | some x => simp only [hl] at h; simp only [he v x hl]; exact h

theorem constructPredicate_mono {pt : PatternTerm} {mu mu' : Binding} {p : WfIri}
    (he : Extends mu mu') (h : constructPredicate pt mu = some p) :
    constructPredicate pt mu' = some p := by
  cases pt with
  | iri i => simpa [constructPredicate] using h
  | bnode _ => simp [constructPredicate] at h
  | literal _ => simp [constructPredicate] at h
  | tripleTerm _ _ _ => simp [constructPredicate] at h
  | var v =>
      simp only [constructPredicate] at h ⊢
      cases hl : mu.lookup v with
      | none => simp [hl] at h
      | some x => simp only [hl] at h; simp only [he v x hl]; exact h

theorem instObject_mono : ∀ {pt : PatternTerm} {mu mu' : Binding} {t : Term},
    Extends mu mu' → instObject id mu pt = some t → instObject id mu' pt = some t := by
  intro pt
  induction pt with
  | iri i => intro mu mu' t _ h; simpa [instObject] using h
  | bnode b => intro mu mu' t _ h; simpa [instObject] using h
  | literal l => intro mu mu' t _ h; simpa [instObject] using h
  | var v =>
      intro mu mu' t he h
      simp only [instObject] at h ⊢
      exact he v t h
  | tripleTerm ps pp po ihs ihp iho =>
      intro mu mu' t he h
      simp only [instObject] at h ⊢
      cases h1 : instObject id mu ps with
      | none => simp [h1] at h
      | some st =>
          simp only [h1] at h
          cases h2 : st.toSubject? with
          | none => simp [h2] at h
          | some sj =>
              simp only [h2] at h
              cases h3 : instObject id mu pp with
              | none => simp [h3] at h
              | some pv =>
                  simp only [h3] at h
                  cases pv with
                  | iri pi =>
                      cases h4 : instObject id mu po with
                      | none => simp [h4] at h
                      | some o =>
                          simp only [h4] at h
                          simp only [ihs he h1, h2, ihp he h3, iho he h4]
                          exact h
                  | bnode _ => simp at h
                  | literal _ => simp at h
                  | tripleTerm _ _ _ => simp at h

theorem instTriple_mono {tp : TriplePattern} {mu mu' : Binding} {t : Triple}
    (he : Extends mu mu') (h : instTriple id mu tp = some t) :
    instTriple id mu' tp = some t := by
  simp only [instTriple] at h ⊢
  cases h1 : instSubject id mu tp.s with
  | none => simp [h1] at h
  | some s =>
      simp only [h1] at h
      cases h2 : constructPredicate tp.p mu with
      | none => simp [h2] at h
      | some p =>
          simp only [h2] at h
          cases h3 : instObject id mu tp.o with
          | none => simp [h3] at h
          | some o =>
              simp only [h3] at h
              simp only [instSubject_mono he h1, constructPredicate_mono he h2,
                         instObject_mono he h3]
              exact h

/-! ## A match instantiates back to the triple it matched

Up to `Term.eqb`, for the reason the header gives: a variable already
bound keeps its first binding, and a literal pattern keeps its own
literal. -/

/-- Reading a subject as a term and back is the identity. -/
@[simp] theorem toTerm_toSubject? (s : Subject) : s.toTerm.toSubject? = some s := by
  cases s <;> rfl

/-- A term engine-equal to a subject's term form reads back as a subject
engine-equal to it. -/
theorem toSubject?_of_eqb_toTerm {x : Term} {s : Subject}
    (h : x.eqb s.toTerm = true) :
    ∃ s', x.toSubject? = some s' ∧ s'.eqb s = true := by
  cases s <;> cases x <;>
    simp_all [Term.eqb, Subject.toTerm, Term.toSubject?, Subject.eqb]

/-- An object position that instantiates to an IRI instantiates as a
PREDICATE to that IRI. The two instantiators agree wherever both are
defined; this is the arm the triple-pattern proof needs, because a match
runs `tryBindTerm` on the predicate while `instTriple` runs
`constructPredicate`. -/
theorem constructPredicate_of_instObject {pt : PatternTerm} {mu : Binding}
    {i : WfIri} (h : instObject id mu pt = some (.iri i)) :
    constructPredicate pt mu = some i := by
  cases pt with
  | iri j => simp only [instObject] at h; simp_all [constructPredicate]
  | bnode _ => simp [instObject] at h
  | literal _ => simp [instObject] at h
  | var v => simp only [instObject] at h; simp [constructPredicate, h]
  | tripleTerm ps pp po =>
      simp only [instObject] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · split at h
            · simp at h
            · simp at h
          · simp at h

theorem tryBindSubject_inst {ps : PatternSubject} {s : Subject} {mu mu' : Binding}
    (h : tryBindSubject ps s mu = some mu') :
    ∃ s', instSubject id mu' ps = some s' ∧ s'.eqb s = true := by
  cases ps with
  | iri i =>
      cases s with
      | iri i' =>
          simp only [tryBindSubject] at h
          split at h
          · rename_i hc
            exact ⟨.iri i, by simp [instSubject], by simpa [Subject.eqb] using hc⟩
          · simp at h
      | bnode _ => simp [tryBindSubject] at h
  | bnode b =>
      cases s with
      | bnode b' =>
          simp only [tryBindSubject] at h
          split at h
          · rename_i hc
            exact ⟨.bnode b, by simp [instSubject], by simpa [Subject.eqb] using hc⟩
          · simp at h
      | iri _ => simp [tryBindSubject] at h
  | tripleTerm _ _ _ => simp [tryBindSubject] at h
  | var v =>
      simp only [tryBindSubject] at h
      cases hl : mu.lookup v with
      | none =>
          simp only [hl, Option.some.injEq] at h
          subst h
          refine ⟨s, ?_, by simp⟩
          cases s <;>
            simp [instSubject, Binding.bind, Binding.lookup, Subject.toTerm]
      | some existing =>
          simp only [hl] at h
          split at h
          · rename_i hc
            obtain rfl : mu = mu' := by simpa using h
            obtain ⟨s', hs', he⟩ := toSubject?_of_eqb_toTerm (by simpa using hc)
            refine ⟨s', ?_, he⟩
            cases existing <;>
              simp_all [instSubject, Term.toSubject?]
          · simp at h

theorem tryBindTerm_inst : ∀ {pt : PatternTerm} {t : Term} {mu mu' : Binding},
    tryBindTerm pt t mu = some mu' →
    ∃ t', instObject id mu' pt = some t' ∧ t'.eqb t = true := by
  intro pt
  induction pt with
  | iri i =>
      intro t mu mu' h
      cases t with
      | iri i' =>
          simp only [tryBindTerm] at h
          split at h
          · rename_i hc
            exact ⟨.iri i, by simp [instObject], by simpa [Term.eqb] using hc⟩
          · simp at h
      | bnode _ => simp [tryBindTerm] at h
      | literal _ => simp [tryBindTerm] at h
      | tripleTerm _ _ _ => simp [tryBindTerm] at h
  | bnode b =>
      intro t mu mu' h
      cases t with
      | bnode b' =>
          simp only [tryBindTerm] at h
          split at h
          · rename_i hc
            exact ⟨.bnode b, by simp [instObject], by simpa [Term.eqb] using hc⟩
          · simp at h
      | iri _ => simp [tryBindTerm] at h
      | literal _ => simp [tryBindTerm] at h
      | tripleTerm _ _ _ => simp [tryBindTerm] at h
  | literal l =>
      intro t mu mu' h
      cases t with
      | literal l' =>
          simp only [tryBindTerm] at h
          split at h
          · rename_i hc
            exact ⟨.literal l, by simp [instObject], by simpa [Term.eqb] using hc⟩
          · simp at h
      | iri _ => simp [tryBindTerm] at h
      | bnode _ => simp [tryBindTerm] at h
      | tripleTerm _ _ _ => simp [tryBindTerm] at h
  | var v =>
      intro t mu mu' h
      simp only [tryBindTerm] at h
      cases hl : mu.lookup v with
      | none =>
          simp only [hl, Option.some.injEq] at h
          subst h
          exact ⟨t, by simp [instObject, Binding.bind, Binding.lookup], by simp⟩
      | some existing =>
          simp only [hl] at h
          split at h
          · rename_i hc
            obtain rfl : mu = mu' := by simpa using h
            exact ⟨existing, by simp [instObject, hl], by simpa using hc⟩
          · simp at h
  | tripleTerm ps pp po ihs ihp iho =>
      intro t mu mu' h
      cases t with
      | tripleTerm s p o =>
          simp only [tryBindTerm] at h
          cases h1 : tryBindTerm ps s.toTerm mu with
          | none => simp [h1] at h
          | some mu1 =>
              simp only [h1] at h
              cases h2 : tryBindTerm pp (.iri p) mu1 with
              | none => simp [h2] at h
              | some mu2 =>
                  simp only [h2] at h
                  have e12 : Extends mu1 mu2 := tryBindTerm_extends h2
                  have e2' : Extends mu2 mu' := tryBindTerm_extends h
                  obtain ⟨st, hst, hste⟩ := ihs h1
                  obtain ⟨pt', hpt', hpte⟩ := ihp h2
                  obtain ⟨o', ho', hoe⟩ := iho h
                  obtain ⟨sj, hsj, hsje⟩ := toSubject?_of_eqb_toTerm hste
                  have hstm : instObject id mu' ps = some st :=
                    instObject_mono (e12.trans e2') hst
                  have hppi : pt' = .iri p := Term.eqb_iri hpte
                  subst hppi
                  have hppm : instObject id mu' pp = some (.iri p) :=
                    instObject_mono e2' hpt'
                  refine ⟨.tripleTerm sj p o', ?_, ?_⟩
                  · simp only [instObject, hstm, hsj, hppm, ho']
                  · simp [Term.eqb, hsje, hoe]
      | iri _ => simp [tryBindTerm] at h
      | bnode _ => simp [tryBindTerm] at h
      | literal _ => simp [tryBindTerm] at h

/-- One triple pattern: a successful match instantiates back to a triple
engine-equal to the one that was matched. -/
theorem tpMatch_inst {tp : TriplePattern} {t : Triple} {mu mu' : Binding}
    (h : tpMatch tp t mu = some mu') :
    ∃ u, instTriple id mu' tp = some u ∧ u.eqb t = true := by
  simp only [tpMatch] at h
  cases h1 : tryBindSubject tp.s t.s mu with
  | none => simp [h1] at h
  | some mu1 =>
      simp only [h1] at h
      cases h2 : tryBindTerm tp.p (.iri t.p) mu1 with
      | none => simp [h2] at h
      | some mu2 =>
          simp only [h2] at h
          have e12 : Extends mu1 mu2 := tryBindTerm_extends h2
          have e2' : Extends mu2 mu' := tryBindTerm_extends h
          obtain ⟨s', hs', hse⟩ := tryBindSubject_inst h1
          obtain ⟨p', hp', hpe⟩ := tryBindTerm_inst h2
          obtain ⟨o', ho', hoe⟩ := tryBindTerm_inst h
          have hsm : instSubject id mu' tp.s = some s' :=
            instSubject_mono (e12.trans e2') hs'
          have hpi : p' = .iri t.p := Term.eqb_iri hpe
          subst hpi
          have hpm : constructPredicate tp.p mu' = some t.p :=
            constructPredicate_of_instObject (instObject_mono e2' hp')
          refine ⟨{ s := s', p := t.p, o := o' }, ?_, ?_⟩
          · simp only [instTriple, hsm, hpm, ho']
          · simp [Triple.eqb, hse, hoe]

/-! ## The theorem

Every triple of a solution's instantiated basic graph pattern is a
triple of the graph, by the engine equality. -/

theorem instBgp_into_graph {g : Graph} : ∀ (b : Bgp) {mu mu' : Binding},
    mu' ∈ evalBgpFrom g b mu → ∀ t ∈ instBgp b mu', Graph.mem t g = true := by
  intro b
  induction b with
  | nil => intro mu mu' _ t ht; simp [instBgp] at ht
  | cons tp rest ih =>
      intro mu mu' h t ht
      simp only [evalBgpFrom, List.mem_flatMap] at h
      obtain ⟨mu1, hmu1, hrest⟩ := h
      simp only [evalTP, List.mem_filterMap] at hmu1
      obtain ⟨u, hu, hmatch⟩ := hmu1
      have e1' : Extends mu1 mu' := evalBgpFrom_extends rest hrest
      obtain ⟨w, hw, hwe⟩ := tpMatch_inst hmatch
      have hw' : instTriple id mu' tp = some w := instTriple_mono e1' hw
      simp only [instBgp, List.filterMap_cons, hw'] at ht
      rcases List.mem_cons.mp ht with rfl | htrest
      · exact graphMem_of_exists ⟨u, hu, by rw [Triple.eqb_symm]; exact hwe⟩
      · exact ih hrest t htrest

/-- Port of `theorem_eval_bgp_instantiates_into_graph`: substituting a
solution of `evalBgp b g` back into `b` lands inside `g`. -/
theorem evalBgp_instantiates_into_graph (b : Bgp) (g : Graph) {mu : Binding}
    (h : mu ∈ evalBgp b g) : ∀ t ∈ instBgp b mu, Graph.mem t g = true :=
  instBgp_into_graph b h

/-! ## Pinned behaviour -/

section Pins

private def pIri : WfIri := ⟨"http://example/p", by decide⟩
private def aIri : WfIri := ⟨"http://example/a", by decide⟩
private def bIri : WfIri := ⟨"http://example/b", by decide⟩

private def gTwo : Graph :=
  [ { s := .iri aIri, p := pIri, o := .iri bIri }
  , { s := .iri bIri, p := pIri, o := .iri aIri } ]

private def qSP : Bgp := [{ s := .var "s", p := .iri pIri, o := .var "o" }]

/-! The empty pattern instantiates to nothing, so the theorem says
something only when the pattern is non-empty. -/
#guard (instBgp [] (Binding.empty)).isEmpty

/-! Two solutions, each instantiating back to the triple it came from. -/
#guard (evalBgp qSP gTwo).length == 2

#guard (evalBgp qSP gTwo).all (fun mu =>
        (instBgp qSP mu).all (fun t => Graph.mem t gTwo))

/-! Non-vacuity: neither instantiation is empty. -/
#guard (evalBgp qSP gTwo).all (fun mu => (instBgp qSP mu).length == 1)

/-! ### Why the conclusion is `Graph.mem` and not `t ∈ g`

The graph holds a language-tagged literal spelled `EN`; the pattern
writes the same tag `en`. `langTagEq` is case-insensitive, so the match
succeeds — and `instBgp` returns the PATTERN's literal, which is not the
graph's own term. Engine membership is true and strict list membership
is false. -/

private def gLang : Graph :=
  [{ s := .iri aIri, p := pIri, o := .literal (Literal.langString "x" "EN") }]

private def qLang : Bgp :=
  [{ s := .iri aIri, p := .iri pIri,
     o := .literal (Literal.langString "x" "en") }]

#guard (evalBgp qLang gLang).length == 1

/-! Non-vacuity for the two guards below. -/
#guard match evalBgp qLang gLang with
       | mu :: _ => (instBgp qLang mu).length == 1
       | []      => false

#guard match evalBgp qLang gLang with
       | mu :: _ => (instBgp qLang mu).all (fun t => Graph.mem t gLang)
       | []      => false

/-! The same triple is NOT in the graph by structural equality. This pin
stops a later reader from strengthening the theorem to `t ∈ g`. -/
#guard match evalBgp qLang gLang with
       | mu :: _ => (instBgp qLang mu).all (fun t => !(gLang.contains t))
       | []      => false

/-! A pattern position that does not bind drops out rather than producing
a wrong triple. -/
#guard (instBgp [{ s := .var "unbound", p := .iri pIri, o := .var "o" }]
                Binding.empty).isEmpty

end Pins

end L4Factoidal.SPARQL
