/-
L4Factoidal.Unified.SparqlAlgebra — the SPARQL algebra ABOVE the basic
graph pattern, as satisfaction over the unified model theory.

Issue https://github.com/danbri/factoidal/issues/614.
`Unified/SparqlAdequacy.lean` proved BGP matching only; nothing above
the BGP had a unified statement. This module adds JOIN.

## What is stated, and at what strength

`SPARQL/AlgebraSpec.lean` already carries §18.5 as relations over
partial functions (`SMap`, `sval`, `Compatible`, `IsMerge`, `InJoin`),
and `SPARQL/JoinRefinement.lean` already relates them to the running
`SPARQL.join`. What was missing is the link from either of those to
`Answers` over `CL.Interp`. Three statements, in increasing distance
from the model theory:

* `answers_bgp_append_iff` — **the §18.5 join IS the conjunction on the
  `EntailsSchema` side.** A full iff with NO hypotheses of any kind:
  answering the concatenated pattern is answering both patterns.
* `unified_adequate_join` — **the gate**, a full iff between the pivot
  `BgpMatches μ b₁ g ∧ BgpMatches μ b₂ g` and `Answers` over the
  concatenated pattern. Same two hypotheses as the stage 6 gate and no
  others: `RDF.GraphTtFree g`, `BgpTtFree b₁`, `BgpTtFree b₂`.
* `inJoin_bgpMatches` / `unified_join_answers` — **§18.5's `InJoin`
  over the two BGP evaluations gives a unified answer**,
  UNCONDITIONALLY. This is where merge and compatibility do their
  work: `merge_extends_left` and `merge_extends_right` make the merged
  mapping extend both, and `Extends` carries `BgpMatches` along.

## What is NOT stated

* **No multiplicity.** `Answers` is a `Prop` and `InJoin` is a `Prop`;
  neither counts. `SPARQL/AlgebraSpec.lean`'s cardinality layer is
  untouched here, and the F* bag-refinement proof is still not ported.
  The registry boundary row stands.
* **No completeness back to the engine's `join` LIST.**
  `unified_join_engine_answers` goes from `μ ∈ SPARQL.join …` to an
  answer, and it carries `join_spec_sound`'s hypothesis, because the
  engine's `Binding.compatible` is strictly coarser than §18.3's
  `Compatible` (`compatible_not_Compatible_of_coarse` is the witness
  that the hypothesis cannot be dropped). The other direction —
  every unified answer of the join is a row the engine returns — is
  NOT proved; see the module's closing note.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.SparqlAdequacy
import L4Factoidal.SPARQL.JoinRefinement

namespace L4Factoidal.Unified

open L4Factoidal
open L4Factoidal.SPARQL (Binding Bgp evalBgp)
open L4Factoidal.SPARQL.AlgebraSpec (SMap sval Compatible IsMerge InJoin
  merge_extends_left merge_extends_right)

/-! ## The pivot splits over concatenation -/

/-- A concatenated basic graph pattern matches exactly when both parts
do. `BgpMatches` quantifies over membership, so this is `List.mem_append`
and nothing else. -/
theorem bgpMatches_append {mu : Binding} {b1 b2 : Bgp} {g : RDF.Graph} :
    BgpMatches mu (b1 ++ b2) g ↔ (BgpMatches mu b1 g ∧ BgpMatches mu b2 g) := by
  constructor
  · intro h
    exact ⟨fun tp htp => h tp (List.mem_append_left _ htp),
           fun tp htp => h tp (List.mem_append_right _ htp)⟩
  · rintro ⟨h1, h2⟩ tp htp
    rcases List.mem_append.mp htp with h | h
    · exact h1 tp h
    · exact h2 tp h

theorem bgpTtFree_append {b1 b2 : Bgp} (h1 : BgpTtFree b1) (h2 : BgpTtFree b2) :
    BgpTtFree (b1 ++ b2) := by
  intro tp htp
  rcases List.mem_append.mp htp with h | h
  · exact h1 tp h
  · exact h2 tp h

/-! ## §18.5's Join is the conjunction on the `EntailsSchema` side -/

/-- Satisfaction of the concatenated body splits. -/
theorem satisfies_bgpBody_append (i : CL.Interp) (mu : Binding) (b1 b2 : Bgp) :
    CL.Satisfies i (bgpBody mu (b1 ++ b2)) ↔
      (CL.Satisfies i (bgpBody mu b1) ∧ CL.Satisfies i (bgpBody mu b2)) := by
  rw [satisfies_bgpBody_iff, satisfies_bgpBody_iff, satisfies_bgpBody_iff]
  constructor
  · intro h
    exact ⟨fun tp htp => h tp (List.mem_append_left _ htp),
           fun tp htp => h tp (List.mem_append_right _ htp)⟩
  · rintro ⟨h1, h2⟩ tp htp
    rcases List.mem_append.mp htp with h | h
    · exact h1 tp h
    · exact h2 tp h

/-- **JOIN on the model-theoretic side, with no hypotheses at all.**
SPARQL 1.1 §18.5 defines `Join(Ω₁, Ω₂)` as the set of merges of
compatible mappings; on the `EntailsSchema` side the merged mapping
answers the concatenated pattern exactly when it answers both parts.
Holds for EVERY condition bundle, schema and premise list. -/
theorem answers_bgp_append_iff (conds : CL.Interp → Prop) (S : Schema)
    (premises : List CL.Sentence) (b1 b2 : Bgp) (mu : Binding) :
    Answers conds S premises (sparqlBgpToQuery (b1 ++ b2)) mu ↔
      (Answers conds S premises (sparqlBgpToQuery b1) mu ∧
       Answers conds S premises (sparqlBgpToQuery b2) mu) := by
  simp only [Answers, EntailsSchema, UQuery.instantiate, sparqlBgpToQuery]
  constructor
  · intro h
    exact ⟨fun i hc hs hp => (satisfies_bgpBody_append i mu b1 b2).mp (h i hc hs hp) |>.1,
           fun i hc hs hp => (satisfies_bgpBody_append i mu b1 b2).mp (h i hc hs hp) |>.2⟩
  · rintro ⟨h1, h2⟩ i hc hs hp
    exact (satisfies_bgpBody_append i mu b1 b2).mpr ⟨h1 i hc hs hp, h2 i hc hs hp⟩

/-- **The JOIN gate** — a FULL iff, with exactly the stage 6 gate's own
hypotheses and no others.

`BgpTtFree` on each side and `GraphTtFree` on the graph are needed only
by the ← direction, for the reason `unified_adequate_bgp` records (the
term model gives every triple term one quarantine constant). NO
blank-node hypothesis: `unified_adequate_bgp` never needed one, and
`unified_adequate_bgp_spec` is the §18.3.1-clean form for the pattern
the query path matches.

**No multiplicity is claimed.** -/
theorem unified_adequate_join (b1 b2 : Bgp) (g : RDF.Graph) (mu : Binding)
    (hg : RDF.GraphTtFree g) (hb1 : BgpTtFree b1) (hb2 : BgpTtFree b2) :
    (BgpMatches mu b1 g ∧ BgpMatches mu b2 g) ↔
      Answers condTrue termEqSchema [rdfToTheorySk g]
        (sparqlBgpToQuery (b1 ++ b2)) mu :=
  bgpMatches_append.symm.trans
    (unified_adequate_bgp (b1 ++ b2) g mu hg (bgpTtFree_append hb1 hb2))

/-- The same gate, written as the two-sided `Answers` conjunction §18.5
reads like. -/
theorem unified_adequate_join_conj (b1 b2 : Bgp) (g : RDF.Graph) (mu : Binding)
    (hg : RDF.GraphTtFree g) (hb1 : BgpTtFree b1) (hb2 : BgpTtFree b2) :
    (BgpMatches mu b1 g ∧ BgpMatches mu b2 g) ↔
      (Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b1) mu ∧
       Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b2) mu) :=
  (unified_adequate_join b1 b2 g mu hg hb1 hb2).trans
    (answers_bgp_append_iff _ _ _ b1 b2 mu)

/-! ## The merge, and why it carries the pivot

§18.3's merge is a RELATION on partial functions (`IsMerge`), so
nothing below depends on the list the engine happens to build. -/

/-- `BgpMatches` survives extending the mapping: `instTriple` only
LOOKS UP variables, and `SPARQL.instTriple_mono` says a lookup that
succeeded still succeeds with the same triple. -/
theorem bgpMatches_mono {mu mu' : Binding} {b : Bgp} {g : RDF.Graph}
    (he : SPARQL.Extends mu mu') (h : BgpMatches mu b g) : BgpMatches mu' b g := by
  intro tp htp
  obtain ⟨t, hi, hm⟩ := h tp htp
  exact ⟨t, SPARQL.instTriple_mono he hi, hm⟩

/-- A merge extends its left argument. -/
theorem extends_of_isMerge_left {mu1 mu2 mu : SMap} (h : IsMerge mu1 mu2 mu) :
    SPARQL.Extends mu1 mu := by
  intro v t hv
  rw [SPARQL.AlgebraRefinement.binding_lookup_eq_sval] at hv ⊢
  exact merge_extends_left h hv

/-- A merge extends its right argument, on COMPATIBLE arguments — and
compatibility here is §18.3's relation (real equality of the shared
values), not the engine's `Binding.compatible`, which folds
language-tag case. -/
theorem extends_of_isMerge_right {mu1 mu2 mu : SMap} (h : IsMerge mu1 mu2 mu)
    (hc : Compatible mu1 mu2) : SPARQL.Extends mu2 mu := by
  intro v t hv
  rw [SPARQL.AlgebraRefinement.binding_lookup_eq_sval] at hv ⊢
  exact merge_extends_right h hc hv

/-- **§18.5's `InJoin` over two BGP evaluations gives the pivot on both
sides.** UNCONDITIONAL. -/
theorem inJoin_bgpMatches {b1 b2 : Bgp} {g : RDF.Graph} {mu : Binding}
    (hj : InJoin (evalBgp b1 g) (evalBgp b2 g) mu) :
    BgpMatches mu b1 g ∧ BgpMatches mu b2 g := by
  obtain ⟨mu1, mu2, h1, h2, hc, hm⟩ := hj
  exact ⟨bgpMatches_mono (extends_of_isMerge_left hm) (bgp_eval_sound h1),
         bgpMatches_mono (extends_of_isMerge_right hm hc) (bgp_eval_sound h2)⟩

/-- **A §18.5 join row is a unified answer.** UNCONDITIONAL: the →
direction of the gate has no hypotheses, so neither does this. -/
theorem unified_join_answers {b1 b2 : Bgp} {g : RDF.Graph} {mu : Binding}
    (hj : InJoin (evalBgp b1 g) (evalBgp b2 g) mu) :
    Answers condTrue termEqSchema [rdfToTheorySk g]
      (sparqlBgpToQuery (b1 ++ b2)) mu := by
  obtain ⟨hm1, hm2⟩ := inJoin_bgpMatches hj
  exact (answers_bgp_append_iff _ _ _ b1 b2 mu).mpr
    ⟨bgp_matches_answers hm1, bgp_matches_answers hm2⟩

/-- **A row of the RUNNING engine's `join` is a unified answer** — with
the hypothesis `SPARQL/JoinRefinement.lean`'s `join_spec_sound`
carries, and for its reason: `Binding.compatible` accepts pairs
§18.3's `Compatible` rejects, because `Literal.eqb` folds language-tag
case (`compatible_not_Compatible_of_coarse` exhibits such a pair, so
the hypothesis is not decoration). -/
theorem unified_join_engine_answers {b1 b2 : Bgp} {g : RDF.Graph} {mu : Binding}
    (hex : ∀ m1 ∈ evalBgp b1 g, ∀ m2 ∈ evalBgp b2 g,
      Binding.compatible m1 m2 = true → Compatible m1 m2)
    (h : mu ∈ SPARQL.join (evalBgp b1 g) (evalBgp b2 g)) :
    Answers condTrue termEqSchema [rdfToTheorySk g]
      (sparqlBgpToQuery (b1 ++ b2)) mu :=
  unified_join_answers (SPARQL.AlgebraRefinement.join_spec_sound hex h)

/-! ## What the join statements do NOT reach

The direction from a unified answer BACK to a row of `SPARQL.join` is
not proved. `bgp_eval_complete` gives, for each side separately, a
mapping the evaluator returns agreeing with `μ` up to `Term.eqb` — but
assembling those two into one row of `join` needs the engine's
`Binding.compatible` to hold of them, which needs a domain lemma for
`evalBgp` that the tree does not have, and the conclusion would in any
case be agreement up to `Term.eqb` rather than membership (correction
note 27). Recorded, not attempted. -/

/-! ## Non-vacuity

`unified_join_answers` would be worth nothing if `InJoin` over two BGP
evaluations were unsatisfiable, or if `Answers` held of everything. -/

section JoinWitnesses

private theorem jIri (s : String) : RDF.isIri ("http://example/" ++ s) = true := by
  simp [RDF.isIri, String.isEmpty]

private def jI (s : String) : RDF.WfIri := ⟨"http://example/" ++ s, jIri s⟩

/-- `<a> <p> <b> . <b> <q> <c>` -/
private def jG : RDF.Graph :=
  [{ s := .iri (jI "a"), p := jI "p", o := .iri (jI "b") },
   { s := .iri (jI "b"), p := jI "q", o := .iri (jI "c") }]

private def jB1 : Bgp := [{ s := .var "x", p := .iri (jI "p"), o := .var "y" }]
private def jB2 : Bgp := [{ s := .var "y", p := .iri (jI "q"), o := .var "z" }]

-- The evaluator conses, so a returned row lists its bindings in
-- reverse discovery order; these are the rows it actually returns.
private def jMu1 : Binding := [("y", .iri (jI "b")), ("x", .iri (jI "a"))]
private def jMu2 : Binding := [("z", .iri (jI "c")), ("y", .iri (jI "b"))]
private def jMu  : Binding := Binding.merge jMu1 jMu2

-- The two sides really are rows of the evaluator, and the merged row
-- really matches the concatenated pattern. Both run on the compiled
-- evaluator, which is what stops the theorems below being vacuous.
#guard jMu1 ∈ evalBgp jB1 jG
#guard jMu2 ∈ evalBgp jB2 jG
#guard bgpMatchesCheck jMu (jB1 ++ jB2) jG
-- …and the join really is a restriction: swapping the two IRIs is not
-- a match, so the pivot is not the everything-relation.
#guard ! bgpMatchesCheck [("x", .iri (jI "b")), ("y", .iri (jI "a")),
                          ("z", .iri (jI "c"))] (jB1 ++ jB2) jG

/-- The witness join, as §18.5 states it: two rows of the two
evaluations, compatible, merging to `jMu`. -/
theorem jCompatible : Compatible jMu1 jMu2 := by
  intro v t1 t2 h1 h2
  simp only [sval, jMu1, jMu2, List.lookup] at h1 h2
  by_cases hy : v = "y"
  · subst hy
    simp only [beq_self_eq_true, show (("y" : String) == "z") = false from by decide] at h1 h2
    exact (Option.some.inj h1).symm.trans (Option.some.inj h2)
  · have hyb : (v == "y") = false := by simp [hy]
    by_cases hx : v = "x"
    · subst hx
      simp only [show (("x" : String) == "z") = false from by decide,
                 show (("x" : String) == "y") = false from by decide] at h2
      exact absurd h2 (by simp)
    · have hxb : (v == "x") = false := by simp [hx]
      simp only [hyb, hxb] at h1
      exact absurd h1 (by simp)

theorem jInJoin : InJoin (evalBgp jB1 jG) (evalBgp jB2 jG) jMu :=
  ⟨jMu1, jMu2, by decide, by decide, jCompatible,
   SPARQL.AlgebraRefinement.merge_isMerge jMu2 jMu1⟩

private theorem jG_ttFree : RDF.GraphTtFree jG := by
  intro t ht
  simp only [jG, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp [RDF.TermTtFree]

private theorem jB1_ttFree : BgpTtFree jB1 := by
  intro tp htp
  simp only [jB1, List.mem_singleton] at htp
  subst htp; exact ⟨trivial, trivial, trivial⟩

private theorem jB2_ttFree : BgpTtFree jB2 := by
  intro tp htp
  simp only [jB2, List.mem_singleton] at htp
  subst htp; exact ⟨trivial, trivial, trivial⟩

/-- A real join answer, through the unconditional chain. -/
theorem unified_join_answer_witness :
    Answers condTrue termEqSchema [rdfToTheorySk jG]
      (sparqlBgpToQuery (jB1 ++ jB2)) jMu :=
  unified_join_answers jInJoin

/-- And not of everything: the reversed mapping is refuted, through the
gate's ← direction. -/
theorem unified_join_no_answer :
    ¬ Answers condTrue termEqSchema [rdfToTheorySk jG]
        (sparqlBgpToQuery (jB1 ++ jB2))
        [("x", .iri (jI "b")), ("y", .iri (jI "a")), ("z", .iri (jI "c"))] := by
  intro h
  have hm := (unified_adequate_join jB1 jB2 jG _ jG_ttFree jB1_ttFree jB2_ttFree).mpr h
  exact absurd (bgpMatchesCheck_iff.mpr (bgpMatches_append.mpr hm)) (by decide)

end JoinWitnesses

/-! ## UNION — §18.5

`Union(Ω₁, Ω₂) = { μ | μ ∈ Ω₁ or μ ∈ Ω₂ }`. There is no basic graph
pattern whose query is the union, so `UQuery` cannot carry it: the
union enters as the DISJUNCTION of the two instantiated bodies, and
`AnswersUnion` is entailment of that disjunction.

That makes the gate a claim that has to be earned rather than
transcribed. `Γ ⊨ A ∨ B` does NOT in general give `Γ ⊨ A` or
`Γ ⊨ B` — `entailsSchema_disj_does_not_split` below exhibits a premise
list where it fails. It DOES hold for the premise list this stage
uses, because `herbQ g` is a canonical model of `rdfToTheorySk g`: a
disjunction true in every model of the graph is true in that one, and
there one disjunct is true outright. So `unified_adequate_union` is a
full iff, and the reason is a property of the RDF premise class, not
of `EntailsSchema`. -/

/-- The union of two BGP bodies under one solution mapping. -/
def bgpDisjBody (mu : Binding) (b1 b2 : Bgp) : CL.Sentence :=
  .disj [bgpBody mu b1, bgpBody mu b2]

/-- μ answers the UNION of two basic graph patterns: the disjunction of
their instantiated bodies is entailed. -/
def AnswersUnion (conds : CL.Interp → Prop) (S : Schema)
    (premises : List CL.Sentence) (b1 b2 : Bgp) (mu : Binding) : Prop :=
  EntailsSchema conds S premises (bgpDisjBody mu b1 b2)

theorem satisfies_bgpDisjBody_iff (i : CL.Interp) (mu : Binding) (b1 b2 : Bgp) :
    CL.Satisfies i (bgpDisjBody mu b1 b2) ↔
      (CL.Satisfies i (bgpBody mu b1) ∨ CL.Satisfies i (bgpBody mu b2)) := by
  simp only [CL.Satisfies, bgpDisjBody, CL.Sat, CL.SatAny, or_false]

/-- **The disjunction of answers is an answer to the union**, for every
condition bundle, schema and premise list. UNCONDITIONAL, and only one
direction: the converse is `entailsSchema_disj_does_not_split`. -/
theorem answers_union_of_or {conds : CL.Interp → Prop} {S : Schema}
    {premises : List CL.Sentence} {b1 b2 : Bgp} {mu : Binding}
    (h : Answers conds S premises (sparqlBgpToQuery b1) mu ∨
         Answers conds S premises (sparqlBgpToQuery b2) mu) :
    AnswersUnion conds S premises b1 b2 mu := by
  intro i hc hs hp
  rw [satisfies_bgpDisjBody_iff]
  rcases h with h | h
  · exact Or.inl (h i hc hs hp)
  · exact Or.inr (h i hc hs hp)

/-- **The UNION gate** — a FULL iff.

The ← direction is where the work is: it instantiates the entailment at
`herbQ g`, the term model in which "true" means "a triple of `g`", and
reads one disjunct back off with `patternAtom_reflect`. That step is
what a general `EntailsSchema` does not license.

Hypotheses: the stage 6 gate's guards on each side, and no others. **No
multiplicity is claimed** — `InUnion` is `Occurs` in either operand,
and §18.5's union ADDS cardinalities, which nothing here states. -/
theorem unified_adequate_union (b1 b2 : Bgp) (g : RDF.Graph) (mu : Binding)
    (hg : RDF.GraphTtFree g) (hb1 : BgpTtFree b1) (hb2 : BgpTtFree b2) :
    (BgpMatches mu b1 g ∨ BgpMatches mu b2 g) ↔
      AnswersUnion condTrue termEqSchema [rdfToTheorySk g] b1 b2 mu := by
  constructor
  · intro h
    refine answers_union_of_or ?_
    rcases h with h | h
    · exact Or.inl (bgp_matches_answers h)
    · exact Or.inr (bgp_matches_answers h)
  · intro hA
    have hsat : CL.Satisfies (herbQ g) (bgpDisjBody mu b1 b2) :=
      hA (herbQ g) trivial (herbQ_satisfiesSchema g) (fun s hs => by
        obtain rfl := List.mem_singleton.mp hs
        exact herbQ_satisfies_sk g hg)
    rcases (satisfies_bgpDisjBody_iff (herbQ g) mu b1 b2).mp hsat with h | h
    · exact Or.inl (fun tp htp => patternAtom_reflect (hb1 tp htp) hg
        ((satisfies_bgpBody_iff (herbQ g) mu b1).mp h tp htp))
    · exact Or.inr (fun tp htp => patternAtom_reflect (hb2 tp htp) hg
        ((satisfies_bgpBody_iff (herbQ g) mu b2).mp h tp htp))

/-! ### From §18.5's `InUnion` -/

/-- `SMapEq` is `Extends` in both directions. -/
theorem extends_of_smapEq {mu mu' : SMap}
    (h : SPARQL.AlgebraSpec.SMapEq mu mu') : SPARQL.Extends mu' mu := by
  intro v t hv
  rw [SPARQL.AlgebraRefinement.binding_lookup_eq_sval] at hv ⊢
  rw [h v]; exact hv

/-- **§18.5's `InUnion` over two BGP evaluations gives the pivot on one
side.** UNCONDITIONAL. -/
theorem inUnion_bgpMatches {b1 b2 : Bgp} {g : RDF.Graph} {mu : Binding}
    (hu : SPARQL.AlgebraSpec.InUnion (evalBgp b1 g) (evalBgp b2 g) mu) :
    BgpMatches mu b1 g ∨ BgpMatches mu b2 g := by
  rcases hu with ⟨mu', hmem, heq⟩ | ⟨mu', hmem, heq⟩
  · exact Or.inl (bgpMatches_mono (extends_of_smapEq heq) (bgp_eval_sound hmem))
  · exact Or.inr (bgpMatches_mono (extends_of_smapEq heq) (bgp_eval_sound hmem))

/-- **A §18.5 union row is a unified answer to the union.**
UNCONDITIONAL. -/
theorem unified_union_answers {b1 b2 : Bgp} {g : RDF.Graph} {mu : Binding}
    (hu : SPARQL.AlgebraSpec.InUnion (evalBgp b1 g) (evalBgp b2 g) mu) :
    AnswersUnion condTrue termEqSchema [rdfToTheorySk g] b1 b2 mu := by
  rcases inUnion_bgpMatches hu with h | h
  · exact answers_union_of_or (Or.inl (bgp_matches_answers h))
  · exact answers_union_of_or (Or.inr (bgp_matches_answers h))

/-- A row of the RUNNING engine's `union` is a unified answer.
UNCONDITIONAL — `SPARQL.union` is list append, so membership in it is
membership in one operand, with no compatibility test to be coarse
about. -/
theorem unified_union_engine_answers {b1 b2 : Bgp} {g : RDF.Graph} {mu : Binding}
    (h : mu ∈ SPARQL.union (evalBgp b1 g) (evalBgp b2 g)) :
    AnswersUnion condTrue termEqSchema [rdfToTheorySk g] b1 b2 mu :=
  unified_union_answers
    ((SPARQL.AlgebraRefinement.occurs_append).mp
      (SPARQL.AlgebraSpec.occurs_of_mem h))

/-! ### Non-vacuity, and the exact strength of the UNION gate -/

section UnionWitnesses

private def uG1 : RDF.Graph := [{ s := .iri (jI "a"), p := jI "p", o := .iri (jI "b") }]
private def uG2 : RDF.Graph := [{ s := .iri (jI "c"), p := jI "q", o := .iri (jI "d") }]

/-- A graph neither branch matches. -/
private def uG3 : RDF.Graph := [{ s := .iri (jI "b"), p := jI "p", o := .iri (jI "a") }]

private def uB1 : Bgp := [{ s := .iri (jI "a"), p := .iri (jI "p"), o := .iri (jI "b") }]
private def uB2 : Bgp := [{ s := .iri (jI "c"), p := .iri (jI "q"), o := .iri (jI "d") }]

-- Each pattern matches its own graph and neither matches the other's.
#guard bgpMatchesCheck [] uB1 uG1
#guard bgpMatchesCheck [] uB2 uG2
#guard ! bgpMatchesCheck [] uB1 uG2
#guard ! bgpMatchesCheck [] uB2 uG1
#guard ! bgpMatchesCheck [] uB1 uG3
#guard ! bgpMatchesCheck [] uB2 uG3

private theorem uG1_ttFree : RDF.GraphTtFree uG1 := by
  intro t ht
  simp only [uG1, List.mem_singleton] at ht
  subst ht; simp [RDF.TermTtFree]

private theorem uG2_ttFree : RDF.GraphTtFree uG2 := by
  intro t ht
  simp only [uG2, List.mem_singleton] at ht
  subst ht; simp [RDF.TermTtFree]

private theorem uG3_ttFree : RDF.GraphTtFree uG3 := by
  intro t ht
  simp only [uG3, List.mem_singleton] at ht
  subst ht; simp [RDF.TermTtFree]

private theorem uB1_ttFree : BgpTtFree uB1 := by
  intro tp htp
  simp only [uB1, List.mem_singleton] at htp
  subst htp; exact ⟨trivial, trivial, trivial⟩

private theorem uB2_ttFree : BgpTtFree uB2 := by
  intro tp htp
  simp only [uB2, List.mem_singleton] at htp
  subst htp; exact ⟨trivial, trivial, trivial⟩

/-- The term model of a graph satisfies the body of a pattern that
matches it. -/
private theorem herbQ_sat_body {b : Bgp} {g : RDF.Graph} (hg : RDF.GraphTtFree g)
    (h : BgpMatches [] b g) : CL.Satisfies (herbQ g) (bgpBody [] b) :=
  bgp_matches_answers h (herbQ g) trivial (herbQ_satisfiesSchema g) (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact herbQ_satisfies_sk g hg)

/-- The term model of a graph REFUTES the body of a pattern that does
not match it (on the triple-term-free fragment). -/
private theorem herbQ_refutes_body {b : Bgp} {g : RDF.Graph} (hg : RDF.GraphTtFree g)
    (hb : BgpTtFree b) (h : ¬ BgpMatches [] b g) :
    ¬ CL.Satisfies (herbQ g) (bgpBody [] b) := by
  intro hsat
  exact h (fun tp htp => patternAtom_reflect (hb tp htp) hg
    ((satisfies_bgpBody_iff (herbQ g) [] b).mp hsat tp htp))

/-- **`EntailsSchema` does NOT let a disjunction split.** The premise
list `[A ∨ B]` entails `A ∨ B` and neither disjunct, so the ← direction
of `unified_adequate_union` is a property of the premise list
`[rdfToTheorySk g]` — it has a canonical model — and not a general fact
about entailment. Recording this is what stops the gate being read as
"an answer to a UNION is an answer to one of its branches" in general.

The two refutations are the term models of the two graphs, each
satisfying its own branch and refuting the other. -/
theorem entailsSchema_disj_does_not_split :
    EntailsSchema condTrue termEqSchema [bgpDisjBody [] uB1 uB2]
      (bgpDisjBody [] uB1 uB2) ∧
    ¬ EntailsSchema condTrue termEqSchema [bgpDisjBody [] uB1 uB2] (bgpBody [] uB1) ∧
    ¬ EntailsSchema condTrue termEqSchema [bgpDisjBody [] uB1 uB2] (bgpBody [] uB2) := by
  have hsat2 : CL.Satisfies (herbQ uG2) (bgpDisjBody [] uB1 uB2) :=
    (satisfies_bgpDisjBody_iff _ _ _ _).mpr
      (Or.inr (herbQ_sat_body uG2_ttFree (bgpMatchesCheck_iff.mp (by rfl))))
  have hsat1 : CL.Satisfies (herbQ uG1) (bgpDisjBody [] uB1 uB2) :=
    (satisfies_bgpDisjBody_iff _ _ _ _).mpr
      (Or.inl (herbQ_sat_body uG1_ttFree (bgpMatchesCheck_iff.mp (by rfl))))
  refine ⟨fun i _ _ hp => hp _ (by simp), ?_, ?_⟩
  · intro hE
    exact herbQ_refutes_body uG2_ttFree uB1_ttFree
      (fun hm => absurd (bgpMatchesCheck_iff.mpr hm) (by decide))
      (hE (herbQ uG2) trivial (herbQ_satisfiesSchema uG2) (fun s hs => by
        obtain rfl := List.mem_singleton.mp hs; exact hsat2))
  · intro hE
    exact herbQ_refutes_body uG1_ttFree uB2_ttFree
      (fun hm => absurd (bgpMatchesCheck_iff.mpr hm) (by decide))
      (hE (herbQ uG1) trivial (herbQ_satisfiesSchema uG1) (fun s hs => by
        obtain rfl := List.mem_singleton.mp hs; exact hsat1))

/-- A real union answer: `uB1` matches `uG1`, so the union does. -/
theorem unified_union_answer_witness :
    AnswersUnion condTrue termEqSchema [rdfToTheorySk uG1] uB1 uB2 [] :=
  (unified_adequate_union uB1 uB2 uG1 [] uG1_ttFree uB1_ttFree uB2_ttFree).mp
    (Or.inl (bgpMatchesCheck_iff.mp (by rfl)))

/-- And not of everything: over a graph neither branch matches, the
union is refuted. -/
theorem unified_union_no_answer :
    ¬ AnswersUnion condTrue termEqSchema [rdfToTheorySk uG3] uB1 uB2 [] := by
  intro h
  rcases (unified_adequate_union uB1 uB2 uG3 [] uG3_ttFree uB1_ttFree uB2_ttFree).mpr h
    with hm | hm
  · exact absurd (bgpMatchesCheck_iff.mpr hm) (by decide)
  · exact absurd (bgpMatchesCheck_iff.mpr hm) (by decide)

end UnionWitnesses

/-! ## FILTER — §18.5, and what a unified `Answers` claim cannot say

`Filter(expr, Ω) = { μ | μ ∈ Ω and expr(μ) has an effective boolean
value of true }`. `SPARQL/AlgebraSpec.lean` states it PARAMETRICALLY in
`FExpr := SMap → Bool`, exactly as §18.5 does, because §17's effective
boolean value is outside the algebra fragment.

Two things follow, and both are stated rather than glossed.

**What holds.** The filter condition is a predicate on the SOLUTION
MAPPING alone. It therefore rides alongside the gate:
`unified_adequate_filter` is a full iff whose filter conjunct appears
unchanged on both sides, and `inFilter_answers` takes a §18.5 filter
row to a unified answer plus that conjunct. Neither theorem gives the
filter any model-theoretic content, and neither pretends to.

**What does not hold, and cannot.** No claim of the shape "the filter's
answers are the entailments of a sentence built from the query body"
is available. `answers_congr_onVars` proves that `Answers` reads the
mapping ONLY through the variables of the pattern — two mappings
agreeing there produce the SAME sentence, hence the same verdict for
every condition bundle, schema and premise list — while a filter
expression reads the whole mapping, `?z ∉ vars(P)` included (§17.4.1.1
`bound`). `filter_not_determined_by_the_query_sentence` turns that into
a refutation: for EVERY function `φ` from sentences to sentences, the
claim "`φ (bgpBody μ b)` is entailed exactly when the filter passes"
is false. `SPARQL/AlgebraRefinement.lean`'s `FExprCongr` is the
algebra-layer counterpart — it assumes congruence up to `SMapEq`,
which is agreement on ALL variables, not on the pattern's.

That is the precise negative result this stage reaches for FILTER, and
it is why the filter stays a side condition on the mapping. -/

open L4Factoidal.SPARQL.AlgebraSpec (FExpr InFilter) in
/-- **A §18.5 filter row is a unified answer plus its side condition.**
UNCONDITIONAL. -/
theorem inFilter_answers {f : FExpr} {b : Bgp} {g : RDF.Graph} {mu : Binding}
    (h : InFilter f (evalBgp b g) mu) :
    Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu ∧
      f mu = true := by
  obtain ⟨⟨mu', hmem, heq⟩, hf⟩ := h
  exact ⟨bgp_matches_answers
    (bgpMatches_mono (extends_of_smapEq heq) (bgp_eval_sound hmem)), hf⟩

open L4Factoidal.SPARQL.AlgebraSpec (FExpr) in
/-- **The FILTER gate.** A full iff — and the filter conjunct is the
same on both sides, because `f μ` is a predicate on the mapping and
has no reading in an interpretation. Stated so that no reader takes the
theorem for more than it is. -/
theorem unified_adequate_filter (f : FExpr) (b : Bgp) (g : RDF.Graph)
    (mu : Binding) (hg : RDF.GraphTtFree g) (hb : BgpTtFree b) :
    (BgpMatches mu b g ∧ f mu = true) ↔
      (Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu ∧
        f mu = true) :=
  and_congr_left (fun _ => unified_adequate_bgp b g mu hg hb)

/-! ### `Answers` sees only the pattern's variables -/

theorem embedPatternTerm_congr {mu mu' : Binding} : ∀ (pt : SPARQL.PatternTerm),
    (∀ v ∈ patternTermVars pt, mu.lookup v = mu'.lookup v) →
    embedPatternTerm mu pt = embedPatternTerm mu' pt
  | .var v, h => by
      simp only [embedPatternTerm, h v (by simp [patternTermVars])]
  | .iri _, _ => rfl
  | .bnode _, _ => rfl
  | .literal _, _ => rfl
  | .tripleTerm a b c, h => by
      simp only [embedPatternTerm]
      rw [embedPatternTerm_congr a (fun v hv => h v (by
            simp only [patternTermVars]; exact List.mem_append_left _ (List.mem_append_left _ hv))),
          embedPatternTerm_congr b (fun v hv => h v (by
            simp only [patternTermVars]
            exact List.mem_append_left _ (List.mem_append_right _ hv))),
          embedPatternTerm_congr c (fun v hv => h v (by
            simp only [patternTermVars]; exact List.mem_append_right _ hv))]

theorem embedPatternSubject_congr {mu mu' : Binding} : ∀ (ps : SPARQL.PatternSubject),
    (∀ v ∈ patternSubjectVars ps, mu.lookup v = mu'.lookup v) →
    embedPatternSubject mu ps = embedPatternSubject mu' ps
  | .var v, h => by
      simp only [embedPatternSubject, h v (by simp [patternSubjectVars])]
  | .iri _, _ => rfl
  | .bnode _, _ => rfl
  | .tripleTerm a b c, h => by
      simp only [embedPatternSubject]
      rw [embedPatternTerm_congr a (fun v hv => h v (by
            simp only [patternSubjectVars]
            exact List.mem_append_left _ (List.mem_append_left _ hv))),
          embedPatternTerm_congr b (fun v hv => h v (by
            simp only [patternSubjectVars]
            exact List.mem_append_left _ (List.mem_append_right _ hv))),
          embedPatternTerm_congr c (fun v hv => h v (by
            simp only [patternSubjectVars]; exact List.mem_append_right _ hv))]

theorem patternAtom_congr {mu mu' : Binding} {tp : SPARQL.TriplePattern}
    (h : ∀ v ∈ tpVars tp, mu.lookup v = mu'.lookup v) :
    patternAtom mu tp = patternAtom mu' tp := by
  simp only [patternAtom]
  rw [embedPatternSubject_congr tp.s (fun v hv => h v (by
        simp only [tpVars]; exact List.mem_append_left _ (List.mem_append_left _ hv))),
      embedPatternTerm_congr tp.p (fun v hv => h v (by
        simp only [tpVars]; exact List.mem_append_left _ (List.mem_append_right _ hv))),
      embedPatternTerm_congr tp.o (fun v hv => h v (by
        simp only [tpVars]; exact List.mem_append_right _ hv))]

/-- **The instantiated body depends on the mapping only through the
pattern's own variables.** A SYNTACTIC equality of sentences, so it
transfers to every claim about them at once. -/
theorem bgpBody_congr {mu mu' : Binding} : ∀ (b : Bgp),
    (∀ v ∈ bgpVars b, mu.lookup v = mu'.lookup v) →
    bgpBody mu b = bgpBody mu' b
  | [], _ => rfl
  | tp :: rest, h => by
      have hrest : bgpBody mu rest = bgpBody mu' rest :=
        bgpBody_congr rest (fun v hv => h v (by
          simp only [bgpVars, List.flatMap_cons]; exact List.mem_append_right _ hv))
      have htp : patternAtom mu tp = patternAtom mu' tp :=
        patternAtom_congr (fun v hv => h v (by
          simp only [bgpVars, List.flatMap_cons]; exact List.mem_append_left _ hv))
      have hlist : List.map (patternAtom mu) rest = List.map (patternAtom mu') rest := by
        simpa only [bgpBody, CL.Sentence.conj.injEq] using hrest
      simp only [bgpBody, List.map_cons, htp, hlist]

/-- **`Answers` cannot see a variable outside the pattern.** For every
condition bundle, schema and premise list. -/
theorem answers_congr_onVars {conds : CL.Interp → Prop} {S : Schema}
    {premises : List CL.Sentence} {b : Bgp} {mu mu' : Binding}
    (h : ∀ v ∈ bgpVars b, mu.lookup v = mu'.lookup v) :
    Answers conds S premises (sparqlBgpToQuery b) mu ↔
      Answers conds S premises (sparqlBgpToQuery b) mu' := by
  simp only [Answers, UQuery.instantiate, sparqlBgpToQuery, bgpBody_congr b h]

/-! ### The refutation -/

section FilterWitnesses

private def fB : Bgp := [{ s := .var "x", p := .iri (jI "p"), o := .iri (jI "b") }]
private def fMu  : Binding := [("x", .iri (jI "a")), ("z", .iri (jI "c"))]
private def fMu' : Binding := [("x", .iri (jI "a"))]

/-- `bound(?z)` — §17.4.1.1, on a variable the pattern does not
mention. -/
private def fF : SPARQL.AlgebraSpec.FExpr := fun mu => (sval "z" mu).isSome

#guard fF fMu
#guard ! fF fMu'
-- Both mappings match the pattern; the filter keeps one and drops the
-- other.
#guard bgpMatchesCheck fMu fB jG
#guard bgpMatchesCheck fMu' fB jG

/-- The two mappings instantiate the pattern to the SAME sentence. -/
theorem fBody_eq : bgpBody fMu fB = bgpBody fMu' fB := rfl

/-- **FILTER is not determined by the query sentence.** For EVERY
function `φ` from sentences to sentences — that is, for every claim of
the form "the filter passes exactly when this sentence, built from the
instantiated body, is entailed" — the claim is false. `fMu` and `fMu'`
instantiate the pattern identically, so `φ` cannot separate them, while
`bound(?z)` does.

This is the negative result the FILTER stage reaches. It does not say
FILTER is unstateable; it says the filter conjunct in
`unified_adequate_filter` cannot be replaced by an entailment, and so
must stay a side condition on the mapping. -/
theorem filter_not_determined_by_the_query_sentence
    (φ : CL.Sentence → CL.Sentence) (premises : List CL.Sentence)
    (conds : CL.Interp → Prop) (S : Schema) :
    ¬ (∀ mu : Binding,
        EntailsSchema conds S premises (φ (bgpBody mu fB)) ↔ fF mu = true) := by
  intro h
  have h1 : EntailsSchema conds S premises (φ (bgpBody fMu fB)) := (h fMu).mpr (by decide)
  rw [fBody_eq] at h1
  have h2 : fF fMu' = true := (h fMu').mp h1
  exact absurd h2 (by decide)

end FilterWitnesses

/-! ## Axiom audits -/

section Audits

#print axioms bgpMatches_append
#print axioms answers_bgp_append_iff
#print axioms unified_adequate_join
#print axioms unified_adequate_join_conj
#print axioms bgpMatches_mono
#print axioms extends_of_isMerge_left
#print axioms extends_of_isMerge_right
#print axioms inJoin_bgpMatches
#print axioms unified_join_answers
#print axioms unified_join_engine_answers
#print axioms jCompatible
#print axioms jInJoin
#print axioms unified_join_answer_witness
#print axioms unified_join_no_answer
#print axioms satisfies_bgpDisjBody_iff
#print axioms answers_union_of_or
#print axioms unified_adequate_union
#print axioms extends_of_smapEq
#print axioms inUnion_bgpMatches
#print axioms unified_union_answers
#print axioms unified_union_engine_answers
#print axioms entailsSchema_disj_does_not_split
#print axioms unified_union_answer_witness
#print axioms unified_union_no_answer
#print axioms inFilter_answers
#print axioms unified_adequate_filter
#print axioms bgpBody_congr
#print axioms answers_congr_onVars
#print axioms fBody_eq
#print axioms filter_not_determined_by_the_query_sentence

end Audits

end L4Factoidal.Unified
