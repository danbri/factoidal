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

end Audits

end L4Factoidal.Unified
