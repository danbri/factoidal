/-
L4Factoidal.Unified.OwlRlAdequacy — the stage 4 gate theorems for
OWL 2 RL under the unified LBase/IKL model theory.

Stage 4 of https://github.com/danbri/factoidal/issues/598, design
document `docs/designissues/2026-08-25-unified-semantics-lean.md` §4.4.

## What is proved here, and at what strength

* **`unified_owlRl_sound`** — the full soundness gate. Every triple the
  RL rule relation derives from a reserved-vocabulary-free graph is
  entailed by the graph's translation, relative to `owlRlSchema` and
  the interpretation-class condition `OwlRlInterpCond` that carries the
  FIVE rows `Unified/OwlRlSchema.lean` does not state as
  object-language sentences (nine before 2026-08-26; the four
  cardinality-literal rows moved into the schema when
  `Unified/Datalog.lean` gained `DTerm.lit`, and
  `owlRlSchema_cardinality_rows` pins them there). The claim is
  exactly as strong as that pair, no stronger: `OwlRlInterpCond` is a
  hypothesis on the interpretation, visible in the statement.
* **`unified_owlRl_clash_unsat` / `unified_owlRl_clash_entails_all`** —
  a graph carrying a `Clash` configuration has no model in the schema
  class, so its translation entails everything.
* **`owlRl_complete_ground`** — ground completeness against the
  CONDITION bundle: on the `RLHerbrand` fragment, a ground triple true
  in every RDF interpretation meeting `RlConditions` and
  `RlClashConditions` that satisfies the saturated closure IS a triple
  of that closure. The countermodel is `rlHerb` and the last step is
  `rlHerb_triple_decode`.

## The Herbrand fragment, and what does NOT widen it

`RlHerbFrag` clause (a) — every object is an IRI or a blank node —
excludes every graph whose closure carries a cardinality literal.
`DTerm.lit` does not widen it, and the reason is worth stating because
the opposite was expected
(https://github.com/danbri/factoidal/issues/613 item 3). Clause (a)
exists for eq-ref, object form: `RlCondEqRefO` demands
`y owl:sameAs y` for every object `y`, and `rlHerb`'s `iext` reads
"the triple is in the graph", so `y` must be expressible as an
`RDF.Subject`. RDF 1.1 Concepts §3.1 gives a triple an IRI or a blank
node as subject, never a literal. The obstruction is the RDF term
algebra reproduced in the syntactic model — `frag_obj_subject` is
consumed at fifteen sites of `rlHerb_conditions` — not the Datalog
term type. Widening past clause (a) needs a different `rlHerbIext` for
the `owl:sameAs` row, and then `rlHerb_triple_decode` would decode an
atom that the RL `Derives` relation cannot produce. Recorded, not
attempted.

## The completeness gap, stated exactly

The design document asks for `unified_owlRl_complete_ground` over
`EntailsSchema … owlRlSchema`, i.e. with the countermodel supplied as a
CL interpretation `liftInterp (rlHerb c)`. That step is NOT taken here.
The obstruction is precise and is not a missing tactic:

`liftInterp r` reads a binary predication as `r.iext p.2 x.2 y.2`, so
satisfaction of a row's universally closed implication at
`liftInterp r` quantifies EVERY position — the predicate position
included — over the whole of `r.idom`. The `RlCond*` rows quantify
their property and class parameters over `WfIri`. For `rlHerb c` the
full-domain reading is still true (a true atom of `rlHerbIext` has an
IRI predicate, and fragment clause (c) forces IRI endpoints on
`owl:disjointWith`), but establishing it is a second pass over all 79
rows, not a corollary of `rlHerb_conditions`. Recorded as a boundary
row rather than asserted.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.OwlRlSchema

namespace L4Factoidal.Unified

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## Soundness -/

/-- **Stage 4 gate, soundness.** Every triple `OWL.RL.Derives` emits
from a reserved-vocabulary-free graph is entailed by the graph's
translation, relative to `owlRlSchema` and `OwlRlInterpCond`.

The `RlReservedFree` hypothesis is the one `RLSemantics.lean` records as
load-bearing: a graph using the reserved `urn:cl:def:` predicates or the
comprehension blank-node labels can make the engine conflate a user
blank node with a comprehension witness, and soundness genuinely fails
there. The conclusion is the existential closure `rdfToTheory [t]`
because the comprehension rows mint blank nodes. -/
theorem unified_owlRl_sound {g : RDF.Graph} {t : RDF.Triple}
    (hres : RlReservedFree g) (h : OWL.RL.Derives g t) :
    EntailsSchema OwlRlInterpCond owlRlSchema [rdfToTheory g] (rdfToTheory [t]) := by
  intro i hc hS hsat
  obtain ⟨hcond, -⟩ := owlRlSchema_conditions hS hc
  have hg : RDF.Satisfies (restrictInterp i) g :=
    (satisfies_rdfToTheory_restrict i g).mp (hsat _ (by simp))
  obtain ⟨A, hA⟩ := hg
  refine (satisfies_rdfToTheory_restrict i [t]).mpr
    ⟨rlExtend (restrictInterp i) A, ?_⟩
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  subst hu
  exact rl_derives_holds hcond hres hA h

/-- A `Clash` configuration has no model in the schema class. The
`AdcMembersIri` hypothesis is the cax-adc row's IRI-member narrowing
(`RLSemantics.lean`'s `RlNCondCaxAdc`). -/
theorem unified_owlRl_clash_unsat {g : RDF.Graph} (hadc : AdcMembersIri g)
    (h : OWL.RL.Clash g) {i : CL.Interp} (hc : OwlRlInterpCond i)
    (hS : SatisfiesSchema i owlRlSchema) :
    ¬ CL.Satisfies i (rdfToTheory g) := by
  intro hsat
  obtain ⟨hcond, hclash⟩ := owlRlSchema_conditions hS hc
  obtain ⟨A, hA⟩ := (satisfies_rdfToTheory_restrict i g).mp hsat
  exact rl_clash_holds_false hclash hcond.listMemBase hcond.listMemStep
    hadc hA h

/-- Consequence: a clashing graph's translation entails every
sentence. -/
theorem unified_owlRl_clash_entails_all {g : RDF.Graph}
    (hadc : AdcMembersIri g) (h : OWL.RL.Clash g) (s : CL.Sentence) :
    EntailsSchema OwlRlInterpCond owlRlSchema [rdfToTheory g] s := by
  intro i hc hS hsat
  exact absurd (hsat _ (by simp)) (unified_owlRl_clash_unsat hadc h hc hS)

/-! ## Ground completeness against the condition bundle

The direction the design document calls T4-mediated. Stated over RDF
interpretations and the `RlCond*` bundle; the module header records why
the CL-interpretation form is not reached here. -/

/-- Entailment relative to the OWL 2 RL condition bundle, over RDF
interpretations: `RDF.EntailsUnder` at the bundle
`RlConditions ∧ RlClashConditions`. -/
def OwlRlEntailsMt (g h : RDF.Graph) : Prop :=
  ∀ i : RDF.Interp, RlConditions i → RlClashConditions i →
    RDF.Satisfies i g → RDF.Satisfies i h

/-- **Stage 4 gate, ground completeness (condition-bundle form).** On a
`Derives`-closed, clash-free `RLHerbrand` fragment graph, a ground
triple at a non-reserved predicate that the graph entails under the RL
condition bundle IS a triple of the graph.

With `RLTheorems`' T2/T4 this instantiates at `c := OWL.RL.closure g
fuel`, where `hcut` is saturation and `c` is the closure. The
hypotheses are the fragment `RLHerbrand.lean` states, not decoration:
`hfrag` clause (a) is what makes the cardinality rows vacuous in the
model, and `hcons` is what the falsity-headed rows need. -/
theorem owlRl_complete_ground {c : RDF.Graph}
    (hcut : ∀ {u : RDF.Triple}, OWL.RL.Derives c u → u ∈ c)
    (hfrag : RlHerbFrag c) (hcons : ¬ OWL.RL.Clash c)
    {t : RDF.Triple} (hp : rlReservedIri t.p = false)
    (htt : RDF.TermTtFree t.o) (hgr : RDF.tripleBnodes t = [])
    (h : OwlRlEntailsMt c [t]) : t ∈ c := by
  have hmodel : RDF.Satisfies (rlHerb c) c := by
    refine ⟨herbAssign c, ?_⟩
    intro u hu
    have hiris := frag_iris hfrag hu
    have := herb_encode (c := c) (s := u.s) (p := u.p) (o := u.o) (by
      cases u; exact hu)
    show (rlHerb c).iext ((rlHerb c).iIri u.p)
      (RDF.denotSubject (rlHerb c) (herbAssign c) u.s)
      (RDF.denotTerm (rlHerb c) (herbAssign c) u.o)
    rw [denotSubject_herbAssign, denotTerm_herbAssign c (frag_ttFree hfrag hu)]
    exact this
  obtain ⟨a, ha⟩ :=
    h (rlHerb c) (rlHerb_conditions hcut hfrag hcons)
      (rlHerb_clash_conditions hfrag hcons) hmodel
  -- the model is term-syntactic, so any assignment that verifies a
  -- GROUND triple verifies it under `herbAssign` too
  have hagree : RDF.AssignmentsAgreeOn (rlHerb c) (RDF.tripleBnodes t) a
      (herbAssign c) := by
    rw [hgr]
    intro b hb
    cases hb
  have hg : RDF.TripleHolds (rlHerb c) (herbAssign c) t :=
    (RDF.tripleHolds_agree (rlHerb c) hagree).mp (ha t (by simp))
  exact rlHerb_triple_decode hp htt hg

/-! ## Non-vacuity

A schema family that no interpretation can violate proves nothing. The
two witnesses below separate the Horn part from the clash part: the
all-true interpretation satisfies every Horn row and violates every
clash row; the all-false interpretation does the reverse on the rows
with a premise-free head. -/

/-- The all-false interpretation. -/
def allFalseInterp : CL.Interp where
  dom := Unit
  domWit := ()
  iName := fun _ => ()
  iStr := fun _ => ()
  rel := fun _ _ => False
  fn := fun _ _ => ()
  iProp := fun _ _ _ => ()

theorem allTrue_satisfies_horn : SatisfiesSchema allTrueInterp owlRlHornSchema := by
  rintro s ⟨row, rfl⟩
  rw [satisfies_ruleSentence_iff _ (rlRowRule_wf row)]
  intro f _
  exact trivial

theorem allTrue_satisfies_family :
    SatisfiesSchema allTrueInterp owlRlFamilySchema := by
  rintro s (⟨p, -, rfl⟩ | ⟨ci, cj, -, rfl⟩ | ⟨a, pr, b, -, rfl⟩ |
    ⟨d1, d2, d3, -, rfl⟩ | ⟨p, w, a, pr, b, -, -, -, rfl⟩)
  · rw [satisfies_ruleSentence_iff _ (ruleEqRefP_wf p)]; intro f _; exact trivial
  · rw [satisfies_ruleSentence_iff _ (ruleCaxAdcToDw_wf ci cj)]
    intro f _; exact trivial
  · rw [satisfies_ruleSentence_iff _ (ruleDtType1_wf a pr b)]
    intro f _; exact trivial
  · rw [satisfies_ruleSentence_iff _ (ruleDtRangeIntersect_wf d1 d2 d3)]
    intro f _; exact trivial
  · rw [satisfies_ruleSentence_iff _ (ruleXsdAxiom_wf p w a pr b)]
    intro f _; exact trivial

/-- The all-true interpretation satisfies both list-valued families at
every length — so `owlRlSeqSchema` is satisfiable and neither family is
empty of models. -/
theorem allTrue_satisfies_seq :
    SatisfiesSchema allTrueInterp owlRlSeqSchema := by
  rintro s (⟨m, rfl⟩ | ⟨m, rfl⟩)
  · rw [satisfies_ruleSentence_iff _ (spo2Rule_wf m)]; intro f _; exact trivial
  · rw [satisfies_ruleSentence_iff _ (keyRule_wf m)]; intro f _; exact trivial

/-- A counter-model for the list-valued families: a one-step chain
whose premises all hold and whose conclusion does not. Without a
witness like this, `owlRlSeqSchema` could be the everything-relation
and `owlRlSchema_seq_rows` would say nothing. -/
def spo2Counter : CL.Interp where
  dom := String
  domWit := ""
  iName := id
  iStr := id
  rel := fun p args =>
    (p = owlPropertyChainAxiom.val ∧ args = ["P", "L"]) ∨
    (p = rdfRest.val ∧ args = ["L", rdfNil.val]) ∨
    (p = rdfFirst.val ∧ args = ["L", "Q"]) ∨
    (p = "Q" ∧ args = ["A", "B"])
  fn := fun _ _ => ""
  iProp := fun _ _ _ => ""

/-- **The list-valued families exclude something.** `spo2Counter`
satisfies every premise of prp-spo2 at chain length 1 and denies its
conclusion, so it is not a model of `owlRlSeqSchema`. -/
theorem seqSchema_not_everything :
    ¬ SatisfiesSchema spo2Counter owlRlSeqSchema := by
  intro h
  have hr := (satisfies_ruleSentence_iff _ (spo2Rule_wf 0)).mp
    (h _ (Or.inl ⟨0, rfl⟩))
  have hhead := hr (seqVal (d := spo2Counter.dom) "" (fun _ => "L")
      (fun _ => "Q") (fun k => if k = 0 then "A" else "B") "P" "" "") ?_
  · rw [show (spo2Rule 0).head
          = dbin (.v nmP) (.v (nmV 0)) (.v (nmV 1)) from rfl] at hhead
    simp only [DAtom.Holds, dbin, List.map_cons, List.map_nil, dv_val] at hhead
    erw [seqVal_P, seqVal_V, seqVal_V] at hhead
    simp [spo2Counter] at hhead
  · intro a ha
    simp only [spo2Rule, List.mem_cons, List.mem_append, List.mem_flatMap,
               List.mem_map, List.mem_range, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | ⟨⟨k, hk, (rfl | rfl)⟩ | ⟨k, hk, rfl⟩⟩
    · simp only [DAtom.Holds, dbin, List.map_cons, List.map_nil, dv_val,
                 DTerm.val, dk]
      erw [seqVal_P, seqVal_L]
      exact Or.inl ⟨rfl, rfl⟩
    · simp only [DAtom.Holds, dbin, List.map_cons, List.map_nil, dv_val,
                 DTerm.val, dk]
      erw [seqVal_L]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · simp only [DAtom.Holds, dbin, List.map_cons, List.map_nil, dv_val,
                 DTerm.val, dk]
      erw [seqVal_L, seqVal_Q]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · obtain rfl : k = 0 := by omega
      simp only [DAtom.Holds, dbin, List.map_cons, List.map_nil, dv_val]
      erw [seqVal_Q, seqVal_V, seqVal_V]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact absurd hk (Nat.not_lt_zero k)

/-- **Separating model, clash side**: the all-true interpretation does
NOT satisfy the clash schema. The clash family therefore excludes
something — it is not vacuously satisfied. -/
theorem allTrue_violates_clash :
    ¬ SatisfiesSchema allTrueInterp owlRlClashSchema := by
  intro h
  have hs := h _ (Or.inl ⟨.clsNothing2, rfl⟩)
  rw [satisfies_negSentence_iff _ (rlNegRowRule_wf .clsNothing2)] at hs
  exact hs (fun _ => ()) (fun _ _ => trivial)

theorem allFalse_no_atom (f : String → allFalseInterp.dom) (a : DAtom) :
    ¬ a.Holds allFalseInterp f := id

theorem exists_mem_of_ne_nil {α : Type} : ∀ {l : List α}, l ≠ [] → ∃ a, a ∈ l
  | [], h => absurd rfl h
  | x :: _, _ => ⟨x, by simp⟩

theorem allFalse_satisfies_clash :
    SatisfiesSchema allFalseInterp owlRlClashSchema := by
  rintro s (⟨row, rfl⟩ | ⟨c1, c2, -, rfl⟩)
  · rw [satisfies_negSentence_iff _ (rlNegRowRule_wf row)]
    intro f hb
    have hne : (rlNegRowRule row).atoms ≠ [] := by
      cases row <;> simp [rlNegRowRule]
    obtain ⟨a, ha⟩ := exists_mem_of_ne_nil hne
    exact allFalse_no_atom f a (hb a ha)
  · rw [satisfies_negSentence_iff _ (negCaxAdc_wf c1 c2)]
    intro f hb
    have hne : (negCaxAdc c1 c2).atoms ≠ [] := by simp [negCaxAdc]
    obtain ⟨a, ha⟩ := exists_mem_of_ne_nil hne
    exact allFalse_no_atom f a (hb a ha)

/-- **Separating model, Horn side**: the all-false interpretation does
NOT satisfy the Horn schema — cls-thing has a premise-free head. The
Horn family therefore asserts something. -/
theorem allFalse_violates_horn :
    ¬ SatisfiesSchema allFalseInterp owlRlHornSchema := by
  intro h
  have hs := h _ (hornSchema_mem .clsThing)
  rw [satisfies_ruleSentence_iff _ (rlRowRule_wf .clsThing)] at hs
  exact (hs (fun _ => ()) (by intro a ha; simp [rlRowRule] at ha) : False)

/-- The schema class is not empty on either half alone. The union is
satisfiable too — `owlRl_complete_ground`'s `rlHerb` model witnesses
that for any clash-free fragment graph. -/
theorem owlRlHornSchema_satisfiable :
    ∃ i : CL.Interp, SatisfiesSchema i owlRlHornSchema :=
  ⟨allTrueInterp, allTrue_satisfies_horn⟩

theorem owlRlClashSchema_satisfiable :
    ∃ i : CL.Interp, SatisfiesSchema i owlRlClashSchema :=
  ⟨allFalseInterp, allFalse_satisfies_clash⟩

/-! ## Axiom audit -/

#print axioms unified_owlRl_sound
#print axioms unified_owlRl_clash_unsat
#print axioms unified_owlRl_clash_entails_all
#print axioms owlRl_complete_ground
#print axioms owlRlSchema_conditions
#print axioms owlRlSchema_cardinality_rows
#print axioms owlRlSchema_seq_rows
#print axioms cond_prpSpo2
#print axioms cond_prpKey
#print axioms allTrue_satisfies_seq
#print axioms seqSchema_not_everything
#print axioms allTrue_violates_clash
#print axioms allFalse_violates_horn

end L4Factoidal.Unified
