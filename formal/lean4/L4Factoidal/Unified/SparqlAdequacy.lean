/-
L4Factoidal.Unified.SparqlAdequacy — BGP matching and the entailment
regimes as satisfaction over the unified model theory.

Stage 6 of https://github.com/danbri/factoidal/issues/598, design
document `docs/designissues/2026-08-25-unified-semantics-lean.md`
§4.6. `Unified/SparqlQuery.lean` carries the definitions and the
syntactic bridge; this module carries the theorems.

## The architecture, and why the design document's single iff split

§4.6 proposes ONE theorem,

    μ ∈ evalBgp b g ↔ (μ.domExact b ∧ μ.rangeIn g ∧ Entails …)

Membership in `evalBgp b g` is LIST membership of a `Binding`, which
is a `List (VarName × Term)`. Two facts make the right-hand side
unable to characterise it:

* **Order.** The evaluator conses bindings as it walks subject →
  predicate → object, left to right through the pattern list, so the
  mapping it returns is one particular PERMUTATION of the pairs. A
  semantic condition cannot see the order.
* **Coarseness.** `tryBindTerm`'s already-bound arm keeps the FIRST
  term bound to a variable and only compares the graph's own term to
  it with `Term.eqb`. So a returned mapping's terms need not be
  structurally the terms of `g`, only engine-equal to them
  (`SPARQL/BgpRefinement.lean`'s header records the same point for
  its conclusion).

Landed instead: a PIVOT and two theorems that meet at it.
`Unified.BgpMatches μ b g` says every pattern instantiates under μ into
`g` by engine equality. Then

* `unified_adequate_bgp` — `BgpMatches μ b g ↔ Answers …`, a full iff,
  the model-theoretic gate;
* `bgp_eval_sound` — `μ ∈ evalBgp b g → BgpMatches μ b g`,
  unconditional;
* `bgp_eval_complete` — `BgpMatches μ b g` plus a domain condition
  gives a mapping the evaluator RETURNS which agrees with μ up to
  `Term.eqb`.

`unified_adequate_bgp_engine` and `unified_bgp_answers_returned` chain
them. Recorded as stage 6 correction note 27.

## The term model

The completeness half needs an interpretation in which "true" means
"a triple of `g`" and NOTHING more, while still satisfying
`termEqSchema` (which demands that `Term.eqb`-equal terms denote the
same individual). The Herbrand model of `RDF/Semantics.lean` fails the
second requirement: its domain is `Term` under structural equality, so
`"a"@EN` and `"a"@en` denote differently there.

`herbQ g` is that model with the domain quotiented by `Term.eqb` —
`Quot.mk` for the identification, `Quot.lift` of `Term.eqb x ·` for
the converse, which is available exactly because `Term.eqb` is proved
reflexive, symmetric and transitive in `RDF/Core.lean`. Triple terms
get a constant, so both halves of the completeness direction carry the
triple-term-free guards, for the same reason `RDF.herbrand` does.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.SparqlQuery

namespace L4Factoidal.Unified

open L4Factoidal

/-! ## The Skolem reading, transported

`rdfToTheorySk g` is `rdfBody g`: blank nodes as free names, no
closure. Its satisfaction is at the interpretation's own name
valuation, where `FreshVal` is trivial, so the stage 1 transport
lemmas apply with no side condition at all. -/

/-- The blank-node assignment a CL interpretation induces on the
Skolem reading: a blank node denotes what its bound name denotes. -/
def skAssign (i : CL.Interp) : RDF.BnodeAssignment (restrictInterp i).idom :=
  fun b => i.iName (bnodeName b)

theorem satisfies_rdfToTheorySk_iff (i : CL.Interp) (g : RDF.Graph) :
    CL.Satisfies i (rdfToTheorySk g) ↔
      ∀ t ∈ g, CL.Satisfies i (tripleAtom t) := by
  simp only [CL.Satisfies, rdfToTheorySk]
  exact sat_rdfBody i i.iName (fun _ => []) g

/-- **Skolem transport**: a CL interpretation satisfies the Skolem
reading of a graph exactly when its restriction holds the graph under
the induced assignment (RDF 1.1 Semantics §6 — no existential
closure, so `HoldsAll` at a FIXED assignment, not `Satisfies`). -/
theorem satisfies_rdfToTheorySk_restrict (i : CL.Interp) (g : RDF.Graph) :
    CL.Satisfies i (rdfToTheorySk g) ↔
      RDF.HoldsAll (restrictInterp i) (skAssign i) g := by
  rw [satisfies_rdfToTheorySk_iff]
  constructor
  · intro h t ht
    exact (sat_tripleAtom_restrict i (skAssign i) (freshVal_iName i) t
      (fun _ _ => rfl)).mp (h t ht)
  · intro h t ht
    exact (sat_tripleAtom_restrict i (skAssign i) (freshVal_iName i) t
      (fun _ _ => rfl)).mpr (h t ht)

/-! ## Engine term equality inside satisfaction

Delimitation 3 of `SparqlQuery.lean`: `Graph.mem` is `Term.eqb`, which
is coarser than syntactic identity, so a predication about an
engine-equal triple transfers only under `termEqSchema`. -/

theorem sat_tripleAtom_eqb {i : CL.Interp}
    (hS : SatisfiesSchema i termEqSchema) {t u : RDF.Triple}
    (h : RDF.Triple.eqb t u = true) :
    CL.Satisfies i (tripleAtom t) ↔ CL.Satisfies i (tripleAtom u) := by
  simp only [RDF.Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  have hs' : t.s = u.s := RDF.Subject.eqb_eq hs
  simp only [CL.Satisfies, tripleAtom, CL.Sat, CL.denotSeq, CL.denotTerm,
             hs', hp, denot_embedTerm_congr_of_schema hS ho]

/-- A graph member's predication holds wherever the Skolem reading and
the term-equality schema do. -/
theorem sat_tripleAtom_of_graphMem {i : CL.Interp} {g : RDF.Graph}
    (hS : SatisfiesSchema i termEqSchema)
    (hsat : CL.Satisfies i (rdfToTheorySk g)) {t : RDF.Triple}
    (hmem : RDF.Graph.mem t g = true) : CL.Satisfies i (tripleAtom t) := by
  obtain ⟨u, hu, hue⟩ := RDF.exists_of_graphMem hmem
  exact (sat_tripleAtom_eqb hS hue).mp
    ((satisfies_rdfToTheorySk_iff i g).mp hsat u hu)

/-! ## The evaluator side, soundness

`SPARQL/BgpRefinement.lean` proves that substituting a returned μ back
into the pattern lands inside the graph. `BgpMatches` needs the same
statement PATTERN-WISE — with the witness that each pattern
instantiates at all — which is the shape its `instBgp_into_graph`
proof already establishes internally. -/

open SPARQL in
theorem evalBgpFrom_matches {g : RDF.Graph} : ∀ (b : Bgp) {mu mu' : Binding},
    mu' ∈ evalBgpFrom g b mu → BgpMatches mu' b g := by
  intro b
  induction b with
  | nil => intro mu mu' _ tp htp; exact absurd htp (by simp)
  | cons tp rest ih =>
      intro mu mu' h tp' htp'
      simp only [evalBgpFrom, List.mem_flatMap] at h
      obtain ⟨mu1, hmu1, hrest⟩ := h
      simp only [evalTP, List.mem_filterMap] at hmu1
      obtain ⟨u, hu, hmatch⟩ := hmu1
      rcases List.mem_cons.mp htp' with rfl | hmem
      · obtain ⟨w, hw, hwe⟩ := tpMatch_inst hmatch
        refine ⟨w, instTriple_mono (evalBgpFrom_extends rest hrest) hw, ?_⟩
        exact RDF.graphMem_of_exists ⟨u, hu, by rw [RDF.Triple.eqb_symm]; exact hwe⟩
      · exact ih hrest tp' hmem

/-- **Evaluator soundness at the pivot**: every mapping the algebra
returns instantiates the whole pattern into the graph. Unconditional —
no fragment guard, no schema. -/
theorem bgp_eval_sound {b : SPARQL.Bgp} {g : RDF.Graph} {mu : SPARQL.Binding}
    (h : mu ∈ SPARQL.evalBgp b g) : BgpMatches mu b g :=
  evalBgpFrom_matches b h

/-! ## The model-theoretic side, soundness half -/

/-- Satisfaction of a query body, pattern by pattern. -/
theorem satisfies_bgpBody_iff (i : CL.Interp) (mu : SPARQL.Binding)
    (b : SPARQL.Bgp) :
    CL.Satisfies i (bgpBody mu b) ↔
      ∀ tp ∈ b, CL.Satisfies i (patternAtom mu tp) := by
  simp only [CL.Satisfies, bgpBody, CL.Sat]
  rw [satAll_forall]
  constructor
  · intro h tp htp
    exact h _ (List.mem_map.mpr ⟨tp, htp, rfl⟩)
  · rintro h s hs
    obtain ⟨tp, htp, rfl⟩ := List.mem_map.mp hs
    exact h tp htp

/-- **Soundness of the pivot**: a mapping that instantiates the whole
pattern into the graph answers the query from the graph's Skolem
reading, under the engine-term-equality schema. -/
theorem bgp_matches_answers {b : SPARQL.Bgp} {g : RDF.Graph}
    {mu : SPARQL.Binding} (h : BgpMatches mu b g) :
    Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) mu := by
  intro i _ hS hsat
  have hg : CL.Satisfies i (rdfToTheorySk g) :=
    hsat _ (List.mem_singleton.mpr rfl)
  refine (satisfies_bgpBody_iff i mu b).mpr (fun tp htp => ?_)
  obtain ⟨t, hinst, hmem⟩ := h tp htp
  rw [patternAtom_eq_tripleAtom hinst]
  exact sat_tripleAtom_of_graphMem hS hg hmem

end L4Factoidal.Unified
