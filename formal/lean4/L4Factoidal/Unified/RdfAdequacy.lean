/-
L4Factoidal.Unified.RdfAdequacy — stage 1 adequacy of the unified
LBase/IKL theory against the native RDF formalization
(https://github.com/danbri/factoidal/issues/598; design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §4.1).

* `unified_adequate_simple` — the stage 1 gate theorem, an
  unconditional iff: CL entailment between translated graphs IS
  RDF 1.1 simple entailment (`RDF.SimpleEntailsMt`,
  `RDF/Semantics.lean`). No triple-term-freedom hypothesis: both
  sides give RDF 1.2 triple terms the same uninterpreted
  component-wise reading.
* `unified_adequate_simple_decided` — the corollary chain through
  `RDF.simpleEntails_iff_mt` and `RDF.SimpleRefinement.simpleEntails_iff_spec` to the
  executable decision procedure, with the `GraphTtFree` hypotheses
  exactly where the native Herbrand construction needs them.
* `rdfToTheory_merge` — merge is conjunction: the translation of the
  standardized-apart union is satisfaction-equivalent to the pair of
  the two graphs' closures (RDF 1.1 Semantics §4.1; the
  standardize-apart machinery is `RDF/DatasetMerge.lean`'s renaming,
  applied through `Graph.prefixBnodes`).
* `rdfToTheory_union_*` / `union_shared_scope_strict` — shared-label
  union is single-scope closure: it entails each part and the merge,
  and the converse FAILS on a machine-checked witness pair (the
  design document §2.3's "NOT in general entailment-equivalent",
  made a theorem).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfTransport
import L4Factoidal.RDF.EntailmentSimpleRefinement
import L4Factoidal.RDF.DatasetMerge

namespace L4Factoidal.Unified

/-! ## The stage 1 gate theorem -/

/-- **Stage 1 adequacy** (design document §4.1): entailment in the
unified theory between two translated graphs coincides with RDF 1.1
simple entailment, model-theoretically, with no side condition. -/
theorem unified_adequate_simple (g h : RDF.Graph) :
    Entails [rdfToTheory g] (rdfToTheory h) ↔ RDF.SimpleEntailsMt g h := by
  constructor
  · intro hE r hg
    have h1 : CL.Satisfies (liftInterp r) (rdfToTheory g) :=
      (satisfies_rdfToTheory_lift r g).mpr hg
    have h2 : CL.Satisfies (liftInterp r) (rdfToTheory h) :=
      hE (liftInterp r) True.intro (fun s hs => by
        obtain rfl := List.mem_singleton.mp hs
        exact h1)
    exact (satisfies_rdfToTheory_lift r h).mp h2
  · intro hMt i _ hsat
    have h1 : RDF.Satisfies (restrictInterp i) g :=
      (satisfies_rdfToTheory_restrict i g).mp
        (hsat _ (List.mem_singleton.mpr rfl))
    exact (satisfies_rdfToTheory_restrict i h).mpr
      (hMt (restrictInterp i) h1)

/-- **The decided corollary**: on triple-term-free graphs (where the
native Herbrand construction applies), unified entailment coincides
with the answer of the executable decision procedure
(`RDF.simpleEntails`, `RDF/Entailment.lean`). -/
theorem unified_adequate_simple_decided (g h : RDF.Graph)
    (hg : RDF.GraphTtFree g) (hh : RDF.GraphTtFree h) :
    Entails [rdfToTheory g] (rdfToTheory h) ↔
      RDF.simpleEntails g h = true :=
  (unified_adequate_simple g h).trans
    ((RDF.simpleEntails_iff_mt hg hh).symm.trans
      (RDF.SimpleRefinement.simpleEntails_iff_spec g h).symm)

/-! ## Native satisfaction laws for merge and union

Proved here (they exist nowhere in the native tree yet): splitting an
append, transporting satisfaction across a blank-node renaming with a
left inverse, and combining satisfaction across a blank-node-disjoint
append via the native locality lemma `RDF.tripleHolds_agree`. -/

theorem satisfies_append_left (r : RDF.Interp) {g1 g2 : RDF.Graph}
    (h : RDF.Satisfies r (g1 ++ g2)) : RDF.Satisfies r g1 := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun t ht => ha t (List.mem_append_left _ ht)⟩

theorem satisfies_append_right (r : RDF.Interp) {g1 g2 : RDF.Graph}
    (h : RDF.Satisfies r (g1 ++ g2)) : RDF.Satisfies r g2 := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun t ht => ha t (List.mem_append_right _ ht)⟩

theorem denotSubject_rename (r : RDF.Interp)
    (a : RDF.BnodeAssignment r.idom) (f : RDF.BNodeId → RDF.BNodeId)
    (s : RDF.Subject) :
    RDF.denotSubject r a (RDF.Subject.renameBnodes f s) =
      RDF.denotSubject r (fun b => a (f b)) s := by
  cases s <;> rfl

theorem denotTerm_rename (r : RDF.Interp)
    (a : RDF.BnodeAssignment r.idom) (f : RDF.BNodeId → RDF.BNodeId) :
    ∀ t : RDF.Term,
      RDF.denotTerm r a (RDF.Term.renameBnodes f t) =
        RDF.denotTerm r (fun b => a (f b)) t
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal _ => rfl
  | .tripleTerm s p o => by
      simp only [RDF.Term.renameBnodes, RDF.denotTerm,
                 denotSubject_rename, denotTerm_rename r a f o]

theorem tripleHolds_rename (r : RDF.Interp)
    (a : RDF.BnodeAssignment r.idom) (f : RDF.BNodeId → RDF.BNodeId)
    (t : RDF.Triple) :
    RDF.TripleHolds r a (RDF.Triple.renameBnodes f t) ↔
      RDF.TripleHolds r (fun b => a (f b)) t := by
  simp only [RDF.TripleHolds, RDF.Triple.renameBnodes,
             denotSubject_rename, denotTerm_rename]

/-- Satisfaction is invariant under a blank-node renaming with a left
inverse (in particular any injective renaming realised by a concrete
inverse — the standardize-apart prefixings below). -/
theorem satisfies_rename_iff (r : RDF.Interp)
    (f finv : RDF.BNodeId → RDF.BNodeId) (hinv : ∀ b, finv (f b) = b)
    (g : RDF.Graph) :
    RDF.Satisfies r (RDF.Graph.renameBnodes f g) ↔ RDF.Satisfies r g := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun b => a (f b), fun t ht => ?_⟩
    exact (tripleHolds_rename r a f t).mp
      (ha (RDF.Triple.renameBnodes f t) (List.mem_map.mpr ⟨t, ht, rfl⟩))
  · rintro ⟨a, ha⟩
    refine ⟨fun c => a (finv c), fun t' ht' => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    rw [tripleHolds_rename]
    have hva : (fun b => a (finv (f b))) = a := by
      funext b; rw [hinv]
    rw [hva]
    exact ha t ht

theorem satisfies_append_of_disjoint (r : RDF.Interp) {g1 g2 : RDF.Graph}
    (hdisj : ∀ b ∈ RDF.graphBnodeIds g1, b ∉ RDF.graphBnodeIds g2)
    (h1 : RDF.Satisfies r g1) (h2 : RDF.Satisfies r g2) :
    RDF.Satisfies r (g1 ++ g2) := by
  obtain ⟨a1, ha1⟩ := h1
  obtain ⟨a2, ha2⟩ := h2
  refine ⟨fun b => if b ∈ RDF.graphBnodeIds g1 then a1 b else a2 b,
          fun t ht => ?_⟩
  rcases List.mem_append.mp ht with ht1 | ht2
  · refine (RDF.tripleHolds_agree r ?_).mpr (ha1 t ht1)
    intro b hb
    have hbg : b ∈ RDF.graphBnodeIds g1 := List.mem_flatMap.mpr ⟨t, ht1, hb⟩
    simp [hbg]
  · refine (RDF.tripleHolds_agree r ?_).mpr (ha2 t ht2)
    intro b hb
    have hb2 : b ∈ RDF.graphBnodeIds g2 := List.mem_flatMap.mpr ⟨t, ht2, hb⟩
    have hb1 : b ∉ RDF.graphBnodeIds g1 := fun hx => hdisj b hx hb2
    simp [hb1]

theorem subjectBnodes_rename (f : RDF.BNodeId → RDF.BNodeId)
    (s : RDF.Subject) :
    RDF.subjectBnodes (RDF.Subject.renameBnodes f s) =
      (RDF.subjectBnodes s).map f := by
  cases s <;> rfl

theorem termBnodes_rename (f : RDF.BNodeId → RDF.BNodeId) :
    ∀ t : RDF.Term,
      RDF.termBnodes (RDF.Term.renameBnodes f t) =
        (RDF.termBnodes t).map f
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal _ => rfl
  | .tripleTerm s p o => by
      simp only [RDF.Term.renameBnodes, RDF.termBnodes,
                 subjectBnodes_rename, termBnodes_rename f o,
                 List.map_append]

theorem tripleBnodes_rename (f : RDF.BNodeId → RDF.BNodeId)
    (t : RDF.Triple) :
    RDF.tripleBnodes (RDF.Triple.renameBnodes f t) =
      (RDF.tripleBnodes t).map f := by
  simp only [RDF.tripleBnodes, RDF.Triple.renameBnodes,
             subjectBnodes_rename, termBnodes_rename, List.map_append]

theorem graphBnodeIds_rename (f : RDF.BNodeId → RDF.BNodeId) :
    ∀ g : RDF.Graph,
      RDF.graphBnodeIds (RDF.Graph.renameBnodes f g) =
        (RDF.graphBnodeIds g).map f
  | [] => rfl
  | t :: rest => by
      have ih := graphBnodeIds_rename f rest
      simp only [RDF.Graph.renameBnodes, List.map_cons] at *
      simp only [RDF.graphBnodeIds, List.flatMap_cons] at *
      rw [tripleBnodes_rename, ih, List.map_append]

/-! ## Merge is conjunction -/

/-- Graph merge (RDF 1.1 Semantics §4.1): union after standardizing
the two graphs' blank nodes apart, by the injective prefixings of
`RDF/DatasetMerge.lean` / `Graph.prefixBnodes`. (The native tree has
the renaming machinery but no named merge operation; this is it, at
graph level.) -/
def mergeGraphs (g h : RDF.Graph) : RDF.Graph :=
  RDF.Graph.prefixBnodes "l" g ++ RDF.Graph.prefixBnodes "r" h

/-- Strip one leading character — the concrete left inverse of a
single-character prefixing. -/
def unprefix1 (c : String) : String := String.ofList c.toList.tail

theorem unprefix1_l (b : String) : unprefix1 ("l" ++ b) = b := by
  simp [unprefix1]

theorem unprefix1_r (b : String) : unprefix1 ("r" ++ b) = b := by
  simp [unprefix1]

theorem prefix_lr_ne (x y : String) : "l" ++ x ≠ "r" ++ y := by
  intro hxy
  have h2 := congrArg String.toList hxy
  simp at h2

theorem merge_bnodes_disjoint (g h : RDF.Graph) :
    ∀ b ∈ RDF.graphBnodeIds (RDF.Graph.prefixBnodes "l" g),
      b ∉ RDF.graphBnodeIds (RDF.Graph.prefixBnodes "r" h) := by
  intro b hb hb2
  rw [show RDF.Graph.prefixBnodes "l" g
        = RDF.Graph.renameBnodes (fun x => "l" ++ x) g from rfl,
      graphBnodeIds_rename] at hb
  rw [show RDF.Graph.prefixBnodes "r" h
        = RDF.Graph.renameBnodes (fun x => "r" ++ x) h from rfl,
      graphBnodeIds_rename] at hb2
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hb
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hb2
  exact prefix_lr_ne x y (hx.trans hy.symm)

theorem satisfies_prefixBnodes_l (r : RDF.Interp) (g : RDF.Graph) :
    RDF.Satisfies r (RDF.Graph.prefixBnodes "l" g) ↔ RDF.Satisfies r g :=
  satisfies_rename_iff r (fun b => "l" ++ b) unprefix1 unprefix1_l g

theorem satisfies_prefixBnodes_r (r : RDF.Interp) (g : RDF.Graph) :
    RDF.Satisfies r (RDF.Graph.prefixBnodes "r" g) ↔ RDF.Satisfies r g :=
  satisfies_rename_iff r (fun b => "r" ++ b) unprefix1 unprefix1_r g

/-- Merged satisfaction is component satisfaction — the native fact
under `rdfToTheory_merge`. -/
theorem satisfies_mergeGraphs_iff (r : RDF.Interp) (g h : RDF.Graph) :
    RDF.Satisfies r (mergeGraphs g h) ↔
      RDF.Satisfies r g ∧ RDF.Satisfies r h := by
  constructor
  · intro hm
    exact ⟨(satisfies_prefixBnodes_l r g).mp (satisfies_append_left r hm),
           (satisfies_prefixBnodes_r r h).mp (satisfies_append_right r hm)⟩
  · rintro ⟨hg, hh⟩
    exact satisfies_append_of_disjoint r (merge_bnodes_disjoint g h)
      ((satisfies_prefixBnodes_l r g).mpr hg)
      ((satisfies_prefixBnodes_r r h).mpr hh)

/-- **Merge is conjunction** (design document §2.3): the translation
of the standardized-apart union is satisfaction-equivalent to the two
closures side by side. -/
theorem rdfToTheory_merge (g h : RDF.Graph) :
    EntailEquiv [rdfToTheory (mergeGraphs g h)]
                [rdfToTheory g, rdfToTheory h] := by
  intro i
  constructor
  · intro hs s hmem
    have hm : RDF.Satisfies (restrictInterp i) (mergeGraphs g h) :=
      (satisfies_rdfToTheory_restrict i _).mp
        (hs _ (List.mem_singleton.mpr rfl))
    obtain ⟨hg, hh⟩ := (satisfies_mergeGraphs_iff _ g h).mp hm
    rcases List.mem_cons.mp hmem with rfl | hmem2
    · exact (satisfies_rdfToTheory_restrict i g).mpr hg
    · obtain rfl := List.mem_singleton.mp hmem2
      exact (satisfies_rdfToTheory_restrict i h).mpr hh
  · intro hs s hmem
    obtain rfl := List.mem_singleton.mp hmem
    have hg : RDF.Satisfies (restrictInterp i) g :=
      (satisfies_rdfToTheory_restrict i g).mp (hs _ (by simp))
    have hh : RDF.Satisfies (restrictInterp i) h :=
      (satisfies_rdfToTheory_restrict i h).mp (hs _ (by simp))
    exact (satisfies_rdfToTheory_restrict i _).mpr
      ((satisfies_mergeGraphs_iff _ g h).mpr ⟨hg, hh⟩)

/-! ## Shared-label union is single-scope closure -/

/-- The union entails its left part. -/
theorem rdfToTheory_union_entails_left (g h : RDF.Graph) :
    Entails [rdfToTheory (g ++ h)] (rdfToTheory g) := by
  intro i _ hsat
  have hu := (satisfies_rdfToTheory_restrict i _).mp
    (hsat _ (List.mem_singleton.mpr rfl))
  exact (satisfies_rdfToTheory_restrict i g).mpr (satisfies_append_left _ hu)

/-- The union entails its right part. -/
theorem rdfToTheory_union_entails_right (g h : RDF.Graph) :
    Entails [rdfToTheory (g ++ h)] (rdfToTheory h) := by
  intro i _ hsat
  have hu := (satisfies_rdfToTheory_restrict i _).mp
    (hsat _ (List.mem_singleton.mpr rfl))
  exact (satisfies_rdfToTheory_restrict i h).mpr (satisfies_append_right _ hu)

/-- The shared-scope union entails the merge: single-scope closure is
at least as strong as separate closures. -/
theorem rdfToTheory_union_entails_merge (g h : RDF.Graph) :
    Entails [rdfToTheory (g ++ h)] (rdfToTheory (mergeGraphs g h)) := by
  intro i _ hsat
  have hu := (satisfies_rdfToTheory_restrict i _).mp
    (hsat _ (List.mem_singleton.mpr rfl))
  exact (satisfies_rdfToTheory_restrict i _).mpr
    ((satisfies_mergeGraphs_iff _ g h).mpr
      ⟨satisfies_append_left _ hu, satisfies_append_right _ hu⟩)

/-! ### The converse fails: a machine-checked witness pair

`unionG` and `unionH` share the label `x`. Their separate closures say
"something is P-related to a" and "something is P-related to b"; the
single-scope union says ONE thing is P-related to both. The refutation
routes entirely through the theorems above and the executable decision
procedure — no hand-built countermodel. -/

private def uA : RDF.WfIri := ⟨"http://u.example/a", by decide⟩
private def uB : RDF.WfIri := ⟨"http://u.example/b", by decide⟩
private def uP : RDF.WfIri := ⟨"http://u.example/p", by decide⟩

def unionG : RDF.Graph := [⟨.bnode "x", uP, .iri uA⟩]
def unionH : RDF.Graph := [⟨.bnode "x", uP, .iri uB⟩]

theorem unionMerge_ttFree : RDF.GraphTtFree (mergeGraphs unionG unionH) := by
  intro t ht
  simp [mergeGraphs, RDF.Graph.prefixBnodes, RDF.Graph.renameBnodes,
        RDF.Triple.renameBnodes, unionG, unionH] at ht
  rcases ht with rfl | rfl <;> trivial

theorem unionUnion_ttFree : RDF.GraphTtFree (unionG ++ unionH) := by
  intro t ht
  simp [unionG, unionH] at ht
  rcases ht with rfl | rfl <;> trivial

/-- The decision procedure separates the two scopings. -/
theorem simpleEntails_merge_union_false :
    RDF.simpleEntails (mergeGraphs unionG unionH) (unionG ++ unionH)
      = false := by decide

/-- **The strictness witness** (design document §2.3): separate
closures do NOT entail the single-scope union — union with shared
labels is not the conjunction of the parts' translations. -/
theorem union_shared_scope_strict :
    ¬ Entails [rdfToTheory unionG, rdfToTheory unionH]
        (rdfToTheory (unionG ++ unionH)) := by
  intro hE
  have hE2 : Entails [rdfToTheory (mergeGraphs unionG unionH)]
      (rdfToTheory (unionG ++ unionH)) :=
    (entailEquiv_entails_iff (rdfToTheory_merge unionG unionH) _).mpr hE
  have hDec : RDF.simpleEntails (mergeGraphs unionG unionH)
      (unionG ++ unionH) = true :=
    (unified_adequate_simple_decided _ _ unionMerge_ttFree
      unionUnion_ttFree).mp hE2
  rw [simpleEntails_merge_union_false] at hDec
  exact Bool.false_ne_true hDec

/-! ## Build-time checks -/

section Checks

/- The witness pair is not degenerate: each direction of the scoping
comparison is exercised — the merge does entail each part. -/

#guard RDF.simpleEntails (mergeGraphs unionG unionH) unionG
#guard RDF.simpleEntails (mergeGraphs unionG unionH) unionH
#guard !(RDF.simpleEntails (mergeGraphs unionG unionH) (unionG ++ unionH))
#guard RDF.simpleEntails (unionG ++ unionH) (mergeGraphs unionG unionH)

/-! Axiom audit — expected at most `propext` / `Classical.choice` /
`Quot.sound` (Lean's own foundations, arriving through `Char`/`String`
library machinery). No `sorryAx`, nothing user-declared. -/

#print axioms unified_adequate_simple
#print axioms unified_adequate_simple_decided
#print axioms rdfToTheory_merge
#print axioms union_shared_scope_strict

end Checks

end L4Factoidal.Unified
