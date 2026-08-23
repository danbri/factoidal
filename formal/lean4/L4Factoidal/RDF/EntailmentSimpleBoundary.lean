/-
L4Factoidal.RDF.EntailmentSimpleBoundary — the document boundary, and
label independence.

Port of `formal/fstar/RDF.Entailment.Simple.Boundary.fst` (332 lines).

## What is and is NOT claimed — read this before citing the module

NOT claimed: that the N-Triples parser implements the N-Triples
grammar. That would need a declarative grammar semantics — a relation
"document D denotes graph G" transcribed from the Recommendation — and
a proof that the parser computes it. No such semantics exists in either
tree, and writing one is separate, larger work. Nothing here substitutes
for it.

Claimed, in two parts:

1. **Composition.** `entailsNTriplesDocuments` is the whole
   document-in, verdict-out path, and the entailment results carry
   through it unchanged. That says: whatever the parser's abstract
   graphs are, the verdict on them is the declarative relation. It
   isolates the parser as the ONLY remaining unproven link.

2. **Label independence** — the part with mathematical content. A
   parser's abstract graph is determined only up to its choice of
   blank-node labels: `_:b0` from a document and `_:genid1` from a
   generated-label path are the same graph, and RDF 1.1 Concepts §3.4
   says so ("blank node identifiers are local to a concrete syntax or
   implementation"). If the verdict could depend on those labels, no
   theorem about abstract graphs would transfer to documents.
   `simpleEntails_rename_invariant` proves it cannot.

## Injectivity is required, and is not decoration

Relabelling by an arbitrary map can only SPECIALISE the pattern: a
non-injective map merges blank nodes, and a merged pattern is harder to
satisfy. That direction (`spec_rename_specialises`) needs no inverse.
The converse needs the map to be injective, and the injectivity is
supplied as a RECORDED INVERSE rather than as an abstract property —
the transported substitution is the original composed with that
inverse, and the left-inverse equation is exactly what makes it work.
-/
import L4Factoidal.RDF.Semantics
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDF.EntailmentTheorems

namespace L4Factoidal.RDF

/-! ## Relabelling

A renaming with its inverse recorded. Carrying the inverse rather than
an injectivity hypothesis is what lets the generalising direction
compose substitutions directly. -/

structure Relabelling where
  fwd : BNodeId → BNodeId
  bwd : BNodeId → BNodeId
  leftInverse : ∀ l, bwd (fwd l) = l

/-! ## Renaming and the instance relation

`Graph.renameBnodes` is the tree's own relabelling; nothing is
redefined here. -/

theorem rename_subj_inst (f : BNodeId → BNodeId) (m : BnodeSubst)
    {ps gs : Subject} (h : SubjInst m (Subject.renameBnodes f ps) gs) :
    SubjInst (fun l => m (f l)) ps gs := by
  cases ps with
  | iri _ => exact h
  | bnode _ => exact h

theorem rename_term_inst (f : BNodeId → BNodeId) (m : BnodeSubst) :
    ∀ {pat g : Term}, TermInst m (Term.renameBnodes f pat) g →
      TermInst (fun l => m (f l)) pat g
  | .iri _, _, h => h
  | .bnode _, _, h => h
  | .literal _, _, h => h
  | .tripleTerm ps pp po, g, h => by
      obtain ⟨gs, go, rfl, hs, ho⟩ := h
      exact ⟨gs, go, rfl, rename_subj_inst f m hs, rename_term_inst f m ho⟩

theorem rename_triple_inst (f : BNodeId → BNodeId) (m : BnodeSubst)
    {tb ta : Triple} (h : TripleInst m (Triple.renameBnodes f tb) ta) :
    TripleInst (fun l => m (f l)) tb ta :=
  ⟨h.1, rename_subj_inst f m h.2.1, rename_term_inst f m h.2.2⟩

/-! The same three, read the other way — needed by the generalising
direction, which builds a renamed pattern rather than taking one
apart. -/

theorem rename_subj_inst_conv (f : BNodeId → BNodeId) (m : BnodeSubst)
    {ps gs : Subject} (h : SubjInst (fun l => m (f l)) ps gs) :
    SubjInst m (Subject.renameBnodes f ps) gs := by
  cases ps with
  | iri _ => exact h
  | bnode _ => exact h

theorem rename_term_inst_conv (f : BNodeId → BNodeId) (m : BnodeSubst) :
    ∀ {pat g : Term}, TermInst (fun l => m (f l)) pat g →
      TermInst m (Term.renameBnodes f pat) g
  | .iri _, _, h => h
  | .bnode _, _, h => h
  | .literal _, _, h => h
  | .tripleTerm ps pp po, g, h => by
      obtain ⟨gs, go, rfl, hs, ho⟩ := h
      exact ⟨gs, go, rfl, rename_subj_inst_conv f m hs, rename_term_inst_conv f m ho⟩

theorem rename_triple_inst_conv (f : BNodeId → BNodeId) (m : BnodeSubst)
    {tb ta : Triple} (h : TripleInst (fun l => m (f l)) tb ta) :
    TripleInst m (Triple.renameBnodes f tb) ta :=
  ⟨h.1, rename_subj_inst_conv f m h.2.1, rename_term_inst_conv f m h.2.2⟩

/-! ## Substitutions that agree pointwise give the same instances -/

theorem subst_ext_subj {m1 m2 : BnodeSubst} (hm : ∀ l, m1 l = m2 l)
    {ps gs : Subject} (h : SubjInst m1 ps gs) : SubjInst m2 ps gs := by
  cases ps with
  | iri _ => exact h
  | bnode b => exact (hm b).symm.trans h

theorem subst_ext_term {m1 m2 : BnodeSubst} (hm : ∀ l, m1 l = m2 l) :
    ∀ {pat g : Term}, TermInst m1 pat g → TermInst m2 pat g
  | .iri _, _, h => h
  | .bnode b, _, h => (hm b).symm.trans h
  | .literal _, _, h => h
  | .tripleTerm _ _ _, _, h => by
      obtain ⟨gs, go, rfl, hs, ho⟩ := h
      exact ⟨gs, go, rfl, subst_ext_subj hm hs, subst_ext_term hm ho⟩

theorem subst_ext_triple {m1 m2 : BnodeSubst} (hm : ∀ l, m1 l = m2 l)
    {tb ta : Triple} (h : TripleInst m1 tb ta) : TripleInst m2 tb ta :=
  ⟨h.1, subst_ext_subj hm h.2.1, subst_ext_term hm h.2.2⟩

/-! ## Relabelling and the specification -/

/-- Relabelling the entailed graph by ANY map can only SPECIALISE it: a
non-injective map merges blank nodes, and a merged pattern is harder to
satisfy. So this direction needs no inverse. -/
theorem spec_rename_specialises (f : BNodeId → BNodeId) {a b : Graph}
    (h : SimpleEntailmentSpec a (Graph.renameBnodes f b)) :
    SimpleEntailmentSpec a b := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun l => m (f l), fun tb htb => ?_⟩
  obtain ⟨ta, hta, hrel⟩ := hm (Triple.renameBnodes f tb)
    (List.mem_map_of_mem htb)
  exact ⟨ta, hta, rename_triple_inst f m hrel⟩

/-- The converse needs injectivity, and the recorded inverse supplies
it: the transported substitution is the original composed with the
inverse, and the left-inverse equation is what makes the two agree on
every label the pattern mentions. -/
theorem spec_rename_generalises (r : Relabelling) {a b : Graph}
    (h : SimpleEntailmentSpec a b) :
    SimpleEntailmentSpec a (Graph.renameBnodes r.fwd b) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun l => m (r.bwd l), fun tb' htb' => ?_⟩
  obtain ⟨tb, htb, rfl⟩ := List.mem_map.mp htb'
  obtain ⟨ta, hta, hrel⟩ := hm tb htb
  refine ⟨ta, hta, ?_⟩
  -- transport `hrel` along the left-inverse equation, then push the
  -- renaming back through the instance relation
  have hext : TripleInst (fun l => (fun l' => m (r.bwd l')) (r.fwd l)) tb ta :=
    subst_ext_triple (fun l => (congrArg m (r.leftInverse l)).symm) hrel
  -- `rename_triple_inst` read backwards: the renamed pattern under the
  -- transported substitution is the original pattern under the
  -- composite, which is what `hext` is
  exact rename_triple_inst_conv r.fwd (fun l => m (r.bwd l)) hext

/-! ## Label independence -/

/-- Relabelling the entailed graph's blank nodes by an INJECTIVE map
does not change whether simple entailment holds. This is what makes
every theorem about abstract graphs transfer to documents, whose
blank-node labels are a syntax-local choice.

Stated about the RELATION, not about the decision procedure's boolean.
The F\* theorem is about its shipping boolean because that tree has the
procedure's completeness; this tree has soundness only
(`RDF.EntailmentTheorems.simpleEntails_sound`), so the boolean version
would need the missing half. A `#guard` below checks the boolean's
invariance on a concrete relabelled pair, which is evidence, not the
theorem. -/
theorem simpleEntails_rename_invariant (r : Relabelling) (a b : Graph) :
    SimpleEntails a b ↔ SimpleEntails a (Graph.renameBnodes r.fwd b) := by
  constructor
  · intro h
    exact (spec_iff_simpleEntails _ _).mp
      (spec_rename_generalises r ((spec_iff_simpleEntails a b).mpr h))
  · intro h
    exact (spec_iff_simpleEntails _ _).mp
      (spec_rename_specialises r.fwd ((spec_iff_simpleEntails _ _).mpr h))

/-! ## The document boundary

The whole path: two N-Triples documents in, a verdict out. `none` when
either document fails to parse — which is the parser's answer, not
this module's, and is exactly the link the header says is unproven. -/

def entailsNTriplesDocuments (docA docB : String) : Option Bool :=
  match Syntax.parseNTriples docA, Syntax.parseNTriples docB with
  | .ok ga, .ok gb => some (simpleEntails ga gb)
  | _, _ => none

/-- **Composition.** When both documents parse, the verdict IS the
declarative relation on the graphs they parsed to. Whatever the
parser's abstract graphs are, the answer about them is the right one —
which isolates the parser as the only remaining unproven link. -/
theorem entailsNTriples_boundary {docA docB : String} {ga gb : Graph}
    (hA : Syntax.parseNTriples docA = .ok ga)
    (hB : Syntax.parseNTriples docB = .ok gb) :
    entailsNTriplesDocuments docA docB = some (simpleEntails ga gb) := by
  simp [entailsNTriplesDocuments, hA, hB]

/-- And composed with the interpolation lemma, a `true` verdict on two
triple-term-free documents is a statement about every interpretation. -/
theorem entailsNTriples_mt {docA docB : String} {ga gb : Graph}
    (hA : Syntax.parseNTriples docA = .ok ga)
    (hB : Syntax.parseNTriples docB = .ok gb)
    (hv : entailsNTriplesDocuments docA docB = some true) :
    SimpleEntailsMt ga gb := by
  rw [entailsNTriples_boundary hA hB] at hv
  exact simpleEntails_sound_mt (simpleEntails_sound (by simpa using hv))

/-! ## Build-time checks -/

section Checks

private def docA : String :=
  "<http://e.org/s> <http://e.org/p> <http://e.org/o> .\n"
private def docB : String := "_:x <http://e.org/p> <http://e.org/o> .\n"

#guard entailsNTriplesDocuments docA docA == some true
#guard entailsNTriplesDocuments docA docB == some true
#guard entailsNTriplesDocuments docB docA == some false

/-! An unparseable document yields `none`, not a verdict — the parser's
answer, kept distinct from "does not entail". -/

#guard entailsNTriplesDocuments "not n-triples" docA == none
#guard entailsNTriplesDocuments docA "not n-triples" == none

/-! Relabelling the entailed graph changes nothing, which is the
theorem above checked on a concrete pair. -/

private def relabelled : Graph :=
  match Syntax.parseNTriples docB with
  | .ok g => Graph.renameBnodes (fun l => "gen" ++ l) g
  | .error _ => []

#guard match Syntax.parseNTriples docA with
       | .ok ga => simpleEntails ga relabelled
       | .error _ => false

end Checks

end L4Factoidal.RDF
