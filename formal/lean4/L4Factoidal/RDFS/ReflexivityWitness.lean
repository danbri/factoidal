/-
L4Factoidal.RDFS.ReflexivityWitness — the finding RS-1 witness, ported
from `RDF.Entailment.RDFS.Refinement` (1613 lines).

Finding RS-1 in the F\* source: `rdfs_reflexivity_axioms` emitted
`C rdfs:subClassOf C` for every `C` typed `owl:Class`, and
`P rdfs:subPropertyOf P` for every `P` typed `owl:ObjectProperty` or
`owl:DatatypeProperty`. Neither is RDFS-entailed. rdfs10 fires on
`rdfs:Class`, not on `owl:Class`. The defect is fixed
(<https://github.com/danbri/factoidal/issues/335>); this module carries
the fact the fix rests on, so a later edit cannot quietly restore the
emission by declaring the self-loop axiomatic.

`selfloop_not_axiomatic` states it: for EVERY IRI `c`, and every
datatype map `D` and container slice `cmps`, the triple
`c rdfs:subClassOf c` is in no axiom table of either vocabulary.

## What the same statement costs in each tree

The F\* proof carries this pragma:

    --fuel 50 --ifuel 2 --z3rlimit 600 --split_queries always
    --using_facts_from '*,-RDFS.Closure.emit_once_term'

and about thirty lines of comment explaining it. The record in that
file: z3 returned "unknown because (incomplete quantifiers)" at 75 of a
240 rlimit, so splitting the conjunction into three queries was needed;
the budget was later raised 600 to 1200; and one unrelated symbol,
`emit_once_term`, had to have its facts EXCLUDED, because its
definition equation sitting in the SMT context tipped an already
borderline `assert_norm` block. Raising rlimit to 1200 and fuel to 100
did not recover it.

None of that is about RDFS. It is about the SMT encoding. The Lean
proof below is a case split on a finite table and needs no budget, no
query splitting, and no fact filtering. The two proofs establish the
same fact and differ only in what the host makes hard.

## Why the statement is unconditional in `D` and `cmps`

Both open axiom families emit only `rdf:type`, `rdfs:domain` and
`rdfs:range` rows — see `rdfsContainerAxioms` and `datatypeAxioms`.
Neither can produce a `rdfs:subClassOf` triple at all, whatever `D` and
`cmps` contain. So no side condition on the datatype map is needed, and
the F\* source's own note that "every axiomatic `rdfs:subClassOf` row
has distinct endpoints" is only about the fixed table.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.OWL.Vocabulary

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-- The witness graph: one IRI typed `owl:Class`, and nothing else. -/
def owlClassGraph (c : WfIri) : Graph :=
  [⟨.iri c, rdfType, .iri L4Factoidal.OWL.RL.owlClass⟩]

/-- The self-loop the pre-fix emitter produced from that graph. -/
def owlClassReflTriple (c : WfIri) : Triple :=
  ⟨.iri c, rdfsSubClassOf, .iri c⟩

/-! ## The open families emit no `rdfs:subClassOf` -/

theorem containerAxioms_pred {cmps : List WfIri} {t : Triple}
    (h : t ∈ rdfsContainerAxioms cmps) :
    t.p = rdfType ∨ t.p = rdfsDomain ∨ t.p = rdfsRange := by
  simp only [rdfsContainerAxioms, List.mem_flatMap] at h
  obtain ⟨c, -, hc⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem datatypeAxioms_pred {D : List WfIri} {t : Triple}
    (h : t ∈ datatypeAxioms D) : t.p = rdfType := by
  simp only [datatypeAxioms, List.mem_map] at h
  obtain ⟨d, -, hd⟩ := h
  rw [← hd]; rfl

theorem rdfAxioms_pred {cmps : List WfIri} {t : Triple}
    (h : t ∈ rdfAxiomaticTriples cmps) : t.p = rdfType := by
  simp only [rdfAxiomaticTriples, List.mem_append, List.mem_map] at h
  rcases h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · obtain ⟨c, -, hc⟩ := h; rw [← hc]; rfl

/-! ## The fixed table has no `rdfs:subClassOf` self-loop

Every `rdfs:subClassOf` row of §9.3 has distinct endpoints. Matching
the self-loop against each in turn forces two different IRIs to be
equal. -/

theorem selfloop_not_in_fixed (c : WfIri) :
    owlClassReflTriple c ∉ rdfsAxiomaticTriplesFixed := by
  intro h
  simp only [rdfsAxiomaticTriplesFixed, owlClassReflTriple, iriTriple,
             List.mem_cons, List.not_mem_nil, or_false, Triple.mk.injEq,
             Subject.iri.injEq, Term.iri.injEq] at h
  rcases h with ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    | ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    | ⟨hs, -, ho⟩ | ⟨hs, -, ho⟩ | ⟨hs, -, ho⟩ | ⟨hs, -, ho⟩
    | ⟨-, hp, -⟩ | ⟨-, hp, -⟩ | ⟨hs, -, ho⟩ | ⟨hs, -, ho⟩
  all_goals first
    | exact absurd hp (by decide)
    | (subst hs; exact absurd ho (by decide))

/-! ## The statement -/

/-- **Finding RS-1's supporting fact.** For every IRI `c`, every
datatype map `D` and every container slice `cmps`, the triple
`c rdfs:subClassOf c` is in no axiom table. So the pre-fix emitter's
output was not justified by the axiom tables, and no later edit can
justify it that way either. -/
theorem selfloop_pred (c : WfIri) : (owlClassReflTriple c).p = rdfsSubClassOf := rfl

theorem selfloop_not_axiomatic (c : WfIri) (D cmps : List WfIri) :
    owlClassReflTriple c ∉ axiomaticTriples D cmps := by
  intro h
  simp only [axiomaticTriples, rdfsAxiomaticTriples, List.mem_append] at h
  rcases h with h | ((h | h) | h)
  · have hp := rdfAxioms_pred h
    rw [selfloop_pred] at hp; exact absurd hp (by decide)
  · exact selfloop_not_in_fixed c h
  · rcases containerAxioms_pred h with hp | hp | hp <;>
      (rw [selfloop_pred] at hp; exact absurd hp (by decide))
  · have hp := datatypeAxioms_pred h
    rw [selfloop_pred] at hp; exact absurd hp (by decide)

/-! ## Build-time checks -/

#guard (owlClassGraph L4Factoidal.OWL.RL.owlClass).length == 1
#guard (owlClassReflTriple L4Factoidal.OWL.RL.owlClass).p == rdfsSubClassOf

/-! ## Axiom audit -/

#print axioms selfloop_not_in_fixed
#print axioms selfloop_not_axiomatic

end L4Factoidal.RDFS
