/-
L4Factoidal.Unified.RdfsSchema — stage 2 of
https://github.com/danbri/factoidal/issues/598, second half: the full
RDFS schema (RDF 1.1 Semantics §8/§9), the RDF-rung schema, the
datatype composition with `dSchema`, the `rdfs:range` clash family,
and the type-application bridge — each with bidirectional adequacy
against the native model theory (design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §3 stage 2,
§4.2).

## Strength of the gate theorems (correction note 9 in the design doc)

The design document predicted soundness-only for full RDFS
(`unified_rdfs_closure_sound`), citing Finding C-1. C-1 blocks the
EXECUTABLE characterisation (RDFS entailment is not simple entailment
of the closure), not model-theoretic adequacy: the native anchor
`RDF.RdfsEntails` (`RDF/EntailmentRdfsModelTheory.lean`) is itself
`EntailsUnder` over the §9 condition bundle, and against it the gate
theorem `unified_adequate_rdfs` is a FULL unconditional iff, by the
same transport as the simple and D gates. The closure-soundness
corollary lands too (`unified_rdfs_closure_sound`, over
`RDFS.fullClosure` via a `DerivesFull` truth-preservation induction);
a decided (executable) corollary is NOT stated — C-1's witness pair is
restated here at the unified level (`rdfs_entails_selfLoop_unified` vs
`rhoDf_not_entails_selfLoop_unified` in `Unified/RhoDfSchema.lean`).

## The rdf:_n infinite families (design doc §5.7)

The schemas state the FULL infinite families, by reusing the native
predicates `RDF.RdfAxiomatic` / `RDF.RdfsAxiomatic` (which carry the
`rdf:_n` family through `IsRdfMemberIri`) as row indices. Both sides
of every gate iff quantify over the same infinite family, so adequacy
needs no finite-slice argument. The §5.7 finite-slice-suffices lemma
(consequences mentioning only harvested `rdf:_n` IRIs are derivable
from the harvested instances) has NO consumer among the theorems
here — it becomes load-bearing only for a decided RDFS corollary,
which C-1 independently blocks — and is recorded as the stage's named
open lemma in the theorem registry rather than proved.

## The type-application bridge (LBase §2)

`typeBridge` — `(forall (x c) (iff (rdf:type x c) (c x)))` — is a
SEPARATE schema, not a row of `rdfsSchema`: the lifted interpretation
`liftInterp r` gives every non-binary predication an empty extension,
so no lifted interpretation satisfies the bridge on a non-empty type
extension, and folding it into `rdfsSchema` would break the gate iff.
What holds instead is CONSERVATIVITY over translated graphs
(`typeBridge_conservative`): adding the bridge changes no entailment
between translated graphs, proved by rel-surgery (`bridgeify`) that
defines unary predication from the binary `rdf:type` extension. The
bridge is not conservative outside the translated fragment —
`bridge_derives_classApp` / `rdfsSchema_no_classApp` pin the
separation on the LBase class-application sentence `(C a)`.

## Witnesses

Satisfiability and non-totality of the RDFS schema and bundle compose
with the native witnesses of `RDF/SemanticsHypothesisWitness.lean`
(`trivialInterp`, `separatingInterp`) through the transport pair. For
the COMBINED RDFS+D bundle the witnesses are stated for `D = []`
(where the datatype conditions are vacuous); a satisfiability witness
for nonempty `D` needs a term-model construction (the interaction of
`CondResource`/reflexivity with literal-excluding conditions defeats
every finite ad-hoc model tried) and is recorded as an open item in
the registry, next to the finite-slice lemma.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RhoDfSchema
import L4Factoidal.RDFS.FullClosureTheorems
import L4Factoidal.RDF.EntailmentRdfsDatatypeClash

namespace L4Factoidal.Unified

/-! ## The eleven RDFS rows beyond the six ρdf rows

One Horn row per §8/§9 semantic condition of
`RDF/EntailmentRdfsModelTheory.lean` that is not an axiom family; the
two IC/IP conjunction conditions each split into two rows. -/

/-- rdfD2's condition: an active predicate is an `rdf:Property`. -/
def rowRdfProperty : CL.Sentence :=
  hornRow ["p", "x", "y"] [⟨.v "p", .v "x", .v "y"⟩]
    ⟨.c RDFS.rdfType, .v "p", .c RDFS.rdfProperty⟩

/-- rdfs4's condition: everything is an `rdfs:Resource` (empty body). -/
def rowResource : CL.Sentence :=
  hornRow ["x"] [] ⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfsResource⟩

/-- rdfs6's condition: subPropertyOf is reflexive on properties. -/
def rowSpRefl : CL.Sentence :=
  hornRow ["x"] [⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfProperty⟩]
    ⟨.c RDFS.rdfsSubPropertyOf, .v "x", .v "x"⟩

/-- §9's "x and y are in IP", left half. -/
def rowSpIp1 : CL.Sentence :=
  hornRow ["x", "y"] [⟨.c RDFS.rdfsSubPropertyOf, .v "x", .v "y"⟩]
    ⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfProperty⟩

/-- §9's "x and y are in IP", right half. -/
def rowSpIp2 : CL.Sentence :=
  hornRow ["x", "y"] [⟨.c RDFS.rdfsSubPropertyOf, .v "x", .v "y"⟩]
    ⟨.c RDFS.rdfType, .v "y", .c RDFS.rdfProperty⟩

/-- rdfs10's condition: subClassOf is reflexive on classes. -/
def rowScRefl : CL.Sentence :=
  hornRow ["x"] [⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfsClass⟩]
    ⟨.c RDFS.rdfsSubClassOf, .v "x", .v "x"⟩

/-- §9's "x and y are in IC", left half. -/
def rowScIc1 : CL.Sentence :=
  hornRow ["x", "y"] [⟨.c RDFS.rdfsSubClassOf, .v "x", .v "y"⟩]
    ⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfsClass⟩

/-- §9's "x and y are in IC", right half. -/
def rowScIc2 : CL.Sentence :=
  hornRow ["x", "y"] [⟨.c RDFS.rdfsSubClassOf, .v "x", .v "y"⟩]
    ⟨.c RDFS.rdfType, .v "y", .c RDFS.rdfsClass⟩

/-- rdfs8's condition: every class is a subclass of `rdfs:Resource`. -/
def rowClassRes : CL.Sentence :=
  hornRow ["x"] [⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfsClass⟩]
    ⟨.c RDFS.rdfsSubClassOf, .v "x", .c RDFS.rdfsResource⟩

/-- rdfs13's condition: every datatype is a subclass of
`rdfs:Literal`. -/
def rowDtLit : CL.Sentence :=
  hornRow ["x"] [⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfsDatatype⟩]
    ⟨.c RDFS.rdfsSubClassOf, .v "x", .c RDFS.rdfsLiteral⟩

/-- rdfs12's condition: every container-membership property is a
subproperty of `rdfs:member`. -/
def rowCmpMember : CL.Sentence :=
  hornRow ["x"]
    [⟨.c RDFS.rdfType, .v "x", .c RDFS.rdfsContainerMembershipProperty⟩]
    ⟨.c RDFS.rdfsSubPropertyOf, .v "x", .c RDFS.rdfsMember⟩

/-! ## The axiom families as ground-atom schemas

Row indices are the NATIVE axiomaticity predicates, which carry the
infinite `rdf:_n` families (module header). -/

/-- The RDF axiomatic rows: one ground atom per `RDF.RdfAxiomatic`
triple (8 finite rows + the infinite `rdf:_n rdf:type rdf:Property`
family). -/
def rdfAxiomSchema : Schema := fun s =>
  ∃ t : RDF.Triple, RDF.RdfAxiomatic t ∧ s = tripleAtom t

/-- The RDFS axiomatic rows: 38 finite rows + the three infinite
`rdf:_n` families. -/
def rdfsAxiomSchema : Schema := fun s =>
  ∃ t : RDF.Triple, RDF.RdfsAxiomatic t ∧ s = tripleAtom t

/-- The rdfs1 rows for a datatype set: every recognised datatype IRI
is an `rdfs:Datatype`. -/
def datatypeSchema (Dset : RDF.DatatypeSet) : Schema := fun s =>
  ∃ a : RDF.WfIri, Dset a ∧
    s = tripleAtom ⟨.iri a, RDFS.rdfType, .iri RDFS.rdfsDatatype⟩

/-! ## Ground atoms, characterised through the transport pair -/

/-- Both-position-IRI check for the axiom tables. -/
def isIriIriB : RDF.Triple → Bool
  | ⟨.iri _, _, .iri _⟩ => true
  | _ => false

theorem shape_of_isIriIri {t : RDF.Triple} (h : isIriIriB t = true) :
    ∃ s o : RDF.WfIri, t = ⟨.iri s, t.p, .iri o⟩ := by
  obtain ⟨ts, tp, to⟩ := t
  cases ts with
  | iri s =>
      cases to with
      | iri o => exact ⟨s, o, rfl⟩
      | bnode b => exact absurd h (by simp [isIriIriB])
      | literal l => exact absurd h (by simp [isIriIriB])
      | tripleTerm a b c => exact absurd h (by simp [isIriIriB])
  | bnode b => exact absurd h (by simp [isIriIriB])

theorem rdfAxiomatic_iriIri {t : RDF.Triple} (h : RDF.RdfAxiomatic t) :
    isIriIriB t = true := by
  rcases h with hmem | ⟨i, _, rfl⟩
  · exact List.all_eq_true.mp
      (by decide : RDF.rdfAxiomaticTriples.all isIriIriB = true) t hmem
  · rfl

theorem rdfsAxiomatic_iriIri {t : RDF.Triple} (h : RDF.RdfsAxiomatic t) :
    isIriIriB t = true := by
  rcases h with hmem | ⟨i, _, hrow⟩
  · exact List.all_eq_true.mp
      (by decide : RDF.rdfsAxiomaticTriples.all isIriIriB = true) t hmem
  · rcases hrow with rfl | rfl | rfl <;> rfl

/-- A both-IRI ground atom is satisfied exactly when it holds under
the restriction — at ANY assignment (the triple mentions no blank
node). -/
theorem satisfies_iriAtom_restrict_iff (i : CL.Interp) (s p o : RDF.WfIri)
    (a : RDF.BnodeAssignment i.dom) :
    CL.Satisfies i (tripleAtom ⟨.iri s, p, .iri o⟩) ↔
      RDF.TripleHolds (restrictInterp i) a ⟨.iri s, p, .iri o⟩ :=
  sat_tripleAtom_restrict i a (freshVal_iName i) _ (fun _ hb => nomatch hb)

/-- The lift-side twin. -/
theorem satisfies_iriAtom_lift_iff (r : RDF.Interp) (s p o : RDF.WfIri)
    (a : RDF.BnodeAssignment r.idom) :
    CL.Satisfies (liftInterp r) (tripleAtom ⟨.iri s, p, .iri o⟩) ↔
      RDF.TripleHolds r a ⟨.iri s, p, .iri o⟩ :=
  sat_tripleAtom_lift r a (freshVal_iName (liftInterp r)) _
    (fun _ hb => nomatch hb)

theorem satisfiesSchema_rdfAxioms_iff (i : CL.Interp) :
    SatisfiesSchema i rdfAxiomSchema ↔ RDF.CondRdfAxioms (restrictInterp i) := by
  constructor
  · intro h a t ht
    obtain ⟨s, o, heq⟩ := shape_of_isIriIri (rdfAxiomatic_iriIri ht)
    rw [heq]
    exact (satisfies_iriAtom_restrict_iff i s t.p o a).mp
      (h _ ⟨t, ht, by rw [heq]⟩)
  · rintro hc s ⟨t, ht, rfl⟩
    obtain ⟨s', o', heq⟩ := shape_of_isIriIri (rdfAxiomatic_iriIri ht)
    rw [heq]
    exact (satisfies_iriAtom_restrict_iff i s' t.p o'
      (fun _ => i.domWit)).mpr (heq ▸ hc (fun _ => i.domWit) t ht)

theorem satisfiesSchema_rdfsAxioms_iff (i : CL.Interp) :
    SatisfiesSchema i rdfsAxiomSchema ↔
      RDF.CondRdfsAxioms (restrictInterp i) := by
  constructor
  · intro h a t ht
    obtain ⟨s, o, heq⟩ := shape_of_isIriIri (rdfsAxiomatic_iriIri ht)
    rw [heq]
    exact (satisfies_iriAtom_restrict_iff i s t.p o a).mp
      (h _ ⟨t, ht, by rw [heq]⟩)
  · rintro hc s ⟨t, ht, rfl⟩
    obtain ⟨s', o', heq⟩ := shape_of_isIriIri (rdfsAxiomatic_iriIri ht)
    rw [heq]
    exact (satisfies_iriAtom_restrict_iff i s' t.p o'
      (fun _ => i.domWit)).mpr (heq ▸ hc (fun _ => i.domWit) t ht)

theorem satisfiesSchema_datatype_iff (i : CL.Interp) (Dset : RDF.DatatypeSet) :
    SatisfiesSchema i (datatypeSchema Dset) ↔
      RDF.CondDatatypes Dset (restrictInterp i) := by
  constructor
  · intro h a ha
    exact (satisfies_iriAtom_restrict_iff i a RDFS.rdfType RDFS.rdfsDatatype
      (fun _ => i.domWit)).mp (h _ ⟨a, ha, rfl⟩)
  · rintro hc s ⟨a, ha, rfl⟩
    exact (satisfies_iriAtom_restrict_iff i a RDFS.rdfType RDFS.rdfsDatatype
      (fun _ => i.domWit)).mpr (hc a ha)

/-! ## Per-row characterisation against the native conditions -/

theorem satisfies_rowRdfProperty_iff (i : CL.Interp) :
    CL.Satisfies i rowRdfProperty ↔ RDF.CondRdfProperty (restrictInterp i) := by
  unfold rowRdfProperty
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h p x y h1
    have hh := h (fun n => if n = "p" then p else if n = "x" then x else y)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "p") (f "x") (f "y") hb

theorem satisfies_rowResource_iff (i : CL.Interp) :
    CL.Satisfies i rowResource ↔ RDF.CondResource (restrictInterp i) := by
  unfold rowResource
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x
    have hh := h (fun _ => x)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh
  · intro hc f _
    exact hc (f "x")

theorem satisfies_rowSpRefl_iff (i : CL.Interp) :
    CL.Satisfies i rowSpRefl ↔ RDF.CondSubPropertyOfRefl (restrictInterp i) := by
  unfold rowSpRefl
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x h1
    have hh := h (fun _ => x)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") hb

theorem satisfies_rowScRefl_iff (i : CL.Interp) :
    CL.Satisfies i rowScRefl ↔ RDF.CondSubClassOfRefl (restrictInterp i) := by
  unfold rowScRefl
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x h1
    have hh := h (fun _ => x)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") hb

theorem satisfies_rowSpIp_iff (i : CL.Interp) :
    (CL.Satisfies i rowSpIp1 ∧ CL.Satisfies i rowSpIp2) ↔
      RDF.CondSubPropertyOfIp (restrictInterp i) := by
  unfold rowSpIp1 rowSpIp2
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide),
      satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · rintro ⟨h1, h2⟩ x y hxy
    constructor
    · have hh := h1 (fun n => if n = "x" then x else y)
      simp [HAtom.HoldsN, HTerm.valN] at hh
      exact hh hxy
    · have hh := h2 (fun n => if n = "x" then x else y)
      simp [HAtom.HoldsN, HTerm.valN] at hh
      exact hh hxy
  · intro hc
    constructor
    · intro f hb
      simp [HAtom.HoldsN, HTerm.valN] at hb
      exact (hc (f "x") (f "y") hb).1
    · intro f hb
      simp [HAtom.HoldsN, HTerm.valN] at hb
      exact (hc (f "x") (f "y") hb).2

theorem satisfies_rowScIc_iff (i : CL.Interp) :
    (CL.Satisfies i rowScIc1 ∧ CL.Satisfies i rowScIc2) ↔
      RDF.CondSubClassOfIc (restrictInterp i) := by
  unfold rowScIc1 rowScIc2
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide),
      satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · rintro ⟨h1, h2⟩ x y hxy
    constructor
    · have hh := h1 (fun n => if n = "x" then x else y)
      simp [HAtom.HoldsN, HTerm.valN] at hh
      exact hh hxy
    · have hh := h2 (fun n => if n = "x" then x else y)
      simp [HAtom.HoldsN, HTerm.valN] at hh
      exact hh hxy
  · intro hc
    constructor
    · intro f hb
      simp [HAtom.HoldsN, HTerm.valN] at hb
      exact (hc (f "x") (f "y") hb).1
    · intro f hb
      simp [HAtom.HoldsN, HTerm.valN] at hb
      exact (hc (f "x") (f "y") hb).2

theorem satisfies_rowClassRes_iff (i : CL.Interp) :
    CL.Satisfies i rowClassRes ↔
      RDF.CondClassSubclassResource (restrictInterp i) := by
  unfold rowClassRes
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x h1
    have hh := h (fun _ => x)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") hb

theorem satisfies_rowDtLit_iff (i : CL.Interp) :
    CL.Satisfies i rowDtLit ↔
      RDF.CondDatatypeSubclassLiteral (restrictInterp i) := by
  unfold rowDtLit
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x h1
    have hh := h (fun _ => x)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") hb

theorem satisfies_rowCmpMember_iff (i : CL.Interp) :
    CL.Satisfies i rowCmpMember ↔ RDF.CondCmpMember (restrictInterp i) := by
  unfold rowCmpMember
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x h1
    have hh := h (fun _ => x)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") hb

/-! ## The schemas -/

/-- **The RDF-rung schema** (RDF 1.1 Semantics §8): the rdfD2-shaped
typing row plus the RDF axiom family. DEVIATION from the design
document's `rdfSchema (D : List WfIri)`: the native RDF-rung bundle
`RDF.RdfConditions` carries no datatype parameter (rdfD1 is excluded
by both engines), so neither does the schema. -/
def rdfSchema : Schema := fun s =>
  s = rowRdfProperty ∨ rdfAxiomSchema s

/-- **The full RDFS schema** (RDF 1.1 Semantics §9): the seventeen
Horn rows (six ρdf + eleven above), both axiom families, and the
rdfs1 datatype rows for `Dset` and for the always-recognised minimal
set (`RDF.dMinimal`). -/
def rdfsSchema (Dset : RDF.DatatypeSet) : Schema := fun s =>
  s = rowRdfProperty ∨ s = rowResource ∨ s = rowSpRefl ∨ s = rowSpIp1 ∨
  s = rowSpIp2 ∨ s = rowScRefl ∨ s = rowScIc1 ∨ s = rowScIc2 ∨
  s = rowClassRes ∨ s = rowDtLit ∨ s = rowCmpMember ∨
  rhoDfSchema s ∨ rdfAxiomSchema s ∨ rdfsAxiomSchema s ∨
  datatypeSchema Dset s ∨ datatypeSchema RDF.dMinimal s

/-- The ρdf schema is a sub-schema of every RDFS schema. -/
theorem rhoDf_sub_rdfsSchema (Dset : RDF.DatatypeSet) :
    ∀ s, rhoDfSchema s → rdfsSchema Dset s := by
  intro s hs
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl hs)))))))))))

/-! ## Schema satisfaction IS the native condition bundle -/

theorem satisfiesSchema_rdf_iff (i : CL.Interp) :
    SatisfiesSchema i rdfSchema ↔ RDF.RdfConditions (restrictInterp i) := by
  constructor
  · intro h
    exact ⟨(satisfies_rowRdfProperty_iff i).mp (h _ (Or.inl rfl)),
           (satisfiesSchema_rdfAxioms_iff i).mp
             (fun s hs => h s (Or.inr hs))⟩
  · rintro ⟨hprop, hax⟩ s hs
    rcases hs with rfl | hs
    · exact (satisfies_rowRdfProperty_iff i).mpr hprop
    · exact (satisfiesSchema_rdfAxioms_iff i).mpr hax s hs

theorem satisfiesSchema_rdfs_iff (i : CL.Interp) (Dset : RDF.DatatypeSet) :
    SatisfiesSchema i (rdfsSchema Dset) ↔
      RDF.RdfsConditions Dset (restrictInterp i) := by
  constructor
  · intro h
    have hrho : RDF.RhoDfConditions (restrictInterp i) :=
      (satisfiesSchema_rhoDf_iff i).mp
        (fun s hs => h s (rhoDf_sub_rdfsSchema Dset s hs))
    obtain ⟨hd, hr, hsp, hspt, hsc, hsct⟩ := hrho
    refine ⟨⟨(satisfies_rowRdfProperty_iff i).mp (h _ (Or.inl rfl)),
             (satisfiesSchema_rdfAxioms_iff i).mp (fun s hs =>
               h s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))))))))))))⟩,
           hd, hr,
           (satisfiesSchema_datatype_iff i Dset).mp (fun s hs =>
             h s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
               (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                 (Or.inl hs)))))))))))))))),
           (satisfiesSchema_datatype_iff i RDF.dMinimal).mp (fun s hs =>
             h s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
               (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                 (Or.inr hs)))))))))))))))),
           (satisfies_rowResource_iff i).mp (h _ (Or.inr (Or.inl rfl))),
           hsp, hspt,
           (satisfies_rowSpRefl_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inl rfl)))),
           (satisfies_rowSpIp_iff i).mp
             ⟨h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
              h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩,
           hsc, hsct,
           (satisfies_rowScRefl_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
           (satisfies_rowScIc_iff i).mp
             ⟨h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl rfl))))))),
              h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl rfl))))))))⟩,
           (satisfies_rowClassRes_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
               (Or.inr (Or.inl rfl)))))))))),
           (satisfies_rowDtLit_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
               (Or.inr (Or.inr (Or.inl rfl))))))))))),
           (satisfies_rowCmpMember_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
               (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))),
           (satisfiesSchema_rdfsAxioms_iff i).mp (fun s hs =>
             h s (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
               (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                 (Or.inl hs)))))))))))))))⟩
  · rintro ⟨⟨hprop, hrdfax⟩, hdom, hran, hdt, hdtm, hres, hsp, hsptr,
            hsprefl, hspip, hsc, hsctr, hscrefl, hscic, hcsr, hdsl, hcmp,
            hrdfsax⟩ s hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | hrho | hax | hax | hdts | hdts
    · exact (satisfies_rowRdfProperty_iff i).mpr hprop
    · exact (satisfies_rowResource_iff i).mpr hres
    · exact (satisfies_rowSpRefl_iff i).mpr hsprefl
    · exact ((satisfies_rowSpIp_iff i).mpr hspip).1
    · exact ((satisfies_rowSpIp_iff i).mpr hspip).2
    · exact (satisfies_rowScRefl_iff i).mpr hscrefl
    · exact ((satisfies_rowScIc_iff i).mpr hscic).1
    · exact ((satisfies_rowScIc_iff i).mpr hscic).2
    · exact (satisfies_rowClassRes_iff i).mpr hcsr
    · exact (satisfies_rowDtLit_iff i).mpr hdsl
    · exact (satisfies_rowCmpMember_iff i).mpr hcmp
    · exact (satisfiesSchema_rhoDf_iff i).mpr
        ⟨hdom, hran, hsp, hsptr, hsc, hsctr⟩ s hrho
    · exact (satisfiesSchema_rdfAxioms_iff i).mpr hrdfax s hax
    · exact (satisfiesSchema_rdfsAxioms_iff i).mpr hrdfsax s hax
    · exact (satisfiesSchema_datatype_iff i Dset).mpr hdt s hdts
    · exact (satisfiesSchema_datatype_iff i RDF.dMinimal).mpr hdtm s hdts

/-! ## The condition bundles transfer through restrict-of-lift -/

theorem tripleHolds_restrict_lift_iri (r : RDF.Interp) (s p o : RDF.WfIri)
    (a : RDF.BnodeAssignment (restrictInterp (liftInterp r)).idom)
    (a' : RDF.BnodeAssignment r.idom)
    (h : RDF.TripleHolds r a' ⟨.iri s, p, .iri o⟩) :
    RDF.TripleHolds (restrictInterp (liftInterp r)) a ⟨.iri s, p, .iri o⟩ := by
  show (restrictInterp (liftInterp r)).iext
    ((restrictInterp (liftInterp r)).iIri p)
    ((restrictInterp (liftInterp r)).iIri s)
    ((restrictInterp (liftInterp r)).iIri o)
  simp only [restrict_lift_iIri]
  exact h

theorem rdfConditions_restrict_lift (r : RDF.Interp)
    (hr : RDF.RdfConditions r) :
    RDF.RdfConditions (restrictInterp (liftInterp r)) := by
  obtain ⟨hprop, hax⟩ := hr
  constructor
  · intro p x y h1
    simp only [RDF.icext, restrict_lift_iIri]
    exact hprop p.2 x.2 y.2 h1
  · intro a t ht
    obtain ⟨s, o, heq⟩ := shape_of_isIriIri (rdfAxiomatic_iriIri ht)
    rw [heq]
    exact tripleHolds_restrict_lift_iri r s t.p o a (fun _ => r.idomWit)
      (heq ▸ hax (fun _ => r.idomWit) t ht)

theorem rdfsConditions_restrict_lift (Dset : RDF.DatatypeSet)
    (r : RDF.Interp) (hr : RDF.RdfsConditions Dset r) :
    RDF.RdfsConditions Dset (restrictInterp (liftInterp r)) := by
  obtain ⟨hrdf, hdom, hran, hdt, hdtm, hres, hsp, hsptr, hsprefl, hspip,
          hsc, hsctr, hscrefl, hscic, hcsr, hdsl, hcmp, hrdfsax⟩ := hr
  obtain ⟨hd', hr', hsp', hspt', hsc', hsct'⟩ :=
    rhoDfConditions_restrict_lift r ⟨hdom, hran, hsp, hsptr, hsc, hsctr⟩
  refine ⟨rdfConditions_restrict_lift r hrdf, hd', hr', ?_, ?_, ?_, hsp',
          hspt', ?_, ?_, hsc', hsct', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [RDF.icext, restrict_lift_iIri]
    exact hdt a ha
  · intro a ha
    simp only [RDF.icext, restrict_lift_iIri]
    exact hdtm a ha
  · intro x
    simp only [RDF.icext, restrict_lift_iIri]
    exact hres x.2
  · intro x hx
    simp only [RDF.icext, restrict_lift_iIri] at hx ⊢
    exact hsprefl x.2 hx
  · intro x y hxy
    simp only [restrict_lift_iIri] at hxy
    simp only [RDF.icext, restrict_lift_iIri]
    exact hspip x.2 y.2 hxy
  · intro x hx
    simp only [RDF.icext, restrict_lift_iIri] at hx ⊢
    exact hscrefl x.2 hx
  · intro x y hxy
    simp only [restrict_lift_iIri] at hxy
    simp only [RDF.icext, restrict_lift_iIri]
    exact hscic x.2 y.2 hxy
  · intro x hx
    simp only [RDF.icext, restrict_lift_iIri] at hx ⊢
    exact hcsr x.2 hx
  · intro x hx
    simp only [RDF.icext, restrict_lift_iIri] at hx ⊢
    exact hdsl x.2 hx
  · intro x hx
    simp only [RDF.icext, restrict_lift_iIri] at hx ⊢
    exact hcmp x.2 hx
  · intro a t ht
    obtain ⟨s, o, heq⟩ := shape_of_isIriIri (rdfsAxiomatic_iriIri ht)
    rw [heq]
    exact tripleHolds_restrict_lift_iri r s t.p o a (fun _ => r.idomWit)
      (heq ▸ hrdfsax (fun _ => r.idomWit) t ht)

/-! ## The stage 2 gate theorems, RDF and RDFS rungs -/

/-- **RDF-rung adequacy**: entailment under the RDF schema between
translated graphs coincides with native RDF entailment
(`RDF.RdfEntails`), unconditionally. -/
theorem unified_adequate_rdf (g h : RDF.Graph) :
    EntailsSchema condTrue rdfSchema [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RdfEntails g h := by
  constructor
  · intro hE r hr hg
    have h1 : CL.Satisfies (liftInterp r) (rdfToTheory g) :=
      (satisfies_rdfToTheory_lift r g).mpr hg
    have h2 : CL.Satisfies (liftInterp r) (rdfToTheory h) :=
      hE (liftInterp r) True.intro
        ((satisfiesSchema_rdf_iff _).mpr (rdfConditions_restrict_lift r hr))
        (fun s hs => by
          obtain rfl := List.mem_singleton.mp hs
          exact h1)
    exact (satisfies_rdfToTheory_lift r h).mp h2
  · intro hMt i _ hsch hsat
    have h1 : RDF.Satisfies (restrictInterp i) g :=
      (satisfies_rdfToTheory_restrict i g).mp
        (hsat _ (List.mem_singleton.mpr rfl))
    exact (satisfies_rdfToTheory_restrict i h).mpr
      (hMt (restrictInterp i) ((satisfiesSchema_rdf_iff i).mp hsch) h1)

/-- **Full-RDFS adequacy** (module header on why this is a full iff
despite Finding C-1): entailment under the RDFS schema between
translated graphs coincides with native RDFS entailment
(`RDF.RdfsEntails`), unconditionally, for every datatype set. -/
theorem unified_adequate_rdfs (Dset : RDF.DatatypeSet) (g h : RDF.Graph) :
    EntailsSchema condTrue (rdfsSchema Dset) [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RdfsEntails Dset g h := by
  constructor
  · intro hE r hr hg
    have h1 : CL.Satisfies (liftInterp r) (rdfToTheory g) :=
      (satisfies_rdfToTheory_lift r g).mpr hg
    have h2 : CL.Satisfies (liftInterp r) (rdfToTheory h) :=
      hE (liftInterp r) True.intro
        ((satisfiesSchema_rdfs_iff _ Dset).mpr
          (rdfsConditions_restrict_lift Dset r hr))
        (fun s hs => by
          obtain rfl := List.mem_singleton.mp hs
          exact h1)
    exact (satisfies_rdfToTheory_lift r h).mp h2
  · intro hMt i _ hsch hsat
    have h1 : RDF.Satisfies (restrictInterp i) g :=
      (satisfies_rdfToTheory_restrict i g).mp
        (hsat _ (List.mem_singleton.mpr rfl))
    exact (satisfies_rdfToTheory_restrict i h).mpr
      (hMt (restrictInterp i) ((satisfiesSchema_rdfs_iff i Dset).mp hsch) h1)

/-- ρdf-schema entailment implies RDFS-schema entailment (schema
monotonicity through the sub-schema inclusion). -/
theorem rhoDf_entails_rdfs_entails (Dset : RDF.DatatypeSet)
    {ps : List CL.Sentence} {c : CL.Sentence}
    (h : EntailsSchema condTrue rhoDfSchema ps c) :
    EntailsSchema condTrue (rdfsSchema Dset) ps c :=
  entailsSchema_mono (fun _ h => h) (rhoDf_sub_rdfsSchema Dset) h

end L4Factoidal.Unified

/-! ## Native bridges introduced with this landing (`RDF` namespace,
per the `Unified/DSchema.lean` convention) -/

namespace L4Factoidal.RDF

open L4Factoidal.RDFS (DerivesFull)
open L4Factoidal.OWL (CondDomain CondRange)

theorem denot_subject_toTerm (i : Interp) (a : BnodeAssignment i.idom)
    (s : Subject) : denotTerm i a s.toTerm = denotSubject i a s := by
  cases s <;> rfl

/-- Everything `DerivesFull` derives is true, in every interpretation
meeting the §8/§9 conditions, under the same assignment that makes the
graph and axiom set true — the truth-preservation induction the
closure-soundness corollary rests on. One case per rule row; each is
one condition of `RdfsConditions`. -/
theorem derivesFull_holds {Dset : DatatypeSet} {i : Interp}
    (hc : RdfsConditions Dset i) {a : BnodeAssignment i.idom}
    {ax g : Graph} (hax : ∀ u ∈ ax, TripleHolds i a u)
    (hg : HoldsAll i a g) {t : Triple} (h : DerivesFull ax g t) :
    TripleHolds i a t := by
  obtain ⟨⟨hprop, _⟩, hdom, hran, _, _, hres, hsp, hsptr, hsprefl, _,
          hsc, hsctr, hscrefl, _, hcsr, hdsl, hcmp, _⟩ := hc
  induction h with
  | base hm => exact hg _ hm
  | axiomatic hm => exact hax _ hm
  | rdfD2 _ ih => exact hprop _ _ _ ih
  | rdfs2 _ _ ih1 ih2 => exact hdom _ _ _ _ ih1 ih2
  | rdfs3 _ _ hsub ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      rw [denot_toSubject? i a hsub]
      exact hran _ _ _ _ ih1 ih2
  | rdfs4a _ ih => exact hres _
  | rdfs4b _ hsub ih =>
      simp only [TripleHolds] at ⊢
      rw [denot_toSubject? i a hsub]
      exact hres _
  | rdfs5 _ hsub _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      rw [← denot_toSubject? i a hsub] at ih1
      exact hsptr _ _ _ ih1 ih2
  | rdfs6 _ ih =>
      simp only [TripleHolds] at ih ⊢
      rw [denot_subject_toTerm]
      exact hsprefl _ ih
  | rdfs7 _ _ ih1 ih2 => exact hsp _ _ _ _ ih1 ih2
  | rdfs8 _ ih => exact hcsr _ ih
  | rdfs9 _ _ ih1 ih2 => exact hsc _ _ _ ih2 ih1
  | rdfs10 _ ih =>
      simp only [TripleHolds] at ih ⊢
      rw [denot_subject_toTerm]
      exact hscrefl _ ih
  | rdfs11 _ hsub _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      rw [← denot_toSubject? i a hsub] at ih1
      exact hsctr _ _ _ ih1 ih2
  | rdfs12 _ ih => exact hcmp _ ih
  | rdfs13 _ ih => exact hdsl _ ih

/-- The seeded axiom set holds in every interpretation meeting the
conditions, under every assignment — provided the harvested `rdf:_n`
slice really is a slice of the family (`IsRdfMemberIri`), AND
`rdf:XMLLiteral` is recognised (`hxml`). The second hypothesis exists
because the closure's seed table `RDFS.rdfsAxiomaticTriplesFixed`
carries two `rdf:XMLLiteral` rows that RDF 1.1 Semantics §9.3 does NOT
list as RDFS axiomatic triples (the specification's note after the
table: "RDF-D interpretations MAY fail to recognize these datatypes"),
so the native `RdfsAxiomatic` predicate rightly excludes them; the two
rows are true exactly when `rdf:XMLLiteral ∈ D` (via `CondDatatypes`
and `CondDatatypeSubclassLiteral`). -/
theorem axiomaticTriples_hold {i : Interp} (a : BnodeAssignment i.idom)
    (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    (hrdfax : CondRdfAxioms i) (hrdfsax : CondRdfsAxioms i)
    (hdt : CondDatatypes (fun x => x ∈ D) i)
    (hdsl : CondDatatypeSubclassLiteral i)
    (hxml : rdfXMLLiteral ∈ D) :
    ∀ u ∈ RDFS.axiomaticTriples D cmps, TripleHolds i a u := by
  intro u hu
  unfold RDFS.axiomaticTriples RDFS.rdfsAxiomaticTriples at hu
  rcases List.mem_append.mp hu with h1 | h23
  · have hsplit : RDFS.rdfAxiomaticTriples cmps
        = RDFS.rdfAxiomaticTriples [] ++ cmps.map
            (fun c => RDFS.iriTriple c RDFS.rdfType RDFS.rdfProperty) := by
      simp [RDFS.rdfAxiomaticTriples]
    rw [hsplit] at h1
    rcases List.mem_append.mp h1 with h8 | hcm
    · refine hrdfax a u (Or.inl ?_)
      exact of_decide_eq_true (List.all_eq_true.mp (by decide :
        (RDFS.rdfAxiomaticTriples []).all
          (fun x => decide (x ∈ RDF.rdfAxiomaticTriples)) = true) u h8)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcm
      exact hrdfax a _ (Or.inr ⟨c, hcmps c hc, rfl⟩)
  · rcases List.mem_append.mp h23 with h2 | h3
    · rcases List.mem_append.mp h2 with hfx | hcont
      · have hcases := of_decide_eq_true (List.all_eq_true.mp (by decide :
          RDFS.rdfsAxiomaticTriplesFixed.all
            (fun x => decide (x ∈ RDF.rdfsAxiomaticTriples ∨
              x = RDFS.iriTriple rdfXMLLiteral RDFS.rdfType RDFS.rdfsDatatype ∨
              x = RDFS.iriTriple rdfXMLLiteral RDFS.rdfsSubClassOf
                    RDFS.rdfsLiteral)) = true) u hfx)
        rcases hcases with hmem | rfl | rfl
        · exact hrdfsax a u (Or.inl hmem)
        · exact hdt rdfXMLLiteral hxml
        · exact hdsl _ (hdt rdfXMLLiteral hxml)
      · obtain ⟨c, hc, hin⟩ := List.mem_flatMap.mp hcont
        simp only [RDFS.iriTriple, List.mem_cons, List.not_mem_nil,
                   or_false] at hin
        rcases hin with rfl | rfl | rfl
        · exact hrdfsax a _ (Or.inr ⟨c, hcmps c hc, Or.inl rfl⟩)
        · exact hrdfsax a _ (Or.inr ⟨c, hcmps c hc, Or.inr (Or.inl rfl)⟩)
        · exact hrdfsax a _ (Or.inr ⟨c, hcmps c hc, Or.inr (Or.inr rfl)⟩)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h3
      exact hdt d hd

end L4Factoidal.RDF

namespace L4Factoidal.Unified

/-! ## Closure soundness at the unified level (design doc §4.2's
`unified_rdfs_closure_sound`) -/

/-- **Everything the full RDFS closure emits is schema-entailed**:
each triple of `RDFS.fullClosure D cmps g` is entailed by `g`'s
translation under the RDFS schema for `D` — provided the harvested
`rdf:_n` slice is genuine (`IsRdfMemberIri`; the engine's own harvest
satisfies this by construction) and `rdf:XMLLiteral ∈ D` (`hxml`: the
closure seeds two `rdf:XMLLiteral` rows that are axiomatic in the seed
table but NOT in RDF 1.1 Semantics §9.3, and they are true in every
§9 interpretation exactly when `rdf:XMLLiteral` is recognised — see
`RDF.axiomaticTriples_hold`). -/
theorem unified_rdfs_closure_sound (D cmps : List RDF.WfIri)
    (hcmps : ∀ c ∈ cmps, RDF.IsRdfMemberIri c)
    (hxml : RDF.rdfXMLLiteral ∈ D) (g : RDF.Graph)
    {t : RDF.Triple} (ht : t ∈ RDFS.fullClosure D cmps g) :
    EntailsSchema condTrue (rdfsSchema (fun x => x ∈ D))
      [rdfToTheory g] (rdfToTheory [t]) := by
  rw [unified_adequate_rdfs]
  intro i hc hsat
  obtain ⟨a, ha⟩ := hsat
  refine ⟨a, fun u hu => ?_⟩
  obtain rfl := List.mem_singleton.mp hu
  refine RDF.derivesFull_holds hc ?_ ha (RDFS.fullClosure_sound D cmps g ht)
  exact RDF.axiomaticTriples_hold a D cmps hcmps hc.1.2
    (fun a' t' ht' => hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a' t' ht')
    hc.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hxml

/-! ## Finding C-1 at the unified level, positive half

`Unified/RhoDfSchema.lean` proved the ρdf schema does NOT entail the
subClassOf self-loop pair; the full RDFS schema DOES (the IC condition
plus subClassOf reflexivity force it). Together: `rdfsSchema` is
STRICTLY stronger than its ρdf sub-schema, and the strictness witness
is exactly C-1's pair. -/

/-- The native positive half (the argument of
`RDFS/RhoDfCompleteness.lean`'s `rdfsEntails_subclassSelfLoop`, restated
for the shared witness pair — that module's pair is file-private). -/
theorem rdfs_entails_selfLoop (Dset : RDF.DatatypeSet) :
    RDF.RdfsEntails Dset c1Prem c1Concl := by
  rintro i hcond ⟨aa, haa⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hrefl, hic, -⟩ := hcond
  have hpremise := haa _ (List.mem_singleton.mpr rfl)
  simp only [RDF.TripleHolds, RDF.denotSubject, RDF.denotTerm] at hpremise
  refine ⟨aa, fun t ht => ?_⟩
  rw [List.mem_singleton.mp ht]
  simp only [RDF.TripleHolds, RDF.denotSubject, RDF.denotTerm]
  exact hrefl _ (hic _ _ hpremise).1

/-- The unified positive half, through the gate. -/
theorem rdfs_entails_selfLoop_unified (Dset : RDF.DatatypeSet) :
    EntailsSchema condTrue (rdfsSchema Dset)
      [rdfToTheory c1Prem] (rdfToTheory c1Concl) :=
  (unified_adequate_rdfs Dset c1Prem c1Concl).mpr (rdfs_entails_selfLoop Dset)

/-! ## Non-vacuity of the RDF/RDFS schemas, by composition with the
native witnesses (`RDF/SemanticsHypothesisWitness.lean`) -/

theorem rdfsSchema_satisfiable (Dset : RDF.DatatypeSet) :
    ∃ i : CL.Interp, SatisfiesSchema i (rdfsSchema Dset) :=
  ⟨liftInterp RDF.trivialInterp,
   (satisfiesSchema_rdfs_iff _ Dset).mpr
     (rdfsConditions_restrict_lift Dset _
       (RDF.trivial_rdfs_conditions Dset))⟩

theorem rdfSchema_satisfiable : ∃ i : CL.Interp, SatisfiesSchema i rdfSchema :=
  ⟨liftInterp RDF.trivialInterp,
   (satisfiesSchema_rdf_iff _).mpr
     (rdfConditions_restrict_lift _ RDF.trivial_rdf_conditions)⟩

/-- RDFS-schema entailment between translated graphs is not the
everything-relation (the native separating interpretation refutes
`RDF.unsatTriple` from the empty graph). -/
theorem rdfsSchema_entails_not_everything (Dset : RDF.DatatypeSet) :
    ¬ EntailsSchema condTrue (rdfsSchema Dset)
        [rdfToTheory []] (rdfToTheory [RDF.unsatTriple]) := by
  rw [unified_adequate_rdfs]
  exact RDF.rdfs_entails_not_everything Dset

theorem rdfSchema_entails_not_everything :
    ¬ EntailsSchema condTrue rdfSchema
        [rdfToTheory []] (rdfToTheory [RDF.unsatTriple]) := by
  rw [unified_adequate_rdf]
  exact RDF.rdf_entails_not_everything

end L4Factoidal.Unified

/-! ## The `rdfs:range` datatype clash, native side -/

namespace L4Factoidal.RDF

/-- The range/type clash condition (RDF 1.1 Semantics §7 + §9, the
model-theoretic counterpart of `hasRangeDatatypeClash` in
`RDF/EntailmentRdfsDatatypeClash.lean`): when a property's range is a
RECOGNISED datatype `c`, no pair of its extension ends in a literal
typed with a DIFFERENT datatype — §7 keeps a recognised datatype's
value space disjoint from any literal not of that datatype (modulo the
numeric chain, which `valueInSpace` handles on the executable side and
which the executable clash rule also excludes by requiring a bare
datatype mismatch). -/
def DRangeCond (D : List WfIri) (i : Interp) : Prop :=
  ∀ c : WfIri, c ∈ D → ∀ l : WfLiteral, l.val.datatype ≠ c →
    ∀ p x : i.idom, i.iext (i.iIri RDFS.rdfsRange) p (i.iIri c) →
      ¬ i.iext p x (i.iLit l)

/-- The combined RDFS+D condition bundle: the §9 conditions, the
D-interpretation conditions of `Unified/DSchema.lean`, and the range
clash condition. -/
def RdfsDInterpCond (Dset : DatatypeSet) (D : List WfIri) (i : Interp) :
    Prop :=
  RdfsConditions Dset i ∧ DInterpCond D i ∧ DRangeCond D i

/-- **RDFS+D entailment, model-theoretically** — the native anchor of
`unified_adequate_rdfs_d`, introduced with this landing (the native
tree's executable side is `rdfsDInconsistent`; it had no
model-theoretic statement). -/
def RdfsDEntailsMt (Dset : DatatypeSet) (D : List WfIri) (g h : Graph) :
    Prop :=
  EntailsUnder (RdfsDInterpCond Dset D) g h

theorem dRangeCond_nil (i : Interp) : DRangeCond [] i :=
  fun _ hc => nomatch hc

end L4Factoidal.RDF

namespace L4Factoidal.Unified

/-! ## The range-clash schema (the `dExclusionSchema` pattern) -/

/-- The clash axiom for a recognised datatype `c` and a literal of a
different datatype: no individual is related, by a property whose
range is `c`, to that literal's individual. Bound names `"x"`, `"p"`
are colon-free (the `FreshVal` discipline). -/
def rangeClashAx (c : RDF.WfIri) (l : RDF.WfLiteral) : CL.Sentence :=
  .neg (.ex [.plain "x", .plain "p"]
    (.conj [.atom (.name "p")
              [.term (.name "x"), .term (embedTerm (.literal l))],
            .atom (.name RDFS.rdfsRange.val)
              [.term (.name "p"), .term (.name c.val)]]))

/-- The clash family: one row per recognised `c` and differently-typed
literal. -/
def rangeClashSchema (D : List RDF.WfIri) : Schema := fun s =>
  ∃ c ∈ D, ∃ l : RDF.WfLiteral, l.val.datatype ≠ c ∧ s = rangeClashAx c l

theorem satisfies_rangeClashAx_iff (i : CL.Interp) (c : RDF.WfIri)
    (l : RDF.WfLiteral) :
    CL.Satisfies i (rangeClashAx c l) ↔
      ∀ xv pv : i.dom,
        ¬ (i.rel pv [xv, litDenot i l] ∧
           i.rel (i.iName RDFS.rdfsRange.val) [pv, i.iName c.val]) := by
  have hfresh : ∀ xv pv : i.dom,
      FreshVal i (CL.updateInd (CL.updateInd i.iName "x" xv) "p" pv) :=
    fun xv pv => freshVal_updateInd
      (freshVal_updateInd (freshVal_iName i) (by decide) xv) (by decide) pv
  have hp : ∀ xv pv : i.dom,
      CL.updateInd (CL.updateInd i.iName "x" xv) "p" pv "p" = pv := by
    intro xv pv; simp [CL.updateInd]
  have hx : ∀ xv pv : i.dom,
      CL.updateInd (CL.updateInd i.iName "x" xv) "p" pv "x" = xv := by
    intro xv pv; simp [CL.updateInd]
  have hrg : ∀ xv pv : i.dom,
      CL.updateInd (CL.updateInd i.iName "x" xv) "p" pv RDFS.rdfsRange.val
        = i.iName RDFS.rdfsRange.val :=
    fun xv pv => hfresh xv pv _ (isIri_has_colon RDFS.rdfsRange.property)
  have hcv : ∀ xv pv : i.dom,
      CL.updateInd (CL.updateInd i.iName "x" xv) "p" pv c.val
        = i.iName c.val :=
    fun xv pv => hfresh xv pv _ (isIri_has_colon c.property)
  simp only [rangeClashAx, CL.Satisfies, CL.Sat, CL.SatExists, CL.SatAll]
  constructor
  · intro hn xv pv ⟨h1, h2⟩
    apply hn
    refine ⟨xv, pv, ?_, ?_, trivial⟩
    · simp only [CL.denotSeq, CL.denotTerm,
                 denot_embedLiteral_fresh i (hfresh xv pv) l, hp, hx]
      exact h1
    · simp only [CL.denotSeq, CL.denotTerm, hp, hrg, hcv]
      exact h2
  · rintro hall ⟨xv, pv, h1, h2, -⟩
    simp only [CL.denotSeq, CL.denotTerm,
               denot_embedLiteral_fresh i (hfresh xv pv) l, hp, hx] at h1
    simp only [CL.denotSeq, CL.denotTerm, hp, hrg, hcv] at h2
    exact hall xv pv ⟨h1, h2⟩

/-- A lifted interpretation meeting the native clash condition
satisfies the clash schema. -/
theorem liftInterp_satisfiesSchema_rangeClash (D : List RDF.WfIri)
    (r : RDF.Interp) (hr : RDF.DRangeCond D r) :
    SatisfiesSchema (liftInterp r) (rangeClashSchema D) := by
  rintro s ⟨c, hcD, l, hne, rfl⟩
  rw [satisfies_rangeClashAx_iff]
  rintro xv pv ⟨h1, h2⟩
  rw [litDenot_lift] at h1
  rw [show (liftInterp r).iName RDFS.rdfsRange.val
        = (some RDFS.rdfsRange.val, r.iIri RDFS.rdfsRange) from
        liftInterp_iName_iri r RDFS.rdfsRange,
      show (liftInterp r).iName c.val = (some c.val, r.iIri c) from
        liftInterp_iName_iri r c] at h2
  exact hr c hcD l hne pv.2 xv.2 h2 h1

/-- The restriction of a clash-schema-satisfying interpretation meets
the native clash condition. -/
theorem restrictInterp_dRangeCond (D : List RDF.WfIri) (i : CL.Interp)
    (hi : SatisfiesSchema i (rangeClashSchema D)) :
    RDF.DRangeCond D (restrictInterp i) := by
  intro c hcD l hne p x h1 h2
  have h := (satisfies_rangeClashAx_iff i c l).mp
    (hi _ ⟨c, hcD, l, hne, rfl⟩)
  exact h x p ⟨h2, h1⟩

/-! ## The combined RDFS+D schema and its gate theorem -/

/-- **The combined schema**: full RDFS rows + the D-interpretation
schema of `Unified/DSchema.lean` + the range-clash family. -/
def rdfsDSchema (Dset : RDF.DatatypeSet) (D : List RDF.WfIri) : Schema :=
  schemaUnion (rdfsSchema Dset) (schemaUnion (dSchema D) (rangeClashSchema D))

/-- **RDFS+D adequacy**: entailment under the combined schema between
translated graphs coincides with native RDFS+D entailment — a full
iff, unconditional, for every `Dset` and recognised list `D`. -/
theorem unified_adequate_rdfs_d (Dset : RDF.DatatypeSet)
    (D : List RDF.WfIri) (g h : RDF.Graph) :
    EntailsSchema condTrue (rdfsDSchema Dset D)
        [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RdfsDEntailsMt Dset D g h := by
  constructor
  · intro hE r hr hg
    obtain ⟨hrdfs, hd, hrange⟩ := hr
    have h1 : CL.Satisfies (liftInterp r) (rdfToTheory g) :=
      (satisfies_rdfToTheory_lift r g).mpr hg
    have hsch : SatisfiesSchema (liftInterp r) (rdfsDSchema Dset D) := by
      rw [rdfsDSchema, satisfiesSchema_union_iff]
      refine ⟨(satisfiesSchema_rdfs_iff _ Dset).mpr
        (rdfsConditions_restrict_lift Dset r hrdfs), ?_⟩
      rw [satisfiesSchema_union_iff]
      exact ⟨liftInterp_satisfiesSchema_d D r hd,
             liftInterp_satisfiesSchema_rangeClash D r hrange⟩
    have h2 : CL.Satisfies (liftInterp r) (rdfToTheory h) :=
      hE (liftInterp r) True.intro hsch (fun s hs => by
        obtain rfl := List.mem_singleton.mp hs
        exact h1)
    exact (satisfies_rdfToTheory_lift r h).mp h2
  · intro hMt i _ hsch hsat
    rw [rdfsDSchema, satisfiesSchema_union_iff] at hsch
    obtain ⟨hs1, hs23⟩ := hsch
    rw [satisfiesSchema_union_iff] at hs23
    obtain ⟨hs2, hs3⟩ := hs23
    have h1 : RDF.Satisfies (restrictInterp i) g :=
      (satisfies_rdfToTheory_restrict i g).mp
        (hsat _ (List.mem_singleton.mpr rfl))
    exact (satisfies_rdfToTheory_restrict i h).mpr
      (hMt (restrictInterp i)
        ⟨(satisfiesSchema_rdfs_iff i Dset).mp hs1,
         restrictInterp_dCond D i hs2,
         restrictInterp_dRangeCond D i hs3⟩ h1)

/-! ## A clash-exhibiting premise entails everything -/

/-- A translated graph exhibiting the range/datatype clash pattern
contradicts its own clash axiom: no schema-satisfying interpretation
satisfies it. -/
theorem rdfsDSchema_clash_unsat (Dset : RDF.DatatypeSet)
    (D : List RDF.WfIri) {g : RDF.Graph} {decl data : RDF.Triple}
    {p c : RDF.WfIri} {l : RDF.WfLiteral}
    (hdecl : decl ∈ g) (hdp : decl.p = RDFS.rdfsRange)
    (hds : decl.s = .iri p) (hdo : decl.o = .iri c) (hcD : c ∈ D)
    (hdata : data ∈ g) (hdatap : data.p = p) (hdatao : data.o = .literal l)
    (hne : l.val.datatype ≠ c) (i : CL.Interp)
    (hsch : SatisfiesSchema i (rdfsDSchema Dset D)) :
    ¬ CL.Satisfies i (rdfToTheory g) := by
  intro hsat
  rw [satisfies_rdfToTheory_iff] at hsat
  obtain ⟨f, hf⟩ := hsat
  have hν : FreshVal i (overrideOn i.iName (graphBnodeNames g) f) :=
    freshVal_overrideOn i (graphBnodeNames_no_colon g) f
  have hexcl := (satisfies_rangeClashAx_iff i c l).mp
    (hsch _ (Or.inr (Or.inr ⟨c, hcD, l, hne, rfl⟩)))
  have hdeclSat := hf decl hdecl
  have hdataSat := hf data hdata
  simp only [tripleAtom] at hdeclSat hdataSat
  rw [hdp, hds, hdo] at hdeclSat
  rw [hdatap, hdatao] at hdataSat
  simp only [CL.Sat, CL.denotSeq, CL.denotTerm, embedSubject, embedTerm,
             hν RDFS.rdfsRange.val
               (isIri_has_colon RDFS.rdfsRange.property),
             hν p.val (isIri_has_colon p.property),
             hν c.val (isIri_has_colon c.property)] at hdeclSat
  simp only [CL.Sat, CL.denotSeq, CL.denotTerm,
             denot_embedLiteral_fresh i hν l,
             hν p.val (isIri_has_colon p.property)] at hdataSat
  exact hexcl _ _ ⟨hdataSat, hdeclSat⟩

/-- The everything-relation on a clash-exhibiting premise — the
unified counterpart of `RDF.rdfsDInconsistent`'s rule (b) verdict. -/
theorem unified_rdfsD_clash_entails_all (Dset : RDF.DatatypeSet)
    (D : List RDF.WfIri) {g : RDF.Graph} {decl data : RDF.Triple}
    {p c : RDF.WfIri} {l : RDF.WfLiteral}
    (hdecl : decl ∈ g) (hdp : decl.p = RDFS.rdfsRange)
    (hds : decl.s = .iri p) (hdo : decl.o = .iri c) (hcD : c ∈ D)
    (hdata : data ∈ g) (hdatap : data.p = p) (hdatao : data.o = .literal l)
    (hne : l.val.datatype ≠ c) (s : CL.Sentence) :
    EntailsSchema condTrue (rdfsDSchema Dset D) [rdfToTheory g] s := by
  intro i _ hsch hsat
  exact absurd (hsat _ (List.mem_singleton.mpr rfl))
    (rdfsDSchema_clash_unsat Dset D hdecl hdp hds hdo hcD hdata hdatap
      hdatao hne i hsch)

/-- The same verdict natively, through the adequacy theorem. -/
theorem rdfsDEntailsMt_clash (Dset : RDF.DatatypeSet)
    (D : List RDF.WfIri) {g : RDF.Graph} {decl data : RDF.Triple}
    {p c : RDF.WfIri} {l : RDF.WfLiteral}
    (hdecl : decl ∈ g) (hdp : decl.p = RDFS.rdfsRange)
    (hds : decl.s = .iri p) (hdo : decl.o = .iri c) (hcD : c ∈ D)
    (hdata : data ∈ g) (hdatap : data.p = p) (hdatao : data.o = .literal l)
    (hne : l.val.datatype ≠ c) (h : RDF.Graph) :
    RDF.RdfsDEntailsMt Dset D g h :=
  (unified_adequate_rdfs_d Dset D g h).mp
    (unified_rdfsD_clash_entails_all Dset D hdecl hdp hds hdo hcD hdata
      hdatap hdatao hne _)

/-! ## The type-application bridge (LBase §2; module header)

`(forall (x c) (iff (rdf:type x c) (c x)))` — LBase's reading of
`rdf:type` as predicate application, which CL's unsegregated universe
permits. A SEPARATE schema: `liftInterp` gives every non-binary
predication an empty extension, so folding the bridge into
`rdfsSchema` would break the gate iff (module header). What holds is
conservativity over translated graphs, by rel-surgery. -/

/-- The bridge sentence. Bound names `"x"`, `"c"` are colon-free. -/
def typeBridgeAx : CL.Sentence :=
  .all (["x", "c"].map .plain)
    (.iff (.atom (.name RDFS.rdfType.val)
             [.term (.name "x"), .term (.name "c")])
          (.atom (.name "c") [.term (.name "x")]))

/-- The bridge as a one-sentence schema. -/
def typeBridge : Schema := fun s => s = typeBridgeAx

/-- Bridge satisfaction, characterised: the binary `rdf:type`
extension and unary predication agree everywhere. -/
theorem satisfies_typeBridge_iff (i : CL.Interp) :
    CL.Satisfies i typeBridgeAx ↔
      ∀ xv cv : i.dom,
        (i.rel (i.iName RDFS.rdfType.val) [xv, cv] ↔ i.rel cv [xv]) := by
  have hb : ∀ f : String → i.dom,
      FreshVal i (overrideOn i.iName ["x", "c"] f) :=
    fun f => freshVal_overrideOn i (by decide) f
  have hx : ∀ f : String → i.dom,
      overrideOn i.iName ["x", "c"] f "x" = f "x" :=
    fun f => if_pos (by simp)
  have hc : ∀ f : String → i.dom,
      overrideOn i.iName ["x", "c"] f "c" = f "c" :=
    fun f => if_pos (by simp)
  unfold typeBridgeAx CL.Satisfies
  simp only [CL.Sat]
  rw [satForall_plains]
  constructor
  · intro h xv cv
    have hh := h (fun n => if n = "x" then xv else cv)
    simp only [CL.Sat, CL.denotSeq, CL.denotTerm, hx, hc,
               hb _ RDFS.rdfType.val
                 (isIri_has_colon RDFS.rdfType.property)] at hh
    simpa using hh
  · intro h f
    simp only [CL.Sat, CL.denotSeq, CL.denotTerm, hx, hc,
               hb _ RDFS.rdfType.val
                 (isIri_has_colon RDFS.rdfType.property)]
    exact h (f "x") (f "c")

/-- **The rel-surgery**: redefine unary predication to read from the
binary `rdf:type` extension; every other arity is untouched. -/
def bridgeify (i : CL.Interp) : CL.Interp :=
  { i with
    rel := fun p args =>
      match args with
      | [x] => i.rel (i.iName RDFS.rdfType.val) [x, p]
      | _ => i.rel p args }

mutual

/-- Denotation never consults `rel`, so the surgery changes no term's
denotation. -/
theorem denotTerm_bridgeify (i : CL.Interp) (ν : String → i.dom)
    (σ : String → List i.dom) :
    ∀ t : CL.Term,
      CL.denotTerm (bridgeify i) ν σ t = CL.denotTerm i ν σ t
  | .name _ => rfl
  | .str _ => rfl
  | .funapp op args => by
      simp only [CL.denotTerm]
      rw [denotTerm_bridgeify i ν σ op, denotSeq_bridgeify i ν σ args]
      rfl
  | .that _ => rfl

theorem denotSeq_bridgeify (i : CL.Interp) (ν : String → i.dom)
    (σ : String → List i.dom) :
    ∀ args : List CL.SeqItem,
      CL.denotSeq (bridgeify i) ν σ args = CL.denotSeq i ν σ args
  | [] => rfl
  | .term t :: r => by
      simp only [CL.denotSeq]
      rw [denotTerm_bridgeify i ν σ t, denotSeq_bridgeify i ν σ r]
      rfl
  | .seqmark m :: r => by
      simp only [CL.denotSeq]
      rw [denotSeq_bridgeify i ν σ r]
      rfl

end

/-- The surgery is invisible to the RDF restriction: `restrictInterp`
reads only binary `rel`, `iName`, `fn` and (through denotation) `iStr`
— none of which the surgery touches. -/
theorem restrictInterp_bridgeify (i : CL.Interp) :
    restrictInterp (bridgeify i) = restrictInterp i := by
  have h : restrictInterp (bridgeify i)
      = { restrictInterp i with
          iLit := fun l => CL.denotTerm (bridgeify i) (bridgeify i).iName
            (fun _ => []) (embedTerm (.literal l)) } := rfl
  rw [h]
  have hlit : (fun l => CL.denotTerm (bridgeify i) (bridgeify i).iName
        (fun _ => []) (embedTerm (.literal l)))
      = (restrictInterp i).iLit := by
    funext l
    exact denotTerm_bridgeify i _ _ _
  rw [hlit]

/-- The surgery makes the bridge true: both sides of the iff read the
same binary `rdf:type` fact by construction. -/
theorem bridgeify_satisfies_bridge (i : CL.Interp) :
    CL.Satisfies (bridgeify i) typeBridgeAx := by
  rw [satisfies_typeBridge_iff]
  intro xv cv
  exact Iff.rfl

theorem satisfies_rdfToTheory_bridgeify (i : CL.Interp) (g : RDF.Graph) :
    CL.Satisfies (bridgeify i) (rdfToTheory g) ↔
      CL.Satisfies i (rdfToTheory g) := by
  rw [satisfies_rdfToTheory_restrict, restrictInterp_bridgeify,
      ← satisfies_rdfToTheory_restrict]

/-- **Conservativity over translated graphs** (module header): adding
the bridge to the RDFS schema changes no entailment between translated
graphs. Left to right is the surgery (any schema-satisfying
interpretation is bridgeified into one that also satisfies the bridge,
agrees on every translated graph, and agrees on the RDFS rows because
its restriction is unchanged); right to left is schema monotonicity. -/
theorem typeBridge_conservative (Dset : RDF.DatatypeSet) (g h : RDF.Graph) :
    EntailsSchema condTrue (schemaUnion (rdfsSchema Dset) typeBridge)
        [rdfToTheory g] (rdfToTheory h)
      ↔ EntailsSchema condTrue (rdfsSchema Dset)
        [rdfToTheory g] (rdfToTheory h) := by
  constructor
  · intro hE i _ hsch hsat
    have hsch' : SatisfiesSchema (bridgeify i)
        (schemaUnion (rdfsSchema Dset) typeBridge) := by
      rw [satisfiesSchema_union_iff]
      constructor
      · rw [satisfiesSchema_rdfs_iff, restrictInterp_bridgeify]
        exact (satisfiesSchema_rdfs_iff i Dset).mp hsch
      · rintro s rfl
        exact bridgeify_satisfies_bridge i
    have hres := hE (bridgeify i) True.intro hsch' (fun s hs => by
      obtain rfl := List.mem_singleton.mp hs
      exact (satisfies_rdfToTheory_bridgeify i g).mpr
        (hsat _ (List.mem_singleton.mpr rfl)))
    exact (satisfies_rdfToTheory_bridgeify i h).mp hres
  · intro hE
    exact entailsSchema_mono (fun _ hi => hi) (fun s hs => Or.inl hs) hE

/-! ## The bridge is NOT conservative outside the translated fragment

The separation is pinned on the LBase class-application sentence
`(C a)`, which is the translation of no RDF graph. -/

/-- LBase class application: the class name in operator position over
the individual. -/
def classApp (c a : RDF.WfIri) : CL.Sentence :=
  .atom (.name c.val) [.term (.name a.val)]

private def baA : RDF.WfIri := ⟨"http://bridge.example/a", by decide⟩
private def baC : RDF.WfIri := ⟨"http://bridge.example/C", by decide⟩

def bridgeDemoG : RDF.Graph := [⟨.iri baA, RDFS.rdfType, .iri baC⟩]

/-- With the bridge, a translated `rdf:type` triple derives the
class-application sentence. -/
theorem bridge_derives_classApp (Dset : RDF.DatatypeSet) :
    EntailsSchema condTrue (schemaUnion (rdfsSchema Dset) typeBridge)
      [rdfToTheory bridgeDemoG] (classApp baC baA) := by
  intro i _ hsch hsat
  have hbr := (satisfies_typeBridge_iff i).mp (hsch typeBridgeAx (Or.inr rfl))
  have hg := hsat _ (List.mem_singleton.mpr rfl)
  rw [satisfies_rdfToTheory_iff] at hg
  obtain ⟨f, hf⟩ := hg
  have hν : FreshVal i (overrideOn i.iName (graphBnodeNames bridgeDemoG) f) :=
    freshVal_overrideOn i (graphBnodeNames_no_colon _) f
  have hatom := hf _ (List.mem_singleton.mpr rfl)
  simp only [tripleAtom, CL.Sat, CL.denotSeq, CL.denotTerm, embedSubject,
             embedTerm,
             hν RDFS.rdfType.val (isIri_has_colon RDFS.rdfType.property),
             hν baA.val (isIri_has_colon baA.property),
             hν baC.val (isIri_has_colon baC.property)] at hatom
  show CL.Sat i i.iName (fun _ => []) (classApp baC baA)
  simp only [classApp, CL.Sat, CL.denotSeq, CL.denotTerm]
  exact (hbr _ _).mp hatom

/-- Without the bridge, the RDFS schema does NOT derive it: the lift
of the trivial interpretation satisfies every RDFS row and every
translated graph, and refutes every unary predication (`liftInterp`
gives non-binary argument lists an empty extension). -/
theorem rdfsSchema_no_classApp (Dset : RDF.DatatypeSet) :
    ¬ EntailsSchema condTrue (rdfsSchema Dset)
        [rdfToTheory bridgeDemoG] (classApp baC baA) := by
  intro hE
  have hsch : SatisfiesSchema (liftInterp RDF.trivialInterp)
      (rdfsSchema Dset) :=
    (satisfiesSchema_rdfs_iff _ Dset).mpr
      (rdfsConditions_restrict_lift Dset _ (RDF.trivial_rdfs_conditions Dset))
  have hsat : CL.Satisfies (liftInterp RDF.trivialInterp)
      (rdfToTheory bridgeDemoG) :=
    (satisfies_rdfToTheory_lift _ _).mpr
      ⟨fun _ => (), fun _ _ => trivial⟩
  have h := hE _ True.intro hsch (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact hsat)
  simp only [classApp, CL.Satisfies, CL.Sat, CL.denotSeq, CL.denotTerm,
             liftInterp] at h

/-! ## A concrete range-clash instance, tied to the executable
detector -/

private def rcP : RDF.WfIri := ⟨"http://clash.example/p", by decide⟩
private def rcA : RDF.WfIri := ⟨"http://clash.example/a", by decide⟩

private def rcLit : RDF.WfLiteral := RDF.Literal.string "abc"

def rangeClashDemoG : RDF.Graph :=
  [⟨.iri rcP, RDFS.rdfsRange, .iri RDF.xsdInteger⟩,
   ⟨.iri rcA, rcP, .literal rcLit⟩]

/-- The demo graph RDFS+D-entails everything — the model-theoretic
verdict the executable detector's `#guard` below agrees with. -/
theorem rangeClash_demo (Dset : RDF.DatatypeSet) (h : RDF.Graph) :
    RDF.RdfsDEntailsMt Dset [RDF.xsdInteger] rangeClashDemoG h :=
  rdfsDEntailsMt_clash Dset [RDF.xsdInteger]
    (List.mem_cons_self ..) rfl rfl rfl (List.mem_singleton.mpr rfl)
    (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)) rfl rfl
    (by decide) h

/-! ## Non-vacuity of the combined RDFS+D bundle and schema, at `D = []`

Over the empty recognised list the datatype and range-clash clauses
are vacuous (`literalIllFormed []` is constantly `false`), so the
native witnesses compose. A witness for nonempty `D` needs a
term-model construction (module header) and is the registry's open
item next to the finite-slice lemma. -/

theorem trivial_rdfsD_cond_nil (Dset : RDF.DatatypeSet) :
    RDF.RdfsDInterpCond Dset [] RDF.trivialInterp :=
  ⟨RDF.trivial_rdfs_conditions Dset,
   ⟨fun _ _ _ => rfl, fun _ hl => by simp [RDF.literalIllFormed] at hl⟩,
   RDF.dRangeCond_nil _⟩

theorem rdfsDSchema_satisfiable_nil (Dset : RDF.DatatypeSet) :
    ∃ i : CL.Interp, SatisfiesSchema i (rdfsDSchema Dset []) := by
  refine ⟨liftInterp RDF.trivialInterp, ?_⟩
  obtain ⟨h1, h2, h3⟩ := trivial_rdfsD_cond_nil Dset
  rw [rdfsDSchema, satisfiesSchema_union_iff]
  refine ⟨(satisfiesSchema_rdfs_iff _ Dset).mpr
    (rdfsConditions_restrict_lift Dset _ h1), ?_⟩
  rw [satisfiesSchema_union_iff]
  exact ⟨liftInterp_satisfiesSchema_d [] _ h2,
         liftInterp_satisfiesSchema_rangeClash [] _ h3⟩

theorem separating_rdfsD_cond_nil (Dset : RDF.DatatypeSet) :
    RDF.RdfsDInterpCond Dset [] RDF.separatingInterp :=
  ⟨RDF.separating_rdfs_conditions Dset,
   ⟨fun _ _ _ => rfl, fun _ hl => by simp [RDF.literalIllFormed] at hl⟩,
   RDF.dRangeCond_nil _⟩

theorem rdfsDEntailsMt_not_everything_nil (Dset : RDF.DatatypeSet) :
    ¬ RDF.RdfsDEntailsMt Dset [] [] [RDF.unsatTriple] := by
  intro h
  exact RDF.separating_rejects
    (h RDF.separatingInterp (separating_rdfsD_cond_nil Dset)
      ⟨fun _ => true, fun _ hm => absurd hm (by simp)⟩)

/-- Combined-schema entailment is not the everything-relation. -/
theorem rdfsDSchema_entails_not_everything_nil (Dset : RDF.DatatypeSet) :
    ¬ EntailsSchema condTrue (rdfsDSchema Dset [])
        [rdfToTheory []] (rdfToTheory [RDF.unsatTriple]) := by
  rw [unified_adequate_rdfs_d]
  exact rdfsDEntailsMt_not_everything_nil Dset

/-! ## Build-time checks -/

section Checks

/- The two `rdf:XMLLiteral` seed rows are in the closure's fixed table
but NOT in the specification's RDFS axiomatic table — the mismatch
that forces the `rdf:XMLLiteral ∈ D` hypothesis on
`unified_rdfs_closure_sound` (see `RDF.axiomaticTriples_hold`). -/

#guard decide (RDFS.iriTriple RDF.rdfXMLLiteral RDFS.rdfType
    RDFS.rdfsDatatype ∈ RDFS.rdfsAxiomaticTriplesFixed)
#guard decide (RDFS.iriTriple RDF.rdfXMLLiteral RDFS.rdfsSubClassOf
    RDFS.rdfsLiteral ∈ RDFS.rdfsAxiomaticTriplesFixed)
#guard !decide (RDFS.iriTriple RDF.rdfXMLLiteral RDFS.rdfType
    RDFS.rdfsDatatype ∈ RDF.rdfsAxiomaticTriples)
#guard !decide (RDFS.iriTriple RDF.rdfXMLLiteral RDFS.rdfsSubClassOf
    RDFS.rdfsLiteral ∈ RDF.rdfsAxiomaticTriples)

/- The executable detector agrees with the model-theoretic clash
verdicts: the range-clash demo is detected, and a clash-free graph is
not. -/

#guard RDF.rdfsDInconsistent rangeClashDemoG [RDF.xsdInteger]
#guard !(RDF.rdfsDInconsistent dNumG [RDF.xsdInteger])

/-! Axiom audit — expected at most `propext` / `Classical.choice` /
`Quot.sound` (Lean's own foundations). No `sorryAx`, nothing
user-declared. -/

#print axioms unified_adequate_rdf
#print axioms unified_adequate_rdfs
#print axioms unified_rdfs_closure_sound
#print axioms RDF.derivesFull_holds
#print axioms RDF.axiomaticTriples_hold
#print axioms rdfs_entails_selfLoop_unified
#print axioms rdfsSchema_satisfiable
#print axioms rdfsSchema_entails_not_everything
#print axioms unified_adequate_rdfs_d
#print axioms unified_rdfsD_clash_entails_all
#print axioms rdfsDEntailsMt_clash
#print axioms rangeClash_demo
#print axioms rdfsDSchema_satisfiable_nil
#print axioms rdfsDEntailsMt_not_everything_nil
#print axioms rdfsDSchema_entails_not_everything_nil
#print axioms typeBridge_conservative
#print axioms bridge_derives_classApp
#print axioms rdfsSchema_no_classApp

end Checks

end L4Factoidal.Unified
