/-
L4Factoidal.RDF.EntailmentRdfsModelTheory — the RDF and RDFS semantic
conditions, and every rule row proved TRUE under them.

Port of `formal/fstar/RDF.Entailment.RDFS.ModelTheory.fst` (952 lines).

`RDF.EntailmentRdfSpec` and `RDF.EntailmentRdfsSpec` transcribe the
SYNTACTIC rule tables of RDF 1.1 Semantics §8 and §9. This module gives
the two rungs their SEMANTIC side — the interpretation conditions those
sections state — and closes the loop: every triple the tables license
is TRUE in every interpretation meeting the conditions that satisfies
the premises.

That is `rdfsLicensed_true`, and it is what makes the rule tables more
than a list. Without it the tables are a transcription nobody has
checked against the semantics; with it, an engine proved to emit only
licensed triples is proved to emit only true ones.

## The conditions are the WEAKEST readings, as at the OWL rung

Only-if halves and IP/IC membership side conditions are dropped where
the specification's own sentence is an implication rather than an
equality. Dropping a condition ENLARGES the interpretation class, and a
soundness result over a larger class is stronger.

## Two conditions carry the axiomatic triples

`CondRdfAxioms` and `CondRdfsAxioms` say every axiomatic triple holds
under EVERY assignment. They are what make the axiomatic rows of the
licensing relation true with no premise, which is exactly their status
in the specification: axioms, not derivations.
-/
import L4Factoidal.RDF.EntailmentRdfsSpec
import L4Factoidal.OWL.Semantics

namespace L4Factoidal.RDF

open L4Factoidal.RDFS
open L4Factoidal.OWL (CondDomain CondRange)

/-! ## The RDF rung's conditions — §8 -/

/-- Everything in some IEXT is a property. -/
def CondRdfProperty (i : Interp) : Prop :=
  ∀ p x y : i.idom, i.iext p x y → icext i p (i.iIri rdfProperty)

/-- Every RDF axiomatic triple holds, under every assignment. -/
def CondRdfAxioms (i : Interp) : Prop :=
  ∀ (a : BnodeAssignment i.idom) (t : Triple), RdfAxiomatic t → TripleHolds i a t

def RdfConditions (i : Interp) : Prop := CondRdfProperty i ∧ CondRdfAxioms i

def RdfEntails (g1 g2 : Graph) : Prop := EntailsUnder RdfConditions g1 g2

/-! ## The RDFS rung's conditions — §9 -/

def CondDatatypes (D : DatatypeSet) (i : Interp) : Prop :=
  ∀ a : WfIri, D a → icext i (i.iIri a) (i.iIri rdfsDatatype)

def CondResource (i : Interp) : Prop := ∀ x : i.idom, icext i x (i.iIri rdfsResource)

def CondSubPropertyOf (i : Interp) : Prop :=
  ∀ x y u v : i.idom, i.iext (i.iIri rdfsSubPropertyOf) x y → i.iext x u v → i.iext y u v

def CondSubPropertyOfTrans (i : Interp) : Prop :=
  ∀ x y z : i.idom, i.iext (i.iIri rdfsSubPropertyOf) x y →
    i.iext (i.iIri rdfsSubPropertyOf) y z → i.iext (i.iIri rdfsSubPropertyOf) x z

def CondSubPropertyOfRefl (i : Interp) : Prop :=
  ∀ x : i.idom, icext i x (i.iIri rdfProperty) → i.iext (i.iIri rdfsSubPropertyOf) x x

def CondSubClassOf (i : Interp) : Prop :=
  ∀ x y u : i.idom, i.iext (i.iIri rdfsSubClassOf) x y → icext i u x → icext i u y

def CondSubClassOfTrans (i : Interp) : Prop :=
  ∀ x y z : i.idom, i.iext (i.iIri rdfsSubClassOf) x y →
    i.iext (i.iIri rdfsSubClassOf) y z → i.iext (i.iIri rdfsSubClassOf) x z

def CondSubClassOfRefl (i : Interp) : Prop :=
  ∀ x : i.idom, icext i x (i.iIri rdfsClass) → i.iext (i.iIri rdfsSubClassOf) x x

def CondClassSubclassResource (i : Interp) : Prop :=
  ∀ x : i.idom, icext i x (i.iIri rdfsClass) →
    i.iext (i.iIri rdfsSubClassOf) x (i.iIri rdfsResource)

def CondDatatypeSubclassLiteral (i : Interp) : Prop :=
  ∀ x : i.idom, icext i x (i.iIri rdfsDatatype) →
    i.iext (i.iIri rdfsSubClassOf) x (i.iIri rdfsLiteral)

def CondCmpMember (i : Interp) : Prop :=
  ∀ x : i.idom, icext i x (i.iIri rdfsContainerMembershipProperty) →
    i.iext (i.iIri rdfsSubPropertyOf) x (i.iIri rdfsMember)

/-- §9's "x and y are in IC" half of the subClassOf condition — the
route rdfs10 and the endpoint reflexivity take. -/
def CondSubClassOfIc (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri rdfsSubClassOf) x y →
    icext i x (i.iIri rdfsClass) ∧ icext i y (i.iIri rdfsClass)

def CondSubPropertyOfIp (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri rdfsSubPropertyOf) x y →
    icext i x (i.iIri rdfProperty) ∧ icext i y (i.iIri rdfProperty)

def CondDatatypesMinimal (i : Interp) : Prop := CondDatatypes dMinimal i

def CondRdfsAxioms (i : Interp) : Prop :=
  ∀ (a : BnodeAssignment i.idom) (t : Triple), RdfsAxiomatic t → TripleHolds i a t

def RdfsConditions (D : DatatypeSet) (i : Interp) : Prop :=
  RdfConditions i ∧ CondDomain i ∧ CondRange i ∧
  CondDatatypes D i ∧ CondDatatypesMinimal i ∧ CondResource i ∧
  CondSubPropertyOf i ∧ CondSubPropertyOfTrans i ∧ CondSubPropertyOfRefl i ∧
  CondSubPropertyOfIp i ∧
  CondSubClassOf i ∧ CondSubClassOfTrans i ∧ CondSubClassOfRefl i ∧
  CondSubClassOfIc i ∧
  CondClassSubclassResource i ∧ CondDatatypeSubclassLiteral i ∧
  CondCmpMember i ∧ CondRdfsAxioms i

def RdfsEntails (D : DatatypeSet) (g1 g2 : Graph) : Prop :=
  EntailsUnder (RdfsConditions D) g1 g2

/-! ## Every row is TRUE under the conditions

One lemma per row. Each takes the row's derivation, the relevant
condition, and the premises holding under an assignment, and concludes
the row's conclusion holds under the SAME assignment — no row here
mints a fresh blank node, which is why one assignment serves. -/

variable {i : Interp} {aa : BnodeAssignment i.idom} {g : Graph} {t : Triple}

theorem rdfD2_true (h : CondRdfProperty i) (hg : HoldsAll i aa g)
    (hd : RdfD2Derives g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, rfl⟩ := hd
  exact h _ _ _ (hg u hu)

theorem rdfs1_true {D : DatatypeSet} (h : CondDatatypes D i) (hd : Rdfs1Derives D t) :
    TripleHolds i aa t := by
  obtain ⟨a, ha, rfl⟩ := hd
  exact h a ha

theorem rdfs2_true (h : CondDomain i) (hg : HoldsAll i aa g) (hd : Rdfs2Derives g t) :
    TripleHolds i aa t := by
  obtain ⟨decl, hdecl, u, hu, a, hp, hs, hup, rfl⟩ := hd
  have h1 := hg decl hdecl
  have h2 := hg u hu
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hp, hs] at h1
  rw [hup] at h2
  exact h _ _ _ _ h1 h2

theorem rdfs3_true (h : CondRange i) (hg : HoldsAll i aa g) (hd : Rdfs3Derives g t) :
    TripleHolds i aa t := by
  obtain ⟨decl, hdecl, u, hu, a, zs, hp, hs, hup, hzs, rfl⟩ := hd
  have h1 := hg decl hdecl
  have h2 := hg u hu
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hp, hs] at h1
  rw [hup] at h2
  rw [show denotSubject i aa zs = denotTerm i aa u.o from
        hzs ▸ (denot_subjTerm i aa zs).symm]
  exact h _ _ _ _ h1 h2

theorem rdfs4a_true (h : CondResource i) (hd : Rdfs4aDerives g t) :
    TripleHolds i aa t := by
  obtain ⟨u, _, rfl⟩ := hd
  exact h _

theorem rdfs4b_true (h : CondResource i) (hd : Rdfs4bDerives g t) :
    TripleHolds i aa t := by
  obtain ⟨u, _, ys, _, rfl⟩ := hd
  exact h _

theorem rdfs5_true (h : CondSubPropertyOfTrans i) (hg : HoldsAll i aa g)
    (hd : Rdfs5Derives g t) : TripleHolds i aa t := by
  obtain ⟨t1, ht1, t2, ht2, ys, hp1, hp2, hys, hs2, rfl⟩ := hd
  have h1 := hg t1 ht1
  have h2 := hg t2 ht2
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hp1] at h1
  rw [hp2, hs2] at h2
  rw [show denotTerm i aa t1.o = denotSubject i aa ys from
        hys ▸ denot_subjTerm i aa ys] at h1
  exact h _ _ _ h1 h2

theorem rdfs6_true (h : CondSubPropertyOfRefl i) (hg : HoldsAll i aa g)
    (hd : Rdfs6Derives g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, hp, ho, rfl⟩ := hd
  have h1 := hg u hu
  simp only [TripleHolds] at h1 ⊢
  rw [hp, ho] at h1
  simp only [denot_subjTerm]
  exact h _ h1

theorem rdfs7_true (h : CondSubPropertyOf i) (hg : HoldsAll i aa g)
    (hd : Rdfs7Derives g t) : TripleHolds i aa t := by
  obtain ⟨decl, hdecl, u, hu, a, b, hp, hs, ho, hup, rfl⟩ := hd
  have h1 := hg decl hdecl
  have h2 := hg u hu
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hp, hs, ho] at h1
  rw [hup] at h2
  exact h _ _ _ _ h1 h2

theorem rdfs8_true (h : CondClassSubclassResource i) (hg : HoldsAll i aa g)
    (hd : Rdfs8Derives g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, hp, ho, rfl⟩ := hd
  have h1 := hg u hu
  simp only [TripleHolds] at h1 ⊢
  rw [hp, ho] at h1
  exact h _ h1

theorem rdfs9_true (h : CondSubClassOf i) (hg : HoldsAll i aa g)
    (hd : Rdfs9Derives g t) : TripleHolds i aa t := by
  obtain ⟨sub, hsub, typ, htyp, xs, hsp, hss, htp, hto, rfl⟩ := hd
  have h1 := hg sub hsub
  have h2 := hg typ htyp
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hsp, hss] at h1
  rw [htp, hto] at h2
  simp only [denot_subjTerm] at h1 h2 ⊢
  exact h _ _ _ h1 h2

theorem rdfs10_true (h : CondSubClassOfRefl i) (hg : HoldsAll i aa g)
    (hd : Rdfs10Derives g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, hp, ho, rfl⟩ := hd
  have h1 := hg u hu
  simp only [TripleHolds] at h1 ⊢
  rw [hp, ho] at h1
  simp only [denot_subjTerm]
  exact h _ h1

theorem rdfs11_true (h : CondSubClassOfTrans i) (hg : HoldsAll i aa g)
    (hd : Rdfs11Derives g t) : TripleHolds i aa t := by
  obtain ⟨t1, ht1, t2, ht2, ys, hp1, hp2, hys, hs2, rfl⟩ := hd
  have h1 := hg t1 ht1
  have h2 := hg t2 ht2
  simp only [TripleHolds] at h1 h2 ⊢
  rw [hp1] at h1
  rw [hp2, hs2] at h2
  rw [show denotTerm i aa t1.o = denotSubject i aa ys from
        hys ▸ denot_subjTerm i aa ys] at h1
  exact h _ _ _ h1 h2

theorem rdfs12_true (h : CondCmpMember i) (hg : HoldsAll i aa g)
    (hd : Rdfs12Derives g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, hp, ho, rfl⟩ := hd
  have h1 := hg u hu
  simp only [TripleHolds] at h1 ⊢
  rw [hp, ho] at h1
  exact h _ h1

theorem rdfs13_true (h : CondDatatypeSubclassLiteral i) (hg : HoldsAll i aa g)
    (hd : Rdfs13Derives g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, hp, ho, rfl⟩ := hd
  have h1 := hg u hu
  simp only [TripleHolds] at h1 ⊢
  rw [hp, ho] at h1
  exact h _ h1

/-! ### The three consequences that are not rows -/

theorem rdfsMemberSubproperty_true (hax : CondRdfsAxioms i) (h : CondCmpMember i)
    (hd : RdfsMemberSubproperty t) : TripleHolds i aa t := by
  obtain ⟨iri, hmem, rfl⟩ := hd
  -- the axiomatic container-membership row supplies the type premise,
  -- and rdfs12's condition turns it into the subPropertyOf conclusion
  exact h _ (hax aa _ (Or.inr ⟨iri, hmem, Or.inl rfl⟩))

theorem rdfsSubClassOfEndpointRefl_true (hic : CondSubClassOfIc i)
    (hrefl : CondSubClassOfRefl i) (hg : HoldsAll i aa g)
    (hd : RdfsSubClassOfEndpointRefl g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, xs, hp, hend, rfl⟩ := hd
  have h1 := hg u hu
  simp only [TripleHolds] at h1 ⊢
  rw [hp] at h1
  simp only [denot_subjTerm]
  rcases hend with hs | ho
  · exact hrefl _ (hs ▸ (hic _ _ h1).1)
  · refine hrefl _ ?_
    rw [show denotSubject i aa xs = denotTerm i aa u.o from
          ho ▸ (denot_subjTerm i aa xs).symm]
    exact (hic _ _ h1).2

theorem rdfsSubPropertyOfEndpointRefl_true (hip : CondSubPropertyOfIp i)
    (hrefl : CondSubPropertyOfRefl i) (hg : HoldsAll i aa g)
    (hd : RdfsSubPropertyOfEndpointRefl g t) : TripleHolds i aa t := by
  obtain ⟨u, hu, xs, hp, hend, rfl⟩ := hd
  have h1 := hg u hu
  simp only [TripleHolds] at h1 ⊢
  rw [hp] at h1
  simp only [denot_subjTerm]
  rcases hend with hs | ho
  · exact hrefl _ (hs ▸ (hip _ _ h1).1)
  · refine hrefl _ ?_
    rw [show denotSubject i aa xs = denotTerm i aa u.o from
          ho ▸ (denot_subjTerm i aa xs).symm]
    exact (hip _ _ h1).2

/-! ## The closing theorem

Everything the licensing relation licenses is true. This is what turns
the transcribed rule tables from a list into a specification an engine
can be measured against. -/

theorem rdfsLicensed_true {D : DatatypeSet} (hc : RdfsConditions D i)
    (hg : HoldsAll i aa g) (hd : RdfsLicensed D g t) : TripleHolds i aa t := by
  obtain ⟨⟨hprop, hrdfax⟩, hdom, hran, hdt, _, hres, hsp, hsptr, hsprefl, hspip,
          hsc, hsctr, hscrefl, hscic, hcsr, hdsl, hcmp, hrdfsax⟩ := hc
  rcases hd with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                 h | h | h | h | h
  · exact hg t h
  · exact hrdfax aa t h
  · exact hrdfsax aa t h
  · exact rdfsMemberSubproperty_true hrdfsax hcmp h
  · exact rdfsSubClassOfEndpointRefl_true hscic hscrefl hg h
  · exact rdfsSubPropertyOfEndpointRefl_true hspip hsprefl hg h
  · exact rdfD2_true hprop hg h
  · exact rdfs1_true hdt h
  · exact rdfs2_true hdom hg h
  · exact rdfs3_true hran hg h
  · exact rdfs4a_true hres h
  · exact rdfs4b_true hres h
  · exact rdfs5_true hsptr hg h
  · exact rdfs6_true hsprefl hg h
  · exact rdfs7_true hsp hg h
  · exact rdfs8_true hcsr hg h
  · exact rdfs9_true hsc hg h
  · exact rdfs10_true hscrefl hg h
  · exact rdfs11_true hsctr hg h
  · exact rdfs12_true hcmp hg h
  · exact rdfs13_true hdsl hg h

/-- A rule PASS that emits only licensed triples preserves truth: if
the input holds under an assignment, so does the output. This is the
shape a fixed-point driver composes. -/
theorem rdfsStepLicensed_holds {D : DatatypeSet} {out : Graph}
    (hc : RdfsConditions D i) (hg : HoldsAll i aa g)
    (hstep : RdfsStepLicensed D g out) : HoldsAll i aa out :=
  fun t ht => rdfsLicensed_true hc hg (hstep t ht)

/-- And therefore such a pass produces an RDFS-ENTAILED graph. -/
theorem rdfsStepLicensed_entails {D : DatatypeSet} {g out : Graph}
    (hstep : RdfsStepLicensed D g out) : RdfsEntails D g out := by
  intro i hc hsat
  obtain ⟨aa, haa⟩ := hsat
  exact ⟨aa, rdfsStepLicensed_holds hc haa hstep⟩

end L4Factoidal.RDF
