/-
L4Factoidal.RDFS.RhoDfCompleteness — port of
`RDF.Entailment.RDFS.Completeness` (829 lines).

`RDF.EntailmentRdfsModelTheory` proves SOUNDNESS: every triple the rule
tables license from a true graph is true. This module proves the
CONVERSE half on a named fragment: on a ρdf-CLOSED graph, ρdf
entailment and simple entailment pick out the same pairs.

The canonical model is the Herbrand interpretation of the closed graph,
reused unchanged from the simple rung (`RDF.Semantics.herbrand`).
SATURATION is what makes it a ρdf interpretation: each semantic
condition's obligation is discharged because the matching rule has
already fired and put its conclusion in the graph.

## Finding C-1, carried over from the F* source

The natural statement — RDFS entailment coincides with simple
entailment of the RDFS closure — is FALSE, and no fragment predicate on
the two graphs repairs it. This module carries the first witness as a
theorem pair rather than as prose:

`rdfsEntails_subclassSelfLoop` — from `[X rdfs:subClassOf Y]`, RDFS
entails `[X rdfs:subClassOf X]`, because `CondSubClassOfIc` puts `X` in
IC and `CondSubClassOfRefl` then forces the self-loop.

`rhoDf_not_entails_subclassSelfLoop` — the same pair is NOT
ρdf-entailed. The Herbrand interpretation of the premise graph is the
countermodel, and this module's own `herbrand_rhoDfConditions` is what
makes it admissible.

So the two entailment relations genuinely differ ON the fragment, and
the completeness result below is stated for ρdf, not for RDFS.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.EntailmentRdfsModelTheory

namespace L4Factoidal.RDF

open L4Factoidal.RDFS
open L4Factoidal.OWL (CondDomain CondRange)

/-! ## 1. The fragment

Two conditions, each needed by exactly one rule row.

`rdfs3` moves a term from OBJECT position into SUBJECT position, so it
cannot fire when that object is a literal or a triple term. `rdfs7`
moves a term into a PREDICATE slot, so a `rdfs:subPropertyOf` object
must be an IRI.

This is a different predicate from `RhoDfGraph` in
`RDF.EntailmentRdfsSpec`, which says the ρdf vocabulary never occurs
outside the predicate slot. Both are called "the ρdf fragment" in the
literature; they constrain different things, so they carry different
names here. -/

def RhoDfModelObjectOk : Term → Prop
  | .iri _ => True
  | .bnode _ => True
  | .literal _ => False
  | .tripleTerm _ _ _ => False

def RhoDfModelFragTriple (t : Triple) : Prop :=
  RhoDfModelObjectOk t.o ∧ (t.p = rdfsSubPropertyOf → ∃ i : WfIri, t.o = .iri i)

def RhoDfModelFragGraph (g : Graph) : Prop := ∀ t ∈ g, RhoDfModelFragTriple t

/-- The fragment implies the standing RDF 1.2 quarantine predicate, so
the Herbrand lemmas of the simple rung apply unchanged. -/
theorem objectOk_ttFree {t : Term} (h : RhoDfModelObjectOk t) : TermTtFree t := by
  cases t with
  | iri _ => trivial
  | bnode _ => trivial
  | literal _ => exact absurd h (by simp [RhoDfModelObjectOk])
  | tripleTerm _ _ _ => exact absurd h (by simp [RhoDfModelObjectOk])

theorem modelFrag_ttFree {g : Graph} (h : RhoDfModelFragGraph g) : GraphTtFree g :=
  fun t ht => objectOk_ttFree (h t ht).1

/-- The fragment also makes every object subject-eligible, which is
what `rdfs3` needs to fire. -/
theorem objectOk_to_subject {t : Term} (h : RhoDfModelObjectOk t) :
    ∃ s : Subject, subjTerm s = t := by
  cases t with
  | iri i => exact ⟨.iri i, rfl⟩
  | bnode b => exact ⟨.bnode b, rfl⟩
  | literal _ => exact absurd h (by simp [RhoDfModelObjectOk])
  | tripleTerm _ _ _ => exact absurd h (by simp [RhoDfModelObjectOk])

/-- A subject whose term view is an IRI IS that IRI as a subject. -/
theorem subjTerm_eq_iri {s : Subject} {i : WfIri} (h : subjTerm s = .iri i) :
    s = .iri i := by
  cases s with
  | iri j => simp only [subjTerm, Term.iri.injEq] at h; rw [h]
  | bnode b => simp [subjTerm] at h

/-! ## 2. The ρdf interpretation class

Exactly the six semantic conditions the six ρdf rows rest on, each
reused unchanged from `RDF.EntailmentRdfsModelTheory`:

| condition | row |
|---|---|
| `CondDomain` | rdfs2 |
| `CondRange` | rdfs3 |
| `CondSubPropertyOf` | rdfs7 |
| `CondSubPropertyOfTrans` | rdfs5 |
| `CondSubClassOf` | rdfs9 |
| `CondSubClassOfTrans` | rdfs11 |

Everything else in `RdfsConditions` — the axiomatic triples, the
reflexivity conditions, `rdfs:Resource` universality, the datatype
conditions — is vocabulary outside ρdf, and is exactly what finding C-1
shows cannot be recovered from a closed graph. -/

def RhoDfConditions (i : Interp) : Prop :=
  CondDomain i ∧ CondRange i ∧
  CondSubPropertyOf i ∧ CondSubPropertyOfTrans i ∧
  CondSubClassOf i ∧ CondSubClassOfTrans i

def RhoDfEntails (g1 g2 : Graph) : Prop := EntailsUnder RhoDfConditions g1 g2

/-- The inclusion: every RDFS interpretation is a ρdf interpretation.
So ρdf entailment is the STRONGER relation — and by finding C-1,
strictly stronger on the fragment. -/
theorem rdfsConditions_imply_rhoDf {D : DatatypeSet} {i : Interp}
    (h : RdfsConditions D i) : RhoDfConditions i := by
  obtain ⟨-, hd, hr, -, -, -, hsp, hspt, -, -, hsc, hsct, -⟩ := h
  exact ⟨hd, hr, hsp, hspt, hsc, hsct⟩

theorem rhoDfEntails_implies_rdfsEntails {D : DatatypeSet} {g e : Graph}
    (h : RhoDfEntails g e) : RdfsEntails D g e :=
  fun i hc hs => h i (rdfsConditions_imply_rhoDf hc) hs

/-! ## 3. ρdf closedness

The six rows of the ρdf deductive system, at the DIAGONAL — both
premises read from the same graph. That is the form the W3C table
states and the form a saturated graph satisfies. -/

def RhoDfClosed (c : Graph) : Prop :=
  (∀ t, Rdfs2Derives c t → t ∈ c) ∧ (∀ t, Rdfs3Derives c t → t ∈ c) ∧
  (∀ t, Rdfs5Derives c t → t ∈ c) ∧ (∀ t, Rdfs7Derives c t → t ∈ c) ∧
  (∀ t, Rdfs9Derives c t → t ∈ c) ∧ (∀ t, Rdfs11Derives c t → t ∈ c)

/-! ## 4. The canonical model is a ρdf interpretation

One lemma per condition, each with the same three moves:

1. read the two Herbrand premises back as triples of `c`;
2. exhibit the ρdf rule instance whose conclusion is wanted;
3. `RhoDfClosed c` puts that conclusion in `c`, which is exactly the
   Herbrand fact the condition asks for.

Move 3 is where saturation does the work. -/

theorem herb_cond_domain {c : Graph} (hc : RhoDfClosed c) : CondDomain (herbrand c) := by
  rintro p cc x y ⟨d, hd, hdp, hpe, hce⟩ ⟨u, hu, hup, hxe, _⟩
  have hdp' : d.p = rdfsDomain := (Term.iri.injEq _ _ ▸ hdp).symm
  have hds : d.s = .iri u.p := subjTerm_eq_iri (hpe ▸ hup : subjTerm d.s = Term.iri u.p)
  have hmem : ({ s := u.s, p := rdfType, o := d.o } : Triple) ∈ c :=
    hc.1 _ ⟨d, hd, u, hu, u.p, hdp', hds, rfl, rfl⟩
  exact ⟨{ s := u.s, p := rdfType, o := d.o }, hmem, rfl, hxe, hce⟩

theorem herb_cond_range {c : Graph} (hc : RhoDfClosed c)
    (hf : RhoDfModelFragGraph c) : CondRange (herbrand c) := by
  rintro p cc x y ⟨d, hd, hdp, hpe, hce⟩ ⟨u, hu, hup, _, hye⟩
  have hdp' : d.p = rdfsRange := (Term.iri.injEq _ _ ▸ hdp).symm
  have hds : d.s = .iri u.p := subjTerm_eq_iri (hpe ▸ hup : subjTerm d.s = Term.iri u.p)
  obtain ⟨zs, hzs⟩ := objectOk_to_subject (hf u hu).1
  have hmem : ({ s := zs, p := rdfType, o := d.o } : Triple) ∈ c :=
    hc.2.1 _ ⟨d, hd, u, hu, u.p, zs, hdp', hds, rfl, hzs, rfl⟩
  exact ⟨{ s := zs, p := rdfType, o := d.o }, hmem, rfl, by rw [hye, ← hzs], hce⟩

theorem herb_cond_subPropertyOf {c : Graph} (hc : RhoDfClosed c)
    (hf : RhoDfModelFragGraph c) : CondSubPropertyOf (herbrand c) := by
  rintro x y u v ⟨d, hd, hdp, hxe, hye⟩ ⟨w, hw, hwp, hue, hve⟩
  have hdp' : d.p = rdfsSubPropertyOf := (Term.iri.injEq _ _ ▸ hdp).symm
  have hds : d.s = .iri w.p := subjTerm_eq_iri (hxe ▸ hwp : subjTerm d.s = Term.iri w.p)
  obtain ⟨b, hb⟩ := (hf d hd).2 hdp'
  have hmem : ({ s := w.s, p := b, o := w.o } : Triple) ∈ c :=
    hc.2.2.2.1 _ ⟨d, hd, w, hw, w.p, b, hdp', hds, hb, rfl, rfl⟩
  exact ⟨{ s := w.s, p := b, o := w.o }, hmem, by rw [hye, hb], hue, hve⟩

theorem herb_cond_subPropertyOf_trans {c : Graph} (hc : RhoDfClosed c) :
    CondSubPropertyOfTrans (herbrand c) := by
  rintro x y z ⟨d, hd, hdp, hxe, hye⟩ ⟨e, he, hep, hye', hze⟩
  have hdp' : d.p = rdfsSubPropertyOf := (Term.iri.injEq _ _ ▸ hdp).symm
  have hep' : e.p = rdfsSubPropertyOf := (Term.iri.injEq _ _ ▸ hep).symm
  have hchain : subjTerm e.s = d.o := by rw [← hye', hye]
  have hmem : ({ s := d.s, p := rdfsSubPropertyOf, o := e.o } : Triple) ∈ c :=
    hc.2.2.1 _ ⟨d, hd, e, he, e.s, hdp', hep', hchain, rfl, rfl⟩
  exact ⟨{ s := d.s, p := rdfsSubPropertyOf, o := e.o }, hmem, rfl, hxe, hze⟩

theorem herb_cond_subClassOf {c : Graph} (hc : RhoDfClosed c) :
    CondSubClassOf (herbrand c) := by
  rintro x y u ⟨d, hd, hdp, hxe, hye⟩ ⟨w, hw, hwp, hue, hxe'⟩
  have hdp' : d.p = rdfsSubClassOf := (Term.iri.injEq _ _ ▸ hdp).symm
  have hwp' : w.p = rdfType := (Term.iri.injEq _ _ ▸ hwp).symm
  have hlink : w.o = subjTerm d.s := by rw [← hxe', hxe]
  have hmem : ({ s := w.s, p := rdfType, o := d.o } : Triple) ∈ c :=
    hc.2.2.2.2.1 _ ⟨d, hd, w, hw, d.s, hdp', rfl, hwp', hlink, rfl⟩
  exact ⟨{ s := w.s, p := rdfType, o := d.o }, hmem, rfl, hue, hye⟩

theorem herb_cond_subClassOf_trans {c : Graph} (hc : RhoDfClosed c) :
    CondSubClassOfTrans (herbrand c) := by
  rintro x y z ⟨d, hd, hdp, hxe, hye⟩ ⟨e, he, hep, hye', hze⟩
  have hdp' : d.p = rdfsSubClassOf := (Term.iri.injEq _ _ ▸ hdp).symm
  have hep' : e.p = rdfsSubClassOf := (Term.iri.injEq _ _ ▸ hep).symm
  have hchain : subjTerm e.s = d.o := by rw [← hye', hye]
  have hmem : ({ s := d.s, p := rdfsSubClassOf, o := e.o } : Triple) ∈ c :=
    hc.2.2.2.2.2 _ ⟨d, hd, e, he, e.s, hdp', hep', hchain, rfl, rfl⟩
  exact ⟨{ s := d.s, p := rdfsSubClassOf, o := e.o }, hmem, rfl, hxe, hze⟩

/-- **The canonical model theorem.** A ρdf-closed graph in the fragment
has a Herbrand interpretation that meets every ρdf condition. -/
theorem herbrand_rhoDfConditions {c : Graph} (hc : RhoDfClosed c)
    (hf : RhoDfModelFragGraph c) : RhoDfConditions (herbrand c) :=
  ⟨herb_cond_domain hc, herb_cond_range hc hf,
   herb_cond_subPropertyOf hc hf, herb_cond_subPropertyOf_trans hc,
   herb_cond_subClassOf hc, herb_cond_subClassOf_trans hc⟩

/-! ## 5. Completeness on a closed graph -/

/-- **The completeness half.** On a ρdf-closed graph in the fragment,
anything ρdf-entailed is already there as an instance-subgraph — which
is simple entailment, by the interpolation lemma. -/
theorem rhoDfClosed_complete {c e : Graph} (hc : RhoDfClosed c)
    (hf : RhoDfModelFragGraph c) (hfe : GraphTtFree e)
    (h : RhoDfEntails c e) : SimpleEntailmentSpec c e :=
  herbrand_reflects
    (h (herbrand c) (herbrand_rhoDfConditions hc hf)
       (herbrand_satisfies (modelFrag_ttFree hf))) hfe

/-- **The soundness half**, which needs no closedness: an
instance-subgraph witness makes every interpretation satisfying `c`
satisfy `e`, ρdf ones included. -/
theorem rhoDfClosed_sound {c e : Graph} (h : SimpleEntailmentSpec c e) :
    RhoDfEntails c e :=
  fun i _ hs => interpolationSound h i hs

/-- The two halves together: on a ρdf-closed graph in the fragment, ρdf
entailment IS simple entailment. -/
theorem rhoDfClosed_iff {c e : Graph} (hc : RhoDfClosed c)
    (hf : RhoDfModelFragGraph c) (hfe : GraphTtFree e) :
    RhoDfEntails c e ↔ SimpleEntailmentSpec c e :=
  ⟨rhoDfClosed_complete hc hf hfe, rhoDfClosed_sound⟩

/-! ## 6. Finding C-1, witness W1: the two relations differ

`[X rdfs:subClassOf Y]` RDFS-entails `[X rdfs:subClassOf X]`, but does
not ρdf-entail it. So "RDFS entailment = simple entailment of the RDFS
closure" is false on the fragment, and cannot be repaired by narrowing
the fragment — this witness is inside it. -/

private def exX : WfIri := ⟨"http://example.org/X", by decide⟩
private def exY : WfIri := ⟨"http://example.org/Y", by decide⟩

private def gSub : Graph := [{ s := .iri exX, p := rdfsSubClassOf, o := .iri exY }]
private def eSelf : Graph := [{ s := .iri exX, p := rdfsSubClassOf, o := .iri exX }]

/-- RDFS DOES entail the self-loop: `CondSubClassOfIc` puts `X` in IC,
and `CondSubClassOfRefl` then forces `X rdfs:subClassOf X`. -/
theorem rdfsEntails_subclassSelfLoop {D : DatatypeSet} :
    RdfsEntails D gSub eSelf := by
  rintro i hcond ⟨aa, haa⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hrefl, hic, -⟩ := hcond
  have hpremise := haa _ (List.mem_singleton.mpr rfl)
  simp only [TripleHolds, denotSubject, denotTerm] at hpremise
  refine ⟨aa, fun t ht => ?_⟩
  rw [List.mem_singleton.mp ht]
  simp only [TripleHolds, denotSubject, denotTerm]
  exact hrefl _ (hic _ _ hpremise).1

/-- ρdf does NOT: the Herbrand interpretation of the premise graph is a
ρdf interpretation that satisfies the premise and not the conclusion.
`herbrand_rhoDfConditions` is what makes the countermodel admissible,
so this theorem depends on the whole of section 4. -/
theorem rhoDf_not_entails_subclassSelfLoop : ¬ RhoDfEntails gSub eSelf := by
  intro h
  have hclosed : RhoDfClosed gSub := by
    refine ⟨?rdfs2, ?rdfs3, ?rdfs5, ?rdfs7, ?rdfs9, ?rdfs11⟩
    case rdfs2 =>
      rintro t ⟨d, hd, -, -, -, hdp, -, -, -⟩
      rw [List.mem_singleton.mp hd] at hdp; exact absurd hdp (by decide)
    case rdfs3 =>
      rintro t ⟨d, hd, -, -, -, -, hdp, -, -, -, -⟩
      rw [List.mem_singleton.mp hd] at hdp; exact absurd hdp (by decide)
    case rdfs5 =>
      rintro t ⟨t1, h1, -, -, -, hp1, -, -, -, -⟩
      rw [List.mem_singleton.mp h1] at hp1; exact absurd hp1 (by decide)
    case rdfs7 =>
      rintro t ⟨d, hd, -, -, -, -, hdp, -, -, -, -⟩
      rw [List.mem_singleton.mp hd] at hdp; exact absurd hdp (by decide)
    case rdfs9 =>
      rintro t ⟨-, -, typ, htyp, -, -, -, htypp, -, -⟩
      rw [List.mem_singleton.mp htyp] at htypp; exact absurd htypp (by decide)
    case rdfs11 =>
      rintro t ⟨t1, h1, t2, h2, ys, -, -, hchain, heq, -⟩
      rw [List.mem_singleton.mp h1] at hchain
      rw [List.mem_singleton.mp h2] at heq
      rw [← heq] at hchain
      exact absurd hchain (by decide)
  have hfrag : RhoDfModelFragGraph gSub := by
    intro t ht
    rw [List.mem_singleton.mp ht]
    exact ⟨trivial, fun hp => absurd hp (by decide)⟩
  have hsat : Satisfies (herbrand gSub) eSelf :=
    h (herbrand gSub) (herbrand_rhoDfConditions hclosed hfrag)
      (herbrand_satisfies (modelFrag_ttFree hfrag))
  obtain ⟨ab, hab⟩ := hsat
  obtain ⟨t, ht, _, _, ho⟩ := hab _ (List.mem_singleton.mpr rfl)
  simp only [gSub, List.mem_singleton] at ht
  subst ht
  simp only [denotTerm, herbrand] at ho
  exact absurd ho (by decide)

/-! ## Axiom audit -/

#print axioms herbrand_rhoDfConditions
#print axioms rhoDfClosed_complete
#print axioms rhoDfClosed_iff
#print axioms rdfsEntails_subclassSelfLoop
#print axioms rhoDf_not_entails_subclassSelfLoop

end L4Factoidal.RDF
