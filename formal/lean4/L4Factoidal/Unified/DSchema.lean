/-
L4Factoidal.Unified.DSchema — D-entailment in the unified LBase/IKL
theory: the datatype-map schema `dSchema`, the native model-theoretic
anchor `RDF.DEntailsMt`, the adequacy theorem `unified_adequate_d`,
and the separating model that shows the ill-typed exclusion schema is
not redundant.

D-entailment landing of
https://github.com/danbri/factoidal/issues/598 (design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §2.5, §4.1,
§5.1; RDF 1.1 Semantics §7,
https://www.w3.org/TR/rdf11-mt/#datatype-entailment).

## The schema (design document §2.5, decided treatment of §5.1)

CL totalises denotation, so RDF 1.1 Semantics §7.1's "an ill-typed
literal cannot denote anything" is encoded, not transcribed:

* **value identification** — for every literal pair the tree's
  D-value equality `RDF.literalValueEq D` accepts, the sentence
  `eq (embed l1) (embed l2)` (§7: "literals with the same value are
  interchangeable");
* **ill-typed exclusion** — for every literal `RDF.literalIllFormed D`
  rejects, the sentence
  `neg (ex [x, r] (atom r [x, embed l]))`: no true predication has
  the ill-typed literal's individual in object position. A translated
  graph containing such a literal in object position contradicts its
  own exclusion axiom, so the theory entails everything
  (`unified_d_illtyped_entails_all`) — the §7.2 verdict, the one
  `RDF.Regime.inconsistent` computes.

## The native anchor, introduced here

The native tree had NO model-theoretic D-entailment before this
landing: `RDF/EntailmentTheorems.lean` deliberately gives the
`literalValueEq` regime variants no soundness theorem, and
`RDF/Semantics.lean` stops at `SimpleEntailsMt`. Per the design
document §4.1 ("the model-theoretic D-entailment the stage also
introduces natively if it is not yet stated"), `RDF.DInterpCond` and
`RDF.DEntailsMt` are defined below, in the `RDF` namespace, as
`EntailsUnder` over the interpretations that (a) identify
value-equal recognised literals and (b) exclude ill-typed recognised
literals from every property extension's object position. This is
the fragment of §7's D-interpretation conditions that the tree's
executable machinery (`RDF/Datatypes.lean`) expresses; completeness
against the full §7 interpretation class (value-space structure,
`rdfs:range` interactions) is NOT claimed — the `rdfs:range` clash
rule is stage 2 material (`RDF/EntailmentRdfsDatatypeClash.lean`).

## The decided corollary is NOT here — a recorded gap

The executable D procedure exists (`RDF.regimeEntails .d`), but the
native characterisation theorem that `unified_adequate_simple_decided`
composed with for the simple regime (`simpleEntails_iff_mt`) has no
D analogue in the tree. Worse, the correspondence FAILS without
triple-term-freedom hypotheses: the executable inconsistency check
collects literals INSIDE RDF 1.2 triple terms (`Term.literals`
recurses through `tripleTerm`), while the model theory — native
`iTt` and the unified `urn:cl:def:tripleTerm` operator alike — reads
a triple term as an uninterpreted function of its components'
denotations, so an ill-typed literal inside a triple term produces no
contradiction. `dEntailsMt_tt_gap` below machine-checks the
disagreement on a witness pair the `#guard`s pin. The decided
corollary therefore waits for a native D-interpolation lemma (with
`GraphTtFree` hypotheses), tracked in the design document's
correction notes.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfAdequacy
import L4Factoidal.RDF.Entailment

/-! ## The native anchor: D-interpretations, model-theoretically -/

namespace L4Factoidal.RDF

/-- The D-interpretation condition bundle (RDF 1.1 Semantics §7, the
fragment the tree's executable datatype machinery expresses):

1. literals the D-value equality `literalValueEq D` identifies denote
   the same resource (§7's lexical-to-value mapping, observed through
   value equality — the comparison `Regime.literalEq` matches with);
2. an ill-typed recognised literal (`literalIllFormed D`) is in no
   property extension's object position — the totalised reading of
   §7.1's "cannot denote anything" (`Interp.iLit` is total, so the
   exclusion carries the unsatisfiability instead of a partial map).

Literals occur in object position only (RDF 1.1 Concepts §3.1;
`Subject` has no literal constructor), so clause 2 reaches every
occurrence the term model can give a literal — except INSIDE an
RDF 1.2 triple term, where `iTt` reads the literal's denotation as an
uninterpreted function argument (see the module header's gap note). -/
def DInterpCond (D : List WfIri) (i : Interp) : Prop :=
  (∀ l1 l2 : WfLiteral, literalValueEq D l1.val l2.val = true →
     i.iLit l1 = i.iLit l2) ∧
  (∀ l : WfLiteral, literalIllFormed D l.val = true →
     ∀ p x : i.idom, ¬ i.iext p x (i.iLit l))

/-- **D-entailment, model-theoretically** (RDF 1.1 Semantics §7):
entailment over the D-interpretations. The native anchor of
`Unified.unified_adequate_d`. -/
def DEntailsMt (D : List WfIri) (g h : Graph) : Prop :=
  EntailsUnder (DInterpCond D) g h

end L4Factoidal.RDF

namespace L4Factoidal.Unified

/-! ## The schema sentences -/

/-- The value-identification sentence for a literal pair
(design document §2.5; RDF 1.1 Semantics §7). -/
def dValueId (l1 l2 : RDF.WfLiteral) : CL.Sentence :=
  .eq (embedTerm (.literal l1)) (embedTerm (.literal l2))

/-- The ill-typed exclusion sentence for a literal (design document
§2.5's `neg (ex [x, r] (atom r [x, literalTerm s d]))`): no
individual stands in any relation to the ill-typed literal's
individual in object position. The bound names `"x"` and `"r"` are
colon-free, so they capture no IRI name and no `urn:cl:def:`
operator name (the `FreshVal` discipline of `Unified/RdfTransport`). -/
def dExclusion (l : RDF.WfLiteral) : CL.Sentence :=
  .neg (.ex [.plain "x", .plain "r"]
    (.atom (.name "r") [.term (.name "x"), .term (embedTerm (.literal l))]))

/-- The value-identification half of the D schema: one `dValueId` row
per literal pair `literalValueEq D` accepts. -/
def dValueSchema (D : List RDF.WfIri) : Schema := fun s =>
  ∃ l1 l2 : RDF.WfLiteral,
    RDF.literalValueEq D l1.val l2.val = true ∧ s = dValueId l1 l2

/-- The exclusion half: one `dExclusion` row per ill-typed recognised
literal. -/
def dExclusionSchema (D : List RDF.WfIri) : Schema := fun s =>
  ∃ l : RDF.WfLiteral, RDF.literalIllFormed D l.val = true ∧ s = dExclusion l

/-- **The D-interpretation schema** (design document §2.5): value
identification plus ill-typed exclusion. Deliberately silent about
ill-typed individuals beyond the exclusion rows — §5.1's soundness
requirement. -/
def dSchema (D : List RDF.WfIri) : Schema :=
  schemaUnion (dValueSchema D) (dExclusionSchema D)

/-! ## Denotation of an embedded literal, valuation-free -/

/-- The individual an embedded literal denotes at the interpretation's
own valuations. Definitionally equal to `(restrictInterp i).iLit l`. -/
def litDenot (i : CL.Interp) (l : RDF.WfLiteral) : i.dom :=
  CL.denotTerm i i.iName (fun _ => []) (embedTerm (.literal l))

theorem freshVal_iName (i : CL.Interp) : FreshVal i i.iName :=
  fun _ _ => rfl

/-- Updating a valuation at a colon-free name preserves freshness. -/
theorem freshVal_updateInd {i : CL.Interp} {ν : String → i.dom}
    (hν : FreshVal i ν) {n : String} (hn : ':' ∉ n.toList) (x : i.dom) :
    FreshVal i (CL.updateInd ν n x) := by
  intro m hm
  have hmn : m ≠ n := fun he => hn (he ▸ hm)
  simp only [CL.updateInd, if_neg hmn]
  exact hν m hm

/-- An embedded literal denotes the same individual at every fresh
valuation: its subterms are quoted strings, the datatype IRI and the
`literalValueOf` operator name, all colon-containing or valuation-free. -/
theorem denot_embedLiteral_fresh (i : CL.Interp) {ν : String → i.dom}
    {σ : String → List i.dom} (hν : FreshVal i ν) (l : RDF.WfLiteral) :
    CL.denotTerm i ν σ (embedTerm (.literal l)) = litDenot i l := by
  simp only [litDenot, embedTerm, CL.denotTerm]
  rw [denotSeq_litArgs i hν l, hν litOp (by decide)]

/-! ## Satisfaction of the schema rows, characterised -/

theorem satisfies_dValueId_iff (i : CL.Interp) (l1 l2 : RDF.WfLiteral) :
    CL.Satisfies i (dValueId l1 l2) ↔ litDenot i l1 = litDenot i l2 := by
  simp only [dValueId, CL.Satisfies, CL.Sat, litDenot]

/-- The exclusion sentence, characterised: no relation extension holds
of any pair ending in the literal's individual. -/
theorem satisfies_dExclusion_iff (i : CL.Interp) (l : RDF.WfLiteral) :
    CL.Satisfies i (dExclusion l) ↔
      ∀ xv rv : i.dom, ¬ i.rel rv [xv, litDenot i l] := by
  have hfresh : ∀ xv rv : i.dom,
      FreshVal i (CL.updateInd (CL.updateInd i.iName "x" xv) "r" rv) :=
    fun xv rv => freshVal_updateInd
      (freshVal_updateInd (freshVal_iName i) (by decide) xv) (by decide) rv
  have hr : ∀ xv rv : i.dom,
      CL.updateInd (CL.updateInd i.iName "x" xv) "r" rv "r" = rv := by
    intro xv rv
    simp [CL.updateInd]
  have hx : ∀ xv rv : i.dom,
      CL.updateInd (CL.updateInd i.iName "x" xv) "r" rv "x" = xv := by
    intro xv rv
    simp [CL.updateInd]
  simp only [dExclusion, CL.Satisfies, CL.Sat, CL.SatExists]
  constructor
  · intro hn xv rv hrel
    apply hn
    refine ⟨xv, rv, ?_⟩
    simp only [CL.denotSeq, CL.denotTerm,
               denot_embedLiteral_fresh i (hfresh xv rv) l, hr, hx]
    exact hrel
  · rintro hall ⟨xv, rv, hatom⟩
    simp only [CL.denotSeq, CL.denotTerm,
               denot_embedLiteral_fresh i (hfresh xv rv) l, hr, hx] at hatom
    exact hall xv rv hatom

/-! ## Transport: the schema and the native condition bundle
correspond through the stage 1 interpretation pair -/

/-- The literal operator on the lifted interpretation computes the RDF
denotation (tagged): `litDenot` of the lift is `r.iLit`. -/
theorem litDenot_lift (r : RDF.Interp) (l : RDF.WfLiteral) :
    litDenot (liftInterp r) l = (none, r.iLit l) := by
  simp only [litDenot, embedTerm, CL.denotTerm]
  exact liftFn_litArgs r (freshVal_iName _) l

/-- A lifted D-interpretation satisfies the D schema. -/
theorem liftInterp_satisfiesSchema_d (D : List RDF.WfIri) (r : RDF.Interp)
    (hr : RDF.DInterpCond D r) :
    SatisfiesSchema (liftInterp r) (dSchema D) := by
  rintro s (⟨l1, l2, hlv, rfl⟩ | ⟨l, hif, rfl⟩)
  · rw [satisfies_dValueId_iff, litDenot_lift, litDenot_lift, hr.1 l1 l2 hlv]
  · rw [satisfies_dExclusion_iff]
    intro xv rv hrel
    rw [litDenot_lift] at hrel
    exact hr.2 l hif rv.2 xv.2 hrel

/-- The restriction of a schema-satisfying CL interpretation is a
D-interpretation. -/
theorem restrictInterp_dCond (D : List RDF.WfIri) (i : CL.Interp)
    (hi : SatisfiesSchema i (dSchema D)) :
    RDF.DInterpCond D (restrictInterp i) := by
  constructor
  · intro l1 l2 hlv
    have h := hi _ (Or.inl ⟨l1, l2, hlv, rfl⟩)
    rw [satisfies_dValueId_iff] at h
    exact h
  · intro l hif p x hrel
    have h := hi _ (Or.inr ⟨l, hif, rfl⟩)
    rw [satisfies_dExclusion_iff] at h
    exact h x p hrel

/-! ## The gate theorem -/

/-- **D-entailment adequacy** (design document §4.1): entailment under
the D schema between translated graphs coincides with model-theoretic
D-entailment over the native D-interpretations, with no side
condition. -/
theorem unified_adequate_d (D : List RDF.WfIri) (g h : RDF.Graph) :
    EntailsSchema condTrue (dSchema D) [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.DEntailsMt D g h := by
  constructor
  · intro hE r hr hg
    have h1 : CL.Satisfies (liftInterp r) (rdfToTheory g) :=
      (satisfies_rdfToTheory_lift r g).mpr hg
    have h2 : CL.Satisfies (liftInterp r) (rdfToTheory h) :=
      hE (liftInterp r) True.intro (liftInterp_satisfiesSchema_d D r hr)
        (fun s hs => by
          obtain rfl := List.mem_singleton.mp hs
          exact h1)
    exact (satisfies_rdfToTheory_lift r h).mp h2
  · intro hMt i _ hsch hsat
    have h1 : RDF.Satisfies (restrictInterp i) g :=
      (satisfies_rdfToTheory_restrict i g).mp
        (hsat _ (List.mem_singleton.mpr rfl))
    exact (satisfies_rdfToTheory_restrict i h).mpr
      (hMt (restrictInterp i) (restrictInterp_dCond D i hsch) h1)

/-! ## Ill-typed premises entail everything (RDF 1.1 Semantics §7.2) -/

/-- A translated graph with an ill-typed recognised literal in object
position contradicts its own exclusion axiom: no schema-satisfying
interpretation satisfies it. -/
theorem dSchema_illtyped_unsat (D : List RDF.WfIri) {g : RDF.Graph}
    {t : RDF.Triple} {l : RDF.WfLiteral} (ht : t ∈ g)
    (ho : t.o = .literal l) (hif : RDF.literalIllFormed D l.val = true)
    (i : CL.Interp) (hsch : SatisfiesSchema i (dSchema D)) :
    ¬ CL.Satisfies i (rdfToTheory g) := by
  intro hsat
  rw [satisfies_rdfToTheory_iff] at hsat
  obtain ⟨f, hf⟩ := hsat
  have hν : FreshVal i (overrideOn i.iName (graphBnodeNames g) f) :=
    freshVal_overrideOn i (graphBnodeNames_no_colon g) f
  have hatom := hf t ht
  have hexcl := (satisfies_dExclusion_iff i l).mp
    (hsch _ (Or.inr ⟨l, hif, rfl⟩))
  simp only [tripleAtom, ho, CL.Sat, CL.denotSeq,
             denot_embedLiteral_fresh i hν l] at hatom
  exact hexcl _ _ hatom

/-- The everything-relation on a D-clashing premise: the unified
counterpart of `RDF.Regime.inconsistent`'s short-circuit (§7.2, "an
inconsistent graph entails any graph"). -/
theorem unified_d_illtyped_entails_all (D : List RDF.WfIri) {g : RDF.Graph}
    {t : RDF.Triple} {l : RDF.WfLiteral} (ht : t ∈ g)
    (ho : t.o = .literal l) (hif : RDF.literalIllFormed D l.val = true)
    (c : CL.Sentence) :
    EntailsSchema condTrue (dSchema D) [rdfToTheory g] c := by
  intro i _ hsch hsat
  exact absurd (hsat _ (List.mem_singleton.mpr rfl))
    (dSchema_illtyped_unsat D ht ho hif i hsch)

/-- The same verdict natively, through the adequacy theorem. -/
theorem dEntailsMt_illtyped (D : List RDF.WfIri) {g : RDF.Graph}
    {t : RDF.Triple} {l : RDF.WfLiteral} (ht : t ∈ g)
    (ho : t.o = .literal l) (hif : RDF.literalIllFormed D l.val = true)
    (h : RDF.Graph) : RDF.DEntailsMt D g h :=
  (unified_adequate_d D g h).mp
    (unified_d_illtyped_entails_all D ht ho hif _)

/-! ## Witness data

Concrete recognised-datatype literals: one ill-typed boolean, and an
integer value written under two lexical forms. `dWitD` recognises
`xsd:boolean` and `xsd:integer`. -/

def dWitD : List RDF.WfIri := [RDF.xsdBoolean, RDF.xsdInteger]

private def dA : RDF.WfIri := ⟨"http://d.example/a", by decide⟩
private def dP : RDF.WfIri := ⟨"http://d.example/p", by decide⟩
private def dQ : RDF.WfIri := ⟨"http://d.example/q", by decide⟩

/-- `"yes"^^xsd:boolean` — ill-typed under `dWitD`. -/
def dBadLit : RDF.WfLiteral :=
  ⟨{ lexicalForm := "yes", datatype := RDF.xsdBoolean,
     langTag := none, direction := none }, by decide⟩

/-- `"1"^^xsd:integer`. -/
def dOneLit : RDF.WfLiteral :=
  ⟨{ lexicalForm := "1", datatype := RDF.xsdInteger,
     langTag := none, direction := none }, by decide⟩

/-- `"01"^^xsd:integer` — a different lexical form of the same value. -/
def dOne2Lit : RDF.WfLiteral :=
  ⟨{ lexicalForm := "01", datatype := RDF.xsdInteger,
     langTag := none, direction := none }, by decide⟩

def dBadGraph : RDF.Graph := [⟨.iri dA, dP, .literal dBadLit⟩]
def dTargetGraph : RDF.Graph := [⟨.iri dA, dQ, .iri dA⟩]
def dNumG : RDF.Graph := [⟨.iri dA, dP, .literal dOneLit⟩]
def dNumH : RDF.Graph := [⟨.iri dA, dP, .literal dOne2Lit⟩]

theorem dBadLit_illFormed : RDF.literalIllFormed dWitD dBadLit.val = true := by
  decide

/-! ## The separating model (design document §5.1)

`dSepInterp` satisfies the whole value-identification half of the
schema AND the translated ill-typed graph, and refutes the exclusion
axiom for `dBadLit` and the target sentence. So: under total
denotation with value identification alone, an ill-typed graph is
satisfiable and entails nothing new; the exclusion schema is the
exact ingredient that turns it into the §7.2 everything-relation.
This is the model §5.1 requires "separating the two readings". -/

/-- Domain `Bool`; only the individual named `dP` has a relation
extension; every functional term (in particular every embedded
literal) denotes `false`. -/
def dSepInterp : CL.Interp where
  dom := Bool
  domWit := true
  iName := fun n => n == dP.val
  iStr := fun _ => false
  rel := fun p _ => p = true
  fn := fun _ _ => false
  iProp := fun _ _ _ => false

theorem dSep_satisfies_valueSchema :
    SatisfiesSchema dSepInterp (dValueSchema dWitD) := by
  rintro s ⟨l1, l2, _, rfl⟩
  rw [satisfies_dValueId_iff]
  simp [litDenot, embedTerm, CL.denotTerm, dSepInterp]

theorem dSep_satisfies_badGraph :
    CL.Satisfies dSepInterp (rdfToTheory dBadGraph) := by
  rw [satisfies_rdfToTheory_iff]
  refine ⟨fun _ => false, fun t ht => ?_⟩
  obtain rfl := List.mem_singleton.mp ht
  have hgb : graphBnodeNames dBadGraph = [] := by decide
  simp [tripleAtom, CL.Sat, CL.denotTerm, embedSubject,
        overrideOn, hgb, dSepInterp]

/-- The exclusion axiom for the ill-typed literal FAILS in the
separating model: the schema row is not redundant. -/
theorem dSep_refutes_exclusion :
    ¬ CL.Satisfies dSepInterp (dExclusion dBadLit) := by
  rw [satisfies_dExclusion_iff]
  intro hall
  exact hall true true rfl

theorem dSep_refutes_target :
    ¬ CL.Satisfies dSepInterp (rdfToTheory dTargetGraph) := by
  rw [satisfies_rdfToTheory_iff]
  rintro ⟨f, hf⟩
  have h := hf _ (List.mem_singleton.mpr rfl)
  have hgb : graphBnodeNames dTargetGraph = [] := by decide
  simp [tripleAtom, CL.Sat, CL.denotTerm, embedSubject,
        overrideOn, hgb, dSepInterp] at h
  exact absurd h (by decide)

/-- **Value identification alone is not enough**: without the
exclusion rows, the ill-typed graph does not entail the target. -/
theorem dValueSchema_alone_insufficient :
    ¬ EntailsSchema condTrue (dValueSchema dWitD)
        [rdfToTheory dBadGraph] (rdfToTheory dTargetGraph) := by
  intro hE
  exact dSep_refutes_target
    (hE dSepInterp True.intro dSep_satisfies_valueSchema
      (fun s hs => by
        obtain rfl := List.mem_singleton.mp hs
        exact dSep_satisfies_badGraph))

/-- **With the exclusion rows it does** — the separation, positive
half. -/
theorem dSchema_exclusion_does_work :
    EntailsSchema condTrue (dSchema dWitD)
      [rdfToTheory dBadGraph] (rdfToTheory dTargetGraph) :=
  unified_d_illtyped_entails_all dWitD (List.mem_singleton.mpr rfl) rfl
    dBadLit_illFormed _

/-! ## Non-vacuity of the schema and the native bundle -/

/-- The empty-extension CL interpretation: nothing is related to
anything. -/
def noRelInterp : CL.Interp where
  dom := Unit
  domWit := ()
  iName := fun _ => ()
  iStr := fun _ => ()
  rel := fun _ _ => False
  fn := fun _ _ => ()
  iProp := fun _ _ _ => ()

/-- The D schema is satisfiable for EVERY recognised set: entailment
under it never holds by schema-vacuity. -/
theorem noRel_satisfiesSchema_d (D : List RDF.WfIri) :
    SatisfiesSchema noRelInterp (dSchema D) := by
  rintro s (⟨l1, l2, _, rfl⟩ | ⟨l, _, rfl⟩)
  · rw [satisfies_dValueId_iff]
    exact rfl
  · rw [satisfies_dExclusion_iff]
    intro xv rv hrel
    exact hrel


theorem noRel_satisfies_empty :
    CL.Satisfies noRelInterp (rdfToTheory ([] : RDF.Graph)) := by
  rw [satisfies_rdfToTheory_iff]
  exact ⟨fun _ => (), fun t ht => absurd ht (by simp)⟩

/-- D-schema entailment is not the everything-relation. -/
theorem dSchema_entails_not_everything (D : List RDF.WfIri) :
    ¬ EntailsSchema condTrue (dSchema D)
        [rdfToTheory ([] : RDF.Graph)] (rdfToTheory dTargetGraph) := by
  intro hE
  have h := hE noRelInterp True.intro (noRel_satisfiesSchema_d D)
    (fun s hs => by
      obtain rfl := List.mem_singleton.mp hs
      exact noRel_satisfies_empty)
  rw [satisfies_rdfToTheory_iff] at h
  obtain ⟨f, hf⟩ := h
  have hbad := hf _ (List.mem_singleton.mpr rfl)
  simp [tripleAtom, CL.Sat, noRelInterp] at hbad

/-- The empty-extension RDF interpretation. -/
def noExtInterp : RDF.Interp where
  idom := Unit
  idomWit := ()
  iIri := fun _ => ()
  iLit := fun _ => ()
  iTt := fun _ _ _ => ()
  iext := fun _ _ _ => False

/-- `DInterpCond` is satisfiable for every recognised set:
`DEntailsMt` never holds by condition-vacuity. -/
theorem noExt_dCond (D : List RDF.WfIri) : RDF.DInterpCond D noExtInterp :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ h => h⟩

/-- Native D-entailment is not the everything-relation. -/
theorem dEntailsMt_not_everything (D : List RDF.WfIri) :
    ¬ RDF.DEntailsMt D [] dTargetGraph := by
  intro h
  obtain ⟨a, ha⟩ := h noExtInterp (noExt_dCond D)
    ⟨fun _ => (), fun t ht => nomatch ht⟩
  exact ha _ (List.mem_singleton.mpr rfl)

/-! ## D strictly extends simple entailment -/

/-- The value-identification instance: `"1"^^xsd:integer` D-entails
`"01"^^xsd:integer` in the same triple. -/
theorem dEntailsMt_value_instance : RDF.DEntailsMt dWitD dNumG dNumH := by
  intro i hi hsat
  obtain ⟨a, ha⟩ := hsat
  refine ⟨a, fun t ht => ?_⟩
  obtain rfl := List.mem_singleton.mp ht
  have h1 := ha _ (List.mem_singleton.mpr rfl)
  have heq : i.iLit dOneLit = i.iLit dOne2Lit :=
    hi.1 dOneLit dOne2Lit (by decide)
  simpa [RDF.TripleHolds, RDF.denotSubject, RDF.denotTerm, heq] using h1

/-- The same instance in the unified theory, through adequacy. -/
theorem unified_d_value_instance :
    EntailsSchema condTrue (dSchema dWitD)
      [rdfToTheory dNumG] (rdfToTheory dNumH) :=
  (unified_adequate_d dWitD dNumG dNumH).mpr dEntailsMt_value_instance

theorem dNumG_ttFree : RDF.GraphTtFree dNumG := by
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  trivial

theorem dNumH_ttFree : RDF.GraphTtFree dNumH := by
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  trivial

/-- SIMPLE entailment does not hold on the instance pair: the D rows
add entailments, so the schema is doing work on the positive side
too. -/
theorem dNum_not_simple : ¬ RDF.SimpleEntailsMt dNumG dNumH := by
  intro h
  have hb : RDF.simpleEntails dNumG dNumH = true :=
    (RDF.SimpleRefinement.simpleEntails_iff_spec _ _).mpr
      ((RDF.simpleEntails_iff_mt dNumG_ttFree dNumH_ttFree).mpr h)
  rw [show RDF.simpleEntails dNumG dNumH = false from by decide] at hb
  exact Bool.false_ne_true hb

/-! ## The executable-procedure gap, machine-checked

`RDF.regimeEntails .d` answers `true` on a premise whose ill-typed
literal sits INSIDE an RDF 1.2 triple term (its inconsistency check
recurses through `Term.literals`); the model theory reads the triple
term as an uninterpreted function and builds a countermodel. The
future decided corollary needs `GraphTtFree` hypotheses — exactly as
`unified_adequate_simple_decided` does. -/

def dTtGraph : RDF.Graph :=
  [⟨.iri dA, dP, .tripleTerm (.iri dA) dQ (.literal dBadLit)⟩]

/-- Everything is true of a triple-term individual; ill-typed literal
individuals are excluded; so `dTtGraph` is satisfied while `dNumG`'s
literal-object triple is refuted. -/
def ttSepInterp : RDF.Interp where
  idom := Bool
  idomWit := true
  iIri := fun _ => true
  iLit := fun _ => false
  iTt := fun _ _ _ => true
  iext := fun _ _ y => y = true

theorem ttSep_dCond : RDF.DInterpCond dWitD ttSepInterp :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ h => Bool.false_ne_true h⟩

/-- The model theory does NOT read a triple-term-interior ill-typed
literal as a clash — the executable procedure does (`#guard` below). -/
theorem dEntailsMt_tt_gap : ¬ RDF.DEntailsMt dWitD dTtGraph dNumG := by
  intro h
  have hsat : RDF.Satisfies ttSepInterp dTtGraph := by
    refine ⟨fun _ => true, fun t ht => ?_⟩
    obtain rfl := List.mem_singleton.mp ht
    exact rfl
  obtain ⟨a, ha⟩ := h ttSepInterp ttSep_dCond hsat
  have hbad := ha _ (List.mem_singleton.mpr rfl)
  exact Bool.false_ne_true hbad

/-! ## Build-time checks -/

section Checks

/- The witness data is what the theorems say it is. -/

#guard RDF.literalIllFormed dWitD dBadLit.val
#guard !RDF.literalIllFormed dWitD dOneLit.val
#guard RDF.literalValueEq dWitD dOneLit.val dOne2Lit.val
#guard !(RDF.simpleEntails dNumG dNumH)

/- Verdict agreement with the executable regime procedure where the
model theory and the procedure are both defined: the ill-typed
premise entails everything, the value instance holds, the empty graph
entails nothing. -/

#guard RDF.regimeEntails .d dWitD dBadGraph dTargetGraph
#guard RDF.regimeEntails .d dWitD dNumG dNumH
#guard !(RDF.regimeEntails .d dWitD ([] : RDF.Graph) dTargetGraph)

/- The gap: the procedure short-circuits on the triple-term-interior
ill-typed literal; `dEntailsMt_tt_gap` refutes the same pair
model-theoretically. -/

#guard RDF.regimeEntails .d dWitD dTtGraph dNumG

/-! Axiom audit — expected at most `propext` / `Classical.choice` /
`Quot.sound` (Lean's own foundations). No `sorryAx`, nothing
user-declared. -/

#print axioms unified_adequate_d
#print axioms unified_d_illtyped_entails_all
#print axioms dEntailsMt_illtyped
#print axioms dValueSchema_alone_insufficient
#print axioms dSchema_exclusion_does_work
#print axioms dEntailsMt_value_instance
#print axioms dNum_not_simple
#print axioms dEntailsMt_tt_gap

end Checks

end L4Factoidal.Unified
