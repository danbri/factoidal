/-
L4Factoidal.Unified.RhoDfSchema — stage 2 of
https://github.com/danbri/factoidal/issues/598, first half: the
reusable Horn-row machinery and the ρdf (rdfs-core / x-rdfscore)
schema with bidirectional adequacy against the native ρdf model theory
(design document `docs/designissues/2026-08-25-unified-semantics-lean.md`
§3 stage 2, §4.2).

## The machinery (used again by `Unified/RdfsSchema.lean`)

* `satForall_plains` — the `SatForall` analogue of
  `Unified.RdfTransport.satExists_plains`: universal closure over a
  plain-name list, characterised as quantification over overrides of
  the ambient valuation.
* `HTerm`/`HAtom`/`hornRow` — ONE combinator for a universally
  quantified definite Horn sentence over binary predications, with ONE
  satisfaction lemma (`satisfies_hornRow_iff`) characterising a row's
  CL satisfaction as its native reading over `restrictInterp`. The
  `CL.Sat` equations are not definitional, so without the combinator
  every schema row re-fights the same quantifier plumbing; with it a
  row is six lines of data plus a short characterisation proof.
* `liftInterp_sat_hornRow` — the generic lift-side transport: a Horn
  row true natively is satisfied by the lifted interpretation
  (`holdsN_restrict_lift` reduces the lifted reading to projections).

## The schema and the gate theorem

`rhoDfSchema` is exactly the six rule rows of `RDFS/Closure.lean`
(rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11) — no axiomatic triples, no
reflexivity rows — and `rdfsCoreSchema` names the same schema for the
x-rdfscore regime table (`RDFS/RegimeDispatch.lean`).

DEVIATION from the design document §4.2 (correction note 8 there): the
gate theorem `unified_adequate_rhoDf` is an UNCONDITIONAL iff — no
fragment hypotheses — against the native model-theoretic relation
`RDF.RhoDfEntails` (`RDFS/RhoDfCompleteness.lean`), which the design
document's statement predates. The fragment (`RhoDfModelFragGraph`),
closedness and triple-term-freedom hypotheses belong to the DECIDED
corollary `unified_adequate_rhoDf_decided`, where the native Herbrand
construction (`rhoDfClosed_iff`) needs them; each is dischargeable by
`decide` through the executable checks (`rhoDfClosedCheck`,
`RDFS.isRhoDfFrag`) on concrete inputs.

The native derivation-soundness bridge (`RDF.rhoDf_derives_holds`:
everything `RDFS.Derives` derives is true in every ρdf interpretation
satisfying the graph) is introduced here, in the `RDF` namespace, per
the same convention as `RDF.DEntailsMt` in `Unified/DSchema.lean` —
the native tree states closure soundness against the rule relation
(`ClosureTheorems.closure_sound`), not against interpretations, and
this bridge is what connects the two.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.DSchema
import L4Factoidal.RDFS.RhoDfCompleteness
import L4Factoidal.RDFS.ClosureTheorems
import L4Factoidal.RDF.SemanticsHypothesisWitness

namespace L4Factoidal.Unified

/-! ## Universal closure over plain names, characterised -/

/-- `SatForall` over a plain-name list: satisfaction at EVERY override
of the ambient valuation at exactly those names. The universal twin of
`satExists_plains`. -/
theorem satForall_plains (i : CL.Interp) (σ : String → List i.dom)
    (body : CL.Sentence) :
    ∀ (names : List String) (ν : String → i.dom),
      CL.SatForall i ν σ (names.map .plain) body ↔
        ∀ f : String → i.dom, CL.Sat i (overrideOn ν names f) σ body
  | [], ν => by
      simp only [List.map_nil, CL.SatForall]
      constructor
      · intro hs f
        have hv : overrideOn ν [] f = ν := by
          funext m; simp [overrideOn]
        rw [hv]; exact hs
      · intro hs
        have hv : overrideOn ν [] (fun _ => i.domWit) = ν := by
          funext m; simp [overrideOn]
        rw [← hv]; exact hs _
  | n :: rest, ν => by
      simp only [List.map_cons, CL.SatForall]
      constructor
      · intro hall f
        have hx := (satForall_plains i σ body rest (CL.updateInd ν n (f n))).mp
          (hall (f n)) f
        have hv : overrideOn (CL.updateInd ν n (f n)) rest f
            = overrideOn ν (n :: rest) f := by
          funext m
          by_cases h1 : m ∈ rest <;> by_cases h2 : m = n <;>
            simp [overrideOn, CL.updateInd, h1, h2]
        rw [hv] at hx; exact hx
      · intro hall x
        refine (satForall_plains i σ body rest (CL.updateInd ν n x)).mpr ?_
        intro f
        have hx := hall (fun m => if m ∈ rest then f m else x)
        have hv : overrideOn ν (n :: rest) (fun m => if m ∈ rest then f m else x)
            = overrideOn (CL.updateInd ν n x) rest f := by
          funext m
          by_cases h1 : m ∈ rest <;> by_cases h2 : m = n <;>
            simp [overrideOn, CL.updateInd, h1, h2]
        rw [hv] at hx; exact hx

/-! ## The Horn-row combinator -/

/-- A term of a Horn row: a quantified variable or an IRI constant. -/
inductive HTerm where
  | v (n : String)
  | c (x : RDF.WfIri)

/-- The CL term a Horn-row term reads as. -/
def HTerm.toTerm : HTerm → CL.Term
  | .v n => .name n
  | .c x => .name x.val

/-- Scoping check: every variable is bound by the row's binder list.
(Constants need no check: an IRI contains a colon and the binder names
never do, so a constant is never captured.) -/
def HTerm.scopedB (vars : List String) : HTerm → Bool
  | .v n => vars.contains n
  | .c _ => true

/-- A binary predication with the predicate in operator position —
the uniform triple reading of the design document §2.3, at the schema
level. -/
structure HAtom where
  p : HTerm
  s : HTerm
  o : HTerm

def HAtom.sentence (a : HAtom) : CL.Sentence :=
  .atom a.p.toTerm [.term a.s.toTerm, .term a.o.toTerm]

def HAtom.scopedB (vars : List String) (a : HAtom) : Bool :=
  a.p.scopedB vars && a.s.scopedB vars && a.o.scopedB vars

/-- **The Horn-row combinator**: the universal closure, over the row's
variables, of body-conjunction implies head. -/
def hornRow (vars : List String) (body : List HAtom) (head : HAtom) :
    CL.Sentence :=
  .all (vars.map .plain) (.impl (.conj (body.map HAtom.sentence)) head.sentence)

/-- The native reading of a Horn-row term over an RDF interpretation,
at a variable valuation. -/
def HTerm.valN (r : RDF.Interp) (f : String → r.idom) : HTerm → r.idom
  | .v n => f n
  | .c x => r.iIri x

/-- The native reading of a Horn-row atom: IEXT of the predicate's
individual at the subject/object pair. -/
def HAtom.HoldsN (r : RDF.Interp) (f : String → r.idom) (a : HAtom) : Prop :=
  r.iext (a.p.valN r f) (a.s.valN r f) (a.o.valN r f)

theorem denot_hterm (i : CL.Interp) {vars : List String}
    (hvars : ∀ n ∈ vars, ':' ∉ n.toList) (f : String → i.dom)
    (σ : String → List i.dom) :
    ∀ {t : HTerm}, t.scopedB vars = true →
      CL.denotTerm i (overrideOn i.iName vars f) σ t.toTerm
        = t.valN (restrictInterp i) f
  | .v n, hs => by
      have hn : n ∈ vars := by
        simpa [HTerm.scopedB, List.contains_iff_mem] using hs
      simp [HTerm.toTerm, CL.denotTerm, HTerm.valN, overrideOn, hn]
  | .c x, _ => by
      have hnm : x.val ∉ vars :=
        fun hmem => hvars _ hmem (isIri_has_colon x.property)
      simp [HTerm.toTerm, CL.denotTerm, HTerm.valN, restrictInterp,
            overrideOn, hnm]

theorem sat_hatom (i : CL.Interp) {vars : List String}
    (hvars : ∀ n ∈ vars, ':' ∉ n.toList) (f : String → i.dom)
    (σ : String → List i.dom) {a : HAtom} (ha : a.scopedB vars = true) :
    CL.Sat i (overrideOn i.iName vars f) σ a.sentence ↔
      a.HoldsN (restrictInterp i) f := by
  obtain ⟨hp, hs, ho⟩ : a.p.scopedB vars = true ∧ a.s.scopedB vars = true ∧
      a.o.scopedB vars = true := by
    simpa [HAtom.scopedB, Bool.and_eq_true, and_assoc] using ha
  simp only [HAtom.sentence, CL.Sat, CL.denotSeq,
             denot_hterm i hvars f σ hp, denot_hterm i hvars f σ hs,
             denot_hterm i hvars f σ ho]
  exact Iff.rfl

/-- **The one satisfaction lemma** every schema row goes through: a
Horn row is satisfied exactly when its native reading holds over the
restriction, at every variable valuation. -/
theorem satisfies_hornRow_iff (i : CL.Interp) {vars : List String}
    {body : List HAtom} {head : HAtom}
    (hvars : ∀ n ∈ vars, ':' ∉ n.toList)
    (hbody : ∀ a ∈ body, a.scopedB vars = true)
    (hhead : head.scopedB vars = true) :
    CL.Satisfies i (hornRow vars body head) ↔
      ∀ f : String → i.dom,
        (∀ a ∈ body, a.HoldsN (restrictInterp i) f) →
          head.HoldsN (restrictInterp i) f := by
  unfold CL.Satisfies hornRow
  simp only [CL.Sat]
  rw [satForall_plains]
  constructor
  · intro h f hb
    have hh := h f
    simp only [CL.Sat] at hh
    rw [satAll_forall] at hh
    refine (sat_hatom i hvars f _ hhead).mp (hh ?_)
    intro s hsmem
    obtain ⟨a, hamem, rfl⟩ := List.mem_map.mp hsmem
    exact (sat_hatom i hvars f _ (hbody a hamem)).mpr (hb a hamem)
  · intro h f
    simp only [CL.Sat]
    rw [satAll_forall]
    intro hb
    refine (sat_hatom i hvars f _ hhead).mpr (h f ?_)
    intro a hamem
    exact (sat_hatom i hvars f _ (hbody a hamem)).mp
      (hb _ (List.mem_map.mpr ⟨a, hamem, rfl⟩))

/-! ## Generic transport of Horn rows through the interpretation pair -/

/-- IEXT of the restriction of a lift, unfolded to projections. -/
theorem restrict_lift_iext (r : RDF.Interp) (p u v : (liftInterp r).dom) :
    (restrictInterp (liftInterp r)).iext p u v ↔ r.iext p.2 u.2 v.2 :=
  Iff.rfl

/-- An IRI's denotation under restriction-of-lift projects to the
native denotation. -/
theorem restrict_lift_iIri (r : RDF.Interp) (x : RDF.WfIri) :
    (restrictInterp (liftInterp r)).iIri x
      = ((some x.val, r.iIri x) : (liftInterp r).dom) :=
  liftInterp_iName_iri r x

theorem valN_restrict_lift (r : RDF.Interp) (f : String → (liftInterp r).dom) :
    ∀ t : HTerm,
      (t.valN (restrictInterp (liftInterp r)) f).2
        = t.valN r (fun n => (f n).2)
  | .v _ => rfl
  | .c x => by
      show ((restrictInterp (liftInterp r)).iIri x).2 = r.iIri x
      rw [restrict_lift_iIri]

theorem holdsN_restrict_lift (r : RDF.Interp)
    (f : String → (liftInterp r).dom) (a : HAtom) :
    a.HoldsN (restrictInterp (liftInterp r)) f ↔
      a.HoldsN r (fun n => (f n).2) := by
  unfold HAtom.HoldsN
  rw [← valN_restrict_lift r f a.p, ← valN_restrict_lift r f a.s,
      ← valN_restrict_lift r f a.o]
  exact Iff.rfl

/-- **Generic lift transport**: a Horn row whose native reading is
true in `r` is satisfied by the lifted interpretation. -/
theorem liftInterp_sat_hornRow (r : RDF.Interp) {vars : List String}
    {body : List HAtom} {head : HAtom}
    (hvars : ∀ n ∈ vars, ':' ∉ n.toList)
    (hbody : ∀ a ∈ body, a.scopedB vars = true)
    (hhead : head.scopedB vars = true)
    (hnat : ∀ f : String → r.idom,
      (∀ a ∈ body, a.HoldsN r f) → head.HoldsN r f) :
    CL.Satisfies (liftInterp r) (hornRow vars body head) := by
  rw [satisfies_hornRow_iff _ hvars hbody hhead]
  intro f hb
  rw [holdsN_restrict_lift]
  exact hnat _ (fun a ha => (holdsN_restrict_lift r f a).mp (hb a ha))

/-! ## The six ρdf rows

Row order and premise shapes follow `RDFS/RdfsCore.lean` (the §9.2
table); each row's native reading is definitionally the semantic
condition of `RDF/EntailmentRdfsModelTheory.lean` /
`OWL/Semantics.lean` that `RDFS/RhoDfCompleteness.lean` rests the row
on. -/

/-- rdfs2 — `(forall (p c x y) (if (and (rdfs:domain p c) (p x y))
(rdf:type x c)))`. -/
def rowRdfs2 : CL.Sentence :=
  hornRow ["p", "c", "x", "y"]
    [⟨.c RDFS.rdfsDomain, .v "p", .v "c"⟩, ⟨.v "p", .v "x", .v "y"⟩]
    ⟨.c RDFS.rdfType, .v "x", .v "c"⟩

/-- rdfs3 — range: the OBJECT falls in the class. -/
def rowRdfs3 : CL.Sentence :=
  hornRow ["p", "c", "x", "y"]
    [⟨.c RDFS.rdfsRange, .v "p", .v "c"⟩, ⟨.v "p", .v "x", .v "y"⟩]
    ⟨.c RDFS.rdfType, .v "y", .v "c"⟩

/-- rdfs5 — subPropertyOf transitivity. -/
def rowRdfs5 : CL.Sentence :=
  hornRow ["x", "y", "z"]
    [⟨.c RDFS.rdfsSubPropertyOf, .v "x", .v "y"⟩,
     ⟨.c RDFS.rdfsSubPropertyOf, .v "y", .v "z"⟩]
    ⟨.c RDFS.rdfsSubPropertyOf, .v "x", .v "z"⟩

/-- rdfs7 — subPropertyOf USE: the sub-property's pairs are the
super-property's. The head predicate is a VARIABLE — legal because CL
is unsegregated. -/
def rowRdfs7 : CL.Sentence :=
  hornRow ["x", "y", "u", "v"]
    [⟨.c RDFS.rdfsSubPropertyOf, .v "x", .v "y"⟩,
     ⟨.v "x", .v "u", .v "v"⟩]
    ⟨.v "y", .v "u", .v "v"⟩

/-- rdfs9 — subClassOf USE. -/
def rowRdfs9 : CL.Sentence :=
  hornRow ["x", "y", "u"]
    [⟨.c RDFS.rdfsSubClassOf, .v "x", .v "y"⟩,
     ⟨.c RDFS.rdfType, .v "u", .v "x"⟩]
    ⟨.c RDFS.rdfType, .v "u", .v "y"⟩

/-- rdfs11 — subClassOf transitivity. -/
def rowRdfs11 : CL.Sentence :=
  hornRow ["x", "y", "z"]
    [⟨.c RDFS.rdfsSubClassOf, .v "x", .v "y"⟩,
     ⟨.c RDFS.rdfsSubClassOf, .v "y", .v "z"⟩]
    ⟨.c RDFS.rdfsSubClassOf, .v "x", .v "z"⟩

/-- **The ρdf schema**: exactly the six rule rows — no axiomatic
triples, no reflexivity rows (design document §3 stage 2). -/
def rhoDfSchema : Schema := fun s =>
  s = rowRdfs2 ∨ s = rowRdfs3 ∨ s = rowRdfs5 ∨ s = rowRdfs7 ∨
  s = rowRdfs9 ∨ s = rowRdfs11

/-- The x-rdfscore regime's schema IS the ρdf schema
(`RDFS/RegimeDispatch.lean` closes with the ρdf closure). Named
separately so the stage 6 regime table can cite it. -/
def rdfsCoreSchema : Schema := rhoDfSchema

theorem rdfsCoreSchema_eq : rdfsCoreSchema = rhoDfSchema := rfl

/-! ## Per-row characterisation, against the native conditions -/

theorem satisfies_rowRdfs2_iff (i : CL.Interp) :
    CL.Satisfies i rowRdfs2 ↔ OWL.CondDomain (restrictInterp i) := by
  unfold rowRdfs2
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h p c x y h1 h2
    have hh := h (fun n => if n = "p" then p else if n = "c" then c
                           else if n = "x" then x else y)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1 h2
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "p") (f "c") (f "x") (f "y") hb.1 hb.2

theorem satisfies_rowRdfs3_iff (i : CL.Interp) :
    CL.Satisfies i rowRdfs3 ↔ OWL.CondRange (restrictInterp i) := by
  unfold rowRdfs3
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h p c x y h1 h2
    have hh := h (fun n => if n = "p" then p else if n = "c" then c
                           else if n = "x" then x else y)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1 h2
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "p") (f "c") (f "x") (f "y") hb.1 hb.2

theorem satisfies_rowRdfs5_iff (i : CL.Interp) :
    CL.Satisfies i rowRdfs5 ↔ RDF.CondSubPropertyOfTrans (restrictInterp i) := by
  unfold rowRdfs5
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x y z h1 h2
    have hh := h (fun n => if n = "x" then x else if n = "y" then y else z)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1 h2
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") (f "y") (f "z") hb.1 hb.2

theorem satisfies_rowRdfs7_iff (i : CL.Interp) :
    CL.Satisfies i rowRdfs7 ↔ RDF.CondSubPropertyOf (restrictInterp i) := by
  unfold rowRdfs7
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x y u v h1 h2
    have hh := h (fun n => if n = "x" then x else if n = "y" then y
                           else if n = "u" then u else v)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1 h2
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") (f "y") (f "u") (f "v") hb.1 hb.2

theorem satisfies_rowRdfs9_iff (i : CL.Interp) :
    CL.Satisfies i rowRdfs9 ↔ RDF.CondSubClassOf (restrictInterp i) := by
  unfold rowRdfs9
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x y u h1 h2
    have hh := h (fun n => if n = "x" then x else if n = "y" then y else u)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1 h2
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") (f "y") (f "u") hb.1 hb.2

theorem satisfies_rowRdfs11_iff (i : CL.Interp) :
    CL.Satisfies i rowRdfs11 ↔ RDF.CondSubClassOfTrans (restrictInterp i) := by
  unfold rowRdfs11
  rw [satisfies_hornRow_iff i (by decide) (by decide) (by decide)]
  constructor
  · intro h x y z h1 h2
    have hh := h (fun n => if n = "x" then x else if n = "y" then y else z)
    simp [HAtom.HoldsN, HTerm.valN] at hh
    exact hh h1 h2
  · intro hc f hb
    simp [HAtom.HoldsN, HTerm.valN] at hb
    exact hc (f "x") (f "y") (f "z") hb.1 hb.2

/-- Schema satisfaction IS the native condition bundle, through the
restriction. -/
theorem satisfiesSchema_rhoDf_iff (i : CL.Interp) :
    SatisfiesSchema i rhoDfSchema ↔ RDF.RhoDfConditions (restrictInterp i) := by
  constructor
  · intro h
    exact ⟨(satisfies_rowRdfs2_iff i).mp (h _ (Or.inl rfl)),
           (satisfies_rowRdfs3_iff i).mp (h _ (Or.inr (Or.inl rfl))),
           (satisfies_rowRdfs7_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
           (satisfies_rowRdfs5_iff i).mp (h _ (Or.inr (Or.inr (Or.inl rfl)))),
           (satisfies_rowRdfs9_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
           (satisfies_rowRdfs11_iff i).mp
             (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))⟩
  · rintro ⟨hd, hr, hsp, hspt, hsc, hsct⟩ s hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (satisfies_rowRdfs2_iff i).mpr hd
    · exact (satisfies_rowRdfs3_iff i).mpr hr
    · exact (satisfies_rowRdfs5_iff i).mpr hspt
    · exact (satisfies_rowRdfs7_iff i).mpr hsp
    · exact (satisfies_rowRdfs9_iff i).mpr hsc
    · exact (satisfies_rowRdfs11_iff i).mpr hsct

/-- The ρdf condition bundle transfers from a native interpretation to
the restriction of its lift: every condition is a Horn fact over
`iext`, and the lifted relation reads projections. -/
theorem rhoDfConditions_restrict_lift (r : RDF.Interp)
    (hr : RDF.RhoDfConditions r) :
    RDF.RhoDfConditions (restrictInterp (liftInterp r)) := by
  obtain ⟨hd, hrg, hsp, hspt, hsc, hsct⟩ := hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p c x y h1 h2
    simp only [RDF.icext, restrict_lift_iIri] at *
    exact hd p.2 c.2 x.2 y.2 h1 h2
  · intro p c x y h1 h2
    simp only [RDF.icext, restrict_lift_iIri] at *
    exact hrg p.2 c.2 x.2 y.2 h1 h2
  · intro x y u v h1 h2
    simp only [restrict_lift_iIri] at *
    exact hsp x.2 y.2 u.2 v.2 h1 h2
  · intro x y z h1 h2
    simp only [restrict_lift_iIri] at *
    exact hspt x.2 y.2 z.2 h1 h2
  · intro x y u h1 h2
    simp only [RDF.icext, restrict_lift_iIri] at *
    exact hsc x.2 y.2 u.2 h1 h2
  · intro x y z h1 h2
    simp only [restrict_lift_iIri] at *
    exact hsct x.2 y.2 z.2 h1 h2

/-! ## The stage 2 gate theorem, ρdf half -/

/-- **ρdf adequacy** (design document §4.2, strengthened per the
module header): entailment under the ρdf schema between translated
graphs coincides with native ρdf entailment — an unconditional iff,
no fragment hypotheses. -/
theorem unified_adequate_rhoDf (g h : RDF.Graph) :
    EntailsSchema condTrue rhoDfSchema [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.RhoDfEntails g h := by
  constructor
  · intro hE r hr hg
    have h1 : CL.Satisfies (liftInterp r) (rdfToTheory g) :=
      (satisfies_rdfToTheory_lift r g).mpr hg
    have h2 : CL.Satisfies (liftInterp r) (rdfToTheory h) :=
      hE (liftInterp r) True.intro
        ((satisfiesSchema_rhoDf_iff _).mpr (rhoDfConditions_restrict_lift r hr))
        (fun s hs => by
          obtain rfl := List.mem_singleton.mp hs
          exact h1)
    exact (satisfies_rdfToTheory_lift r h).mp h2
  · intro hMt i _ hsch hsat
    have h1 : RDF.Satisfies (restrictInterp i) g :=
      (satisfies_rdfToTheory_restrict i g).mp
        (hsat _ (List.mem_singleton.mpr rfl))
    exact (satisfies_rdfToTheory_restrict i h).mpr
      (hMt (restrictInterp i) ((satisfiesSchema_rhoDf_iff i).mp hsch) h1)

end L4Factoidal.Unified

/-! ## The native derivation-soundness bridge (introduced here, in the
`RDF` namespace — see the module header) -/

namespace L4Factoidal.RDF

open L4Factoidal.RDFS (Derives)

/-- Everything the ρdf rule relation derives is true, in every ρdf
interpretation, under the same assignment that makes the graph true —
the interpretation-level soundness the native tree deliberately did
not state (`RDFS/RdfsCore.lean` module header). One induction; each
case is one condition of `RhoDfConditions`. -/
theorem rhoDf_derives_holds {i : Interp} (hc : RhoDfConditions i)
    {a : BnodeAssignment i.idom} {g : Graph} (hg : HoldsAll i a g)
    {t : Triple} (h : Derives g t) : TripleHolds i a t := by
  obtain ⟨hd, hr, hsp, hspt, hsc, hsct⟩ := hc
  induction h with
  | base hm => exact hg _ hm
  | rdfs2 _ _ ih1 ih2 =>
      exact hd _ _ _ _ ih1 ih2
  | rdfs3 _ _ hsub ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      rw [denot_toSubject? i a hsub]
      exact hr _ _ _ _ ih1 ih2
  | rdfs5 _ hsub _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      rw [← denot_toSubject? i a hsub] at ih1
      exact hspt _ _ _ ih1 ih2
  | rdfs7 _ _ ih1 ih2 =>
      exact hsp _ _ _ _ ih1 ih2
  | rdfs9 _ _ ih1 ih2 =>
      exact hsc _ _ _ ih2 ih1
  | rdfs11 _ hsub _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      rw [← denot_toSubject? i a hsub] at ih1
      exact hsct _ _ _ ih1 ih2

/-- ρdf entailment is invariant under replacing the premise graph by
its executable closure: the closure adds only `Derives`-derivable
triples (`ClosureTheorems.closure_sound`), and those are true in every
admissible model of the premise (`rhoDf_derives_holds`). -/
theorem rhoDfEntails_closure_iff (g h : Graph) (fuel : Nat) :
    RhoDfEntails (RDFS.closure g fuel) h ↔ RhoDfEntails g h := by
  constructor
  · intro hc i hcond hsat
    obtain ⟨a, ha⟩ := hsat
    exact hc i hcond
      ⟨a, fun t ht => rhoDf_derives_holds hcond ha (RDFS.closure_sound fuel g ht)⟩
  · intro hgent i hcond hsat
    obtain ⟨a, ha⟩ := hsat
    exact hgent i hcond ⟨a, fun t ht => ha t (RDFS.closure_extensive fuel g ht)⟩

/-! ### Executable sufficient checks for the decided corollary's
hypotheses -/

/-- `Term.toSubject?` recovers the subject `subjTerm` came from — the
converse of `subjTerm_of_toSubject?`. -/
theorem toSubject?_subjTerm (s : Subject) :
    (subjTerm s).toSubject? = some s := by
  cases s <;> rfl

/-- The rdfs9 conclusions the executable step does NOT emit: the
specification row `Rdfs9Derives` fires for a BLANK-NODE class term
(`sub.s` is any subject), while `RDFS.rdfs9For` reads the class off a
`rdf:type` object and requires an IRI. The closedness check must
cover both, because `RhoDfClosed` is stated over the specification
relations. -/
def rdfs9BnodeConclusions (c : Graph) : List Triple :=
  c.flatMap (fun typ =>
    if typ.p == RDFS.rdfType then
      match typ.o with
      | .bnode b =>
          (RDFS.objectsOf c (.bnode b) RDFS.rdfsSubClassOf).map
            (fun o => ⟨typ.s, RDFS.rdfType, o⟩)
      | _ => []
    else [])

/-- Executable ρdf-closedness check: every one-round conclusion is
already a member (STRICT list membership — the specification-level
`RhoDfClosed` is stated over `∈`, not the engine's coarser
`Triple.eqb`, so the check must be too). -/
def rhoDfClosedCheck (c : Graph) : Bool :=
  (RDFS.stepConclusions c ++ rdfs9BnodeConclusions c).all
    (fun t => decide (t ∈ c))

/-- Bridge, rdfs2: the specification row's conclusion is a one-round
conclusion of the executable step. -/
private theorem spec2_step {c : Graph} {t : Triple}
    (h : Rdfs2Derives c t) : t ∈ RDFS.stepConclusions c := by
  obtain ⟨decl, hdecl, u, hu, a, hp, hs, hup, rfl⟩ := h
  refine RDFS.mem_stepConclusions_rdfs2 hdecl ?_
  unfold RDFS.rdfs2For
  simp only [hs, hp, beq_self_eq_true, reduceIte]
  exact List.mem_map.mpr ⟨u, RDFS.mem_triplesWithPredicate_of hu hup, rfl⟩

private theorem spec3_step {c : Graph} {t : Triple}
    (h : Rdfs3Derives c t) : t ∈ RDFS.stepConclusions c := by
  obtain ⟨decl, hdecl, u, hu, a, zs, hp, hs, hup, hzs, rfl⟩ := h
  refine RDFS.mem_stepConclusions_rdfs3 hdecl ?_
  unfold RDFS.rdfs3For
  simp only [hs, hp, beq_self_eq_true, reduceIte]
  refine List.mem_filterMap.mpr ⟨u, RDFS.mem_triplesWithPredicate_of hu hup, ?_⟩
  rw [← hzs, toSubject?_subjTerm]

private theorem spec5_step {c : Graph} {t : Triple}
    (h : Rdfs5Derives c t) : t ∈ RDFS.stepConclusions c := by
  obtain ⟨t1, h1, t2, h2, ys, hp1, hp2, hys, hs2, rfl⟩ := h
  refine RDFS.mem_stepConclusions_rdfs5 h1 ?_
  have ho : t1.o.toSubject? = some ys := by
    rw [← hys, toSubject?_subjTerm]
  unfold RDFS.rdfs5For
  simp only [hp1, ho, beq_self_eq_true, reduceIte]
  refine List.mem_map.mpr ⟨t2.o, ?_, rfl⟩
  refine RDFS.mem_objectsOf_of_mem ?_
  have he : t2 = ⟨ys, RDFS.rdfsSubPropertyOf, t2.o⟩ := by
    cases t2; simp_all
  rw [← he]; exact h2

private theorem spec7_step {c : Graph} {t : Triple}
    (h : Rdfs7Derives c t) : t ∈ RDFS.stepConclusions c := by
  obtain ⟨decl, hdecl, u, hu, a, b, hp, hs, ho, hup, rfl⟩ := h
  refine RDFS.mem_stepConclusions_rdfs7 hdecl ?_
  unfold RDFS.rdfs7For
  simp only [hs, ho, hp, beq_self_eq_true, reduceIte]
  exact List.mem_map.mpr ⟨u, RDFS.mem_triplesWithPredicate_of hu hup, rfl⟩

private theorem spec9_step {c : Graph} {t : Triple}
    (h : Rdfs9Derives c t) :
    t ∈ RDFS.stepConclusions c ++ rdfs9BnodeConclusions c := by
  obtain ⟨sub, hsub, typ, htyp, xs, hsp, hss, htp, hto, rfl⟩ := h
  have hsubm : (⟨xs, RDFS.rdfsSubClassOf, sub.o⟩ : Triple) ∈ c := by
    have he : sub = ⟨xs, RDFS.rdfsSubClassOf, sub.o⟩ := by
      cases sub; simp_all
    rw [← he]; exact hsub
  cases hxs : xs with
  | iri xi =>
      refine List.mem_append_left _ (RDFS.mem_stepConclusions_rdfs9 htyp ?_)
      rw [hxs] at hto
      have hto' : typ.o = Term.iri xi := hto
      unfold RDFS.rdfs9For
      simp only [hto', htp, beq_self_eq_true, reduceIte]
      refine List.mem_map.mpr ⟨sub.o, ?_, rfl⟩
      exact RDFS.mem_objectsOf_of_mem (hxs ▸ hsubm)
  | bnode xb =>
      refine List.mem_append_right _ ?_
      rw [hxs] at hto
      have hto' : typ.o = Term.bnode xb := hto
      unfold rdfs9BnodeConclusions
      refine List.mem_flatMap.mpr ⟨typ, htyp, ?_⟩
      simp only [htp, beq_self_eq_true, reduceIte, hto']
      refine List.mem_map.mpr ⟨sub.o, ?_, rfl⟩
      exact RDFS.mem_objectsOf_of_mem (hxs ▸ hsubm)

private theorem spec11_step {c : Graph} {t : Triple}
    (h : Rdfs11Derives c t) : t ∈ RDFS.stepConclusions c := by
  obtain ⟨t1, h1, t2, h2, ys, hp1, hp2, hys, hs2, rfl⟩ := h
  refine RDFS.mem_stepConclusions_rdfs11 h1 ?_
  have ho : t1.o.toSubject? = some ys := by
    rw [← hys, toSubject?_subjTerm]
  unfold RDFS.rdfs11For
  simp only [hp1, ho, beq_self_eq_true, reduceIte]
  refine List.mem_map.mpr ⟨t2.o, ?_, rfl⟩
  refine RDFS.mem_objectsOf_of_mem ?_
  have he : t2 = ⟨ys, RDFS.rdfsSubClassOf, t2.o⟩ := by
    cases t2; simp_all
  rw [← he]; exact h2

/-- The executable check is sufficient for specification-level
closedness. -/
theorem rhoDfClosed_of_check {c : Graph}
    (h : rhoDfClosedCheck c = true) : RhoDfClosed c := by
  have hmem : ∀ t ∈ RDFS.stepConclusions c ++ rdfs9BnodeConclusions c, t ∈ c := by
    intro t ht
    exact of_decide_eq_true (List.all_eq_true.mp h t ht)
  have hstep : ∀ t ∈ RDFS.stepConclusions c, t ∈ c :=
    fun t ht => hmem t (List.mem_append_left _ ht)
  exact ⟨fun t hd => hstep t (spec2_step hd),
         fun t hd => hstep t (spec3_step hd),
         fun t hd => hstep t (spec5_step hd),
         fun t hd => hstep t (spec7_step hd),
         fun t hd => hmem t (spec9_step hd),
         fun t hd => hstep t (spec11_step hd)⟩

/-- The executable fragment check (`RDFS/Closure.lean`) is sufficient
for the model-fragment predicate of `RDFS/RhoDfCompleteness.lean`. -/
theorem rhoDfModelFrag_of_check {g : Graph}
    (h : RDFS.isRhoDfFrag g = true) : RhoDfModelFragGraph g := by
  intro t ht
  have hb := List.all_eq_true.mp h t ht
  simp only [RDFS.isRhoDfFragTriple, Bool.and_eq_true] at hb
  obtain ⟨hobj, hsp⟩ := hb
  constructor
  · cases ho : t.o with
    | iri x => trivial
    | bnode b => trivial
    | literal l => simp [ho] at hobj
    | tripleTerm s p o => simp [ho] at hobj
  · intro hp
    rw [hp] at hsp
    simp only [bne_self_eq_false, Bool.false_or] at hsp
    cases ho : t.o with
    | iri x => exact ⟨x, by simp⟩
    | bnode b => simp [ho] at hsp
    | literal l => simp [ho] at hsp
    | tripleTerm s p o => simp [ho] at hsp

end L4Factoidal.RDF

namespace L4Factoidal.Unified

/-! ## The decided corollary

The chain: gate iff → closure invariance → the native
closed-graph characterisation (`rhoDfClosed_iff`, Herbrand) → the
executable decision procedure. The three hypotheses are exactly where
`RhoDfCompleteness` needs them, and each has an executable sufficient
check (`rhoDfClosedCheck`, `RDFS.isRhoDfFrag`) dischargeable by
`decide` on concrete inputs — the instance below does exactly that. -/

theorem unified_adequate_rhoDf_decided (g h : RDF.Graph) (fuel : Nat)
    (hclosed : RDF.RhoDfClosed (RDFS.closure g fuel))
    (hf : RDF.RhoDfModelFragGraph (RDFS.closure g fuel))
    (hfe : RDF.GraphTtFree h) :
    EntailsSchema condTrue rhoDfSchema [rdfToTheory g] (rdfToTheory h)
      ↔ RDF.simpleEntails (RDFS.closure g fuel) h = true :=
  ((((unified_adequate_rhoDf g h).trans
      (RDF.rhoDfEntails_closure_iff g h fuel).symm).trans
      (RDF.rhoDfClosed_iff hclosed hf hfe)).trans
      (RDF.spec_iff_simpleEntails _ h)).trans
      (RDF.SimpleRefinement.simpleEntails_iff_spec _ h).symm

/-! ### A fully decided instance, positive and negative

`demoG` closes in one round: the subclass chain plus a typed
individual. The three hypotheses of the corollary are discharged by
`decide` through the executable checks; the verdicts on both sides of
the iff are pinned by `#guard`s below. -/

private def dmA : RDF.WfIri := ⟨"http://rho.example/a", by decide⟩
private def dmC1 : RDF.WfIri := ⟨"http://rho.example/C1", by decide⟩
private def dmC2 : RDF.WfIri := ⟨"http://rho.example/C2", by decide⟩

def demoG : RDF.Graph :=
  [⟨.iri dmA, RDFS.rdfType, .iri dmC1⟩,
   ⟨.iri dmC1, RDFS.rdfsSubClassOf, .iri dmC2⟩]

def demoH : RDF.Graph := [⟨.iri dmA, RDFS.rdfType, .iri dmC2⟩]

theorem demoH_ttFree : RDF.GraphTtFree demoH := by
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  trivial

/-- The decided chain end to end: the schema entailment holds because
the executable pipeline says so. -/
theorem unified_rhoDf_demo :
    EntailsSchema condTrue rhoDfSchema
      [rdfToTheory demoG] (rdfToTheory demoH) :=
  (unified_adequate_rhoDf_decided demoG demoH 3
      (RDF.rhoDfClosed_of_check (by decide))
      (RDF.rhoDfModelFrag_of_check (by decide))
      demoH_ttFree).mpr (by decide)

/-! ## Finding C-1 at the unified level, negative half

`[X rdfs:subClassOf Y]` does NOT ρdf-schema-entail
`[X rdfs:subClassOf X]`. The refutation flows entirely through the
decided corollary and the executable decision procedure — the premise
graph is its own ρdf closure. (`RDFS/RhoDfCompleteness.lean` proves the
native counterpart with the Herbrand countermodel; its witness pair is
file-private, hence the local copy.) `Unified/RdfsSchema.lean` proves
the POSITIVE half — the full RDFS schema does entail the pair — making
this the strictness witness between the two schemas, and the
not-everything guard for `rhoDfSchema`. -/

private def c1X : RDF.WfIri := ⟨"http://example.org/X", by decide⟩
private def c1Y : RDF.WfIri := ⟨"http://example.org/Y", by decide⟩

def c1Prem : RDF.Graph := [⟨.iri c1X, RDFS.rdfsSubClassOf, .iri c1Y⟩]
def c1Concl : RDF.Graph := [⟨.iri c1X, RDFS.rdfsSubClassOf, .iri c1X⟩]

theorem c1Concl_ttFree : RDF.GraphTtFree c1Concl := by
  intro t ht
  obtain rfl := List.mem_singleton.mp ht
  trivial

theorem rhoDf_not_entails_selfLoop_unified :
    ¬ EntailsSchema condTrue rhoDfSchema
        [rdfToTheory c1Prem] (rdfToTheory c1Concl) := by
  intro hE
  have hb := (unified_adequate_rhoDf_decided c1Prem c1Concl 1
      (RDF.rhoDfClosed_of_check (by decide))
      (RDF.rhoDfModelFrag_of_check (by decide))
      c1Concl_ttFree).mp hE
  rw [show RDF.simpleEntails (RDFS.closure c1Prem 1) c1Concl = false
        from by decide] at hb
  exact Bool.false_ne_true hb

/-- The same refutation against the native relation, through the gate
theorem — `rhoDfSchema`-entailment between translated graphs is not
the everything-relation. -/
theorem rhoDfEntails_not_selfLoop : ¬ RDF.RhoDfEntails c1Prem c1Concl :=
  fun h => rhoDf_not_entails_selfLoop_unified
    ((unified_adequate_rhoDf c1Prem c1Concl).mpr h)

/-! ## Non-vacuity: the schema and the native bundle are satisfiable -/

/-- The ρdf schema is satisfiable (by the lift of the native trivial
interpretation, whose conditions `RDF/SemanticsHypothesisWitness.lean`
established) — entailment under it never holds by schema-vacuity. -/
theorem rhoDfSchema_satisfiable : ∃ i : CL.Interp, SatisfiesSchema i rhoDfSchema :=
  ⟨liftInterp RDF.trivialInterp,
   (satisfiesSchema_rhoDf_iff _).mpr
     (rhoDfConditions_restrict_lift _
       (RDF.rdfsConditions_imply_rhoDf
         (RDF.trivial_rdfs_conditions (fun _ => False))))⟩

/-! ## Build-time checks -/

section Checks

/- The executable pipeline agrees with the theorems above: the demo
closure saturates inside the fuel, stays in the fragment, and decides
the instance positively; the C-1 pair decides negatively. -/

#guard RDF.rhoDfClosedCheck (RDFS.closure demoG 3)
#guard RDFS.isRhoDfFrag (RDFS.closure demoG 3)
#guard RDF.simpleEntails (RDFS.closure demoG 3) demoH
#guard RDF.rhoDfClosedCheck (RDFS.closure c1Prem 1)
#guard RDFS.isRhoDfFrag (RDFS.closure c1Prem 1)
#guard !(RDF.simpleEntails (RDFS.closure c1Prem 1) c1Concl)

/- A graph that is NOT closed fails the closedness check — the check
is not vacuously true. -/

#guard !(RDF.rhoDfClosedCheck demoG)

/-! Axiom audit — expected at most `propext` / `Classical.choice` /
`Quot.sound` (Lean's own foundations). No `sorryAx`, nothing
user-declared. -/

#print axioms satForall_plains
#print axioms satisfies_hornRow_iff
#print axioms liftInterp_sat_hornRow
#print axioms unified_adequate_rhoDf
#print axioms RDF.rhoDf_derives_holds
#print axioms RDF.rhoDfEntails_closure_iff
#print axioms RDF.rhoDfClosed_of_check
#print axioms unified_adequate_rhoDf_decided
#print axioms unified_rhoDf_demo
#print axioms rhoDf_not_entails_selfLoop_unified
#print axioms rhoDfSchema_satisfiable

end Checks

end L4Factoidal.Unified
