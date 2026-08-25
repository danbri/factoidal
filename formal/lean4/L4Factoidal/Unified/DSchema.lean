/-
L4Factoidal.Unified.DSchema — D-entailment in the unified LBase/IKL
theory: the datatype-map schema `dSchema`, the native model-theoretic
anchor `RDF.DEntailsMt`, the adequacy theorem `unified_adequate_d`,
the soundness half of the decided corollary
(`unified_adequate_d_decided_sound`), and the separating models that
show each exclusion ingredient is not redundant.

D-entailment landing of
https://github.com/danbri/factoidal/issues/598 (design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §2.5, §4.1,
§5.1; RDF 1.1 Semantics §7,
https://www.w3.org/TR/rdf11-mt/#datatype-entailment), REPAIRED per
https://github.com/danbri/factoidal/issues/602 (see "Triple terms"
below).

## The schema (design document §2.5, decided treatment of §5.1)

CL totalises denotation, so "an ill-typed literal cannot denote
anything" is encoded, not transcribed:

* **value identification** — for every literal pair the tree's
  D-value equality `RDF.literalValueEq D` accepts, the sentence
  `eq (embed l1) (embed l2)` (§7: "literals with the same value are
  interchangeable");
* **ill-typed exclusion** — for every TERM whose mentioned literals
  (`RDF.termIllTypedMention D`, triple-term interiors included)
  contain an ill-typed recognised literal, the sentence
  `neg (ex [x, r, b…] (atom r [x, embed t]))`: no true predication has
  the term's individual in object position, at any value of the term's
  blank nodes. A translated graph USING such a term contradicts its
  own exclusion axiom, so the theory entails everything
  (`unified_d_illtyped_entails_all`) — the §7.2 verdict, the one
  `RDF.Regime.inconsistent` computes.

## Triple terms — the spec anchor (issue 602)

The exclusion schema covers triple-term INTERIORS. Anchor: RDF 1.2
Semantics, W3C Working Draft 7 April 2026,
https://www.w3.org/TR/rdf12-semantics/ — §5 gives a ground triple term
the compositional denotation `I(E) = IT(I(E.s), I(E.p), I(E.o))`, and
§7.1 says an ill-typed recognised literal "cannot denote anything. In
this case, any triple containing the literal must be false. Thus, any
triple, and hence any graph, containing an ill-typed literal will be
D-unsatisfiable." An interior literal's denotation reaches the
containing triple term's through the compositional clause, so
"containing" covers interiors — encoded by the W3C rdf12
`rdf-semantics` test `malformed-literal` ("Malformed literals are
allowed in triple terms, but cause inconsistency"). Status caveat:
that document is a Working Draft, not a Recommendation, and RDF 1.1
Semantics has no triple-term clause at all; the anchor decision is
recorded on issue 602.

History: this module first shipped with a top-level-only exclusion
(clause 2 reached `i.iLit` directly and nothing else), read the
executable's interior collection as the DEFECT, and pinned the
disagreement as `dEntailsMt_tt_gap`. That attribution was wrong — the
executable agreed with the WD and its test suite; the totalized model
theory did not. The superseded bundle survives below as
`DInterpCondTopLevel`, with the separation theorems that show the
interior clause is the exact ingredient the repair added.

## The decided corollary — sound half landed, complete half named

`unified_adequate_d_decided_sound`: an executable `true`
(`RDF.regimeEntails .d`) now implies schema entailment,
UNCONDITIONALLY — no `GraphTtFree` hypothesis, because the repaired
clause 2 covers exactly the occurrences the executable collects, and
value-equal matching is sound under clause 1 even inside triple terms
(`termMatch` compares interior literals with the regime's `leq`).
The COMPLETENESS direction (model-theoretic entailment implies
executable `true`) is NOT claimed and is not a triple-term matter:
it needs (a) a D-Herbrand interpretation quotienting literals by
`literalValueEq D` (clause 1 forces value-equal literals to share a
denotation, so the plain term model does not qualify), and (b) a
completeness lemma for `searchInstance` under the regime's restricted
`Regime.bindable` (the existing `entailsWith_complete` requires
`bindable` universally true). Recorded as the registry's named open
lemma for this section.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfAdequacy
import L4Factoidal.RDF.Entailment

/-! ## The native anchor: D-interpretations, model-theoretically -/

namespace L4Factoidal.RDF

/-- The D-interpretation condition bundle (RDF 1.1 Semantics §7 plus
the RDF 1.2 Semantics WD triple-term clause — module header):

1. literals the D-value equality `literalValueEq D` identifies denote
   the same resource (§7's lexical-to-value mapping, observed through
   value equality — the comparison `Regime.literalEq` matches with);
2. a term that MENTIONS an ill-typed recognised literal
   (`termIllTypedMention D` — the term itself, or a triple-term
   interior at any depth) is in no property extension's object
   position, under every blank-node assignment — the totalised reading
   of WD §7.1's "cannot denote anything" composed through §5's
   `I(E) = IT(I(E.s), I(E.p), I(E.o))` (`Interp.iLit` and `Interp.iTt`
   are total, so the exclusion carries the unsatisfiability instead of
   a partial map).

Literals and triple terms occur in object position only (RDF 1.1/1.2
Concepts §3.1; `Subject` has neither constructor), so clause 2 reaches
every occurrence the term model can give them. -/
def DInterpCond (D : List WfIri) (i : Interp) : Prop :=
  (∀ l1 l2 : WfLiteral, literalValueEq D l1.val l2.val = true →
     i.iLit l1 = i.iLit l2) ∧
  (∀ t : Term, termIllTypedMention D t = true →
     ∀ (a : BnodeAssignment i.idom) (p x : i.idom),
       ¬ i.iext p x (denotTerm i a t))

/-- **D-entailment, model-theoretically** (RDF 1.1 Semantics §7 +
the WD triple-term reading): entailment over the D-interpretations.
The native anchor of `Unified.unified_adequate_d`. -/
def DEntailsMt (D : List WfIri) (g h : Graph) : Prop :=
  EntailsUnder (DInterpCond D) g h

/-- A used term with an ill-typed mention makes the graph
D-unsatisfiable, natively (WD §5 + §7.1; the `malformed-literal`
verdict): the premise entails everything. -/
theorem dEntailsMt_illtyped_native (D : List WfIri) {g : Graph}
    {t : Triple} (ht : t ∈ g)
    (ho : termIllTypedMention D t.o = true)
    (h : Graph) : DEntailsMt D g h := by
  intro i hi hsat
  obtain ⟨a, ha⟩ := hsat
  exact absurd (ha t ht) (hi.2 t.o ho a _ _)

/-! ## Soundness of the executable D-procedure

`RDF.regimeEntails .d` answers `inconsistent ∨ instance-found`. Both
disjuncts are sound for `DEntailsMt`, with no side condition — the
issue-602 repair is what makes the inconsistent disjunct's interior
collection sound, and clause 1 is what makes value-equal literal
matching sound (also inside triple terms, where `termMatch` recurses
with the regime's `leq`). -/

/-- A `termMatch` under `literalValueEq D` preserves denotation in
every interpretation satisfying clause 1. -/
theorem termMatch_valueEq_denot (D : List WfIri) (i : Interp)
    (h1 : ∀ l1 l2 : WfLiteral, literalValueEq D l1.val l2.val = true →
       i.iLit l1 = i.iLit l2)
    (a : BnodeAssignment i.idom) :
    ∀ {u v : Term}, termMatch (literalValueEq D) u v = true →
      denotTerm i a u = denotTerm i a v := by
  intro u
  induction u with
  | iri x =>
      intro v h
      cases v <;> simp only [termMatch, beq_iff_eq] at h <;> try simp at h
      subst h; rfl
  | bnode b =>
      intro v h
      cases v <;> simp only [termMatch, beq_iff_eq] at h <;> try simp at h
      subst h; rfl
  | literal l =>
      intro v h
      cases v <;> simp only [termMatch] at h <;> try simp at h
      simp only [denotTerm]
      exact h1 _ _ h
  | tripleTerm s p o ih =>
      intro v h
      cases v <;> simp only [termMatch, Bool.and_eq_true, beq_iff_eq] at h
        <;> try simp at h
      obtain ⟨⟨hs, hp⟩, ho⟩ := h
      subst hs; subst hp
      simp only [denotTerm, ih ho]

/-- Denotation of an instantiated subject under the composed
assignment. -/
theorem denot_instance_subject (i : Interp) (a : BnodeAssignment i.idom)
    (σ : BNodeId → Term) {s : Subject} {s' : Subject}
    (h : s.instance? σ = some s') :
    denotSubject i (fun b => denotTerm i a (σ b)) s =
      denotSubject i a s' := by
  cases s with
  | iri x =>
      simp only [Subject.instance?, Option.some.injEq] at h
      subst h; rfl
  | bnode b =>
      simp only [Subject.instance?] at h
      exact (denot_toSubject? i a h).symm

/-- Denotation of an instantiated term under the composed
assignment. -/
theorem denot_instance_term (i : Interp) (a : BnodeAssignment i.idom)
    (σ : BNodeId → Term) :
    ∀ {u u' : Term}, u.instance? σ = some u' →
      denotTerm i (fun b => denotTerm i a (σ b)) u = denotTerm i a u' := by
  intro u
  induction u with
  | iri x =>
      intro u' h
      simp only [Term.instance?, Option.some.injEq] at h
      subst h; rfl
  | bnode b =>
      intro u' h
      simp only [Term.instance?, Option.some.injEq] at h
      subst h; rfl
  | literal l =>
      intro u' h
      simp only [Term.instance?, Option.some.injEq] at h
      subst h; rfl
  | tripleTerm s p o ih =>
      intro u' h
      simp only [Term.instance?] at h
      cases hs : s.instance? σ with
      | none => rw [hs] at h; simp at h
      | some s' =>
          cases ho : o.instance? σ with
          | none => rw [hs, ho] at h; simp at h
          | some o' =>
              rw [hs, ho] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [denotTerm, denot_instance_subject i a σ hs, ih ho]

/-- A passing certificate carries satisfaction of the conclusion, in
every interpretation meeting clause 1. -/
theorem holdsAll_of_instanceCert_valueEq (D : List WfIri) (i : Interp)
    (h1 : ∀ l1 l2 : WfLiteral, literalValueEq D l1.val l2.val = true →
       i.iLit l1 = i.iLit l2)
    {m : Mapping} {g h : Graph}
    (hc : instanceCert (literalValueEq D) m g h = true)
    {a : BnodeAssignment i.idom} (ha : HoldsAll i a g) :
    HoldsAll i (fun b => denotTerm i a (m.toFun b)) h := by
  intro t ht
  simp only [instanceCert, List.all_eq_true] at hc
  have hct := hc t ht
  revert hct
  cases hinst : t.instance? m.toFun with
  | none => intro hct; simp at hct
  | some t' =>
    intro hct
    simp only [List.any_eq_true] at hct
    obtain ⟨u, hu, hm⟩ := hct
    obtain ⟨hsi, hoi, hpe⟩ := SimpleRefinement.instance?_parts hinst
    simp only [tripleMatch, Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨hus, hup⟩, humatch⟩ := hm
    have hg := ha u hu
    have hps : t.p = u.p := (hup.trans hpe).symm
    have hsub : denotSubject i (fun b => denotTerm i a (m.toFun b)) t.s
        = denotSubject i a u.s := by
      rw [denot_instance_subject i a m.toFun hsi, ← hus]
    have hobj : denotTerm i (fun b => denotTerm i a (m.toFun b)) t.o
        = denotTerm i a u.o := by
      rw [denot_instance_term i a m.toFun hoi,
          ← termMatch_valueEq_denot D i h1 a humatch]
    unfold TripleHolds at hg ⊢
    rw [hps, hsub, hobj]
    exact hg

/-- `entailsWith` under `literalValueEq D` is sound for satisfaction
transfer, for ANY bindability filter (the filter only prunes the
search; the certificate is what carries the claim). -/
theorem entailsWith_valueEq_sound (D : List WfIri) (bnd : Term → Bool)
    {g h : Graph}
    (he : entailsWith (literalValueEq D) bnd g h = true)
    (i : Interp)
    (h1 : ∀ l1 l2 : WfLiteral, literalValueEq D l1.val l2.val = true →
       i.iLit l1 = i.iLit l2)
    (hsat : Satisfies i g) : Satisfies i h := by
  obtain ⟨a, ha⟩ := hsat
  unfold entailsWith at he
  revert he
  cases hsr : searchInstance (literalValueEq D) bnd g h [] with
  | none => intro he; simp at he
  | some m =>
      intro he
      exact ⟨_, holdsAll_of_instanceCert_valueEq D i h1 he ha⟩

/-- **Soundness of the executable D-regime**, unconditional: when
`regimeEntails .d` answers `true`, the model theory agrees. The
converse (completeness) is NOT claimed — module header. -/
theorem regimeEntails_d_sound_mt (D : List WfIri) {g h : Graph}
    (he : regimeEntails .d D g h = true) : DEntailsMt D g h := by
  have he' : (hasIllFormedLiteral D g ||
      entailsWith (literalValueEq D) (Regime.bindable .d D) g h) = true := he
  rcases Bool.or_eq_true_iff.mp he' with hinc | hent
  · obtain ⟨t, ht, htm⟩ := hasIllFormedLiteral_iff.mp hinc
    exact dEntailsMt_illtyped_native D ht htm h
  · intro i hi hsat
    exact entailsWith_valueEq_sound D _ hent i hi.1 hsat

end L4Factoidal.RDF

namespace L4Factoidal.Unified

/-! ## The schema sentences -/

/-- The value-identification sentence for a literal pair
(design document §2.5; RDF 1.1 Semantics §7). -/
def dValueId (l1 l2 : RDF.WfLiteral) : CL.Sentence :=
  .eq (embedTerm (.literal l1)) (embedTerm (.literal l2))

/-- The bound-name list of a term's exclusion sentence: the relation
and object variables, then the term's blank nodes under the colon-free
spelling. All colon-free, so nothing captures an IRI name or a
`urn:cl:def:` operator name (the `FreshVal` discipline of
`Unified/RdfTransport`). -/
def dExclusionNames (t : RDF.Term) : List String :=
  "x" :: "r" :: (RDF.termBnodes t).map bnodeName

theorem dExclusionNames_no_colon (t : RDF.Term) :
    ∀ n ∈ dExclusionNames t, ':' ∉ n.toList := by
  intro n hn
  simp only [dExclusionNames, List.mem_cons] at hn
  rcases hn with rfl | rfl | hn
  · decide
  · decide
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hn
    exact bnodeName_no_colon b

/-- The ill-typed exclusion sentence for a TERM (the WD §5 + §7.1
composition — module header): no individual stands in any relation to
the term's individual in object position, at any value of the term's
blank nodes. Generalises the design document §2.5 literal sentence
`neg (ex [x, r] (atom r [x, literalTerm s d]))` to triple terms with
ill-typed interiors (issue 602). -/
def dExclusionTerm (t : RDF.Term) : CL.Sentence :=
  .neg (.ex ((dExclusionNames t).map .plain)
    (.atom (.name "r") [.term (.name "x"), .term (embedTerm t)]))

/-- The literal instance of the exclusion sentence — the shape the
§5.1 separating model reasons about. -/
def dExclusion (l : RDF.WfLiteral) : CL.Sentence :=
  dExclusionTerm (.literal l)

/-- The value-identification half of the D schema: one `dValueId` row
per literal pair `literalValueEq D` accepts. -/
def dValueSchema (D : List RDF.WfIri) : Schema := fun s =>
  ∃ l1 l2 : RDF.WfLiteral,
    RDF.literalValueEq D l1.val l2.val = true ∧ s = dValueId l1 l2

/-- The exclusion half: one `dExclusionTerm` row per term with an
ill-typed recognised mention (triple-term interiors included — the
literal rows are the `t = .literal l` instances). -/
def dExclusionSchema (D : List RDF.WfIri) : Schema := fun s =>
  ∃ t : RDF.Term, RDF.termIllTypedMention D t = true ∧ s = dExclusionTerm t

/-- **The D-interpretation schema** (design document §2.5 + the
issue-602 repair): value identification plus ill-typed exclusion.
Deliberately silent about ill-typed individuals beyond the exclusion
rows — §5.1's soundness requirement. -/
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

/-- The exclusion sentence for a TERM, characterised: no relation
extension holds of any pair ending in the term's individual, at any
blank-node assignment (read through `restrictInterp`, which is what
gives the free-standing sentence an RDF-side denotation to speak
about). -/
theorem satisfies_dExclusionTerm_iff (i : CL.Interp) (t : RDF.Term) :
    CL.Satisfies i (dExclusionTerm t) ↔
      ∀ (xv rv : i.dom) (a : RDF.BnodeAssignment i.dom),
        ¬ i.rel rv [xv, RDF.denotTerm (restrictInterp i) a t] := by
  have hν : ∀ f : String → i.dom,
      FreshVal i (overrideOn i.iName (dExclusionNames t) f) :=
    fun f => freshVal_overrideOn i (dExclusionNames_no_colon t) f
  have hsat : ∀ f : String → i.dom,
      CL.Sat i (overrideOn i.iName (dExclusionNames t) f) (fun _ => [])
          (.atom (.name "r") [.term (.name "x"), .term (embedTerm t)]) ↔
        i.rel (overrideOn i.iName (dExclusionNames t) f "r")
          [overrideOn i.iName (dExclusionNames t) f "x",
           RDF.denotTerm (restrictInterp i)
             (fun b => overrideOn i.iName (dExclusionNames t) f (bnodeName b))
             t] := by
    intro f
    simp only [CL.Sat, CL.denotSeq, CL.denotTerm,
               denot_embedTerm_restrict i
                 (fun b => overrideOn i.iName (dExclusionNames t) f (bnodeName b))
                 (hν f) t (fun _ _ => rfl)]
    rfl
  unfold dExclusionTerm CL.Satisfies
  simp only [CL.Sat]
  rw [satExists_plains]
  constructor
  · intro hn xv rv a hrel
    apply hn
    have hxm : "x" ∈ dExclusionNames t := List.mem_cons_self ..
    have hrm : "r" ∈ dExclusionNames t :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have hdx : bnodeNameDecode "x" = none := by decide
    have hdr : bnodeNameDecode "r" = none := by decide
    refine ⟨fun n => (bnodeNameDecode n).elim
      (if n == "x" then xv else rv) a, ?_⟩
    rw [hsat]
    have hx : overrideOn i.iName (dExclusionNames t)
        (fun n => (bnodeNameDecode n).elim (if n == "x" then xv else rv) a)
        "x" = xv := by
      simp [overrideOn, hxm, hdx]
    have hrv : overrideOn i.iName (dExclusionNames t)
        (fun n => (bnodeNameDecode n).elim (if n == "x" then xv else rv) a)
        "r" = rv := by
      simp [overrideOn, hrm, hdr]
    have hagree : RDF.denotTerm (restrictInterp i)
        (fun b => overrideOn i.iName (dExclusionNames t)
          (fun n => (bnodeNameDecode n).elim (if n == "x" then xv else rv) a)
          (bnodeName b)) t
        = RDF.denotTerm (restrictInterp i) a t := by
      refine RDF.denot_term_agree (restrictInterp i) (fun b hb => ?_)
      have hmem : bnodeName b ∈ dExclusionNames t :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨b, hb, rfl⟩))
      simp only [overrideOn, hmem, bnodeNameDecode_bnodeName, Option.elim]
      rfl
    rw [hx, hrv]
    exact Eq.mpr (congrArg (fun y => i.rel rv [xv, y]) hagree) hrel
  · rintro hall ⟨f, hf⟩
    rw [hsat] at hf
    exact hall _ _ _ hf

/-- The literal instance, in the shape the separating-model section
uses: the blank-node assignment is irrelevant to a literal's
denotation. -/
theorem satisfies_dExclusion_iff (i : CL.Interp) (l : RDF.WfLiteral) :
    CL.Satisfies i (dExclusion l) ↔
      ∀ xv rv : i.dom, ¬ i.rel rv [xv, litDenot i l] := by
  rw [show dExclusion l = dExclusionTerm (.literal l) from rfl,
      satisfies_dExclusionTerm_iff]
  constructor
  · intro h xv rv
    exact h xv rv (fun _ => i.domWit)
  · intro h xv rv a
    exact h xv rv

/-! ## Transport: the schema and the native condition bundle
correspond through the stage 1 interpretation pair -/

/-- The literal operator on the lifted interpretation computes the RDF
denotation (tagged): `litDenot` of the lift is `r.iLit`. -/
theorem litDenot_lift (r : RDF.Interp) (l : RDF.WfLiteral) :
    litDenot (liftInterp r) l = (none, r.iLit l) := by
  simp only [litDenot, embedTerm, CL.denotTerm]
  exact liftFn_litArgs r (freshVal_iName _) l

/-- Projection of the round-trip denotation: denotation under
`restrictInterp (liftInterp r)` projects (second component) to the
native denotation under the projected assignment — subjects. -/
theorem denotSubject_restrictLift_proj (r : RDF.Interp)
    (a : RDF.BnodeAssignment (restrictInterp (liftInterp r)).idom)
    (s : RDF.Subject) :
    (RDF.denotSubject (restrictInterp (liftInterp r)) a s).2 =
      RDF.denotSubject r (fun b => (a b).2) s := by
  cases s with
  | iri x =>
      show ((liftInterp r).iName x.val).2 = r.iIri x
      rw [liftInterp_iName_iri]
  | bnode b => rfl

/-- … and terms (the triple-term arm is `liftFn_tt`, the literal arm
`litDenot_lift`). -/
theorem denotTerm_restrictLift_proj (r : RDF.Interp)
    (a : RDF.BnodeAssignment (restrictInterp (liftInterp r)).idom) :
    ∀ t : RDF.Term,
      (RDF.denotTerm (restrictInterp (liftInterp r)) a t).2 =
        RDF.denotTerm r (fun b => (a b).2) t
  | .iri x => by
      show ((liftInterp r).iName x.val).2 = r.iIri x
      rw [liftInterp_iName_iri]
  | .bnode _ => rfl
  | .literal l => by
      show (litDenot (liftInterp r) l).2 = r.iLit l
      rw [litDenot_lift]
  | .tripleTerm s p o => by
      have hs := denotSubject_restrictLift_proj r a s
      have ho := denotTerm_restrictLift_proj r a o
      have hp : ((restrictInterp (liftInterp r)).iIri p).2 = r.iIri p := by
        show ((liftInterp r).iName p.val).2 = r.iIri p
        rw [liftInterp_iName_iri]
      have htt := liftFn_tt r
        (show (liftInterp r).dom from
          RDF.denotSubject (restrictInterp (liftInterp r)) a s)
        (show (liftInterp r).dom from
          (restrictInterp (liftInterp r)).iIri p)
        (show (liftInterp r).dom from
          RDF.denotTerm (restrictInterp (liftInterp r)) a o)
      have h2 : (RDF.denotTerm (restrictInterp (liftInterp r)) a
          (.tripleTerm s p o)).2
          = r.iTt (RDF.denotSubject (restrictInterp (liftInterp r)) a s).2
              ((restrictInterp (liftInterp r)).iIri p).2
              (RDF.denotTerm (restrictInterp (liftInterp r)) a o).2 :=
        congrArg Prod.snd htt
      rw [h2, hs, ho, hp]
      rfl

/-- A lifted D-interpretation satisfies the D schema. -/
theorem liftInterp_satisfiesSchema_d (D : List RDF.WfIri) (r : RDF.Interp)
    (hr : RDF.DInterpCond D r) :
    SatisfiesSchema (liftInterp r) (dSchema D) := by
  rintro s (⟨l1, l2, hlv, rfl⟩ | ⟨t, htm, rfl⟩)
  · rw [satisfies_dValueId_iff, litDenot_lift, litDenot_lift, hr.1 l1 l2 hlv]
  · rw [satisfies_dExclusionTerm_iff]
    intro xv rv a hrel
    have hrel2 : r.iext rv.2 xv.2
        (RDF.denotTerm (restrictInterp (liftInterp r)) a t).2 := hrel
    rw [denotTerm_restrictLift_proj r a t] at hrel2
    exact hr.2 t htm (fun b => (a b).2) rv.2 xv.2 hrel2

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
  · intro t htm a p x hrel
    have h := (satisfies_dExclusionTerm_iff i t).mp
      (hi _ (Or.inr ⟨t, htm, rfl⟩))
    exact h x p a hrel

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

/-- **The decided corollary, sound half** — unconditional (module
header): an executable `true` implies schema entailment. The
completeness direction is the registry's named open lemma
(D-Herbrand literal quotient + `bindable`-restricted search
completeness). -/
theorem unified_adequate_d_decided_sound (D : List RDF.WfIri)
    (g h : RDF.Graph) (he : RDF.regimeEntails .d D g h = true) :
    EntailsSchema condTrue (dSchema D) [rdfToTheory g] (rdfToTheory h) :=
  (unified_adequate_d D g h).mpr (RDF.regimeEntails_d_sound_mt D he)

/-! ## Ill-typed premises entail everything (WD §5 + §7.1; RDF 1.1
Semantics §7.2 for the top-level case) -/

/-- A translated graph USING a term with an ill-typed recognised
mention (top-level literal, or triple-term interior at any depth)
contradicts its own exclusion axiom: no schema-satisfying
interpretation satisfies it. -/
theorem dSchema_illtyped_unsat (D : List RDF.WfIri) {g : RDF.Graph}
    {t : RDF.Triple} (ht : t ∈ g)
    (ho : RDF.termIllTypedMention D t.o = true)
    (i : CL.Interp) (hsch : SatisfiesSchema i (dSchema D)) :
    ¬ CL.Satisfies i (rdfToTheory g) := by
  intro hsat
  rw [satisfies_rdfToTheory_iff] at hsat
  obtain ⟨f, hf⟩ := hsat
  have hν : FreshVal i (overrideOn i.iName (graphBnodeNames g) f) :=
    freshVal_overrideOn i (graphBnodeNames_no_colon g) f
  have hatom := hf t ht
  have hexcl := (satisfies_dExclusionTerm_iff i t.o).mp
    (hsch _ (Or.inr ⟨t.o, ho, rfl⟩))
  simp only [tripleAtom, CL.Sat, CL.denotSeq, CL.denotTerm,
             denot_embedTerm_restrict i
               (fun b => overrideOn i.iName (graphBnodeNames g) f (bnodeName b))
               hν t.o (fun _ _ => rfl)] at hatom
  exact hexcl _ _ _ hatom

/-- The everything-relation on a D-clashing premise: the unified
counterpart of `RDF.Regime.inconsistent`'s short-circuit ("an
inconsistent graph entails any graph"). -/
theorem unified_d_illtyped_entails_all (D : List RDF.WfIri) {g : RDF.Graph}
    {t : RDF.Triple} (ht : t ∈ g)
    (ho : RDF.termIllTypedMention D t.o = true)
    (c : CL.Sentence) :
    EntailsSchema condTrue (dSchema D) [rdfToTheory g] c := by
  intro i _ hsch hsat
  exact absurd (hsat _ (List.mem_singleton.mpr rfl))
    (dSchema_illtyped_unsat D ht ho i hsch)

/-- The same verdict natively, through the adequacy theorem (also
provable directly — `RDF.dEntailsMt_illtyped_native`). -/
theorem dEntailsMt_illtyped (D : List RDF.WfIri) {g : RDF.Graph}
    {t : RDF.Triple} (ht : t ∈ g)
    (ho : RDF.termIllTypedMention D t.o = true)
    (h : RDF.Graph) : RDF.DEntailsMt D g h :=
  (unified_adequate_d D g h).mp
    (unified_d_illtyped_entails_all D ht ho _)

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
  unified_d_illtyped_entails_all dWitD (List.mem_singleton.mpr rfl)
    (by decide) _

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
  rintro s (⟨l1, l2, _, rfl⟩ | ⟨t, _, rfl⟩)
  · rw [satisfies_dValueId_iff]
    exact rfl
  · rw [satisfies_dExclusionTerm_iff]
    intro xv rv a hrel
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
`DEntailsMt` never holds by condition-vacuity — the repaired clause 2
included. -/
theorem noExt_dCond (D : List RDF.WfIri) : RDF.DInterpCond D noExtInterp :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ h => h⟩

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

/-! ## Triple-term agreement, and the superseded top-level-only bundle

`dTtGraph` is the issue-602 witness: the only ill-typed literal sits
INSIDE a used triple term. Under the repaired semantics both layers
now answer TRUE on `dTtGraph ⊨ dNumG` — `dEntailsMt_tt_illtyped` is
the model theory's verdict (the pin this repair flipped: it FAILED
against the pre-repair semantics, whose `dEntailsMt_tt_gap` proved its
negation), and the `#guard` below pins the executable's.

The pre-repair clause 2 survives as `DInterpCondTopLevel`, to prove
the interior clause is NOT redundant: `ttSepInterp` meets the
top-level bundle while satisfying `dTtGraph`, so under the superseded
reading the `malformed-literal` inconsistency was underivable — the
disagreement `dEntailsMt_tt_gap` pinned, restated with the defect on
the side the WD anchor puts it. -/

def dTtGraph : RDF.Graph :=
  [⟨.iri dA, dP, .tripleTerm (.iri dA) dQ (.literal dBadLit)⟩]

/-- **The flipped pin** (W3C rdf12 `malformed-literal` shape): a used
triple term with an ill-typed interior literal makes the premise
D-inconsistent, so it entails everything — including `dNumG`. -/
theorem dEntailsMt_tt_illtyped : RDF.DEntailsMt dWitD dTtGraph dNumG :=
  RDF.dEntailsMt_illtyped_native dWitD (List.mem_singleton.mpr rfl)
    (by decide) dNumG

/-- The SUPERSEDED bundle: value identification plus top-level-only
exclusion (clause 2 reaches `iLit` directly and nothing else). This
was `DInterpCond` before the issue-602 repair. -/
def DInterpCondTopLevel (D : List RDF.WfIri) (i : RDF.Interp) : Prop :=
  (∀ l1 l2 : RDF.WfLiteral, RDF.literalValueEq D l1.val l2.val = true →
     i.iLit l1 = i.iLit l2) ∧
  (∀ l : RDF.WfLiteral, RDF.literalIllFormed D l.val = true →
     ∀ p x : i.idom, ¬ i.iext p x (i.iLit l))

/-- The repaired bundle refines the superseded one (the literal
instance of clause 2). -/
theorem dInterpCond_topLevel {D : List RDF.WfIri} {i : RDF.Interp}
    (h : RDF.DInterpCond D i) : DInterpCondTopLevel D i :=
  ⟨h.1, fun l hl p x =>
    h.2 (.literal l)
      (by simp [RDF.termIllTypedMention, RDF.Term.mentionedLiterals, hl])
      (fun _ => i.idomWit) p x⟩

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

theorem ttSep_topLevelCond : DInterpCondTopLevel dWitD ttSepInterp :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ h => Bool.false_ne_true h⟩

/-- `ttSepInterp` violates the repaired clause 2 at the witness triple
term — the inclusion `dInterpCond_topLevel` is strict. -/
theorem ttSep_not_dCond : ¬ RDF.DInterpCond dWitD ttSepInterp := by
  intro h
  exact h.2 (.tripleTerm (.iri dA) dQ (.literal dBadLit)) (by decide)
    (fun _ => true) true true rfl

/-- **The interior clause is not redundant**: under the superseded
top-level-only bundle, the `malformed-literal` inconsistency is
underivable — the content the removed `dEntailsMt_tt_gap` pinned,
now stated about the variant it was actually evidence against. -/
theorem topLevel_exclusion_insufficient_for_tt :
    ¬ RDF.EntailsUnder (DInterpCondTopLevel dWitD) dTtGraph dNumG := by
  intro h
  have hsat : RDF.Satisfies ttSepInterp dTtGraph := by
    refine ⟨fun _ => true, fun t ht => ?_⟩
    obtain rfl := List.mem_singleton.mp ht
    exact rfl
  obtain ⟨a, ha⟩ := h ttSepInterp ttSep_topLevelCond hsat
  have hbad := ha _ (List.mem_singleton.mpr rfl)
  exact Bool.false_ne_true hbad

/-! ## The W3C fixture shape, pinned

`malformed-literal` (rdf12 rdf-semantics): action
`:a1 :p1 <<( :a :b "c"^^xsd:integer )>>`, regime "RDF", recognised
`xsd:integer`, `mf:result false` — the action graph is D-inconsistent.
(The suite's `malformed-literal-control` is the TOP-LEVEL assertion of
the same literal, covered by the `dBadGraph` family above.) The third
`#guard` pins WD §7.1's last sentence instead: an unrecognised type
IRI is not ill-typed, so with `D = []` the same graph is
consistent. -/

def wdMalformedLit : RDF.WfLiteral :=
  ⟨{ lexicalForm := "c", datatype := RDF.xsdInteger,
     langTag := none, direction := none }, by decide⟩

def wdMalformedGraph : RDF.Graph :=
  [⟨.iri dA, dP, .tripleTerm (.iri dA) dQ (.literal wdMalformedLit)⟩]

theorem wdMalformed_dEntailsMt (h : RDF.Graph) :
    RDF.DEntailsMt [RDF.xsdInteger] wdMalformedGraph h :=
  RDF.dEntailsMt_illtyped_native _ (List.mem_singleton.mpr rfl)
    (by decide) h

/-! ## Build-time checks -/

section Checks

/- The witness data is what the theorems say it is. -/

#guard RDF.literalIllFormed dWitD dBadLit.val
#guard !RDF.literalIllFormed dWitD dOneLit.val
#guard RDF.literalValueEq dWitD dOneLit.val dOne2Lit.val
#guard !(RDF.simpleEntails dNumG dNumH)

/- Verdict agreement with the executable regime procedure: the
ill-typed premise entails everything, the value instance holds, the
empty graph entails nothing. -/

#guard RDF.regimeEntails .d dWitD dBadGraph dTargetGraph
#guard RDF.regimeEntails .d dWitD dNumG dNumH
#guard !(RDF.regimeEntails .d dWitD ([] : RDF.Graph) dTargetGraph)

/- AGREEMENT on the issue-602 witness (formerly pinned as a gap): the
executable short-circuits on the triple-term-interior ill-typed
literal, and `dEntailsMt_tt_illtyped` now proves the model theory
gives the same verdict. `regimeEntails_d_sound_mt` covers every such
pair at once. -/

#guard RDF.regimeEntails .d dWitD dTtGraph dNumG

/- The W3C `malformed-literal` shape: D-inconsistent under the
fixture's regime ("RDF") and recognised list; consistent when the
datatype is not recognised (`malformed-literal-control`). -/

#guard RDF.regimeInconsistent .rdf [RDF.xsdInteger] wdMalformedGraph
#guard RDF.regimeInconsistent .d [RDF.xsdInteger] wdMalformedGraph
#guard !(RDF.regimeInconsistent .rdf [] wdMalformedGraph)

/-! Axiom audit — expected at most `propext` / `Classical.choice` /
`Quot.sound` (Lean's own foundations). No `sorryAx`, nothing
user-declared. -/

#print axioms unified_adequate_d
#print axioms unified_adequate_d_decided_sound
#print axioms RDF.regimeEntails_d_sound_mt
#print axioms unified_d_illtyped_entails_all
#print axioms dEntailsMt_illtyped
#print axioms RDF.dEntailsMt_illtyped_native
#print axioms dValueSchema_alone_insufficient
#print axioms dSchema_exclusion_does_work
#print axioms dEntailsMt_value_instance
#print axioms dNum_not_simple
#print axioms dEntailsMt_tt_illtyped
#print axioms wdMalformed_dEntailsMt
#print axioms topLevel_exclusion_insufficient_for_tt
#print axioms ttSep_not_dCond

end Checks

end L4Factoidal.Unified
