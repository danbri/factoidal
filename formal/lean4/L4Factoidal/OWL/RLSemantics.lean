/-
L4Factoidal.OWL.RLSemantics — the model-theoretic truth layer for the
OWL 2 RL/RDF rule relation `OWL.RL.Derives`: one rule-shaped semantic
condition per rule-table row, and ONE induction proving that every
derivable triple is true in every interpretation meeting the bundle.

This is the layer `RLTheorems.lean`'s header names as NOT ported
("truth preservation (model theory) is not ported") — stage 4 of
https://github.com/danbri/factoidal/issues/598 supplies it, and
`Unified/OwlRlSchema.lean` / `Unified/OwlRlAdequacy.lean` lift it to
the unified LBase/IKL theory (design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §4.4).

## The condition style

`OWL/Semantics.lean` carries ~33 weakest-reading table conditions
(`Cond*`); they are NOT one per rule row, and several are stated over
every domain element where the corresponding `Derives` constructor
fixes an IRI. The conditions here (`RlCond*`) are authored per ROW, in
the same citation discipline, mirroring each constructor EXACTLY:

* a constructor parameter of type `WfIri` becomes a `∀ (p : WfIri)`
  over IRIs (the row family the unified schema indexes by `p`);
* a `Subject`/`Term` parameter becomes a `∀ (x : i.idom)` over the
  whole domain;
* a `LIST[...]` premise becomes either the reserved vocabulary below
  (`ListMember`-shaped rows) or a `SeqIs` premise
  (`ListDenotes`-shaped rows — `SeqIs` is OWL 2 RDF-Based Semantics
  §3's sequence condition, from `OWL/Semantics.lean`).

Each condition cites its OWL 2 RL/RDF table row id
(https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules,
Tables 4-9) or, for the `[ext]` rows, the `RLRules.lean` constructor it
mirrors (whose doc comment carries the OWL 2 RDF-Based Semantics
condition justifying it).

## Reserved vocabulary

Two auxiliary predicates in the unified layer's `urn:cl:def:`
operator namespace (`urn:cl:def:listMember`,
`urn:cl:def:typedAllMembers`) give the `ListMember`-shaped rows a
first-order Horn form: the RDF collection walk becomes two Horn
axioms per predicate instead of one sentence per list length. The
engine's comprehension rows reserve blank-node labels
(`__rl_comp__…`, `__rl_minc1__…` — `RLClosure`'s skolem functions).
Truth preservation therefore carries the hypothesis `RlReservedFree g`
— the input graph uses neither the reserved IRIs nor the reserved
labels. A graph violating it can make the engine CONFLATE a user
blank node with a comprehension witness, and soundness genuinely
fails there (the hypothesis is not defensive decoration).

## The two comprehension witnesses

`caxDwToComplement` / `clsMaxqc1ToComplement` / `minCard1Comprehension`
mint blank nodes. Truth preservation extends the premise assignment at
exactly the reserved labels, by choice, with the witnesses the
comprehension conditions provide (`compWitness`, `minc1Witness`) —
which is why `rl_derives_holds` concludes at `rlExtend i A`, not at
`A`, and why the conclusion of the unified soundness theorem is the
existential closure `rdfToTheory [t]`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RLTheorems
import L4Factoidal.OWL.Semantics

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## Reserved vocabulary and label decoding -/

/-- The list-membership helper predicate (reserved; see header). -/
def uListMem : WfIri := ⟨"urn:cl:def:listMember", by decide⟩

/-- The typed-in-every-member helper predicate (reserved). It holds of
`⟨y, l⟩` when `l` is a NON-EMPTY collection and `y` is `rdf:type`-d
into every member — non-empty so that the base case is premise-backed
(an unconditional base would assert facts about arbitrary
individuals, which the completeness model cannot honour). -/
def uTypedAll : WfIri := ⟨"urn:cl:def:typedAllMembers", by decide⟩

/-- Strip an expected prefix off a character list. -/
def stripPre : List Char → List Char → Option (List Char)
  | [], r => some r
  | p :: ps, c :: cs => if c = p then stripPre ps cs else none
  | _ :: _, [] => none

theorem stripPre_append (p r : List Char) : stripPre p (p ++ r) = some r := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [stripPre, ih]

/-- The reserved IRI namespace: the `urn:cl:def:` operator vocabulary. -/
def reservedIriPre : List Char := "urn:cl:def:".toList

/-- The comprehension-witness label prefixes of `RLClosure`
(`complementWitness`, `minCard1Witness`). -/
def compBnodePre : List Char := "__rl_comp__".toList
def minc1BnodePre : List Char := "__rl_minc1__".toList

def rlReservedIri (w : WfIri) : Bool :=
  (stripPre reservedIriPre w.val.toList).isSome

/-- Decode a comprehension-witness label back to its argument IRI. -/
def decodeComp (b : BNodeId) : Option WfIri :=
  match stripPre compBnodePre b.toList with
  | some r => if h : isIri (String.ofList r) then some ⟨_, h⟩ else none
  | none => none

def decodeMinc1 (b : BNodeId) : Option WfIri :=
  match stripPre minc1BnodePre b.toList with
  | some r => if h : isIri (String.ofList r) then some ⟨_, h⟩ else none
  | none => none

def rlReservedBnode (b : BNodeId) : Bool :=
  (stripPre compBnodePre b.toList).isSome ||
  (stripPre minc1BnodePre b.toList).isSome

theorem prefixed_toList (pre : String) (s : String) :
    (pre ++ s).toList = pre.toList ++ s.toList := by
  simp [String.toList_append]

theorem decodeComp_witness (c : WfIri) :
    decodeComp ("__rl_comp__" ++ c.val) = some c := by
  unfold decodeComp
  rw [prefixed_toList]
  show (match stripPre compBnodePre (compBnodePre ++ c.val.toList) with
        | some r => if h : isIri (String.ofList r) then some ⟨_, h⟩ else none
        | none => none) = some c
  rw [stripPre_append]
  simp only [String.ofList_toList]
  rw [dif_pos c.property]

theorem decodeMinc1_witness (p : WfIri) :
    decodeMinc1 ("__rl_minc1__" ++ p.val) = some p := by
  unfold decodeMinc1
  rw [prefixed_toList]
  show (match stripPre minc1BnodePre (minc1BnodePre ++ p.val.toList) with
        | some r => if h : isIri (String.ofList r) then some ⟨_, h⟩ else none
        | none => none) = some p
  rw [stripPre_append]
  simp only [String.ofList_toList]
  rw [dif_pos p.property]

/-- The two witness prefixes are incompatible: a `__rl_minc1__` label
never decodes as a complement witness (they differ at the sixth
character), so `rlExtend`'s first match arm cannot capture the second's
labels. -/
theorem decodeComp_minc1 (p : WfIri) :
    decodeComp ("__rl_minc1__" ++ p.val) = none := by
  unfold decodeComp
  rw [prefixed_toList]
  show (match stripPre compBnodePre (minc1BnodePre ++ p.val.toList) with
        | some r => if h : isIri (String.ofList r) then some ⟨_, h⟩ else none
        | none => none) = none
  rfl

theorem decode_of_not_reserved {b : BNodeId} (h : rlReservedBnode b = false) :
    decodeComp b = none ∧ decodeMinc1 b = none := by
  simp only [rlReservedBnode, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
             Option.isNone_iff_eq_none] at h
  constructor
  · unfold decodeComp; rw [h.1]
  · unfold decodeMinc1; rw [h.2]

/-! ## Reserved-freeness of a graph, and its preservation by `Derives`
(IRI positions) -/

def subjNonReserved : Subject → Bool
  | .iri i => !rlReservedIri i
  | .bnode b => !rlReservedBnode b

/-- No reserved IRI and no reserved blank-node label in any position.
A literal's datatype IRI is exempt: no rule row moves a datatype IRI
into a predicate or argument position. -/
def termNonReserved : Term → Bool
  | .iri i => !rlReservedIri i
  | .bnode b => !rlReservedBnode b
  | .literal _ => true
  | .tripleTerm s p o => subjNonReserved s && !rlReservedIri p && termNonReserved o

def tripleNonReserved (t : Triple) : Bool :=
  subjNonReserved t.s && !rlReservedIri t.p && termNonReserved t.o

/-- The soundness hypothesis: the input graph mentions no reserved IRI
and no reserved blank-node label (module header). Executable via
`rlReservedFreeCheck`. -/
def RlReservedFree (g : Graph) : Prop := ∀ t ∈ g, tripleNonReserved t = true

def rlReservedFreeCheck (g : Graph) : Bool := g.all tripleNonReserved

theorem rlReservedFree_of_check {g : Graph}
    (h : rlReservedFreeCheck g = true) : RlReservedFree g :=
  fun t ht => List.all_eq_true.mp h t ht

/-- IRI positions only — what `Derives` preserves (the minted witness
labels ARE reserved, so blank-node reservedness is deliberately not
claimed for derived triples). -/
def subjIrisNonReserved : Subject → Bool
  | .iri i => !rlReservedIri i
  | .bnode _ => true

def termIrisNonReserved : Term → Bool
  | .iri i => !rlReservedIri i
  | .bnode _ => true
  | .literal _ => true
  | .tripleTerm s p o =>
      subjIrisNonReserved s && !rlReservedIri p && termIrisNonReserved o

def tripleIrisNonReserved (t : Triple) : Bool :=
  subjIrisNonReserved t.s && !rlReservedIri t.p && termIrisNonReserved t.o

theorem subjIris_of_nonReserved {s : Subject}
    (h : subjNonReserved s = true) : subjIrisNonReserved s = true := by
  cases s with
  | iri i => exact h
  | bnode b => rfl

theorem termIris_of_nonReserved : ∀ {t : Term},
    termNonReserved t = true → termIrisNonReserved t = true
  | .iri _, h => h
  | .bnode _, _ => rfl
  | .literal _, _ => rfl
  | .tripleTerm s p o, h => by
      simp only [termNonReserved, Bool.and_eq_true] at h
      simp only [termIrisNonReserved, Bool.and_eq_true]
      exact ⟨⟨subjIris_of_nonReserved h.1.1, h.1.2⟩,
             termIris_of_nonReserved h.2⟩

theorem tripleIris_of_nonReserved {t : Triple}
    (h : tripleNonReserved t = true) : tripleIrisNonReserved t = true := by
  simp only [tripleNonReserved, Bool.and_eq_true] at h
  simp only [tripleIrisNonReserved, Bool.and_eq_true]
  exact ⟨⟨subjIris_of_nonReserved h.1.1, h.1.2⟩, termIris_of_nonReserved h.2⟩

theorem subjIris_toTerm (s : Subject) :
    termIrisNonReserved s.toTerm = subjIrisNonReserved s := by
  cases s <;> rfl

/-! ### Small constructors/destructors for the IRI invariant -/

theorem tin_mk {s : Subject} {p : WfIri} {o : Term}
    (hs : subjIrisNonReserved s = true) (hp : rlReservedIri p = false)
    (ho : termIrisNonReserved o = true) :
    tripleIrisNonReserved ⟨s, p, o⟩ = true := by
  simp [tripleIrisNonReserved, hs, hp, ho]

theorem tin_s {t : Triple} (h : tripleIrisNonReserved t = true) :
    subjIrisNonReserved t.s = true := by
  simp only [tripleIrisNonReserved, Bool.and_eq_true] at h
  exact h.1.1

theorem tin_p {t : Triple} (h : tripleIrisNonReserved t = true) :
    rlReservedIri t.p = false := by
  simp only [tripleIrisNonReserved, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

theorem tin_o {t : Triple} (h : tripleIrisNonReserved t = true) :
    termIrisNonReserved t.o = true := by
  simp only [tripleIrisNonReserved, Bool.and_eq_true] at h
  exact h.2

theorem sin_toTerm {s : Subject} (h : subjIrisNonReserved s = true) :
    termIrisNonReserved s.toTerm = true := (subjIris_toTerm s) ▸ h

theorem sin_of_toTerm {s : Subject} (h : termIrisNonReserved s.toTerm = true) :
    subjIrisNonReserved s = true := (subjIris_toTerm s) ▸ h

theorem irw_of_termIri {w : WfIri} (h : termIrisNonReserved (.iri w) = true) :
    rlReservedIri w = false := by
  simpa [termIrisNonReserved] using h

theorem irw_of_subjIri {w : WfIri} (h : subjIrisNonReserved (.iri w) = true) :
    rlReservedIri w = false := by
  simpa [subjIrisNonReserved] using h

theorem sin_iri {w : WfIri} (h : rlReservedIri w = false) :
    subjIrisNonReserved (.iri w) = true := by
  simp [subjIrisNonReserved, h]

theorem oin_iri {w : WfIri} (h : rlReservedIri w = false) :
    termIrisNonReserved (.iri w) = true := by
  simp [termIrisNonReserved, h]

/-! ### The invariant flows through the collection relations -/

theorem listMember_termIris {gc : Graph}
    (hgc : ∀ u ∈ gc, tripleIrisNonReserved u = true) {lst e : Term}
    (h : ListMember gc lst e) : termIrisNonReserved e = true := by
  induction h with
  | here hf => exact tin_o (hgc _ hf)
  | there _ _ ih => exact ih

theorem chainHolds_start_subjIris {gc : Graph}
    (hgc : ∀ u ∈ gc, tripleIrisNonReserved u = true) {s : Subject}
    {ps : List WfIri} {fin : Term} (hne : ps ≠ [])
    (h : ChainHolds gc s ps fin) : subjIrisNonReserved s = true := by
  cases h with
  | nil => exact absurd rfl hne
  | last hm => exact tin_s (hgc _ hm)
  | step hm _ => exact tin_s (hgc _ hm)

theorem chainHolds_fin_termIris {gc : Graph}
    (hgc : ∀ u ∈ gc, tripleIrisNonReserved u = true) {s : Subject}
    {ps : List WfIri} {fin : Term}
    (h : ChainHolds gc s ps fin) : ps ≠ [] → termIrisNonReserved fin = true := by
  induction h with
  | nil => intro hne; exact absurd rfl hne
  | last hm => intro _; exact tin_o (hgc _ hm)
  | step hm hr ih =>
      intro _
      cases hr with
      | nil => exact tin_o (hgc _ hm)
      | last hm2 => exact tin_o (hgc _ hm2)
      | step hm2 hr2 => exact ih (by simp)

theorem typesAll_subjIris {gc : Graph}
    (hgc : ∀ u ∈ gc, tripleIrisNonReserved u = true) {y : Subject}
    {cs : List Term} (h : TypesAll gc y cs) (hne : cs ≠ []) :
    subjIrisNonReserved y = true := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hm _ => exact tin_s (hgc _ hm)

theorem iriIndividuals_nonres {gc : Graph}
    (hgc : ∀ u ∈ gc, tripleIrisNonReserved u = true) {i : WfIri}
    (h : i ∈ iriIndividuals gc) : rlReservedIri i = false := by
  simp only [iriIndividuals, List.mem_flatMap] at h
  obtain ⟨u, hu, hi⟩ := h
  rcases List.mem_append.mp hi with hs | ho
  · have := tin_s (hgc _ hu)
    cases hus : u.s with
    | iri w =>
        rw [hus] at hs this
        simp only [List.mem_singleton] at hs
        subst hs
        exact irw_of_subjIri this
    | bnode b => rw [hus] at hs; simp at hs
  · have := tin_o (hgc _ hu)
    cases huo : u.o with
    | iri w =>
        rw [huo] at ho this
        simp only [List.mem_singleton] at ho
        subst ho
        exact irw_of_termIri this
    | bnode b => rw [huo] at ho; simp at ho
    | literal l => rw [huo] at ho; simp at ho
    | tripleTerm s p o => rw [huo] at ho; simp at ho

/-! ### Table conclusions are non-reserved (concrete tables) -/

theorem xsdAxiomTriples_nonres :
    ∀ t ∈ xsdAxiomTriples, tripleIrisNonReserved t = true := by decide

theorem builtinDatatypeAxioms_nonres :
    ∀ t ∈ builtinDatatypeAxioms, tripleIrisNonReserved t = true := by decide

theorem premiseFreeAxioms_nonres :
    ∀ t ∈ premiseFreeAxioms, tripleIrisNonReserved t = true := by decide

theorem rangeIntersect_nonres {d1 d2 d3 : WfIri}
    (h : rangeIntersectLicenses d1 d2 d3 = true) :
    rlReservedIri d3 = false := by
  simp only [rangeIntersectLicenses, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨e, he, -, hd3⟩ := h
  have hmem : d3 ∈ e.2.2 := by
    simpa [List.contains_iff_mem] using hd3
  simp only [xsdRangeIntersections, List.mem_cons, List.not_mem_nil,
             or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  · subst hmem; decide
  · subst hmem; decide
  · subst hmem; decide
  · rcases hmem with rfl | rfl <;> decide

/-- **`Derives` preserves the IRI invariant**: from a reserved-free
graph, every derivable triple mentions only non-reserved IRIs (its
blank nodes may be minted witnesses — that is the point of the
weakened statement). Feeds the `eq-ref` predicate-conclusion row,
whose schema family is restricted to non-reserved predicates. -/
theorem derives_irisNonReserved {g : Graph} (hg : RlReservedFree g)
    {t : Triple} (h : Derives g t) : tripleIrisNonReserved t = true := by
  induction h with
  | base hm => exact tripleIris_of_nonReserved (hg _ hm)
  | eqRefS _ ih => exact tin_mk (tin_s ih) (by decide) (sin_toTerm (tin_s ih))
  | eqRefP _ ih =>
      exact tin_mk (sin_iri (tin_p ih)) (by decide) (oin_iri (tin_p ih))
  | eqRefO _ ih =>
      exact tin_mk (sin_of_toTerm (tin_o ih)) (by decide) (tin_o ih)
  | eqSym _ ih =>
      exact tin_mk (sin_of_toTerm (tin_o ih)) (by decide) (sin_toTerm (tin_s ih))
  | eqTrans _ _ ih1 ih2 => exact tin_mk (tin_s ih1) (by decide) (tin_o ih2)
  | eqRepS _ _ ih1 ih2 =>
      exact tin_mk (sin_of_toTerm (tin_o ih1)) (tin_p ih2) (tin_o ih2)
  | eqRepP _ _ ih1 ih2 =>
      exact tin_mk (tin_s ih2) (irw_of_termIri (tin_o ih1)) (tin_o ih2)
  | eqRepO _ _ ih1 ih2 => exact tin_mk (tin_s ih2) (tin_p ih2) (tin_o ih1)
  | prpDom _ _ ih1 ih2 => exact tin_mk (tin_s ih2) (by decide) (tin_o ih1)
  | prpRng _ _ ih1 ih2 =>
      exact tin_mk (sin_of_toTerm (tin_o ih2)) (by decide) (tin_o ih1)
  | prpFp _ _ _ ih1 ih2 ih3 =>
      exact tin_mk (sin_of_toTerm (tin_o ih2)) (by decide) (tin_o ih3)
  | prpIfp _ _ _ ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih2) (by decide) (sin_toTerm (tin_s ih3))
  | prpSymp _ _ ih1 ih2 =>
      exact tin_mk (sin_of_toTerm (tin_o ih2)) (tin_p ih2) (sin_toTerm (tin_s ih2))
  | prpTrp _ _ _ ih1 ih2 ih3 => exact tin_mk (tin_s ih2) (tin_p ih2) (tin_o ih3)
  | prpSpo1 _ _ ih1 ih2 =>
      exact tin_mk (tin_s ih2) (irw_of_termIri (tin_o ih1)) (tin_o ih2)
  | prpSpo2 _ _ hl hne hc ihgc ih =>
      exact tin_mk (chainHolds_start_subjIris ihgc hne hc)
        (irw_of_subjIri (tin_s ih)) (chainHolds_fin_termIris ihgc hc hne)
  | prpEqp1 _ _ ih1 ih2 =>
      exact tin_mk (tin_s ih2) (irw_of_termIri (tin_o ih1)) (tin_o ih2)
  | prpEqp2 _ _ ih1 ih2 =>
      exact tin_mk (tin_s ih2) (irw_of_subjIri (tin_s ih1)) (tin_o ih2)
  | prpInv1 _ _ ih1 ih2 =>
      exact tin_mk (sin_of_toTerm (tin_o ih2)) (irw_of_termIri (tin_o ih1))
        (sin_toTerm (tin_s ih2))
  | prpInv2 _ _ ih1 ih2 =>
      exact tin_mk (sin_of_toTerm (tin_o ih2)) (irw_of_subjIri (tin_s ih1))
        (sin_toTerm (tin_s ih2))
  | prpKey _ _ hl hne _ _ hs ihgc ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih2) (by decide) (sin_toTerm (tin_s ih3))
  | clsThing => decide
  | clsNothing1 => decide
  | clsInt1 _ _ hl hne ht ihgc ih =>
      exact tin_mk (typesAll_subjIris ihgc ht hne) (by decide)
        (sin_toTerm (tin_s ih))
  | clsInt2 _ _ hm _ ihgc ih1 ih2 =>
      exact tin_mk (tin_s ih2) (by decide) (listMember_termIris ihgc hm)
  | clsUni _ _ hm _ ihgc ih1 ih2 =>
      exact tin_mk (tin_s ih2) (by decide) (sin_toTerm (tin_s ih1))
  | clsSvf1 _ _ _ _ ih1 ih2 ih3 ih4 =>
      exact tin_mk (tin_s ih3) (by decide) (sin_toTerm (tin_s ih1))
  | clsSvf2 _ _ _ ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih3) (by decide) (sin_toTerm (tin_s ih1))
  | clsAvf _ _ _ _ ih1 ih2 ih3 ih4 =>
      exact tin_mk (sin_of_toTerm (tin_o ih4)) (by decide) (tin_o ih1)
  | clsHv1 _ _ _ ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih3) (irw_of_termIri (tin_o ih2)) (tin_o ih1)
  | clsHv2 _ _ _ ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih3) (by decide) (sin_toTerm (tin_s ih1))
  | clsHs1 _ _ _ ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih3) (irw_of_termIri (tin_o ih2))
        (sin_toTerm (tin_s ih3))
  | clsHs2 _ _ _ ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih3) (by decide) (sin_toTerm (tin_s ih1))
  | clsMaxc2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact tin_mk (sin_of_toTerm (tin_o ih4)) (by decide) (tin_o ih5)
  | clsOo _ _ hm ihgc ih =>
      exact tin_mk (sin_of_toTerm (listMember_termIris ihgc hm)) (by decide)
        (sin_toTerm (tin_s ih))
  | caxSco _ _ ih1 ih2 => exact tin_mk (tin_s ih2) (by decide) (tin_o ih1)
  | caxEqc1 _ _ ih1 ih2 => exact tin_mk (tin_s ih2) (by decide) (tin_o ih1)
  | caxEqc2 _ _ ih1 ih2 =>
      exact tin_mk (tin_s ih2) (by decide) (sin_toTerm (tin_s ih1))
  | scmClsSelf _ ih => exact tin_mk (tin_s ih) (by decide) (sin_toTerm (tin_s ih))
  | scmClsEqc _ ih => exact tin_mk (tin_s ih) (by decide) (sin_toTerm (tin_s ih))
  | scmClsThing _ ih => exact tin_mk (tin_s ih) (by decide) (by decide)
  | scmClsNothing _ ih => exact tin_mk (by decide) (by decide) (sin_toTerm (tin_s ih))
  | scmSco _ _ ih1 ih2 => exact tin_mk (tin_s ih1) (by decide) (tin_o ih2)
  | scmEqc1a _ ih => exact tin_mk (tin_s ih) (by decide) (tin_o ih)
  | scmEqc1b _ ih =>
      exact tin_mk (sin_of_toTerm (tin_o ih)) (by decide) (sin_toTerm (tin_s ih))
  | scmEqc2 _ _ ih1 ih2 => exact tin_mk (tin_s ih1) (by decide) (tin_o ih1)
  | scmSpo _ _ ih1 ih2 => exact tin_mk (tin_s ih1) (by decide) (tin_o ih2)
  | scmEqp1a _ ih => exact tin_mk (tin_s ih) (by decide) (tin_o ih)
  | scmEqp1b _ ih =>
      exact tin_mk (sin_of_toTerm (tin_o ih)) (by decide) (sin_toTerm (tin_s ih))
  | scmEqp2 _ _ ih1 ih2 => exact tin_mk (tin_s ih1) (by decide) (tin_o ih1)
  | scmDom1 _ _ ih1 ih2 => exact tin_mk (tin_s ih1) (by decide) (tin_o ih2)
  | scmDom2 _ _ ih1 ih2 => exact tin_mk (tin_s ih2) (by decide) (tin_o ih1)
  | scmRng1 _ _ ih1 ih2 => exact tin_mk (tin_s ih1) (by decide) (tin_o ih2)
  | scmRng2 _ _ ih1 ih2 => exact tin_mk (tin_s ih2) (by decide) (tin_o ih1)
  | scmOpSub _ ih => exact tin_mk (tin_s ih) (by decide) (sin_toTerm (tin_s ih))
  | scmOpEqp _ ih => exact tin_mk (tin_s ih) (by decide) (sin_toTerm (tin_s ih))
  | scmDpSub _ ih => exact tin_mk (tin_s ih) (by decide) (sin_toTerm (tin_s ih))
  | scmDpEqp _ ih => exact tin_mk (tin_s ih) (by decide) (sin_toTerm (tin_s ih))
  | scmSvf1 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact tin_mk (tin_s ih1) (by decide) (sin_toTerm (tin_s ih3))
  | scmSvf2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact tin_mk (tin_s ih1) (by decide) (sin_toTerm (tin_s ih3))
  | scmAvf1 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact tin_mk (tin_s ih1) (by decide) (sin_toTerm (tin_s ih3))
  | scmAvf2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact tin_mk (tin_s ih3) (by decide) (sin_toTerm (tin_s ih1))
  | scmHv _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact tin_mk (tin_s ih1) (by decide) (sin_toTerm (tin_s ih3))
  | scmInt _ _ hm ihgc ih =>
      exact tin_mk (tin_s ih) (by decide) (listMember_termIris ihgc hm)
  | scmUni _ _ hm ihgc ih =>
      exact tin_mk (sin_of_toTerm (listMember_termIris ihgc hm)) (by decide)
        (sin_toTerm (tin_s ih))
  | eqDiffSym _ ih =>
      exact tin_mk (sin_of_toTerm (tin_o ih)) (by decide) (sin_toTerm (tin_s ih))
  | pdwToDiff _ _ _ hne ih1 ih2 ih3 =>
      exact tin_mk (sin_of_toTerm (tin_o ih2)) (by decide) (tin_o ih3)
  | caxDwToDiff _ _ _ hne ih1 ih2 ih3 =>
      exact tin_mk (tin_s ih2) (by decide) (sin_toTerm (tin_s ih3))
  | fpDiffToDiff _ _ _ _ hne ih1 ih2 ih3 ih4 =>
      exact tin_mk (tin_s ih2) (by decide) (sin_toTerm (tin_s ih3))
  | ifpDiffToDiff _ _ _ _ hne ih1 ih2 ih3 ih4 =>
      exact tin_mk (sin_of_toTerm (tin_o ih2)) (by decide) (tin_o ih3)
  | chainToTrans _ _ hl ihgc ih =>
      exact tin_mk (tin_s ih) (by decide) (by decide)
  | prpRfl _ _ hind ihgc ih =>
      exact tin_mk (sin_iri (iriIndividuals_nonres ihgc hind))
        (irw_of_subjIri (tin_s ih)) (oin_iri (iriIndividuals_nonres ihgc hind))
  | xsdAxioms _ hx hax ih => exact xsdAxiomTriples_nonres _ hax
  | dtRangeIntersect _ _ hlic ih1 ih2 =>
      exact tin_mk (tin_s ih1) (by decide) (oin_iri (rangeIntersect_nonres hlic))
  | premiseFreeAxiom hax => exact premiseFreeAxioms_nonres _ hax
  | caxDwToComplement _ hax ih =>
      simp only [complementWitnessTriples, complementWitnessPair,
                 List.mem_append, List.mem_cons, List.not_mem_nil,
                 or_false] at hax
      rcases hax with ((rfl | rfl | h') | (rfl | rfl | h')) | (rfl | rfl | h') <;>
        first
        | exact tin_mk rfl (by decide) (by decide)
        | exact tin_mk rfl (by decide) (tin_o ih)
        | exact tin_mk rfl (by decide) (sin_toTerm (tin_s ih))
        | exact tin_mk (tin_s ih) (by decide) rfl
        | exact tin_mk (sin_of_toTerm (tin_o ih)) (by decide) rfl
        | simp at h'
  | clsMaxqc1ToComplement _ _ _ _ _ _ _ _ hax ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 =>
      simp only [complementTypeTriples, complementWitnessPair,
                 List.mem_append, List.mem_cons, List.not_mem_nil,
                 or_false] at hax
      rcases hax with (rfl | rfl | h') | (rfl | h') <;>
        first
        | exact tin_mk rfl (by decide) (by decide)
        | exact tin_mk rfl (by decide) (tin_o ih3)
        | exact tin_mk (sin_of_toTerm (tin_o ih6)) (by decide) rfl
        | simp at h'
  | minCard1Comprehension _ hax ih =>
      simp only [minCard1WitnessTriples, List.mem_cons, List.not_mem_nil,
                 or_false] at hax
      rcases hax with rfl | rfl | rfl | rfl | h' <;>
        first
        | exact tin_mk rfl (by decide) (by decide)
        | exact tin_mk rfl (by decide) (sin_toTerm (tin_s ih))
        | exact tin_mk rfl (by decide) rfl
        | simp at h'
  | caxAdcToDw _ _ _ h1 h2 hne ihgc ih1 ih2 =>
      exact tin_mk
        (sin_iri (irw_of_termIri (listMember_termIris ihgc h1))) (by decide)
        (listMember_termIris ihgc h2)
  | invFlipDomRng _ _ ih1 ih2 =>
      exact tin_mk (sin_iri (irw_of_termIri (tin_o ih1))) (by decide)
        (tin_o ih2)
  | invFlipRngDom _ _ ih1 ih2 =>
      exact tin_mk (sin_iri (irw_of_termIri (tin_o ih1))) (by decide) (tin_o ih2)
  | invFlipDomRngRev _ _ ih1 ih2 =>
      exact tin_mk (tin_s ih1) (by decide) (tin_o ih2)
  | invFlipRngDomRev _ _ ih1 ih2 =>
      exact tin_mk (tin_s ih1) (by decide) (tin_o ih2)
  | invFpIfp _ _ ih1 _ =>
      exact tin_mk (sin_iri (irw_of_termIri (tin_o ih1))) (by decide) (by decide)
  | invIfpFp _ _ ih1 _ =>
      exact tin_mk (sin_iri (irw_of_termIri (tin_o ih1))) (by decide) (by decide)
  | invFpIfpRev _ _ ih1 _ =>
      exact tin_mk (tin_s ih1) (by decide) (by decide)
  | invIfpFpRev _ _ ih1 _ =>
      exact tin_mk (tin_s ih1) (by decide) (by decide)

/-! ## Semantic chain relations for the `ListDenotes`-shaped rows

`SeqIs` (OWL 2 RDF-Based Semantics §3, `OWL/Semantics.lean`) reads a
collection; these two read the DATA premises prp-spo2 and prp-key
batch over a property sequence. -/

/-- prp-spo2's chain of data steps along a property sequence: the
semantic counterpart of `ChainHolds`. -/
def SemChain (i : Interp) : i.idom → List i.idom → i.idom → Prop
  | u, [], w => u = w
  | u, q :: qs, w => ∃ v : i.idom, i.iext q u v ∧ SemChain i v qs w

/-- prp-key's shared values along a property sequence: the semantic
counterpart of `SharesKeyValues` (and the premise shape of
`OWL/Semantics.lean`'s `CondHasKey`). -/
def SemShares (i : Interp) (x y : i.idom) (qs : List i.idom) : Prop :=
  ∀ q ∈ qs, ∃ v : i.idom, i.iext q x v ∧ i.iext q y v

/-! ## The rule-shaped conditions, one per `Derives` row

Row ids are the OWL 2 RL/RDF table ids
(https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules);
`[ext]` rows cite their `RLRules.lean` constructor. Every condition
mirrors its constructor exactly (module header). -/

section Conditions

variable (i : Interp)

/-- **eq-ref**, subject conclusion. -/
def RlCondEqRefS : Prop :=
  ∀ (p : WfIri) (x y : i.idom), i.iext (i.iIri p) x y →
    i.iext (i.iIri owlSameAs) x x

/-- **eq-ref**, predicate conclusion. RESTRICTED to non-reserved
predicates: the unified completeness model realises the reserved
helper predicates by list-walk semantics, and their extensions carry
no self-`owl:sameAs` fact to conclude. `derives_irisNonReserved`
discharges the guard in the soundness induction. -/
def RlCondEqRefP : Prop :=
  ∀ (p : WfIri), rlReservedIri p = false → ∀ (x y : i.idom),
    i.iext (i.iIri p) x y →
    i.iext (i.iIri owlSameAs) (i.iIri p) (i.iIri p)

/-- **eq-ref**, object conclusion. -/
def RlCondEqRefO : Prop :=
  ∀ (p : WfIri) (x y : i.idom), i.iext (i.iIri p) x y →
    i.iext (i.iIri owlSameAs) y y

/-- **eq-sym**. -/
def RlCondEqSym : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlSameAs) x y →
    i.iext (i.iIri owlSameAs) y x

/-- **eq-trans**. -/
def RlCondEqTrans : Prop :=
  ∀ x y z : i.idom, i.iext (i.iIri owlSameAs) x y →
    i.iext (i.iIri owlSameAs) y z → i.iext (i.iIri owlSameAs) x z

/-- **eq-rep-s**. -/
def RlCondEqRepS : Prop :=
  ∀ (p : WfIri) (s s' o : i.idom), i.iext (i.iIri owlSameAs) s s' →
    i.iext (i.iIri p) s o → i.iext (i.iIri p) s' o

/-- **eq-rep-p**. -/
def RlCondEqRepP : Prop :=
  ∀ (p p' : WfIri) (x y : i.idom),
    i.iext (i.iIri owlSameAs) (i.iIri p) (i.iIri p') →
    i.iext (i.iIri p) x y → i.iext (i.iIri p') x y

/-- **eq-rep-o**. -/
def RlCondEqRepO : Prop :=
  ∀ (p : WfIri) (s o o' : i.idom), i.iext (i.iIri owlSameAs) o o' →
    i.iext (i.iIri p) s o → i.iext (i.iIri p) s o'

/-- **prp-dom** — the `WfIri`-instance family of
`OWL/Semantics.lean`'s `CondDomain`. -/
def RlCondPrpDom : Prop :=
  ∀ (p : WfIri) (c x y : i.idom), i.iext (i.iIri rdfsDomain) (i.iIri p) c →
    i.iext (i.iIri p) x y → icext i x c

/-- **prp-rng** — the `WfIri`-instance family of `CondRange`. -/
def RlCondPrpRng : Prop :=
  ∀ (p : WfIri) (c x y : i.idom), i.iext (i.iIri rdfsRange) (i.iIri p) c →
    i.iext (i.iIri p) x y → icext i y c

/-- **prp-fp**. Unlike `CondFunctional` (which concludes an identity),
the row concludes an `owl:sameAs` fact — the shape the schema states. -/
def RlCondPrpFp : Prop :=
  ∀ (p : WfIri) (x y1 y2 : i.idom),
    icext i (i.iIri p) (i.iIri owlFunctionalProperty) →
    i.iext (i.iIri p) x y1 → i.iext (i.iIri p) x y2 →
    i.iext (i.iIri owlSameAs) y1 y2

/-- **prp-ifp**. -/
def RlCondPrpIfp : Prop :=
  ∀ (p : WfIri) (x1 x2 y : i.idom),
    icext i (i.iIri p) (i.iIri owlInverseFunctionalProperty) →
    i.iext (i.iIri p) x1 y → i.iext (i.iIri p) x2 y →
    i.iext (i.iIri owlSameAs) x1 x2

/-- **prp-symp** — the `WfIri`-instance family of `CondSymmetric`. -/
def RlCondPrpSymp : Prop :=
  ∀ (p : WfIri) (x y : i.idom),
    icext i (i.iIri p) (i.iIri owlSymmetricProperty) →
    i.iext (i.iIri p) x y → i.iext (i.iIri p) y x

/-- **prp-trp** — the `WfIri`-instance family of `CondTransitive`. -/
def RlCondPrpTrp : Prop :=
  ∀ (p : WfIri) (x y z : i.idom),
    icext i (i.iIri p) (i.iIri owlTransitiveProperty) →
    i.iext (i.iIri p) x y → i.iext (i.iIri p) y z → i.iext (i.iIri p) x z

/-- **prp-spo1**. -/
def RlCondPrpSpo1 : Prop :=
  ∀ (p1 p2 : WfIri) (x y : i.idom),
    i.iext (i.iIri rdfsSubPropertyOf) (i.iIri p1) (i.iIri p2) →
    i.iext (i.iIri p1) x y → i.iext (i.iIri p2) x y

/-- **prp-spo2** — chain premise as `SeqIs` + `SemChain`. -/
def RlCondPrpSpo2 : Prop :=
  ∀ (p : WfIri) (l u w : i.idom) (qs : List i.idom), qs ≠ [] →
    i.iext (i.iIri owlPropertyChainAxiom) (i.iIri p) l →
    SeqIs i l qs → SemChain i u qs w → i.iext (i.iIri p) u w

/-- **prp-eqp1**. -/
def RlCondPrpEqp1 : Prop :=
  ∀ (p1 p2 : WfIri) (x y : i.idom),
    i.iext (i.iIri owlEquivalentProperty) (i.iIri p1) (i.iIri p2) →
    i.iext (i.iIri p1) x y → i.iext (i.iIri p2) x y

/-- **prp-eqp2**. -/
def RlCondPrpEqp2 : Prop :=
  ∀ (p1 p2 : WfIri) (x y : i.idom),
    i.iext (i.iIri owlEquivalentProperty) (i.iIri p1) (i.iIri p2) →
    i.iext (i.iIri p2) x y → i.iext (i.iIri p1) x y

/-- **prp-inv1**. -/
def RlCondPrpInv1 : Prop :=
  ∀ (p1 p2 : WfIri) (x y : i.idom),
    i.iext (i.iIri owlInverseOf) (i.iIri p1) (i.iIri p2) →
    i.iext (i.iIri p1) x y → i.iext (i.iIri p2) y x

/-- **prp-inv2**. -/
def RlCondPrpInv2 : Prop :=
  ∀ (p1 p2 : WfIri) (x y : i.idom),
    i.iext (i.iIri owlInverseOf) (i.iIri p1) (i.iIri p2) →
    i.iext (i.iIri p2) x y → i.iext (i.iIri p1) y x

/-- **prp-key** — list premise as `SeqIs`, shared values as
`SemShares` (the premise shape of `CondHasKey`). -/
def RlCondPrpKey : Prop :=
  ∀ (c l x y : i.idom) (qs : List i.idom), qs ≠ [] →
    i.iext (i.iIri owlHasKey) c l → SeqIs i l qs →
    icext i x c → icext i y c → SemShares i x y qs →
    i.iext (i.iIri owlSameAs) x y

/-- **cls-thing**. -/
def RlCondClsThing : Prop := icext i (i.iIri owlThing) (i.iIri owlClass)

/-- **cls-nothing1**. -/
def RlCondClsNothing1 : Prop := icext i (i.iIri owlNothing) (i.iIri owlClass)

/-- **cls-int1**, through the reserved `uTypedAll` helper (which is
non-empty-list-valued by construction, matching the row's `cs ≠ []`
side condition). -/
def RlCondClsInt1 : Prop :=
  ∀ c y l : i.idom, i.iext (i.iIri owlIntersectionOf) c l →
    i.iext (i.iIri uTypedAll) y l → icext i y c

/-- The `uTypedAll` base axiom: a one-member collection all of whose
members type `y`. -/
def RlCondTypedAllBase : Prop :=
  ∀ y l e : i.idom, i.iext (i.iIri rdfFirst) l e →
    i.iext (i.iIri rdfRest) l (i.iIri rdfNil) → icext i y e →
    i.iext (i.iIri uTypedAll) y l

/-- The `uTypedAll` step axiom. -/
def RlCondTypedAllStep : Prop :=
  ∀ y l l' e : i.idom, i.iext (i.iIri rdfFirst) l e →
    i.iext (i.iIri rdfRest) l l' → icext i y e →
    i.iext (i.iIri uTypedAll) y l' → i.iext (i.iIri uTypedAll) y l

/-- The `uListMem` base axiom: the head cell's `rdf:first` value is a
member. -/
def RlCondListMemBase : Prop :=
  ∀ l e : i.idom, i.iext (i.iIri rdfFirst) l e →
    i.iext (i.iIri uListMem) l e

/-- The `uListMem` step axiom: anything the tail holds, the head
holds. -/
def RlCondListMemStep : Prop :=
  ∀ l l' e : i.idom, i.iext (i.iIri rdfRest) l l' →
    i.iext (i.iIri uListMem) l' e → i.iext (i.iIri uListMem) l e

/-- **cls-int2**, through `uListMem`. -/
def RlCondClsInt2 : Prop :=
  ∀ c y l ci : i.idom, i.iext (i.iIri owlIntersectionOf) c l →
    i.iext (i.iIri uListMem) l ci → icext i y c → icext i y ci

/-- **cls-uni**, through `uListMem`. -/
def RlCondClsUni : Prop :=
  ∀ c y l ci : i.idom, i.iext (i.iIri owlUnionOf) c l →
    i.iext (i.iIri uListMem) l ci → icext i y ci → icext i y c

/-- **cls-svf1**. -/
def RlCondClsSvf1 : Prop :=
  ∀ (p : WfIri) (x u v yc : i.idom),
    i.iext (i.iIri owlSomeValuesFrom) x yc →
    i.iext (i.iIri owlOnProperty) x (i.iIri p) →
    i.iext (i.iIri p) u v → icext i v yc → icext i u x

/-- **cls-svf2**. -/
def RlCondClsSvf2 : Prop :=
  ∀ (p : WfIri) (x u v : i.idom),
    i.iext (i.iIri owlSomeValuesFrom) x (i.iIri owlThing) →
    i.iext (i.iIri owlOnProperty) x (i.iIri p) →
    i.iext (i.iIri p) u v → icext i u x

/-- **cls-avf**. -/
def RlCondClsAvf : Prop :=
  ∀ (p : WfIri) (x u v yc : i.idom),
    i.iext (i.iIri owlAllValuesFrom) x yc →
    i.iext (i.iIri owlOnProperty) x (i.iIri p) →
    icext i u x → i.iext (i.iIri p) u v → icext i v yc

/-- **cls-hv1**. -/
def RlCondClsHv1 : Prop :=
  ∀ (p : WfIri) (x u yv : i.idom), i.iext (i.iIri owlHasValue) x yv →
    i.iext (i.iIri owlOnProperty) x (i.iIri p) → icext i u x →
    i.iext (i.iIri p) u yv

/-- **cls-hv2**. -/
def RlCondClsHv2 : Prop :=
  ∀ (p : WfIri) (x u yv : i.idom), i.iext (i.iIri owlHasValue) x yv →
    i.iext (i.iIri owlOnProperty) x (i.iIri p) →
    i.iext (i.iIri p) u yv → icext i u x

/-- **cls-hs1** — the `owl:hasSelf` object denotes through `iLit`,
matched lexically exactly as the engine matches it. -/
def RlCondClsHs1 : Prop :=
  ∀ (p : WfIri) (c u : i.idom),
    i.iext (i.iIri owlHasSelf) c (i.iLit litTrueBoolean) →
    i.iext (i.iIri owlOnProperty) c (i.iIri p) → icext i u c →
    i.iext (i.iIri p) u u

/-- **cls-hs2**. -/
def RlCondClsHs2 : Prop :=
  ∀ (p : WfIri) (c u : i.idom),
    i.iext (i.iIri owlHasSelf) c (i.iLit litTrueBoolean) →
    i.iext (i.iIri owlOnProperty) c (i.iIri p) →
    i.iext (i.iIri p) u u → icext i u c

/-- **cls-maxc2** — the cardinality literal denotes through `iLit`,
matched lexically exactly as the engine matches it. -/
def RlCondClsMaxc2 : Prop :=
  ∀ (p : WfIri) (x u y1 y2 : i.idom),
    i.iext (i.iIri owlMaxCardinality) x (i.iLit litNni1) →
    i.iext (i.iIri owlOnProperty) x (i.iIri p) → icext i u x →
    i.iext (i.iIri p) u y1 → i.iext (i.iIri p) u y2 →
    i.iext (i.iIri owlSameAs) y1 y2

/-- **cls-oo**, through `uListMem`. -/
def RlCondClsOo : Prop :=
  ∀ c l yi : i.idom, i.iext (i.iIri owlOneOf) c l →
    i.iext (i.iIri uListMem) l yi → icext i yi c

/-- **cax-sco** — the domain-quantified form is
`RDF.CondSubClassOf`; this is the same shape (no `WfIri`
parameters occur in the constructor). -/
def RlCondCaxSco : Prop :=
  ∀ c1 c2 x : i.idom, i.iext (i.iIri rdfsSubClassOf) c1 c2 →
    icext i x c1 → icext i x c2

/-- **cax-eqc1**. -/
def RlCondCaxEqc1 : Prop :=
  ∀ c1 c2 x : i.idom, i.iext (i.iIri owlEquivalentClass) c1 c2 →
    icext i x c1 → icext i x c2

/-- **cax-eqc2**. -/
def RlCondCaxEqc2 : Prop :=
  ∀ c1 c2 x : i.idom, i.iext (i.iIri owlEquivalentClass) c1 c2 →
    icext i x c2 → icext i x c1

/-- **scm-cls**, conclusions 1-4. -/
def RlCondScmClsSelf : Prop :=
  ∀ c : i.idom, icext i c (i.iIri owlClass) →
    i.iext (i.iIri rdfsSubClassOf) c c

def RlCondScmClsEqc : Prop :=
  ∀ c : i.idom, icext i c (i.iIri owlClass) →
    i.iext (i.iIri owlEquivalentClass) c c

def RlCondScmClsThing : Prop :=
  ∀ c : i.idom, icext i c (i.iIri owlClass) →
    i.iext (i.iIri rdfsSubClassOf) c (i.iIri owlThing)

def RlCondScmClsNothing : Prop :=
  ∀ c : i.idom, icext i c (i.iIri owlClass) →
    i.iext (i.iIri rdfsSubClassOf) (i.iIri owlNothing) c

/-- **scm-sco** — same shape as `RDF.CondSubClassOfTrans`. -/
def RlCondScmSco : Prop :=
  ∀ c1 c2 c3 : i.idom, i.iext (i.iIri rdfsSubClassOf) c1 c2 →
    i.iext (i.iIri rdfsSubClassOf) c2 c3 →
    i.iext (i.iIri rdfsSubClassOf) c1 c3

/-- **scm-eqc1**, both conclusions (the two halves of
`CondEquivalentClass`). -/
def RlCondScmEqc1a : Prop :=
  ∀ c1 c2 : i.idom, i.iext (i.iIri owlEquivalentClass) c1 c2 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2

def RlCondScmEqc1b : Prop :=
  ∀ c1 c2 : i.idom, i.iext (i.iIri owlEquivalentClass) c1 c2 →
    i.iext (i.iIri rdfsSubClassOf) c2 c1

/-- **scm-eqc2** — same shape as `CondMutualSubclassEquivalent`. -/
def RlCondScmEqc2 : Prop :=
  ∀ c1 c2 : i.idom, i.iext (i.iIri rdfsSubClassOf) c1 c2 →
    i.iext (i.iIri rdfsSubClassOf) c2 c1 →
    i.iext (i.iIri owlEquivalentClass) c1 c2

/-- **scm-spo** — same shape as `RDF.CondSubPropertyOfTrans`. -/
def RlCondScmSpo : Prop :=
  ∀ p1 p2 p3 : i.idom, i.iext (i.iIri rdfsSubPropertyOf) p1 p2 →
    i.iext (i.iIri rdfsSubPropertyOf) p2 p3 →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p3

/-- **scm-eqp1**, both conclusions (the halves of
`CondEquivalentProperty`). -/
def RlCondScmEqp1a : Prop :=
  ∀ p1 p2 : i.idom, i.iext (i.iIri owlEquivalentProperty) p1 p2 →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p2

def RlCondScmEqp1b : Prop :=
  ∀ p1 p2 : i.idom, i.iext (i.iIri owlEquivalentProperty) p1 p2 →
    i.iext (i.iIri rdfsSubPropertyOf) p2 p1

/-- **scm-eqp2** — same shape as `CondMutualSubpropertyEquivalent`. -/
def RlCondScmEqp2 : Prop :=
  ∀ p1 p2 : i.idom, i.iext (i.iIri rdfsSubPropertyOf) p1 p2 →
    i.iext (i.iIri rdfsSubPropertyOf) p2 p1 →
    i.iext (i.iIri owlEquivalentProperty) p1 p2

/-- **scm-dom1** — same shape as `CondDomainSubclass`. -/
def RlCondScmDom1 : Prop :=
  ∀ p c1 c2 : i.idom, i.iext (i.iIri rdfsDomain) p c1 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2 → i.iext (i.iIri rdfsDomain) p c2

/-- **scm-dom2** — same shape as `CondDomainSubprop`. -/
def RlCondScmDom2 : Prop :=
  ∀ p1 p2 c : i.idom, i.iext (i.iIri rdfsDomain) p2 c →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p2 → i.iext (i.iIri rdfsDomain) p1 c

/-- **scm-rng1** — same shape as `CondRangeSubclass`. -/
def RlCondScmRng1 : Prop :=
  ∀ p c1 c2 : i.idom, i.iext (i.iIri rdfsRange) p c1 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2 → i.iext (i.iIri rdfsRange) p c2

/-- **scm-rng2** — same shape as `CondRangeSubprop`. -/
def RlCondScmRng2 : Prop :=
  ∀ p1 p2 c : i.idom, i.iext (i.iIri rdfsRange) p2 c →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p2 → i.iext (i.iIri rdfsRange) p1 c

/-- **scm-op** (conclusion 1 of 2). -/
def RlCondScmOpSub : Prop :=
  ∀ p : i.idom, icext i p (i.iIri owlObjectProperty) →
    i.iext (i.iIri rdfsSubPropertyOf) p p

/-- **scm-op** (conclusion 2 of 2). -/
def RlCondScmOpEqp : Prop :=
  ∀ p : i.idom, icext i p (i.iIri owlObjectProperty) →
    i.iext (i.iIri owlEquivalentProperty) p p

/-- **scm-svf1** — two existential restrictions on the SAME property
whose fillers are ordered are themselves ordered. -/
def RlCondScmSvf1 : Prop :=
  ∀ c1 c2 y1 y2 p : i.idom,
    i.iext (i.iIri owlSomeValuesFrom) c1 y1 →
    i.iext (i.iIri owlOnProperty) c1 p →
    i.iext (i.iIri owlSomeValuesFrom) c2 y2 →
    i.iext (i.iIri owlOnProperty) c2 p →
    i.iext (i.iIri rdfsSubClassOf) y1 y2 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2

/-- **scm-svf2** — the same filler over ordered properties. -/
def RlCondScmSvf2 : Prop :=
  ∀ c1 c2 y p1 p2 : i.idom,
    i.iext (i.iIri owlSomeValuesFrom) c1 y →
    i.iext (i.iIri owlOnProperty) c1 p1 →
    i.iext (i.iIri owlSomeValuesFrom) c2 y →
    i.iext (i.iIri owlOnProperty) c2 p2 →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p2 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2

/-- **scm-avf1** — the universal mirror of scm-svf1. -/
def RlCondScmAvf1 : Prop :=
  ∀ c1 c2 y1 y2 p : i.idom,
    i.iext (i.iIri owlAllValuesFrom) c1 y1 →
    i.iext (i.iIri owlOnProperty) c1 p →
    i.iext (i.iIri owlAllValuesFrom) c2 y2 →
    i.iext (i.iIri owlOnProperty) c2 p →
    i.iext (i.iIri rdfsSubClassOf) y1 y2 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2

/-- **scm-avf2** — the same filler over ordered properties, with the
conclusion the other way round. -/
def RlCondScmAvf2 : Prop :=
  ∀ c1 c2 y p1 p2 : i.idom,
    i.iext (i.iIri owlAllValuesFrom) c1 y →
    i.iext (i.iIri owlOnProperty) c1 p1 →
    i.iext (i.iIri owlAllValuesFrom) c2 y →
    i.iext (i.iIri owlOnProperty) c2 p2 →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p2 →
    i.iext (i.iIri rdfsSubClassOf) c2 c1

/-- **scm-hv** — the same value over ordered properties. -/
def RlCondScmHv : Prop :=
  ∀ c1 c2 iv p1 p2 : i.idom,
    i.iext (i.iIri owlHasValue) c1 iv →
    i.iext (i.iIri owlOnProperty) c1 p1 →
    i.iext (i.iIri owlHasValue) c2 iv →
    i.iext (i.iIri owlOnProperty) c2 p2 →
    i.iext (i.iIri rdfsSubPropertyOf) p1 p2 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2

/-- **scm-dp** (conclusion 1 of 2). -/
def RlCondScmDpSub : Prop :=
  ∀ p : i.idom, icext i p (i.iIri owlDatatypeProperty) →
    i.iext (i.iIri rdfsSubPropertyOf) p p

/-- **scm-dp** (conclusion 2 of 2). -/
def RlCondScmDpEqp : Prop :=
  ∀ p : i.idom, icext i p (i.iIri owlDatatypeProperty) →
    i.iext (i.iIri owlEquivalentProperty) p p

/-- **scm-int**, through `uListMem`. -/
def RlCondScmInt : Prop :=
  ∀ c l ci : i.idom, i.iext (i.iIri owlIntersectionOf) c l →
    i.iext (i.iIri uListMem) l ci → i.iext (i.iIri rdfsSubClassOf) c ci

/-- **scm-uni**, through `uListMem`. -/
def RlCondScmUni : Prop :=
  ∀ c l ci : i.idom, i.iext (i.iIri owlUnionOf) c l →
    i.iext (i.iIri uListMem) l ci → i.iext (i.iIri rdfsSubClassOf) ci c

/-- **eq-diff-sym** `[ext]` — same shape as
`CondDifferentFromSymmetric`. -/
def RlCondEqDiffSym : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlDifferentFrom) x y →
    i.iext (i.iIri owlDifferentFrom) y x

/-- **prp-pdw-diff** `[ext]` (`pdwToDiff`). The constructor's
syntactic `o1 ≠ o2` side condition is DROPPED: without it the
condition is stronger, still true in every OWL 2 RDF-Based
interpretation reading `owl:propertyDisjointWith` as extension
disjointness, and the completeness model discharges the extra
instances through the prp-pdw clash hypothesis. -/
def RlCondPdwToDiff : Prop :=
  ∀ (p1 p2 : WfIri) (x o1 o2 : i.idom),
    i.iext (i.iIri owlPropertyDisjointWith) (i.iIri p1) (i.iIri p2) →
    i.iext (i.iIri p1) x o1 → i.iext (i.iIri p2) x o2 →
    i.iext (i.iIri owlDifferentFrom) o1 o2

/-- **cax-dw-diff** `[ext]` (`caxDwToDiff`), `x ≠ y` dropped as
above (cax-dw clash covers the diagonal). -/
def RlCondCaxDwToDiff : Prop :=
  ∀ (c1 c2 : WfIri) (x y : i.idom),
    i.iext (i.iIri owlDisjointWith) (i.iIri c1) (i.iIri c2) →
    icext i x (i.iIri c1) → icext i y (i.iIri c2) →
    i.iext (i.iIri owlDifferentFrom) x y

/-- **prp-fp-diff** `[ext]` (`fpDiffToDiff`), `y1 ≠ y2` dropped
(eq-diff1 clash covers the diagonal after prp-fp fires). -/
def RlCondFpDiffToDiff : Prop :=
  ∀ (p : WfIri) (y1 y2 x1 x2 : i.idom),
    icext i (i.iIri p) (i.iIri owlFunctionalProperty) →
    i.iext (i.iIri p) y1 x1 → i.iext (i.iIri p) y2 x2 →
    i.iext (i.iIri owlDifferentFrom) x1 x2 →
    i.iext (i.iIri owlDifferentFrom) y1 y2

/-- **prp-ifp-diff** `[ext]` (`ifpDiffToDiff`), `y1 ≠ y2` dropped. -/
def RlCondIfpDiffToDiff : Prop :=
  ∀ (p : WfIri) (x1 x2 y1 y2 : i.idom),
    icext i (i.iIri p) (i.iIri owlInverseFunctionalProperty) →
    i.iext (i.iIri p) x1 y1 → i.iext (i.iIri p) x2 y2 →
    i.iext (i.iIri owlDifferentFrom) x1 x2 →
    i.iext (i.iIri owlDifferentFrom) y1 y2

/-- **scm-trans-from-chain** `[ext]` (`chainToTrans`) — the flat form
of `SeqIs i l [p, p]`. -/
def RlCondChainToTrans : Prop :=
  ∀ (p : WfIri) (l l' : i.idom),
    i.iext (i.iIri owlPropertyChainAxiom) (i.iIri p) l →
    i.iext (i.iIri rdfFirst) l (i.iIri p) → i.iext (i.iIri rdfRest) l l' →
    i.iext (i.iIri rdfFirst) l' (i.iIri p) →
    i.iext (i.iIri rdfRest) l' (i.iIri rdfNil) →
    icext i (i.iIri p) (i.iIri owlTransitiveProperty)

/-- **prp-rfl** `[ext]` (`prpRfl`), subject-occurrence guard: the
individual occurs as the subject of SOME fact. -/
def RlCondPrpRflS : Prop :=
  ∀ (p j : WfIri) (q y : i.idom),
    icext i (i.iIri p) (i.iIri owlReflexiveProperty) →
    i.iext q (i.iIri j) y → i.iext (i.iIri p) (i.iIri j) (i.iIri j)

/-- **prp-rfl** `[ext]`, object-occurrence guard. -/
def RlCondPrpRflO : Prop :=
  ∀ (p j : WfIri) (q x : i.idom),
    icext i (i.iIri p) (i.iIri owlReflexiveProperty) →
    i.iext q x (i.iIri j) → i.iext (i.iIri p) (i.iIri j) (i.iIri j)

/-- **xsd-axioms** `[ext]` (`xsdAxioms`): a datatype-position use of
an XSD IRI makes every triple of the XSD tower table true. -/
def RlCondXsdAxioms : Prop :=
  ∀ (p : WfIri), p ∈ datatypePositionPredicates →
    ∀ (w : WfIri), iriInXsdNs w = true →
    ∀ (a pr b : WfIri),
      (⟨Subject.iri a, pr, Term.iri b⟩ : Triple) ∈ xsdAxiomTriples →
      ∀ x : i.idom, i.iext (i.iIri p) x (i.iIri w) →
        i.iext (i.iIri pr) (i.iIri a) (i.iIri b)

/-- **dt-rng-intersect** `[ext]` (`dtRangeIntersect`). -/
def RlCondDtRangeIntersect : Prop :=
  ∀ (d1 d2 d3 : WfIri), rangeIntersectLicenses d1 d2 d3 = true →
    ∀ pd : i.idom, i.iext (i.iIri rdfsRange) pd (i.iIri d1) →
      i.iext (i.iIri rdfsRange) pd (i.iIri d2) →
      i.iext (i.iIri rdfsRange) pd (i.iIri d3)

/-- **dt-type1** and the Table 5.3 annotation-property typings `[ext]`
(`premiseFreeAxiom`): the axiom triples that hold with no premise. -/
def RlCondPremiseFreeAxiom : Prop :=
  ∀ (a pr b : WfIri),
    (⟨Subject.iri a, pr, Term.iri b⟩ : Triple) ∈ premiseFreeAxioms →
    i.iext (i.iIri pr) (i.iIri a) (i.iIri b)

/-- **cax-adc-dw** `[ext]` (`caxAdcToDw`), through `uListMem`; the
member pair is a distinct pair of IRIs, exactly as in the
constructor. -/
def RlCondCaxAdcToDw : Prop :=
  ∀ (ci cj : WfIri), ci ≠ cj → ∀ y l : i.idom,
    icext i y (i.iIri owlAllDisjointClasses) →
    i.iext (i.iIri owlMembers) y l →
    i.iext (i.iIri uListMem) l (i.iIri ci) →
    i.iext (i.iIri uListMem) l (i.iIri cj) →
    i.iext (i.iIri owlDisjointWith) (i.iIri ci) (i.iIri cj)

/-- **inv-flip** `[ext]`, the four directions. -/
def RlCondInvFlipDomRng : Prop :=
  ∀ (p q c : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    i.iext (i.iIri rdfsDomain) (i.iIri p) (i.iIri c) →
    i.iext (i.iIri rdfsRange) (i.iIri q) (i.iIri c)

def RlCondInvFlipRngDom : Prop :=
  ∀ (p q c : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    i.iext (i.iIri rdfsRange) (i.iIri p) (i.iIri c) →
    i.iext (i.iIri rdfsDomain) (i.iIri q) (i.iIri c)

def RlCondInvFlipDomRngRev : Prop :=
  ∀ (p q c : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    i.iext (i.iIri rdfsDomain) (i.iIri q) (i.iIri c) →
    i.iext (i.iIri rdfsRange) (i.iIri p) (i.iIri c)

def RlCondInvFlipRngDomRev : Prop :=
  ∀ (p q c : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    i.iext (i.iIri rdfsRange) (i.iIri q) (i.iIri c) →
    i.iext (i.iIri rdfsDomain) (i.iIri p) (i.iIri c)

/-- **inv-fp** `[ext]`, the four directions. Each is a consequence of
`OWL.CondInverseOf` (Table 5.13) with `OWL.CondFunctional` and the
inverse-functional condition (Table 5.14); see
`rlCondInvFpIfp_of_semantics` below. -/
def RlCondInvFpIfp : Prop :=
  ∀ (p q : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    icext i (i.iIri p) (i.iIri owlFunctionalProperty) →
    icext i (i.iIri q) (i.iIri owlInverseFunctionalProperty)

def RlCondInvIfpFp : Prop :=
  ∀ (p q : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    icext i (i.iIri p) (i.iIri owlInverseFunctionalProperty) →
    icext i (i.iIri q) (i.iIri owlFunctionalProperty)

def RlCondInvFpIfpRev : Prop :=
  ∀ (p q : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    icext i (i.iIri q) (i.iIri owlFunctionalProperty) →
    icext i (i.iIri p) (i.iIri owlInverseFunctionalProperty)

def RlCondInvIfpFpRev : Prop :=
  ∀ (p q : WfIri), i.iext (i.iIri owlInverseOf) (i.iIri p) (i.iIri q) →
    icext i (i.iIri q) (i.iIri owlInverseFunctionalProperty) →
    icext i (i.iIri p) (i.iIri owlFunctionalProperty)

/-! ### The comprehension conditions (`caxDwToComplement`,
`clsMaxqc1ToComplement`, `minCard1Comprehension`)

One witness per argument class/property, SHARED across every row that
mentions it — the engine mints ONE blank node per argument, so the
witness's properties must cover every emitted edge at once (which is
why the `∀ a` parts sit INSIDE the existential). -/

/-- The qualified-cardinality contrapositive's premise bundle
(`clsMaxqc1ToComplement` premises 1-8, minus the conclusion). -/
def MqcBody (c : WfIri) (x u y1 y2 pe : i.idom) : Prop :=
  i.iext (i.iIri owlMaxQualifiedCardinality) x (i.iLit litNni1) ∧
  i.iext (i.iIri owlOnProperty) x pe ∧
  i.iext (i.iIri owlOnClass) x (i.iIri c) ∧
  icext i u x ∧ i.iext pe u y1 ∧ i.iext pe u y2 ∧
  icext i y1 (i.iIri c) ∧ i.iext (i.iIri owlDifferentFrom) y1 y2

/-- What the complement witness of `c` satisfies: it is a class, the
complement of `c`, every class disjoint with `c` (in either premise
direction) is inside it, and every excess qualified-cardinality value
over `c` is typed into it. -/
def CompProps (c : WfIri) (z : i.idom) : Prop :=
  icext i z (i.iIri owlClass) ∧
  i.iext (i.iIri owlComplementOf) z (i.iIri c) ∧
  (∀ a : i.idom, i.iext (i.iIri owlDisjointWith) a (i.iIri c) →
    i.iext (i.iIri rdfsSubClassOf) a z) ∧
  (∀ a : i.idom, i.iext (i.iIri owlDisjointWith) (i.iIri c) a →
    i.iext (i.iIri rdfsSubClassOf) a z) ∧
  (∀ x u y1 y2 pe : i.idom, MqcBody i c x u y1 y2 pe → icext i y2 z)

/-- **cax-dw-comp** `[ext]` (`caxDwToComplement`): a disjointness
mention of `c` guarantees the complement witness. -/
def RlCondCompDw : Prop :=
  ∀ (c : WfIri),
    (∃ a : i.idom, i.iext (i.iIri owlDisjointWith) a (i.iIri c) ∨
      i.iext (i.iIri owlDisjointWith) (i.iIri c) a) →
    ∃ z : i.idom, CompProps i c z

/-- **cls-maxqc1-comp** `[ext]` (`clsMaxqc1ToComplement`): a
qualified-cardinality overflow on `c` guarantees the witness. -/
def RlCondCompMqc : Prop :=
  ∀ (c : WfIri), (∃ x u y1 y2 pe : i.idom, MqcBody i c x u y1 y2 pe) →
    ∃ z : i.idom, CompProps i c z

/-- What the `minCardinality 1` witness of `p` satisfies
(`minCard1WitnessTriples`). -/
def Minc1Props (p : WfIri) (z : i.idom) : Prop :=
  icext i z (i.iIri owlRestriction) ∧
  i.iext (i.iIri owlOnProperty) z (i.iIri p) ∧
  i.iext (i.iIri owlMinCardinality) z (i.iLit litNni1) ∧
  i.iext (i.iIri owlMinCardinality) z (i.iLit litInt1)

/-- **minc1-comp** `[ext]` (`minCard1Comprehension`). -/
def RlCondMinc1 : Prop :=
  ∀ (p : WfIri), icext i (i.iIri p) (i.iIri owlObjectProperty) →
    ∃ z : i.idom, Minc1Props i p z

/-! ### The four `inv-fp` conditions are consequences, not table rows

`RlCondInvFpIfp` and its three companions are the only conditions in
this file that do not mirror a published table row. They follow from
three conditions that ARE published: `CondInverseOf` (OWL 2 RDF-Based
Semantics, 2nd Edition, Table 5.13) and the Table 5.14 conditions for
`owl:FunctionalProperty` and `owl:InverseFunctionalProperty`. Table 5.14
states each characteristic as an `iff`; `OWL.CondFunctional` carries
only the half that READS a membership, so the half that CONCLUDES one
is stated here under its table name and taken as a hypothesis of the
derivation, not added to any bundle. -/

/-- Table 5.14, `owl:FunctionalProperty`, the half that reads a
membership. The same statement as `OWL.CondFunctional`. -/
def T514FunctionalElim : Prop :=
  ∀ p x y z : i.idom, icext i p (i.iIri owlFunctionalProperty) →
    i.iext p x y → i.iext p x z → y = z

/-- Table 5.14, `owl:FunctionalProperty`, the half that concludes a
membership. -/
def T514FunctionalIntro : Prop :=
  ∀ p : i.idom, (∀ x y z : i.idom, i.iext p x y → i.iext p x z → y = z) →
    icext i p (i.iIri owlFunctionalProperty)

/-- Table 5.14, `owl:InverseFunctionalProperty`, the half that reads a
membership. -/
def T514InverseFunctionalElim : Prop :=
  ∀ p x1 x2 y : i.idom, icext i p (i.iIri owlInverseFunctionalProperty) →
    i.iext p x1 y → i.iext p x2 y → x1 = x2

/-- Table 5.14, `owl:InverseFunctionalProperty`, the half that concludes
a membership. -/
def T514InverseFunctionalIntro : Prop :=
  ∀ p : i.idom,
    (∀ x1 x2 y : i.idom, i.iext p x1 y → i.iext p x2 y → x1 = x2) →
    icext i p (i.iIri owlInverseFunctionalProperty)

theorem rlCondInvFpIfp_of_semantics (hinv : CondInverseOf i)
    (hfe : T514FunctionalElim i) (hii : T514InverseFunctionalIntro i) :
    RlCondInvFpIfp i := by
  intro p q hpq hfp
  refine hii _ (fun x1 x2 y h1 h2 => ?_)
  exact hfe _ y x1 x2 hfp ((hinv _ _ y x1 hpq).mpr h1)
    ((hinv _ _ y x2 hpq).mpr h2)

theorem rlCondInvIfpFp_of_semantics (hinv : CondInverseOf i)
    (hie : T514InverseFunctionalElim i) (hfi : T514FunctionalIntro i) :
    RlCondInvIfpFp i := by
  intro p q hpq hifp
  refine hfi _ (fun x y z h1 h2 => ?_)
  exact hie _ y z x hifp ((hinv _ _ y x hpq).mpr h1)
    ((hinv _ _ z x hpq).mpr h2)

theorem rlCondInvFpIfpRev_of_semantics (hinv : CondInverseOf i)
    (hfe : T514FunctionalElim i) (hii : T514InverseFunctionalIntro i) :
    RlCondInvFpIfpRev i := by
  intro p q hpq hfp
  refine hii _ (fun x1 x2 y h1 h2 => ?_)
  exact hfe _ y x1 x2 hfp ((hinv _ _ x1 y hpq).mp h1)
    ((hinv _ _ x2 y hpq).mp h2)

theorem rlCondInvIfpFpRev_of_semantics (hinv : CondInverseOf i)
    (hie : T514InverseFunctionalElim i) (hfi : T514FunctionalIntro i) :
    RlCondInvIfpFpRev i := by
  intro p q hpq hifp
  refine hfi _ (fun x y z h1 h2 => ?_)
  exact hie _ y z x hifp ((hinv _ _ x y hpq).mp h1)
    ((hinv _ _ x z hpq).mp h2)

end Conditions

/-- **The derivation-condition bundle**: one field per `Derives` row
(the schema `Unified/OwlRlSchema.lean` states is its object-language
counterpart, row for row). -/
structure RlConditions (i : Interp) : Prop where
  eqRefS : RlCondEqRefS i
  eqRefP : RlCondEqRefP i
  eqRefO : RlCondEqRefO i
  eqSym : RlCondEqSym i
  eqTrans : RlCondEqTrans i
  eqRepS : RlCondEqRepS i
  eqRepP : RlCondEqRepP i
  eqRepO : RlCondEqRepO i
  prpDom : RlCondPrpDom i
  prpRng : RlCondPrpRng i
  prpFp : RlCondPrpFp i
  prpIfp : RlCondPrpIfp i
  prpSymp : RlCondPrpSymp i
  prpTrp : RlCondPrpTrp i
  prpSpo1 : RlCondPrpSpo1 i
  prpSpo2 : RlCondPrpSpo2 i
  prpEqp1 : RlCondPrpEqp1 i
  prpEqp2 : RlCondPrpEqp2 i
  prpInv1 : RlCondPrpInv1 i
  prpInv2 : RlCondPrpInv2 i
  prpKey : RlCondPrpKey i
  clsThing : RlCondClsThing i
  clsNothing1 : RlCondClsNothing1 i
  clsInt1 : RlCondClsInt1 i
  typedAllBase : RlCondTypedAllBase i
  typedAllStep : RlCondTypedAllStep i
  listMemBase : RlCondListMemBase i
  listMemStep : RlCondListMemStep i
  clsInt2 : RlCondClsInt2 i
  clsUni : RlCondClsUni i
  clsSvf1 : RlCondClsSvf1 i
  clsSvf2 : RlCondClsSvf2 i
  clsAvf : RlCondClsAvf i
  clsHv1 : RlCondClsHv1 i
  clsHv2 : RlCondClsHv2 i
  clsHs1 : RlCondClsHs1 i
  clsHs2 : RlCondClsHs2 i
  clsMaxc2 : RlCondClsMaxc2 i
  clsOo : RlCondClsOo i
  caxSco : RlCondCaxSco i
  caxEqc1 : RlCondCaxEqc1 i
  caxEqc2 : RlCondCaxEqc2 i
  scmClsSelf : RlCondScmClsSelf i
  scmClsEqc : RlCondScmClsEqc i
  scmClsThing : RlCondScmClsThing i
  scmClsNothing : RlCondScmClsNothing i
  scmSco : RlCondScmSco i
  scmEqc1a : RlCondScmEqc1a i
  scmEqc1b : RlCondScmEqc1b i
  scmEqc2 : RlCondScmEqc2 i
  scmSpo : RlCondScmSpo i
  scmEqp1a : RlCondScmEqp1a i
  scmEqp1b : RlCondScmEqp1b i
  scmEqp2 : RlCondScmEqp2 i
  scmDom1 : RlCondScmDom1 i
  scmDom2 : RlCondScmDom2 i
  scmRng1 : RlCondScmRng1 i
  scmRng2 : RlCondScmRng2 i
  scmOpSub : RlCondScmOpSub i
  scmOpEqp : RlCondScmOpEqp i
  scmDpSub : RlCondScmDpSub i
  scmDpEqp : RlCondScmDpEqp i
  scmSvf1 : RlCondScmSvf1 i
  scmSvf2 : RlCondScmSvf2 i
  scmAvf1 : RlCondScmAvf1 i
  scmAvf2 : RlCondScmAvf2 i
  scmHv : RlCondScmHv i
  scmInt : RlCondScmInt i
  scmUni : RlCondScmUni i
  eqDiffSym : RlCondEqDiffSym i
  pdwToDiff : RlCondPdwToDiff i
  caxDwToDiff : RlCondCaxDwToDiff i
  fpDiffToDiff : RlCondFpDiffToDiff i
  ifpDiffToDiff : RlCondIfpDiffToDiff i
  chainToTrans : RlCondChainToTrans i
  prpRflS : RlCondPrpRflS i
  prpRflO : RlCondPrpRflO i
  xsdAxioms : RlCondXsdAxioms i
  dtRangeIntersect : RlCondDtRangeIntersect i
  premiseFreeAxiom : RlCondPremiseFreeAxiom i
  caxAdcToDw : RlCondCaxAdcToDw i
  invFlipDomRng : RlCondInvFlipDomRng i
  invFlipRngDom : RlCondInvFlipRngDom i
  invFlipDomRngRev : RlCondInvFlipDomRngRev i
  invFlipRngDomRev : RlCondInvFlipRngDomRev i
  invFpIfp : RlCondInvFpIfp i
  invIfpFp : RlCondInvIfpFp i
  invFpIfpRev : RlCondInvFpIfpRev i
  invIfpFpRev : RlCondInvIfpFpRev i
  compDw : RlCondCompDw i
  compMqc : RlCondCompMqc i
  minc1 : RlCondMinc1 i

/-! ## Clash-row conditions (falsity-headed) -/

section ClashConditions

variable (i : Interp)

/-- **eq-diff1**. -/
def RlNCondEqDiff1 : Prop :=
  ∀ x y : i.idom, ¬ (i.iext (i.iIri owlSameAs) x y ∧
    i.iext (i.iIri owlDifferentFrom) x y)

/-- **prp-irp**. -/
def RlNCondPrpIrp : Prop :=
  ∀ (p : WfIri) (x : i.idom),
    ¬ (icext i (i.iIri p) (i.iIri owlIrreflexiveProperty) ∧
       i.iext (i.iIri p) x x)

/-- **prp-asyp**. -/
def RlNCondPrpAsyp : Prop :=
  ∀ (p : WfIri) (x y : i.idom),
    ¬ (icext i (i.iIri p) (i.iIri owlAsymmetricProperty) ∧
       i.iext (i.iIri p) x y ∧ i.iext (i.iIri p) y x)

/-- **prp-pdw**. -/
def RlNCondPrpPdw : Prop :=
  ∀ (p1 p2 : WfIri) (x y : i.idom),
    ¬ (i.iext (i.iIri owlPropertyDisjointWith) (i.iIri p1) (i.iIri p2) ∧
       i.iext (i.iIri p1) x y ∧ i.iext (i.iIri p2) x y)

/-- **prp-npa1**. -/
def RlNCondPrpNpa1 : Prop :=
  ∀ (p : WfIri) (w x y : i.idom),
    ¬ (i.iext (i.iIri owlSourceIndividual) w x ∧
       i.iext (i.iIri owlAssertionProperty) w (i.iIri p) ∧
       i.iext (i.iIri owlTargetIndividual) w y ∧ i.iext (i.iIri p) x y)

/-- **prp-npa2**. -/
def RlNCondPrpNpa2 : Prop :=
  ∀ (p : WfIri) (w x y : i.idom),
    ¬ (i.iext (i.iIri owlSourceIndividual) w x ∧
       i.iext (i.iIri owlAssertionProperty) w (i.iIri p) ∧
       i.iext (i.iIri owlTargetValue) w y ∧ i.iext (i.iIri p) x y)

/-- **cls-nothing2**. -/
def RlNCondClsNothing2 : Prop :=
  ∀ x : i.idom, ¬ icext i x (i.iIri owlNothing)

/-- **cls-com**. -/
def RlNCondClsCom : Prop :=
  ∀ c1 c2 x : i.idom, ¬ (i.iext (i.iIri owlComplementOf) c1 c2 ∧
    icext i x c1 ∧ icext i x c2)

/-- **cls-maxc1**. -/
def RlNCondClsMaxc1 : Prop :=
  ∀ (p : WfIri) (x u y : i.idom),
    ¬ (i.iext (i.iIri owlMaxCardinality) x (i.iLit litNni0) ∧
       i.iext (i.iIri owlOnProperty) x (i.iIri p) ∧ icext i u x ∧
       i.iext (i.iIri p) u y)

/-- **cls-maxqc1**. -/
def RlNCondClsMaxqc1 : Prop :=
  ∀ (p : WfIri) (x u y c : i.idom),
    ¬ (i.iext (i.iIri owlMaxQualifiedCardinality) x (i.iLit litNni0) ∧
       i.iext (i.iIri owlOnProperty) x (i.iIri p) ∧
       i.iext (i.iIri owlOnClass) x c ∧ icext i u x ∧
       i.iext (i.iIri p) u y ∧ icext i y c)

/-- **cls-maxqc2**. -/
def RlNCondClsMaxqc2 : Prop :=
  ∀ (p : WfIri) (x u y : i.idom),
    ¬ (i.iext (i.iIri owlMaxQualifiedCardinality) x (i.iLit litNni0) ∧
       i.iext (i.iIri owlOnProperty) x (i.iIri p) ∧
       i.iext (i.iIri owlOnClass) x (i.iIri owlThing) ∧ icext i u x ∧
       i.iext (i.iIri p) u y)

/-- **cax-dw**. -/
def RlNCondCaxDw : Prop :=
  ∀ c1 c2 x : i.idom, ¬ (i.iext (i.iIri owlDisjointWith) c1 c2 ∧
    icext i x c1 ∧ icext i x c2)

/-- **cax-adc**, through `uListMem`, member pair restricted to
distinct IRIs (the constructor's distinct-TERM deviation, further
narrowed to the IRI pairs the schema family can name — the non-IRI
member gap is recorded in the stage notes). -/
def RlNCondCaxAdc : Prop :=
  ∀ (c1 c2 : WfIri), c1 ≠ c2 → ∀ y l z : i.idom,
    ¬ (icext i y (i.iIri owlAllDisjointClasses) ∧
       i.iext (i.iIri owlMembers) y l ∧
       i.iext (i.iIri uListMem) l (i.iIri c1) ∧
       i.iext (i.iIri uListMem) l (i.iIri c2) ∧
       icext i z (i.iIri c1) ∧ icext i z (i.iIri c2))

/-- **eq-diff2**, through `uListMem`, member pair restricted to
distinct IRIs — the same narrowing `RlNCondCaxAdc` records, for the
same reason (the schema family is indexed by IRI pairs). -/
def RlNCondEqDiff2 : Prop :=
  ∀ (z1 z2 : WfIri), z1 ≠ z2 → ∀ y l : i.idom,
    ¬ (icext i y (i.iIri owlAllDifferent) ∧
       i.iext (i.iIri owlMembers) y l ∧
       i.iext (i.iIri uListMem) l (i.iIri z1) ∧
       i.iext (i.iIri uListMem) l (i.iIri z2) ∧
       i.iext (i.iIri owlSameAs) (i.iIri z1) (i.iIri z2))

/-- **eq-diff3** — eq-diff2 through `owl:distinctMembers`. -/
def RlNCondEqDiff3 : Prop :=
  ∀ (z1 z2 : WfIri), z1 ≠ z2 → ∀ y l : i.idom,
    ¬ (icext i y (i.iIri owlAllDifferent) ∧
       i.iext (i.iIri owlDistinctMembers) y l ∧
       i.iext (i.iIri uListMem) l (i.iIri z1) ∧
       i.iext (i.iIri uListMem) l (i.iIri z2) ∧
       i.iext (i.iIri owlSameAs) (i.iIri z1) (i.iIri z2))

/-- **prp-adp**, through `uListMem`. The member pair is a pair of
IRIs with no extra narrowing: the members occupy PREDICATE position,
where only an IRI can stand. -/
def RlNCondPrpAdp : Prop :=
  ∀ (p1 p2 : WfIri), p1 ≠ p2 → ∀ y l u v : i.idom,
    ¬ (icext i y (i.iIri owlAllDisjointProperties) ∧
       i.iext (i.iIri owlMembers) y l ∧
       i.iext (i.iIri uListMem) l (i.iIri p1) ∧
       i.iext (i.iIri uListMem) l (i.iIri p2) ∧
       i.iext (i.iIri p1) u v ∧ i.iext (i.iIri p2) u v)

end ClashConditions

/-- **The clash-condition bundle**: one field per `Clash` row. -/
structure RlClashConditions (i : Interp) : Prop where
  eqDiff1 : RlNCondEqDiff1 i
  prpIrp : RlNCondPrpIrp i
  prpAsyp : RlNCondPrpAsyp i
  prpPdw : RlNCondPrpPdw i
  prpNpa1 : RlNCondPrpNpa1 i
  prpNpa2 : RlNCondPrpNpa2 i
  clsNothing2 : RlNCondClsNothing2 i
  clsCom : RlNCondClsCom i
  clsMaxc1 : RlNCondClsMaxc1 i
  clsMaxqc1 : RlNCondClsMaxqc1 i
  clsMaxqc2 : RlNCondClsMaxqc2 i
  caxDw : RlNCondCaxDw i
  caxAdc : RlNCondCaxAdc i
  eqDiff2 : RlNCondEqDiff2 i
  eqDiff3 : RlNCondEqDiff3 i
  prpAdp : RlNCondPrpAdp i

/-! ## Truth of the collection premises under the conditions -/

theorem denot_toTerm (i : Interp) (a : BnodeAssignment i.idom) (s : Subject) :
    denotTerm i a s.toTerm = denotSubject i a s := by
  cases s <;> rfl

section HoldsHelpers

variable {i : Interp} {a : BnodeAssignment i.idom} {gc : Graph}

theorem holds_listMember (hbase : RlCondListMemBase i)
    (hstep : RlCondListMemStep i)
    (hgc : ∀ u ∈ gc, TripleHolds i a u) {lst e : Term}
    (h : ListMember gc lst e) :
    i.iext (i.iIri uListMem) (denotTerm i a lst) (denotTerm i a e) := by
  induction h with
  | @here node e hf =>
      have := hgc _ hf
      rw [denot_toTerm]
      exact hbase _ _ this
  | @there node tail e hr _ ih =>
      have := hgc _ hr
      rw [denot_toTerm]
      exact hstep _ _ _ this ih

theorem holds_typedAll (hbase : RlCondTypedAllBase i)
    (hstep : RlCondTypedAllStep i)
    (hgc : ∀ u ∈ gc, TripleHolds i a u) {y : Subject} :
    ∀ {lst : Term} {cs : List Term}, cs ≠ [] → ListDenotes gc lst cs →
      TypesAll gc y cs →
      i.iext (i.iIri uTypedAll) (denotSubject i a y) (denotTerm i a lst) := by
  intro lst cs hne hl ht
  induction hl with
  | nil => exact absurd rfl hne
  | @cons node e tail rest hnil hf hr htail ih =>
      cases ht with
      | cons hty htrest =>
          rw [denot_toTerm]
          cases htail with
          | nil =>
              exact hbase _ _ _ (hgc _ hf) (hgc _ hr) (hgc _ hty)
          | cons hnil2 hf2 hr2 htail2 =>
              refine hstep _ _ _ _ (hgc _ hf) (hgc _ hr) (hgc _ hty) ?_
              exact ih (by simp) htrest

theorem holds_seqIs (hgc : ∀ u ∈ gc, TripleHolds i a u) {lst : Term}
    {es : List Term} (h : ListDenotes gc lst es) :
    SeqIs i (denotTerm i a lst) (es.map (denotTerm i a)) := by
  induction h with
  | nil => simp [SeqIs, denotTerm]
  | @cons node e tail rest hnil hf hr htail ih =>
      rw [denot_toTerm]
      exact ⟨denotTerm i a tail, hgc _ hf, hgc _ hr, ih⟩

theorem holds_semChain (hgc : ∀ u ∈ gc, TripleHolds i a u) {s : Subject}
    {ps : List WfIri} {fin : Term} (h : ChainHolds gc s ps fin) :
    SemChain i (denotSubject i a s) (ps.map (i.iIri ·)) (denotTerm i a fin) := by
  induction h with
  | nil => exact (denot_toTerm i a _).symm
  | @last s p o hm => exact ⟨denotTerm i a o, hgc _ hm, rfl⟩
  | @step s mid p rest fin hm _ ih =>
      refine ⟨denotSubject i a mid, ?_, ih⟩
      have := hgc _ hm
      rwa [TripleHolds, denot_toTerm] at this

theorem holds_shares (hgc : ∀ u ∈ gc, TripleHolds i a u) {x y : Subject}
    {ps : List WfIri} (h : SharesKeyValues gc x y ps) :
    SemShares i (denotSubject i a x) (denotSubject i a y)
      (ps.map (i.iIri ·)) := by
  induction h with
  | nil => intro q hq; simp at hq
  | @cons p o rest hx hy _ ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨denotTerm i a o, hgc _ hx, hgc _ hy⟩
      · exact ih q hq

end HoldsHelpers

/-! ## Table shapes -/

theorem xsdAxiomTriples_shape :
    ∀ t ∈ xsdAxiomTriples, ∃ (a pr b : WfIri),
      t = ⟨Subject.iri a, pr, Term.iri b⟩ := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp h
    exact ⟨e.1, rdfsSubClassOf, e.2, rfl⟩
  · obtain ⟨w, _, rfl⟩ := List.mem_map.mp h
    exact ⟨w, rdfType, rdfsDatatype, rfl⟩

theorem builtinDatatypeAxioms_shape :
    ∀ t ∈ builtinDatatypeAxioms, ∃ (a pr b : WfIri),
      t = ⟨Subject.iri a, pr, Term.iri b⟩ := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨xsdInteger, rdfType, rdfsDatatype, rfl⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨xsdString, rdfType, rdfsDatatype, rfl⟩
    · simp at ht

theorem premiseFreeAxioms_shape :
    ∀ t ∈ premiseFreeAxioms, ∃ (a pr b : WfIri),
      t = ⟨Subject.iri a, pr, Term.iri b⟩ := by
  intro t ht
  simp only [premiseFreeAxioms, builtinDatatypeAxioms,
    vocabAnnotationPropertyAxioms, rdfsVocabAxioms, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  repeat' (rcases ht with rfl | ht)
  all_goals exact ⟨_, _, _, rfl⟩

/-! ## The comprehension witnesses and the extended assignment -/

open Classical in
/-- The chosen complement-class witness for `c` (the individual the
minted `__rl_comp__` label denotes), when the conditions provide one. -/
noncomputable def compWitness (i : Interp) (c : WfIri) : i.idom :=
  if h : ∃ z, CompProps i c z then h.choose else i.idomWit

open Classical in
theorem compWitness_props {i : Interp} {c : WfIri}
    (h : ∃ z, CompProps i c z) : CompProps i c (compWitness i c) := by
  rw [compWitness, dif_pos h]
  exact h.choose_spec

open Classical in
noncomputable def minc1Witness (i : Interp) (p : WfIri) : i.idom :=
  if h : ∃ z, Minc1Props i p z then h.choose else i.idomWit

open Classical in
theorem minc1Witness_props {i : Interp} {p : WfIri}
    (h : ∃ z, Minc1Props i p z) : Minc1Props i p (minc1Witness i p) := by
  rw [minc1Witness, dif_pos h]
  exact h.choose_spec

/-- The premise assignment extended at the reserved labels with the
comprehension witnesses. -/
noncomputable def rlExtend (i : Interp) (A : BnodeAssignment i.idom) :
    BnodeAssignment i.idom :=
  fun b =>
    match decodeComp b with
    | some c => compWitness i c
    | none =>
        match decodeMinc1 b with
        | some p => minc1Witness i p
        | none => A b

theorem rlExtend_comp (i : Interp) (A : BnodeAssignment i.idom) (c : WfIri) :
    rlExtend i A ("__rl_comp__" ++ c.val) = compWitness i c := by
  unfold rlExtend
  rw [decodeComp_witness]

theorem rlExtend_minc1 (i : Interp) (A : BnodeAssignment i.idom) (p : WfIri) :
    rlExtend i A ("__rl_minc1__" ++ p.val) = minc1Witness i p := by
  unfold rlExtend
  rw [decodeComp_minc1, decodeMinc1_witness]

theorem rlExtend_of_not_reserved {i : Interp} {A : BnodeAssignment i.idom}
    {b : BNodeId} (h : rlReservedBnode b = false) : rlExtend i A b = A b := by
  obtain ⟨h1, h2⟩ := decode_of_not_reserved h
  unfold rlExtend
  rw [h1, h2]

/-- Denotation of the minted complement label. -/
theorem denot_compWitness (i : Interp) (A : BnodeAssignment i.idom)
    (c : WfIri) :
    denotSubject i (rlExtend i A) (complementWitness c) = compWitness i c := by
  show rlExtend i A ("__rl_comp__" ++ c.val) = compWitness i c
  exact rlExtend_comp i A c

theorem denot_minc1Witness (i : Interp) (A : BnodeAssignment i.idom)
    (p : WfIri) :
    denotSubject i (rlExtend i A) (minCard1Witness p) = minc1Witness i p := by
  show rlExtend i A ("__rl_minc1__" ++ p.val) = minc1Witness i p
  exact rlExtend_minc1 i A p

theorem subjBnodes_nonres {s : Subject} (h : subjNonReserved s = true) :
    ∀ b ∈ subjectBnodes s, rlReservedBnode b = false := by
  intro b hb
  cases s with
  | iri w => simp [subjectBnodes] at hb
  | bnode b' =>
      simp only [subjectBnodes, List.mem_singleton] at hb
      subst hb
      simpa [subjNonReserved] using h

theorem termBnodes_nonres : ∀ {o : Term}, termNonReserved o = true →
    ∀ b ∈ termBnodes o, rlReservedBnode b = false
  | .iri _, _, b, hb => by simp [termBnodes] at hb
  | .bnode b', h, b, hb => by
      simp only [termBnodes, List.mem_singleton] at hb
      subst hb
      simpa [termNonReserved] using h
  | .literal _, _, b, hb => by simp [termBnodes] at hb
  | .tripleTerm s p o, h, b, hb => by
      simp only [termNonReserved, Bool.and_eq_true] at h
      rcases List.mem_append.mp hb with hs | ho
      · exact subjBnodes_nonres h.1.1 b hs
      · exact termBnodes_nonres h.2 b ho

/-- A reserved-free triple holds at the extension exactly when it
holds at the base assignment. -/
theorem holds_rlExtend_of_nonReserved {i : Interp}
    {A : BnodeAssignment i.idom} {t : Triple}
    (hnr : tripleNonReserved t = true) (h : TripleHolds i A t) :
    TripleHolds i (rlExtend i A) t := by
  refine (tripleHolds_agree i (a1 := A) (a2 := rlExtend i A) ?_).mp h
  intro b hb
  refine (rlExtend_of_not_reserved ?_).symm
  simp only [tripleNonReserved, Bool.and_eq_true] at hnr
  rcases List.mem_append.mp hb with hs | ho
  · exact subjBnodes_nonres hnr.1.1 b hs
  · exact termBnodes_nonres hnr.2 b ho

/-! ## Truth preservation — the missing model-theoretic layer -/

/-- **Truth preservation for the OWL 2 RL/RDF rule relation** (the
port of the F* `OWL.Semantics.Soundness` layer this tree lacked —
`RLTheorems.lean` header, "what is NOT proved" item 1): in every
interpretation satisfying the row conditions, every triple `Derives`
derives from a reserved-free graph is true under the premise
assignment extended at the comprehension witnesses. One induction,
all 73 constructors. -/
theorem rl_derives_holds {i : Interp} (hc : RlConditions i) {g : Graph}
    (hres : RlReservedFree g) {A : BnodeAssignment i.idom}
    (hA : HoldsAll i A g) {t : Triple} (h : Derives g t) :
    TripleHolds i (rlExtend i A) t := by
  induction h with
  | base hm => exact holds_rlExtend_of_nonReserved (hres _ hm) (hA _ hm)
  | eqRefS _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.eqRefS _ _ _ ih
  | eqRefP hprem ih =>
      have hnp := tin_p (derives_irisNonReserved hres hprem)
      simp only [TripleHolds] at ih ⊢
      exact hc.eqRefP _ hnp _ _ ih
  | eqRefO _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.eqRefO _ _ _ ih
  | eqSym _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.eqSym _ _ ih
  | eqTrans _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.eqTrans _ _ _ ih1 ih2
  | eqRepS _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.eqRepS _ _ _ _ ih1 ih2
  | eqRepP _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.eqRepP _ _ _ _ ih1 ih2
  | eqRepO _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.eqRepO _ _ _ _ ih1 ih2
  | prpDom _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.prpDom _ _ _ _ ih1 ih2
  | prpRng _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.prpRng _ _ _ _ ih1 ih2
  | prpFp _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.prpFp _ _ _ _ ih1 ih2 ih3
  | prpIfp _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.prpIfp _ _ _ _ ih1 ih2 ih3
  | prpSymp _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.prpSymp _ _ _ ih1 ih2
  | prpTrp _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.prpTrp _ _ _ _ ih1 ih2 ih3
  | prpSpo1 _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.prpSpo1 _ _ _ _ ih1 ih2
  | prpSpo2 _ _ hl hne hch ihgc ih =>
      have hseq := holds_seqIs ihgc hl
      rw [List.map_map] at hseq
      have hmap : (denotTerm i (rlExtend i A) ∘ Term.iri) =
          (fun q => i.iIri q) := by funext q; rfl
      rw [hmap] at hseq
      have hchain := holds_semChain ihgc hch
      simp only [TripleHolds] at ih ⊢
      refine hc.prpSpo2 _ _ _ _ _ ?_ ih hseq hchain
      simpa using hne
  | prpEqp1 _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.prpEqp1 _ _ _ _ ih1 ih2
  | prpEqp2 _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.prpEqp2 _ _ _ _ ih1 ih2
  | prpInv1 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.prpInv1 _ _ _ _ ih1 ih2
  | prpInv2 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.prpInv2 _ _ _ _ ih1 ih2
  | prpKey _ _ hl hne _ _ hs ihgc ih1 ih2 ih3 =>
      have hseq := holds_seqIs ihgc hl
      rw [List.map_map] at hseq
      have hmap : (denotTerm i (rlExtend i A) ∘ Term.iri) =
          (fun q => i.iIri q) := by funext q; rfl
      rw [hmap] at hseq
      have hsh := holds_shares ihgc hs
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      refine hc.prpKey _ _ _ _ _ ?_ ih1 hseq ih2 ih3 hsh
      simpa using hne
  | clsThing => exact hc.clsThing
  | clsNothing1 => exact hc.clsNothing1
  | clsInt1 _ _ hl hne ht ihgc ih =>
      have hta := holds_typedAll hc.typedAllBase hc.typedAllStep ihgc hne hl ht
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.clsInt1 _ _ _ ih hta
  | clsInt2 _ _ hm _ ihgc ih1 ih2 =>
      have hlm := holds_listMember hc.listMemBase hc.listMemStep ihgc hm
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.clsInt2 _ _ _ _ ih1 hlm ih2
  | clsUni _ _ hm _ ihgc ih1 ih2 =>
      have hlm := holds_listMember hc.listMemBase hc.listMemStep ihgc hm
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.clsUni _ _ _ _ ih1 hlm ih2
  | clsSvf1 _ _ _ _ ih1 ih2 ih3 ih4 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ⊢
      exact hc.clsSvf1 _ _ _ _ _ ih1 ih2 ih3 ih4
  | clsSvf2 _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.clsSvf2 _ _ _ _ ih1 ih2 ih3
  | clsAvf _ _ _ _ ih1 ih2 ih3 ih4 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ⊢
      exact hc.clsAvf _ _ _ _ _ ih1 ih2 ih3 ih4
  | clsHv1 _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.clsHv1 _ _ _ _ ih1 ih2 ih3
  | clsHv2 _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.clsHv2 _ _ _ _ ih1 ih2 ih3
  | clsHs1 _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.clsHs1 _ _ _ ih1 ih2 ih3
  | clsHs2 _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.clsHs2 _ _ _ ih1 ih2 ih3
  | clsMaxc2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ih5 ⊢
      exact hc.clsMaxc2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | clsOo _ _ hm ihgc ih =>
      have hlm := holds_listMember hc.listMemBase hc.listMemStep ihgc hm
      rw [denot_toTerm] at hlm
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.clsOo _ _ _ ih hlm
  | caxSco _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.caxSco _ _ _ ih1 ih2
  | caxEqc1 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.caxEqc1 _ _ _ ih1 ih2
  | caxEqc2 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.caxEqc2 _ _ _ ih1 ih2
  | scmClsSelf _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmClsSelf _ ih
  | scmClsEqc _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmClsEqc _ ih
  | scmClsThing _ ih =>
      simp only [TripleHolds] at ih ⊢
      exact hc.scmClsThing _ ih
  | scmClsNothing _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmClsNothing _ ih
  | scmSco _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmSco _ _ _ ih1 ih2
  | scmEqc1a _ ih =>
      simp only [TripleHolds] at ih ⊢
      exact hc.scmEqc1a _ _ ih
  | scmEqc1b _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmEqc1b _ _ ih
  | scmEqc2 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmEqc2 _ _ ih1 ih2
  | scmSpo _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmSpo _ _ _ ih1 ih2
  | scmEqp1a _ ih =>
      simp only [TripleHolds] at ih ⊢
      exact hc.scmEqp1a _ _ ih
  | scmEqp1b _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmEqp1b _ _ ih
  | scmEqp2 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmEqp2 _ _ ih1 ih2
  | scmDom1 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmDom1 _ _ _ ih1 ih2
  | scmDom2 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmDom2 _ _ _ ih1 ih2
  | scmRng1 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmRng1 _ _ _ ih1 ih2
  | scmRng2 _ _ ih1 ih2 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ⊢
      exact hc.scmRng2 _ _ _ ih1 ih2
  | scmOpSub _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmOpSub _ ih
  | scmOpEqp _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmOpEqp _ ih
  | scmDpSub _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmDpSub _ ih
  | scmDpEqp _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmDpEqp _ ih
  | scmSvf1 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ih5 ⊢
      exact hc.scmSvf1 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | scmSvf2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ih5 ⊢
      exact hc.scmSvf2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | scmAvf1 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ih5 ⊢
      exact hc.scmAvf1 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | scmAvf2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ih5 ⊢
      exact hc.scmAvf2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | scmHv _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ih5 ⊢
      exact hc.scmHv _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | scmInt _ _ hm ihgc ih =>
      have hlm := holds_listMember hc.listMemBase hc.listMemStep ihgc hm
      simp only [TripleHolds] at ih ⊢
      exact hc.scmInt _ _ _ ih hlm
  | scmUni _ _ hm ihgc ih =>
      have hlm := holds_listMember hc.listMemBase hc.listMemStep ihgc hm
      rw [denot_toTerm] at hlm
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.scmUni _ _ _ ih hlm
  | eqDiffSym _ ih =>
      simp only [TripleHolds, denot_toTerm] at ih ⊢
      exact hc.eqDiffSym _ _ ih
  | pdwToDiff _ _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.pdwToDiff _ _ _ _ _ ih1 ih2 ih3
  | caxDwToDiff _ _ _ _ ih1 ih2 ih3 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ⊢
      exact hc.caxDwToDiff _ _ _ _ ih1 ih2 ih3
  | fpDiffToDiff _ _ _ _ _ ih1 ih2 ih3 ih4 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ⊢
      exact hc.fpDiffToDiff _ _ _ _ _ ih1 ih2 ih3 ih4
  | ifpDiffToDiff _ _ _ _ _ ih1 ih2 ih3 ih4 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ⊢
      exact hc.ifpDiffToDiff _ _ _ _ _ ih1 ih2 ih3 ih4
  | chainToTrans _ _ hl ihgc ih =>
      cases hl with
      | cons hnil1 hf1 hr1 htail1 =>
          cases htail1 with
          | cons hnil2 hf2 hr2 htail2 =>
              cases htail2 with
              | nil =>
                  have h1 := ihgc _ hf1
                  have h2 := ihgc _ hr1
                  have h3 := ihgc _ hf2
                  have h4 := ihgc _ hr2
                  simp only [TripleHolds, denot_toTerm] at h1 h2 h3 h4 ih ⊢
                  exact hc.chainToTrans _ _ _ ih h1 h2 h3 h4
  | @prpRfl pr j gc hgc hdecl hind ihgc ih =>
      simp only [iriIndividuals, List.mem_flatMap] at hind
      obtain ⟨u, hu, hi⟩ := hind
      obtain ⟨us, up, uo⟩ := u
      have hu' := ihgc _ hu
      rcases List.mem_append.mp hi with hs | ho
      · cases us with
        | iri w =>
            have hw : j = w := by simpa using hs
            subst hw
            simp only [TripleHolds] at hu' ih ⊢
            exact hc.prpRflS _ _ _ _ ih hu'
        | bnode b => exact absurd hs (by simp)
      · cases uo with
        | iri w =>
            have hw : j = w := by simpa using ho
            subst hw
            simp only [TripleHolds] at hu' ih ⊢
            exact hc.prpRflO _ _ _ _ ih hu'
        | bnode b => exact absurd ho (by simp)
        | literal l => exact absurd ho (by simp)
        | tripleTerm s p o => exact absurd ho (by simp)
  | @xsdAxioms d t hd hx hax ih =>
      obtain ⟨a, pr, b, rfl⟩ := xsdAxiomTriples_shape _ hax
      simp only [drivesXsdAxioms, Bool.and_eq_true] at hx
      obtain ⟨hp, ho⟩ := hx
      have hpmem : d.p ∈ datatypePositionPredicates :=
        List.contains_iff_mem.mp hp
      obtain ⟨ds, dp, dobj⟩ := d
      cases dobj with
      | iri w =>
          simp only [TripleHolds] at ih ⊢
          exact hc.xsdAxioms _ hpmem w (by simpa using ho) a pr b hax _ ih
      | bnode b' => simp at ho
      | literal l => simp at ho
      | tripleTerm s p o => simp at ho
  | dtRangeIntersect _ _ hlic ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.dtRangeIntersect _ _ _ hlic _ ih1 ih2
  | premiseFreeAxiom hax =>
      obtain ⟨a, pr, b, rfl⟩ := premiseFreeAxioms_shape _ hax
      exact hc.premiseFreeAxiom _ _ _ hax
  | @caxDwToComplement c1 c2 t hdecl hax ih =>
      simp only [TripleHolds] at ih
      have hz2 := compWitness_props (hc.compDw c2 ⟨i.iIri c1, Or.inl ih⟩)
      have hz1 := compWitness_props (hc.compDw c1 ⟨i.iIri c2, Or.inr ih⟩)
      obtain ⟨hcl2, hco2, hdwa2, hdwb2, -⟩ := hz2
      obtain ⟨hcl1, hco1, hdwa1, hdwb1, -⟩ := hz1
      simp only [complementWitnessTriples, complementWitnessPair,
                 List.mem_append, List.mem_cons, List.not_mem_nil,
                 or_false] at hax
      rcases hax with ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)
      · simp only [TripleHolds]
        rw [denot_compWitness]
        exact hcl2
      · simp only [TripleHolds]
        rw [denot_compWitness]
        exact hco2
      · simp only [TripleHolds]
        rw [denot_compWitness]
        exact hcl1
      · simp only [TripleHolds]
        rw [denot_compWitness]
        exact hco1
      · simp only [TripleHolds, denot_toTerm]
        rw [denot_compWitness]
        exact hdwa2 _ ih
      · simp only [TripleHolds, denot_toTerm]
        rw [denot_compWitness]
        exact hdwb1 _ ih
  | @clsMaxqc1ToComplement x u y1s y2s p c t hmqc honp honc hty h1 h2 hy1c
      hdiff hax ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 =>
      simp only [TripleHolds, denot_toTerm] at ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8
      have hbody : MqcBody i c _ _ _ _ (i.iIri p) :=
        ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7, ih8⟩
      have hz := compWitness_props (hc.compMqc c ⟨_, _, _, _, _, hbody⟩)
      obtain ⟨hcl, hco, -, -, hmq⟩ := hz
      simp only [complementTypeTriples, complementWitnessPair,
                 List.mem_append, List.mem_cons, List.not_mem_nil,
                 or_false] at hax
      rcases hax with (rfl | rfl) | rfl
      · simp only [TripleHolds]
        rw [denot_compWitness]
        exact hcl
      · simp only [TripleHolds]
        rw [denot_compWitness]
        exact hco
      · simp only [TripleHolds, denot_toTerm]
        rw [denot_compWitness]
        exact hmq _ _ _ _ _ hbody
  | @minCard1Comprehension p t hdecl hax ih =>
      simp only [TripleHolds] at ih
      have hz := minc1Witness_props (hc.minc1 _ ih)
      obtain ⟨hr, hop, hn1, hi1⟩ := hz
      simp only [minCard1WitnessTriples, List.mem_cons, List.not_mem_nil,
                 or_false] at hax
      rcases hax with rfl | rfl | rfl | rfl
      · simp only [TripleHolds]
        rw [denot_minc1Witness]
        exact hr
      · simp only [TripleHolds]
        rw [denot_minc1Witness]
        exact hop
      · simp only [TripleHolds]
        rw [denot_minc1Witness]
        exact hn1
      · simp only [TripleHolds]
        rw [denot_minc1Witness]
        exact hi1
  | caxAdcToDw _ _ _ h1 h2 hne ihgc ih1 ih2 =>
      have hlm1 := holds_listMember hc.listMemBase hc.listMemStep ihgc h1
      have hlm2 := holds_listMember hc.listMemBase hc.listMemStep ihgc h2
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.caxAdcToDw _ _ hne _ _ ih1 ih2 hlm1 hlm2
  | invFlipDomRng _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invFlipDomRng _ _ _ ih1 ih2
  | invFlipRngDom _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invFlipRngDom _ _ _ ih1 ih2
  | invFlipDomRngRev _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invFlipDomRngRev _ _ _ ih1 ih2
  | invFlipRngDomRev _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invFlipRngDomRev _ _ _ ih1 ih2
  | invFpIfp _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invFpIfp _ _ ih1 ih2
  | invIfpFp _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invIfpFp _ _ ih1 ih2
  | invFpIfpRev _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invFpIfpRev _ _ ih1 ih2
  | invIfpFpRev _ _ ih1 ih2 =>
      simp only [TripleHolds] at ih1 ih2 ⊢
      exact hc.invIfpFpRev _ _ ih1 ih2

/-! ## The clash rows are unsatisfiable configurations -/

/-- The one restriction the clash schema carries beyond the engine:
`owl:AllDisjointClasses` member lists whose members are all IRIs (the
schema's cax-adc family is indexed by IRI pairs — the non-IRI-member
gap is recorded in the stage notes). -/
def AdcMembersIri (g : Graph) : Prop :=
  ∀ (y : Subject) (lst ci : Term),
    (⟨y, rdfType, Term.iri owlAllDisjointClasses⟩ : Triple) ∈ g →
    (⟨y, owlMembers, lst⟩ : Triple) ∈ g → ListMember g lst ci →
    ∃ w : WfIri, ci = .iri w

/-- The same narrowing for the eq-diff2 / eq-diff3 rows: the members of
an `owl:AllDifferent` collection are IRIs. Both rows read their member
pair through the IRI-indexed schema family, exactly as cax-adc does. -/
def DiffMembersIri (g : Graph) : Prop :=
  ∀ (y : Subject) (lst ci : Term),
    (⟨y, rdfType, Term.iri owlAllDifferent⟩ : Triple) ∈ g →
    ((⟨y, owlMembers, lst⟩ : Triple) ∈ g ∨
     (⟨y, owlDistinctMembers, lst⟩ : Triple) ∈ g) →
    ListMember g lst ci → ∃ w : WfIri, ci = .iri w

theorem subj_toTerm_iri {s : Subject} {w : WfIri}
    (h : s.toTerm = Term.iri w) : s = Subject.iri w := by
  cases s with
  | iri v => simp only [Subject.toTerm, Term.iri.injEq] at h; rw [h]
  | bnode b => simp [Subject.toTerm] at h

/-- **Clash truth-refutation**: a graph carrying a `Clash`
configuration is false under every assignment in every interpretation
meeting the clash conditions (plus the two list axioms, which the
cax-adc row reads its member premises through). -/
theorem rl_clash_holds_false {i : Interp} (hcc : RlClashConditions i)
    (hlmB : RlCondListMemBase i) (hlmS : RlCondListMemStep i) {g : Graph}
    (hadc : AdcMembersIri g) (hdiff : DiffMembersIri g)
    {A : BnodeAssignment i.idom}
    (hA : HoldsAll i A g) (h : Clash g) : False := by
  cases h with
  | eqDiff1 h1 h2 =>
      have t1 := hA _ h1
      have t2 := hA _ h2
      exact hcc.eqDiff1 _ _ ⟨t1, t2⟩
  | prpIrp hdecl hd =>
      have t1 := hA _ hdecl
      have t2 := hA _ hd
      simp only [TripleHolds, denot_toTerm] at t1 t2
      exact hcc.prpIrp _ _ ⟨t1, t2⟩
  | prpAsyp hdecl h1 h2 =>
      have t1 := hA _ hdecl
      have t2 := hA _ h1
      have t3 := hA _ h2
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3
      exact hcc.prpAsyp _ _ _ ⟨t1, t2, t3⟩
  | prpPdw hdecl h1 h2 =>
      have t1 := hA _ hdecl
      have t2 := hA _ h1
      have t3 := hA _ h2
      simp only [TripleHolds] at t1 t2 t3
      exact hcc.prpPdw _ _ _ _ ⟨t1, t2, t3⟩
  | prpNpa1 hsrc hap hti hd =>
      have t1 := hA _ hsrc
      have t2 := hA _ hap
      have t3 := hA _ hti
      have t4 := hA _ hd
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3 t4
      exact hcc.prpNpa1 _ _ _ _ ⟨t1, t2, t3, t4⟩
  | prpNpa2 hsrc hap htv hd =>
      have t1 := hA _ hsrc
      have t2 := hA _ hap
      have t3 := hA _ htv
      have t4 := hA _ hd
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3 t4
      exact hcc.prpNpa2 _ _ _ _ ⟨t1, t2, t3, t4⟩
  | clsNothing2 h1 => exact hcc.clsNothing2 _ (hA _ h1)
  | clsCom hdecl h1 h2 =>
      have t1 := hA _ hdecl
      have t2 := hA _ h1
      have t3 := hA _ h2
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3
      exact hcc.clsCom _ _ _ ⟨t1, t2, t3⟩
  | clsMaxc1 hmc honp hty hd =>
      have t1 := hA _ hmc
      have t2 := hA _ honp
      have t3 := hA _ hty
      have t4 := hA _ hd
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3 t4
      exact hcc.clsMaxc1 _ _ _ _ ⟨t1, t2, t3, t4⟩
  | clsMaxqc1 hmqc honp honc hty hd hyc =>
      have t1 := hA _ hmqc
      have t2 := hA _ honp
      have t3 := hA _ honc
      have t4 := hA _ hty
      have t5 := hA _ hd
      have t6 := hA _ hyc
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3 t4 t5 t6
      exact hcc.clsMaxqc1 _ _ _ _ _ ⟨t1, t2, t3, t4, t5, t6⟩
  | clsMaxqc2 hmqc honp honc hty hd =>
      have t1 := hA _ hmqc
      have t2 := hA _ honp
      have t3 := hA _ honc
      have t4 := hA _ hty
      have t5 := hA _ hd
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3 t4 t5
      exact hcc.clsMaxqc2 _ _ _ _ ⟨t1, t2, t3, t4, t5⟩
  | caxDw hdecl h1 h2 =>
      have t1 := hA _ hdecl
      have t2 := hA _ h1
      have t3 := hA _ h2
      simp only [TripleHolds, denot_toTerm] at t1 t2 t3
      exact hcc.caxDw _ _ _ ⟨t1, t2, t3⟩
  | @caxAdc y z lst ci cj hty hmem h1 h2 hne t1m t2m =>
      obtain ⟨w1, rfl⟩ := hadc _ _ _ hty hmem h1
      obtain ⟨w2, rfl⟩ := hadc _ _ _ hty hmem h2
      have hwne : w1 ≠ w2 := fun he => hne (by rw [he])
      have u1 := hA _ hty
      have u2 := hA _ hmem
      have u3 := hA _ t1m
      have u4 := hA _ t2m
      have hlm1 := holds_listMember hlmB hlmS hA h1
      have hlm2 := holds_listMember hlmB hlmS hA h2
      simp only [TripleHolds] at u1 u2 u3 u4
      exact hcc.caxAdc w1 w2 hwne _ _ _ ⟨u1, u2, hlm1, hlm2, u3, u4⟩
  | @eqDiff2 y zi lst zj hty hmem h1 h2 hne hsame =>
      obtain ⟨w1, hw1⟩ := hdiff _ _ _ hty (Or.inl hmem) h1
      obtain ⟨w2, rfl⟩ := hdiff _ _ _ hty (Or.inl hmem) h2
      obtain rfl : zi = Subject.iri w1 := subj_toTerm_iri hw1
      have hwne : w1 ≠ w2 := by
        intro he
        exact hne (by rw [he]; rfl)
      have u1 := hA _ hty
      have u2 := hA _ hmem
      have u3 := hA _ hsame
      have hlm1 := holds_listMember hlmB hlmS hA h1
      have hlm2 := holds_listMember hlmB hlmS hA h2
      simp only [TripleHolds] at u1 u2 u3
      exact hcc.eqDiff2 w1 w2 hwne _ _ ⟨u1, u2, hlm1, hlm2, u3⟩
  | @eqDiff3 y zi lst zj hty hmem h1 h2 hne hsame =>
      obtain ⟨w1, hw1⟩ := hdiff _ _ _ hty (Or.inr hmem) h1
      obtain ⟨w2, rfl⟩ := hdiff _ _ _ hty (Or.inr hmem) h2
      obtain rfl : zi = Subject.iri w1 := subj_toTerm_iri hw1
      have hwne : w1 ≠ w2 := by
        intro he
        exact hne (by rw [he]; rfl)
      have u1 := hA _ hty
      have u2 := hA _ hmem
      have u3 := hA _ hsame
      have hlm1 := holds_listMember hlmB hlmS hA h1
      have hlm2 := holds_listMember hlmB hlmS hA h2
      simp only [TripleHolds] at u1 u2 u3
      exact hcc.eqDiff3 w1 w2 hwne _ _ ⟨u1, u2, hlm1, hlm2, u3⟩
  | @prpAdp y u lst v p1 p2 hty hmem h1 h2 hne t1 t2 =>
      have u1 := hA _ hty
      have u2 := hA _ hmem
      have u3 := hA _ t1
      have u4 := hA _ t2
      have hlm1 := holds_listMember hlmB hlmS hA h1
      have hlm2 := holds_listMember hlmB hlmS hA h2
      simp only [TripleHolds] at u1 u2 u3 u4
      exact hcc.prpAdp p1 p2 hne _ _ _ _ ⟨u1, u2, hlm1, hlm2, u3, u4⟩

end L4Factoidal.OWL.RL
