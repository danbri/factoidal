/-
L4Factoidal.OWL.RLHerbrand — the completeness model for the OWL 2
RL/RDF truth layer: an enriched Herbrand interpretation of a saturated
closure satisfies every row condition of `OWL/RLSemantics.lean`.

Stage 4 of https://github.com/danbri/factoidal/issues/598. This is
what mediates the design document §4.4's `unified_owlRl_complete_ground`
through T4: a `CL` interpretation in the schema class is obtained as
`liftInterp (rlHerb (closure g fuel))`, and the decode lemma at the
end turns satisfaction of a ground conclusion back into closure
membership.

## The model

`RDF/Semantics.lean`'s `herbrand` (domain = the RDF terms, everything
denoting itself, IEXT = the graph read off syntactically) EXTENDED at
the two reserved helper predicates: `urn:cl:def:listMember` reads
`ListMember`, `urn:cl:def:typedAllMembers` reads non-empty
`ListDenotes`+`TypesAll`. The `iTt` quarantine point is the same
constant as in `herbrand`, which is why the fragment excludes
triple-term objects.

## The fragment `RlHerbFrag`, and why each clause exists

The conditions mirror the `Derives` constructors, whose slots are
TYPED (`Subject`/`WfIri`) where the conditions quantify over the whole
domain. The Herbrand model closes that gap only on graphs where the
mismatch cannot fire:

* **(a) every object is an IRI or a blank node.** eq-ref (object
  form) demands `y owl:sameAs y` for every object `y`; a literal
  object would demand a literal SUBJECT, which `RDF/Core.lean`'s
  `Subject` cannot express (the same term-algebra boundary the
  `RLRules.lean` header records for dt-eq/dt-diff). Consequence: the
  completeness theorem does not reach graphs using cardinality
  literals or the comprehension rows' literal emissions — a recorded
  gap, not a defect.
* **(b) `rdf:nil` heads no cons cell.** `ListDenotes.cons` carries
  the `≠ rdf:nil` guard; the syntactic model must be able to
  reconstruct it from the atoms.
* **(c) `owl:disjointWith` triples have IRI subjects and objects.**
  The shared complement witness's `∀ a` clauses (`CompProps`) range
  over every disjointness partner, and the engine mints subclass
  edges only for IRI pairs.
* **(d) no reserved IRI occurs in any position.** A user-asserted
  `urn:cl:def:` triple would fire the helper-consuming rows on facts
  the engine never derived.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RLSemantics

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## The enriched Herbrand interpretation -/

/-- `uTypedAll`'s reading: `y` is a subject typed into every member of
the NON-EMPTY collection `l`. -/
def TypedAllSem (c : Graph) (y l : Term) : Prop :=
  ∃ (ys : Subject) (cs : List Term), cs ≠ [] ∧ y = ys.toTerm ∧
    ListDenotes c l cs ∧ TypesAll c ys cs

/-- The enriched IEXT: the graph read syntactically, plus the two
helper predicates read by their list semantics. -/
def rlHerbIext (c : Graph) (p x y : Term) : Prop :=
  herbIext c p x y ∨
  (p = .iri uListMem ∧ ListMember c x y) ∨
  (p = .iri uTypedAll ∧ TypedAllSem c x y)

/-- The completeness model (module header). -/
def rlHerb (c : Graph) : Interp :=
  { idom := Term
  , idomWit := .bnode ""
  , iIri := fun w => .iri w
  , iLit := fun l => .literal l
  , iTt := fun _ _ _ => .bnode ""
  , iext := rlHerbIext c }

/-! ## The fragment -/

def herbFragTriple (t : Triple) : Bool :=
  (match t.o with | .iri _ => true | .bnode _ => true | _ => false) &&
  !(t.s == Subject.iri rdfNil && (t.p == rdfFirst || t.p == rdfRest)) &&
  (!(t.p == owlDisjointWith) ||
    ((match t.s with | .iri _ => true | _ => false) &&
     (match t.o with | .iri _ => true | _ => false))) &&
  tripleIrisNonReserved t

/-- The Herbrand fragment (module header, clauses (a)-(d)).
Executable: `rlHerbFragCheck`. -/
def RlHerbFrag (c : Graph) : Prop := ∀ t ∈ c, herbFragTriple t = true

def rlHerbFragCheck (c : Graph) : Bool := c.all herbFragTriple

theorem rlHerbFrag_of_check {c : Graph} (h : rlHerbFragCheck c = true) :
    RlHerbFrag c :=
  fun t ht => List.all_eq_true.mp h t ht

section FragAccessors

variable {c : Graph} (hfrag : RlHerbFrag c)
include hfrag

theorem frag_obj_subject {t : Triple} (ht : t ∈ c) :
    ∃ os : Subject, t.o = os.toTerm := by
  have h := hfrag t ht
  simp only [herbFragTriple, Bool.and_eq_true] at h
  have := h.1.1.1
  cases ho : t.o with
  | iri w => exact ⟨.iri w, rfl⟩
  | bnode b => exact ⟨.bnode b, rfl⟩
  | literal l => rw [ho] at this; simp at this
  | tripleTerm s p o => rw [ho] at this; simp at this

theorem frag_not_nil_cons {t : Triple} (ht : t ∈ c)
    (hp : t.p = rdfFirst ∨ t.p = rdfRest) : t.s ≠ Subject.iri rdfNil := by
  have h := hfrag t ht
  simp only [herbFragTriple, Bool.and_eq_true] at h
  have h2 := h.1.1.2
  intro hs
  rw [hs] at h2
  rcases hp with hp | hp <;> rw [hp] at h2 <;> simp at h2

theorem frag_dw {t : Triple} (ht : t ∈ c) (hp : t.p = owlDisjointWith) :
    (∃ w1 : WfIri, t.s = Subject.iri w1) ∧
    (∃ w2 : WfIri, t.o = Term.iri w2) := by
  have h := hfrag t ht
  simp only [herbFragTriple, Bool.and_eq_true] at h
  have h3 := h.1.2
  rw [hp] at h3
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or,
             Bool.and_eq_true] at h3
  constructor
  · cases hs : t.s with
    | iri w => exact ⟨w, rfl⟩
    | bnode b => rw [hs] at h3; simp at h3
  · cases ho : t.o with
    | iri w => exact ⟨w, rfl⟩
    | bnode b => rw [ho] at h3; simp at h3
    | literal l => rw [ho] at h3; simp at h3
    | tripleTerm s p o => rw [ho] at h3; simp at h3

theorem frag_iris {t : Triple} (ht : t ∈ c) :
    tripleIrisNonReserved t = true := by
  have h := hfrag t ht
  simp only [herbFragTriple, Bool.and_eq_true] at h
  exact h.2

theorem frag_ttFree {t : Triple} (ht : t ∈ c) : TermTtFree t.o := by
  have h := hfrag t ht
  simp only [herbFragTriple, Bool.and_eq_true] at h
  have := h.1.1.1
  cases ho : t.o with
  | iri w => trivial
  | bnode b => trivial
  | literal l => trivial
  | tripleTerm s p o => rw [ho] at this; simp at this

end FragAccessors

/-! ## Small syntactic bridges -/

theorem toTerm_subjTerm (s : Subject) : s.toTerm = subjTerm s := by
  cases s <;> rfl

theorem subjTerm_iri {s : Subject} {w : WfIri}
    (h : subjTerm s = Term.iri w) : s = Subject.iri w := by
  cases s with
  | iri v => simp only [subjTerm, Term.iri.injEq] at h; rw [h]
  | bnode b => simp [subjTerm] at h

theorem toTerm_ne_nil {s : Subject} (h : s ≠ Subject.iri rdfNil) :
    s.toTerm ≠ Term.iri rdfNil := by
  intro he
  apply h
  rw [toTerm_subjTerm] at he
  exact subjTerm_iri he

/-! ## Atom decode / encode -/

section DecodeEncode

variable {c : Graph}

/-- Encode: a graph triple is a true atom. -/
theorem herb_encode {s : Subject} {p : WfIri} {o : Term}
    (h : (⟨s, p, o⟩ : Triple) ∈ c) :
    rlHerbIext c (.iri p) (subjTerm s) o :=
  Or.inl ⟨_, h, rfl, rfl, rfl⟩

/-- Decode at a NON-RESERVED predicate: only the syntactic reading
applies. -/
theorem herb_decode {q : WfIri} (hq : rlReservedIri q = false)
    {x y : Term} (h : rlHerbIext c (.iri q) x y) :
    ∃ (s : Subject) (o : Term), (⟨s, q, o⟩ : Triple) ∈ c ∧
      x = subjTerm s ∧ y = o := by
  rcases h with ⟨t, ht, hp, hx, hy⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · injection hp with h'
    refine ⟨t.s, t.o, ?_, hx, hy⟩
    rw [h']
    exact ht
  · injection hp with h'
    rw [h'] at hq
    exact absurd hq (by decide)
  · injection hp with h'
    rw [h'] at hq
    exact absurd hq (by decide)

/-- Decode the `uListMem` helper (its syntactic reading is barred by
fragment clause (d)). -/
theorem listMem_decode (hfrag : RlHerbFrag c) {x y : Term}
    (h : rlHerbIext c (.iri uListMem) x y) : ListMember c x y := by
  rcases h with ⟨t, ht, hp, _, _⟩ | ⟨_, hm⟩ | ⟨hp, _⟩
  · exfalso
    have hnr := tin_p (frag_iris hfrag ht)
    injection hp with h'
    rw [← h'] at hnr
    exact absurd hnr (by decide)
  · exact hm
  · exfalso
    injection hp with h'
    exact absurd h' (by decide)

theorem typedAll_decode (hfrag : RlHerbFrag c) {x y : Term}
    (h : rlHerbIext c (.iri uTypedAll) x y) : TypedAllSem c x y := by
  rcases h with ⟨t, ht, hp, _, _⟩ | ⟨hp, _⟩ | ⟨_, hm⟩
  · exfalso
    have hnr := tin_p (frag_iris hfrag ht)
    injection hp with h'
    rw [← h'] at hnr
    exact absurd hnr (by decide)
  · exfalso
    injection hp with h'
    exact absurd h' (by decide)
  · exact hm

/-- No non-reserved atom relates anything to a literal, on the
fragment (clause (a)) — the vacuity engine for the cardinality rows. -/
theorem no_literal_object (hfrag : RlHerbFrag c) {q : WfIri}
    (hq : rlReservedIri q = false) {x : Term} {l : WfLiteral} :
    ¬ rlHerbIext c (.iri q) x (.literal l) := by
  intro h
  obtain ⟨s, o, hm, _, ho⟩ := herb_decode hq h
  obtain ⟨os, hos⟩ := frag_obj_subject hfrag hm
  rw [show (⟨s, q, o⟩ : Triple).o = o from rfl] at hos
  rw [← ho] at hos
  cases os <;> simp [Subject.toTerm] at hos

end DecodeEncode

/-! ## Backing and replacement helpers

`hcut` is the closure property the saturated closure provides (via T2
+ T4): everything one `Derives` step away from `c` is already in `c`. -/

theorem toTerm_inj {a b : Subject} (h : a.toTerm = b.toTerm) : a = b := by
  rw [toTerm_subjTerm, toTerm_subjTerm] at h
  exact subjTerm_injective h

section Helpers

variable {c : Graph} (hcut : ∀ {t : Triple}, Derives c t → t ∈ c)

theorem listMember_head_backed {x y : Term} (h : ListMember c x y) :
    ∃ t ∈ c, x = t.s.toTerm := by
  cases h with
  | here hf => exact ⟨_, hf, rfl⟩
  | there hr _ => exact ⟨_, hr, rfl⟩

theorem listMember_object_backed {x y : Term} (h : ListMember c x y) :
    ∃ n : Subject, (⟨n, rdfFirst, y⟩ : Triple) ∈ c := by
  induction h with
  | here hf => exact ⟨_, hf⟩
  | there _ _ ih => exact ih

include hcut

/-- Every subject of a graph triple is self-`owl:sameAs` (eq-ref). -/
theorem self_sameAs_subj {t : Triple} (ht : t ∈ c) :
    rlHerbIext c (.iri owlSameAs) t.s.toTerm t.s.toTerm := by
  have hd := hcut (Derives.eqRefS (Derives.base ht))
  have := herb_encode hd
  rwa [← toTerm_subjTerm] at this

variable (hfrag : RlHerbFrag c)
include hfrag

/-- Every object of a graph triple is self-`owl:sameAs` (eq-ref,
object form; fragment clause (a) recovers the subject shape). -/
theorem self_sameAs_obj {t : Triple} (ht : t ∈ c) :
    rlHerbIext c (.iri owlSameAs) t.o t.o := by
  obtain ⟨os, ho⟩ := frag_obj_subject hfrag ht
  rw [ho]
  have hd := hcut (Derives.eqRefO (Derives.base (show
    (⟨t.s, t.p, os.toTerm⟩ : Triple) ∈ c by rw [← ho]; exact ht)))
  have := herb_encode hd
  rwa [← toTerm_subjTerm] at this

omit hfrag

/-- `eq-rep-s` transports list-headship along `owl:sameAs`. -/
theorem listMember_replace_head {s1 os' : Subject}
    (hsame : (⟨s1, owlSameAs, os'.toTerm⟩ : Triple) ∈ c) {x0 y : Term}
    (h : ListMember c x0 y) (hx : x0 = s1.toTerm) :
    ListMember c os'.toTerm y := by
  cases h with
  | @here node e hf =>
      have hn : node = s1 := toTerm_inj hx
      subst hn
      exact ListMember.here
        (hcut (Derives.eqRepS (Derives.base hsame) (Derives.base hf)))
  | @there node tail e hr htail =>
      have hn : node = s1 := toTerm_inj hx
      subst hn
      exact ListMember.there
        (hcut (Derives.eqRepS (Derives.base hsame) (Derives.base hr))) htail

/-- `eq-rep-o` transports list membership along `owl:sameAs`. -/
theorem listMember_replace_mem {so : Subject} {oo : Term}
    (hsame : (⟨so, owlSameAs, oo⟩ : Triple) ∈ c) {l y0 : Term}
    (h : ListMember c l y0) (hy : y0 = so.toTerm) : ListMember c l oo := by
  revert hy
  induction h with
  | here hf =>
      intro hy
      subst hy
      exact ListMember.here
        (hcut (Derives.eqRepO (Derives.base hsame) (Derives.base hf)))
  | there hr _ ih => intro hy; exact ListMember.there hr (ih hy)

/-- `eq-rep-s` transports the typed-all reading's individual. -/
theorem typedAllSem_replace_head {s1 os' : Subject}
    (hsame : (⟨s1, owlSameAs, os'.toTerm⟩ : Triple) ∈ c) {l : Term}
    (h : TypedAllSem c s1.toTerm l) : TypedAllSem c os'.toTerm l := by
  obtain ⟨ys, cs, hne, hy, hld, hty⟩ := h
  have hys : ys = s1 := toTerm_inj hy.symm
  subst hys
  refine ⟨os', cs, hne, rfl, hld, ?_⟩
  clear hy hld hne
  induction hty with
  | nil => exact TypesAll.nil
  | cons hm _ ih =>
      exact TypesAll.cons
        (hcut (Derives.eqRepS (Derives.base hsame) (Derives.base hm))) ih

include hfrag

/-- `eq-rep-s` on the cons-cell triples transports the typed-all
reading's collection head. -/
theorem typedAllSem_replace_list {so os2 : Subject}
    (hsame : (⟨so, owlSameAs, os2.toTerm⟩ : Triple) ∈ c) {y l0 : Term}
    (h : TypedAllSem c y l0) (hl : l0 = so.toTerm) :
    TypedAllSem c y os2.toTerm := by
  obtain ⟨ys, cs, hne, hy, hld, hty⟩ := h
  cases hld with
  | nil => exact absurd rfl hne
  | @cons node e tail rest hnil hf hr htail =>
      have hn : node = so := toTerm_inj hl
      subst hn
      have hf' := hcut (Derives.eqRepS (Derives.base hsame) (Derives.base hf))
      have hr' := hcut (Derives.eqRepS (Derives.base hsame) (Derives.base hr))
      refine ⟨ys, e :: rest, by simp, hy, ?_, hty⟩
      exact ListDenotes.cons
        (toTerm_ne_nil (frag_not_nil_cons hfrag hf' (Or.inl rfl)))
        hf' hr' htail

omit hcut in
/-- Decode a `SeqIs` reading of the syntactic model into the
collection relation (the whole-sequence direction). -/
theorem seqIs_decode {l : Term} {qs : List Term}
    (h : SeqIs (rlHerb c) l qs) : ListDenotes c l qs := by
  induction qs generalizing l with
  | nil => exact h ▸ ListDenotes.nil
  | cons q qs' ih =>
      obtain ⟨l', hf, hr, hrest⟩ := h
      obtain ⟨n1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hf
      obtain ⟨n2, o2, hm2, hn2, rfl⟩ := herb_decode (by decide) hr
      have hn : n2 = n1 := subjTerm_injective hn2.symm
      subst hn
      rw [← toTerm_subjTerm]
      exact ListDenotes.cons
        (toTerm_ne_nil (frag_not_nil_cons hfrag hm1 (Or.inl rfl)))
        hm1 hm2 (ih hrest)

omit hcut

/-- IRI elements of a graph collection are non-reserved (fragment
clause (d)). -/
theorem listDenotes_iri_nonres {l : Term} {qs : List Term}
    (h : ListDenotes c l qs) :
    ∀ q ∈ qs, ∀ w : WfIri, q = Term.iri w → rlReservedIri w = false := by
  induction h with
  | nil => intro q hq; simp at hq
  | cons hnil hf hr htail ih =>
      intro q hq w hw
      rcases List.mem_cons.mp hq with rfl | hq
      · subst hw
        exact irw_of_termIri (tin_o (frag_iris hfrag hf))
      · exact ih q hq w hw

include hcut

omit hcut hfrag in
/-- Decode a semantic chain along IRI elements into `ChainHolds`. -/
theorem semChain_decode {qs : List Term}
    (hqs : ∀ q ∈ qs, ∀ w : WfIri, q = Term.iri w → rlReservedIri w = false)
    {u w : Term} (h : SemChain (rlHerb c) u qs w) (hne : qs ≠ []) :
    ∃ (su : Subject) (preds : List WfIri), qs = preds.map Term.iri ∧
      u = su.toTerm ∧ ChainHolds c su preds w := by
  induction qs generalizing u with
  | nil => exact absurd rfl hne
  | cons q qs' ih =>
      obtain ⟨v, hquv, hrest⟩ := h
      cases q with
      | iri w0 =>
          have hnr := hqs (Term.iri w0) (List.mem_cons_self ..) w0 rfl
          obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode hnr hquv
          cases qs' with
          | nil =>
              have hw : v = w := hrest
              refine ⟨s1, [w0], rfl, (toTerm_subjTerm s1).symm, ?_⟩
              rw [← hw]
              exact ChainHolds.last hm1
          | cons q2 qs'' =>
              obtain ⟨sv, preds', hqeq, hveq, hch⟩ :=
                ih (fun q hq => hqs q (List.mem_cons_of_mem _ hq)) hrest
                  (by simp)
              rw [hveq] at hm1
              refine ⟨s1, w0 :: preds', by simp [hqeq],
                      (toTerm_subjTerm s1).symm, ?_⟩
              exact ChainHolds.step hm1 hch
      | bnode b0 =>
          exfalso
          rcases hquv with ⟨t, _, hp, _, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp at hp
      | literal l0 =>
          exfalso
          rcases hquv with ⟨t, _, hp, _, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp at hp
      | tripleTerm s0 p0 o0 =>
          exfalso
          rcases hquv with ⟨t, _, hp, _, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp at hp

omit hcut hfrag in
/-- Decode shared key values into `SharesKeyValues`. -/
theorem semShares_decode {sx sy : Subject} {qs : List Term}
    (hqs : ∀ q ∈ qs, ∀ w : WfIri, q = Term.iri w → rlReservedIri w = false)
    (h : SemShares (rlHerb c) sx.toTerm sy.toTerm qs) :
    ∃ preds : List WfIri, qs = preds.map Term.iri ∧
      SharesKeyValues c sx sy preds := by
  induction qs with
  | nil => exact ⟨[], rfl, SharesKeyValues.nil⟩
  | cons q qs' ih =>
      obtain ⟨v, hxv, hyv⟩ := h q (List.mem_cons_self ..)
      cases q with
      | iri w0 =>
          have hnr := hqs (Term.iri w0) (List.mem_cons_self ..) w0 rfl
          obtain ⟨s1, o1, hm1, hx1, rfl⟩ := herb_decode hnr hxv
          obtain ⟨s2, o2, hm2, hy2, ho2⟩ := herb_decode hnr hyv
          have hs1 : s1 = sx := by
            apply subjTerm_injective
            rw [← hx1, toTerm_subjTerm]
          have hs2 : s2 = sy := by
            apply subjTerm_injective
            rw [← hy2, toTerm_subjTerm]
          subst hs1
          subst hs2
          obtain ⟨preds', hqeq, hsh⟩ :=
            ih (fun q hq => hqs q (List.mem_cons_of_mem _ hq))
              (fun q hq => h q (List.mem_cons_of_mem _ hq))
          refine ⟨w0 :: preds', by simp [hqeq], ?_⟩
          refine SharesKeyValues.cons hm1 ?_ hsh
          rw [← ho2] at hm2
          exact hm2
      | bnode b0 =>
          exfalso
          rcases hxv with ⟨t, _, hp, _, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp at hp
      | literal l0 =>
          exfalso
          rcases hxv with ⟨t, _, hp, _, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp at hp
      | tripleTerm s0 p0 o0 =>
          exfalso
          rcases hxv with ⟨t, _, hp, _, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp at hp

end Helpers

/-! ## More decode helpers -/

section Helpers2

variable {c : Graph}

theorem iriIndividuals_of_subj {j : WfIri} {t : Triple} (ht : t ∈ c)
    (hs : t.s = Subject.iri j) : j ∈ iriIndividuals c := by
  simp only [iriIndividuals, List.mem_flatMap]
  refine ⟨t, ht, ?_⟩
  rw [hs]
  simp

theorem iriIndividuals_of_obj {j : WfIri} {t : Triple} (ht : t ∈ c)
    (ho : t.o = Term.iri j) : j ∈ iriIndividuals c := by
  simp only [iriIndividuals, List.mem_flatMap]
  refine ⟨t, ht, ?_⟩
  rw [ho]
  cases t.s <;> simp

theorem listDenotes_head_backed {l : Term} {cs : List Term}
    (h : ListDenotes c l cs) (hne : cs ≠ []) :
    ∃ t ∈ c, l = t.s.toTerm ∧ t.p = rdfFirst := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hnil hf hr htail => exact ⟨_, hf, rfl, rfl⟩

theorem dpp_nonres : ∀ p ∈ datatypePositionPredicates,
    rlReservedIri p = false := by decide

variable (hcut : ∀ {t : Triple}, Derives c t → t ∈ c)
    (hfrag : RlHerbFrag c)
include hcut hfrag

/-- The complement witness's properties, given that its comprehension
pair is in the closure. Parts 3-4 mint their own subclass edges from
the disjointness triples they decode; part 5 is vacuous on the
fragment (clause (a)). -/
theorem herb_compProps {c0 : WfIri}
    (hpair : ∀ t ∈ complementWitnessPair c0, t ∈ c) :
    CompProps (rlHerb c) c0 ((complementWitness c0).toTerm) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm : (⟨complementWitness c0, rdfType, Term.iri owlClass⟩ : Triple) ∈ c :=
      hpair _ (by simp [complementWitnessPair])
    have := herb_encode hm
    show rlHerbIext c (Term.iri RDFS.rdfType) _ _
    rwa [← toTerm_subjTerm] at this
  · have hm : (⟨complementWitness c0, owlComplementOf, Term.iri c0⟩ : Triple) ∈ c :=
      hpair _ (by simp [complementWitnessPair])
    have := herb_encode hm
    rwa [← toTerm_subjTerm] at this
  · intro a' ha'
    obtain ⟨s2, o2, hm2, rfl, ho2⟩ := herb_decode (by decide) ha'
    have ho2' : o2 = Term.iri c0 := ho2.symm
    subst ho2'
    obtain ⟨⟨w2, hs2⟩, -⟩ := frag_dw hfrag hm2 rfl
    subst hs2
    have hedge := hcut (Derives.caxDwToComplement (Derives.base hm2)
      (show (⟨Subject.iri w2, rdfsSubClassOf,
        (complementWitness c0).toTerm⟩ : Triple) ∈
          complementWitnessTriples w2 c0 by
        simp [complementWitnessTriples, complementWitnessPair]))
    exact herb_encode hedge
  · intro a' ha'
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) ha'
    have hs2 : s2 = Subject.iri c0 := subjTerm_iri hx2.symm
    subst hs2
    obtain ⟨-, ⟨w2, ho2⟩⟩ := frag_dw hfrag hm2 rfl
    subst ho2
    have hedge := hcut (Derives.caxDwToComplement (Derives.base hm2)
      (show (⟨Subject.iri w2, rdfsSubClassOf,
        (complementWitness c0).toTerm⟩ : Triple) ∈
          complementWitnessTriples c0 w2 by
        simp [complementWitnessTriples, complementWitnessPair]))
    have := herb_encode hedge
    show rlHerbIext c (Term.iri rdfsSubClassOf) (Term.iri w2) _
    exact this
  · intro x u y1 y2 pe hbody
    exact absurd hbody.1 (no_literal_object hfrag (by decide))

end Helpers2

/-! ## The Herbrand model meets every derivation condition -/

section HerbConditions

variable {c : Graph} (hcut : ∀ {t : Triple}, Derives c t → t ∈ c)
    (hfrag : RlHerbFrag c) (hcons : ¬ Clash c)
include hcut hfrag

omit hcons in
/-- Every row condition holds in `rlHerb c`, for a `Derives`-closed,
clash-free fragment graph. With `RLTheorems`' T2+T4 this instantiates
at `c := closure g fuel`. The `hcons` hypothesis serves the four
`[ext]` differentFrom rows, whose conditions drop the constructors'
syntactic distinctness side conditions. -/
theorem rlHerb_conditions (hcons : ¬ Clash c) :
    RlConditions (rlHerb c) where
  eqRefS := by
    intro p x y hxy
    have h' : rlHerbIext c (Term.iri p) x y := hxy
    show rlHerbIext c (Term.iri owlSameAs) x x
    rcases h' with ⟨t, ht, hp, rfl, -⟩ | ⟨-, hm⟩ | ⟨-, hta⟩
    · rw [← toTerm_subjTerm]
      exact self_sameAs_subj hcut ht
    · obtain ⟨t0, ht0, rfl⟩ := listMember_head_backed hm
      exact self_sameAs_subj hcut ht0
    · obtain ⟨ys, cs, hne, rfl, hld, hty⟩ := hta
      cases hty with
      | nil => exact absurd rfl hne
      | cons hm0 _ => exact self_sameAs_subj hcut hm0
  eqRefP := by
    intro p hp x y hxy
    obtain ⟨s1, o1, hm1, -, -⟩ := herb_decode hp hxy
    exact herb_encode (hcut (Derives.eqRefP (Derives.base hm1)))
  eqRefO := by
    intro p x y hxy
    have h' : rlHerbIext c (Term.iri p) x y := hxy
    show rlHerbIext c (Term.iri owlSameAs) y y
    rcases h' with ⟨t, ht, hp, -, rfl⟩ | ⟨-, hm⟩ | ⟨-, hta⟩
    · exact self_sameAs_obj hcut hfrag ht
    · obtain ⟨n, hm0⟩ := listMember_object_backed hm
      exact self_sameAs_obj hcut hfrag hm0
    · obtain ⟨ys, cs, hne, -, hld, -⟩ := hta
      obtain ⟨t0, ht0, rfl, -⟩ := listDenotes_head_backed hld hne
      exact self_sameAs_subj hcut ht0
  eqSym := by
    intro x y hxy
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hxy
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm1
    have he := herb_encode (hcut (Derives.eqSym (Derives.base hm1)))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  eqTrans := by
    intro x y z h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hy2, rfl⟩ := herb_decode (by decide) h2
    rw [hy2, ← toTerm_subjTerm] at hm1
    exact herb_encode (hcut (Derives.eqTrans (Derives.base hm1)
      (Derives.base hm2)))
  eqRepS := by
    intro p s s' o hss hso
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hss
    obtain ⟨os', rfl⟩ := frag_obj_subject hfrag hm1
    have h' : rlHerbIext c (Term.iri p) (subjTerm s1) o := hso
    show rlHerbIext c (Term.iri p) os'.toTerm o
    rcases h' with ⟨t, ht, hp, hx, rfl⟩ | ⟨hp, hm⟩ | ⟨hp, hta⟩
    · injection hp with hp'
      have hst : t.s = s1 := subjTerm_injective hx.symm
      have ht' : (⟨s1, p, t.o⟩ : Triple) ∈ c := by
        rw [hp', ← hst]
        exact ht
      have he := herb_encode (hcut (Derives.eqRepS (Derives.base hm1)
        (Derives.base ht')))
      rwa [← toTerm_subjTerm] at he
    · exact Or.inr (Or.inl ⟨hp,
        listMember_replace_head hcut hm1 hm (toTerm_subjTerm s1).symm⟩)
    · rw [← toTerm_subjTerm] at hta
      exact Or.inr (Or.inr ⟨hp, typedAllSem_replace_head hcut hm1 hta⟩)
  eqRepP := by
    intro p p' x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri p' := hy1.symm
    subst ho1
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    exact herb_encode (hcut (Derives.eqRepP (Derives.base hm1)
      (Derives.base hm2)))
  eqRepO := by
    intro p s o o' hoo hso
    obtain ⟨so, oo, hm1, hxo, rfl⟩ := herb_decode (by decide) hoo
    obtain ⟨os2, rfl⟩ := frag_obj_subject hfrag hm1
    have h' : rlHerbIext c (Term.iri p) s o := hso
    show rlHerbIext c (Term.iri p) s os2.toTerm
    rcases h' with ⟨t, ht, hp, rfl, rfl⟩ | ⟨hp, hm⟩ | ⟨hp, hta⟩
    · injection hp with hp'
      have ht' : (⟨t.s, p, so.toTerm⟩ : Triple) ∈ c := by
        rw [hp', toTerm_subjTerm, ← hxo]
        exact ht
      exact herb_encode (hcut (Derives.eqRepO (Derives.base hm1)
        (Derives.base ht')))
    · exact Or.inr (Or.inl ⟨hp, listMember_replace_mem hcut hm1 hm
        (hxo.trans (toTerm_subjTerm so).symm)⟩)
    · exact Or.inr (Or.inr ⟨hp, typedAllSem_replace_list hcut hfrag hm1 hta
        (hxo.trans (toTerm_subjTerm so).symm)⟩)
  prpDom := by
    intro p cel x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, rfl⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p := subjTerm_iri hx1.symm
    subst hs1
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    exact herb_encode (hcut (Derives.prpDom (Derives.base hm1)
      (Derives.base hm2)))
  prpRng := by
    intro p cel x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, rfl⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p := subjTerm_iri hx1.symm
    subst hs1
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm2
    have he := herb_encode (hcut (Derives.prpRng (Derives.base hm1)
      (Derives.base hm2)))
    show rlHerbIext c (Term.iri RDFS.rdfType) _ _
    rwa [← toTerm_subjTerm] at he
  prpFp := by
    intro p x y1 y2 hdecl h1 h2
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlFunctionalProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode hnp h1
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode hnp h2
    have hs2 : s2 = s1 := subjTerm_injective hx2.symm
    subst hs2
    obtain ⟨os1, rfl⟩ := frag_obj_subject hfrag hm1
    have he := herb_encode (hcut (Derives.prpFp (Derives.base hm0)
      (Derives.base hm1) (Derives.base hm2)))
    show rlHerbIext c (Term.iri owlSameAs) _ _
    rwa [← toTerm_subjTerm] at he
  prpIfp := by
    intro p x1 x2 y hdecl h1 h2
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlInverseFunctionalProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode hnp h1
    obtain ⟨s2, o2, hm2, rfl, hy2⟩ := herb_decode hnp h2
    rw [← hy2] at hm2
    have he := herb_encode (hcut (Derives.prpIfp (Derives.base hm0)
      (Derives.base hm1) (Derives.base hm2)))
    show rlHerbIext c (Term.iri owlSameAs) _ _
    rwa [← toTerm_subjTerm] at he
  prpSymp := by
    intro p x y hdecl h1
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlSymmetricProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode hnp h1
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm1
    have he := herb_encode (hcut (Derives.prpSymp (Derives.base hm0)
      (Derives.base hm1)))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  prpTrp := by
    intro p x y z hdecl h1 h2
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlTransitiveProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode hnp h1
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode hnp h2
    rw [hx2, ← toTerm_subjTerm] at hm1
    exact herb_encode (hcut (Derives.prpTrp (Derives.base hm0)
      (Derives.base hm1) (Derives.base hm2)))
  prpSpo1 := by
    intro p1 p2 x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p1 := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri p2 := hy1.symm
    subst ho1
    have hnp : rlReservedIri p1 = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    exact herb_encode (hcut (Derives.prpSpo1 (Derives.base hm1)
      (Derives.base hm2)))
  prpSpo2 := by
    intro p l u w qs hne hax hseq hchain
    obtain ⟨s0, o0, hm0, hx0, rfl⟩ := herb_decode (by decide) hax
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have hld := seqIs_decode hfrag hseq
    obtain ⟨su, preds, rfl, rfl, hch⟩ :=
      semChain_decode (listDenotes_iri_nonres hfrag hld) hchain hne
    have hpne : preds ≠ [] := by
      intro he
      rw [he] at hne
      exact hne rfl
    have he := herb_encode (hcut (Derives.prpSpo2
      (fun u hu => Derives.base hu) (Derives.base hm0) hld hpne hch))
    rw [toTerm_subjTerm]
    exact he
  prpEqp1 := by
    intro p1 p2 x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p1 := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri p2 := hy1.symm
    subst ho1
    have hnp : rlReservedIri p1 = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    exact herb_encode (hcut (Derives.prpEqp1 (Derives.base hm1)
      (Derives.base hm2)))
  prpEqp2 := by
    intro p1 p2 x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p1 := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri p2 := hy1.symm
    subst ho1
    have hnp : rlReservedIri p2 = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    exact herb_encode (hcut (Derives.prpEqp2 (Derives.base hm1)
      (Derives.base hm2)))
  prpInv1 := by
    intro p1 p2 x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p1 := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri p2 := hy1.symm
    subst ho1
    have hnp : rlReservedIri p1 = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm2
    have he := herb_encode (hcut (Derives.prpInv1 (Derives.base hm1)
      (Derives.base hm2)))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  prpInv2 := by
    intro p1 p2 x y h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p1 := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri p2 := hy1.symm
    subst ho1
    have hnp : rlReservedIri p2 = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm1))
    obtain ⟨s2, o2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm2
    have he := herb_encode (hcut (Derives.prpInv2 (Derives.base hm1)
      (Derives.base hm2)))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  prpKey := by
    intro cel l x y qs hne hk hseq hx hy hsh
    obtain ⟨s0, o0, hm0, rfl, rfl⟩ := herb_decode (by decide) hk
    have hld := seqIs_decode hfrag hseq
    obtain ⟨sx, ox, hmx, rfl, hox⟩ := herb_decode (by decide) hx
    obtain ⟨sy, oy, hmy, rfl, hoy⟩ := herb_decode (by decide) hy
    have hmx' : (⟨sx, rdfType, s0.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hox]
      exact hmx
    have hmy' : (⟨sy, rdfType, s0.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hoy]
      exact hmy
    rw [← toTerm_subjTerm, ← toTerm_subjTerm (s := sy)] at hsh
    obtain ⟨preds, rfl, hshare⟩ :=
      semShares_decode (listDenotes_iri_nonres hfrag hld) hsh
    have hpne : preds ≠ [] := by
      intro he
      rw [he] at hne
      exact hne rfl
    have he := herb_encode (hcut (Derives.prpKey
      (fun u hu => Derives.base hu) (Derives.base hm0) hld hpne
      (Derives.base hmx') (Derives.base hmy') hshare))
    rw [toTerm_subjTerm] at he
    exact he
  clsThing := herb_encode (hcut Derives.clsThing)
  clsNothing1 := herb_encode (hcut Derives.clsNothing1)
  clsInt1 := by
    intro cel y l h1 h2
    obtain ⟨s0, o0, hm0, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨ys, cs, hne, rfl, hld, hty⟩ := typedAll_decode hfrag h2
    have he := herb_encode (hcut (Derives.clsInt1
      (fun u hu => Derives.base hu) (Derives.base hm0) hld hne hty))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  typedAllBase := by
    intro y l e hf hr hty
    obtain ⟨n1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hf
    obtain ⟨n2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) hr
    have hn2 : n2 = n1 := subjTerm_injective hx2.symm
    subst hn2
    have ho2 : o2 = Term.iri rdfNil := hy2.symm
    subst ho2
    obtain ⟨ys, oy, hmy, rfl, hyy⟩ := herb_decode (by decide) hty
    have hmy' : (⟨ys, rdfType, e⟩ : Triple) ∈ c := by
      rw [hyy]
      exact hmy
    refine Or.inr (Or.inr ⟨rfl, ys, [e], by simp,
      (toTerm_subjTerm ys).symm, ?_, TypesAll.cons hmy' TypesAll.nil⟩)
    rw [← toTerm_subjTerm]
    exact ListDenotes.cons
      (toTerm_ne_nil (frag_not_nil_cons hfrag hm1 (Or.inl rfl)))
      hm1 hm2 ListDenotes.nil
  typedAllStep := by
    intro y l l' e hf hr hty hta
    obtain ⟨n1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hf
    obtain ⟨n2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) hr
    have hn2 : n2 = n1 := subjTerm_injective hx2.symm
    subst hn2
    obtain ⟨ys, oy, hmy, rfl, hyy⟩ := herb_decode (by decide) hty
    have hmy' : (⟨ys, rdfType, e⟩ : Triple) ∈ c := by
      rw [hyy]
      exact hmy
    obtain ⟨ys', cs', hne', hy', hld', hty'⟩ := typedAll_decode hfrag hta
    have hys : ys' = ys := by
      apply subjTerm_injective
      rw [← toTerm_subjTerm, ← hy']
    subst hys
    refine Or.inr (Or.inr ⟨rfl, ys', e :: cs', by simp,
      (toTerm_subjTerm ys').symm, ?_, TypesAll.cons hmy' hty'⟩)
    rw [← toTerm_subjTerm]
    exact ListDenotes.cons
      (toTerm_ne_nil (frag_not_nil_cons hfrag hm1 (Or.inl rfl)))
      hm1 hm2 hld'
  listMemBase := by
    intro l e hf
    obtain ⟨n1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hf
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    rw [← toTerm_subjTerm]
    exact ListMember.here hm1
  listMemStep := by
    intro l l' e hr hlm
    obtain ⟨n1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hr
    have hm := listMem_decode hfrag hlm
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    rw [← toTerm_subjTerm]
    exact ListMember.there hm1 hm
  clsInt2 := by
    intro cel y l ci h1 hlm hy
    obtain ⟨s0, o0, hm0, rfl, rfl⟩ := herb_decode (by decide) h1
    have hm := listMem_decode hfrag hlm
    obtain ⟨ys, oy, hmy, rfl, hoy⟩ := herb_decode (by decide) hy
    have hmy' : (⟨ys, rdfType, s0.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hoy]
      exact hmy
    exact herb_encode (hcut (Derives.clsInt2
      (fun u hu => Derives.base hu) (Derives.base hm0) hm
      (Derives.base hmy')))
  clsUni := by
    intro cel y l ci h1 hlm hy
    obtain ⟨s0, o0, hm0, rfl, rfl⟩ := herb_decode (by decide) h1
    have hm := listMem_decode hfrag hlm
    obtain ⟨ys, oy, hmy, rfl, hoy⟩ := herb_decode (by decide) hy
    have hmy' : (⟨ys, rdfType, ci⟩ : Triple) ∈ c := by
      rw [hoy]
      exact hmy
    have he := herb_encode (hcut (Derives.clsUni
      (fun u hu => Derives.base hu) (Derives.base hm0) hm
      (Derives.base hmy')))
    rw [toTerm_subjTerm] at he
    exact he
  clsSvf1 := by
    intro p x u v yc h1 h2 h3 h4
    obtain ⟨sx, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨sx2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hsx : sx2 = sx := subjTerm_injective hx2.symm
    subst hsx
    have ho2 : o2 = Term.iri p := hy2.symm
    subst ho2
    have hnp : rlReservedIri p = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm2))
    obtain ⟨su, ov, hm3, rfl, rfl⟩ := herb_decode hnp h3
    obtain ⟨sv, ovy, hm4, hx4, hy4⟩ := herb_decode (by decide) h4
    have hm3' : (⟨su, p, sv.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, ← hx4]
      exact hm3
    have hm4' : (⟨sv, rdfType, yc⟩ : Triple) ∈ c := by
      rw [hy4]
      exact hm4
    have he := herb_encode (hcut (Derives.clsSvf1 (Derives.base hm1)
      (Derives.base hm2) (Derives.base hm3') (Derives.base hm4')))
    rw [toTerm_subjTerm] at he
    exact he
  clsSvf2 := by
    intro p x u v h1 h2 h3
    obtain ⟨sx, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) h1
    have ho1 : o1 = Term.iri owlThing := hy1.symm
    subst ho1
    obtain ⟨sx2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hsx : sx2 = sx := subjTerm_injective hx2.symm
    subst hsx
    have ho2 : o2 = Term.iri p := hy2.symm
    subst ho2
    have hnp : rlReservedIri p = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm2))
    obtain ⟨su, ov, hm3, rfl, rfl⟩ := herb_decode hnp h3
    have he := herb_encode (hcut (Derives.clsSvf2 (Derives.base hm1)
      (Derives.base hm2) (Derives.base hm3)))
    rw [toTerm_subjTerm] at he
    exact he
  clsAvf := by
    intro p x u v yc h1 h2 h3 h4
    obtain ⟨sx, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨sx2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hsx : sx = sx2 := subjTerm_injective hx2
    subst hsx
    have ho2 : o2 = Term.iri p := hy2.symm
    subst ho2
    have hnp : rlReservedIri p = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm2))
    obtain ⟨su, o3, hm3, rfl, hy3⟩ := herb_decode (by decide) h3
    have hm3' : (⟨su, rdfType, sx.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy3]
      exact hm3
    obtain ⟨su2, ov, hm4, hx4, rfl⟩ := herb_decode hnp h4
    have hsu : su = su2 := subjTerm_injective hx4
    subst hsu
    obtain ⟨osv, rfl⟩ := frag_obj_subject hfrag hm4
    have he := herb_encode (hcut (Derives.clsAvf (Derives.base hm1)
      (Derives.base hm2) (Derives.base hm3') (Derives.base hm4)))
    rw [toTerm_subjTerm]
    exact he
  clsHv1 := by
    intro p x u yv h1 h2 h3
    obtain ⟨sx, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨sx2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hsx : sx = sx2 := subjTerm_injective hx2
    subst hsx
    have ho2 : o2 = Term.iri p := hy2.symm
    subst ho2
    obtain ⟨su, o3, hm3, rfl, hy3⟩ := herb_decode (by decide) h3
    have hm3' : (⟨su, rdfType, sx.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy3]
      exact hm3
    exact herb_encode (hcut (Derives.clsHv1 (Derives.base hm1)
      (Derives.base hm2) (Derives.base hm3')))
  clsHv2 := by
    intro p x u yv h1 h2 h3
    obtain ⟨sx, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨sx2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hsx : sx2 = sx := subjTerm_injective hx2.symm
    subst hsx
    have ho2 : o2 = Term.iri p := hy2.symm
    subst ho2
    have hnp : rlReservedIri p = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm2))
    obtain ⟨su, o3, hm3, rfl, hy3⟩ := herb_decode hnp h3
    have hm3' : (⟨su, p, yv⟩ : Triple) ∈ c := by
      rw [hy3]
      exact hm3
    have he := herb_encode (hcut (Derives.clsHv2 (Derives.base hm1)
      (Derives.base hm2) (Derives.base hm3')))
    rw [toTerm_subjTerm] at he
    exact he
  clsHs1 := by
    intro p c u h1 _ _
    exact absurd h1 (no_literal_object hfrag (by decide))
  clsHs2 := by
    intro p c u h1 _ _
    exact absurd h1 (no_literal_object hfrag (by decide))
  clsMaxc2 := by
    intro p x u y1 y2 h1 _ _ _ _
    exact absurd h1 (no_literal_object hfrag (by decide))
  clsOo := by
    intro cel l yi h1 hlm
    obtain ⟨s0, o0, hm0, rfl, rfl⟩ := herb_decode (by decide) h1
    have hm := listMem_decode hfrag hlm
    obtain ⟨n, hmf⟩ := listMember_object_backed hm
    obtain ⟨oys, hoys⟩ := frag_obj_subject hfrag hmf
    rw [show (⟨n, rdfFirst, yi⟩ : Triple).o = yi from rfl] at hoys
    subst hoys
    have he := herb_encode (hcut (Derives.clsOo
      (fun u hu => Derives.base hu) (Derives.base hm0) hm))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  caxSco := by
    intro c1 c2 x h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨sx, ox, hm2, rfl, hox⟩ := herb_decode (by decide) h2
    have hm2' : (⟨sx, rdfType, s1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hox]
      exact hm2
    exact herb_encode (hcut (Derives.caxSco (Derives.base hm1)
      (Derives.base hm2')))
  caxEqc1 := by
    intro c1 c2 x h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨sx, ox, hm2, rfl, hox⟩ := herb_decode (by decide) h2
    have hm2' : (⟨sx, rdfType, s1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hox]
      exact hm2
    exact herb_encode (hcut (Derives.caxEqc1 (Derives.base hm1)
      (Derives.base hm2')))
  caxEqc2 := by
    intro c1 c2 x h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨sx, ox, hm2, rfl, hox⟩ := herb_decode (by decide) h2
    have hm2' : (⟨sx, rdfType, c2⟩ : Triple) ∈ c := by
      rw [hox]
      exact hm2
    have he := herb_encode (hcut (Derives.caxEqc2 (Derives.base hm1)
      (Derives.base hm2')))
    rw [toTerm_subjTerm] at he
    exact he
  scmClsSelf := by
    intro cel h
    obtain ⟨s1, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) h
    have ho1 : o1 = Term.iri owlClass := hy1.symm
    subst ho1
    have he := herb_encode (hcut (Derives.scmClsSelf (Derives.base hm1)))
    rw [toTerm_subjTerm] at he
    exact he
  scmClsEqc := by
    intro cel h
    obtain ⟨s1, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) h
    have ho1 : o1 = Term.iri owlClass := hy1.symm
    subst ho1
    have he := herb_encode (hcut (Derives.scmClsEqc (Derives.base hm1)))
    rw [toTerm_subjTerm] at he
    exact he
  scmClsThing := by
    intro cel h
    obtain ⟨s1, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) h
    have ho1 : o1 = Term.iri owlClass := hy1.symm
    subst ho1
    exact herb_encode (hcut (Derives.scmClsThing (Derives.base hm1)))
  scmClsNothing := by
    intro cel h
    obtain ⟨s1, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) h
    have ho1 : o1 = Term.iri owlClass := hy1.symm
    subst ho1
    have he := herb_encode (hcut (Derives.scmClsNothing (Derives.base hm1)))
    rw [toTerm_subjTerm] at he
    exact he
  scmSco := by
    intro c1 c2 c3 h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) h2
    rw [hx2, ← toTerm_subjTerm] at hm1
    exact herb_encode (hcut (Derives.scmSco (Derives.base hm1)
      (Derives.base hm2)))
  scmEqc1a := by
    intro c1 c2 h
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h
    exact herb_encode (hcut (Derives.scmEqc1a (Derives.base hm1)))
  scmEqc1b := by
    intro c1 c2 h
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm1
    have he := herb_encode (hcut (Derives.scmEqc1b (Derives.base hm1)))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  scmEqc2 := by
    intro c1 c2 h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hm1' : (⟨s1, rdfsSubClassOf, s2.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, ← hx2]
      exact hm1
    have hm2' : (⟨s2, rdfsSubClassOf, s1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy2]
      exact hm2
    have he := herb_encode (hcut (Derives.scmEqc2 (Derives.base hm1')
      (Derives.base hm2')))
    rw [toTerm_subjTerm] at he
    rw [hx2]
    exact he
  scmSpo := by
    intro p1 p2 p3 h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) h2
    rw [hx2, ← toTerm_subjTerm] at hm1
    exact herb_encode (hcut (Derives.scmSpo (Derives.base hm1)
      (Derives.base hm2)))
  scmEqp1a := by
    intro p1 p2 h
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h
    exact herb_encode (hcut (Derives.scmEqp1a (Derives.base hm1)))
  scmEqp1b := by
    intro p1 p2 h
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm1
    have he := herb_encode (hcut (Derives.scmEqp1b (Derives.base hm1)))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  scmEqp2 := by
    intro p1 p2 h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hm1' : (⟨s1, rdfsSubPropertyOf, s2.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, ← hx2]
      exact hm1
    have hm2' : (⟨s2, rdfsSubPropertyOf, s1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy2]
      exact hm2
    have he := herb_encode (hcut (Derives.scmEqp2 (Derives.base hm1')
      (Derives.base hm2')))
    rw [toTerm_subjTerm] at he
    rw [hx2]
    exact he
  scmDom1 := by
    intro p c1 c2 h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) h2
    rw [hx2, ← toTerm_subjTerm] at hm1
    exact herb_encode (hcut (Derives.scmDom1 (Derives.base hm1)
      (Derives.base hm2)))
  scmDom2 := by
    intro p1 p2 cel h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, rfl, hy2⟩ := herb_decode (by decide) h2
    have hm2' : (⟨s2, rdfsSubPropertyOf, s1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy2]
      exact hm2
    exact herb_encode (hcut (Derives.scmDom2 (Derives.base hm1)
      (Derives.base hm2')))
  scmRng1 := by
    intro p c1 c2 h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) h2
    rw [hx2, ← toTerm_subjTerm] at hm1
    exact herb_encode (hcut (Derives.scmRng1 (Derives.base hm1)
      (Derives.base hm2)))
  scmRng2 := by
    intro p1 p2 cel h1 h2
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, rfl, hy2⟩ := herb_decode (by decide) h2
    have hm2' : (⟨s2, rdfsSubPropertyOf, s1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy2]
      exact hm2
    exact herb_encode (hcut (Derives.scmRng2 (Derives.base hm1)
      (Derives.base hm2')))
  scmInt := by
    intro cel l ci h1 hlm
    obtain ⟨s0, o0, hm0, rfl, rfl⟩ := herb_decode (by decide) h1
    have hm := listMem_decode hfrag hlm
    exact herb_encode (hcut (Derives.scmInt
      (fun u hu => Derives.base hu) (Derives.base hm0) hm))
  scmUni := by
    intro cel l ci h1 hlm
    obtain ⟨s0, o0, hm0, rfl, rfl⟩ := herb_decode (by decide) h1
    have hm := listMem_decode hfrag hlm
    obtain ⟨n, hmf⟩ := listMember_object_backed hm
    obtain ⟨ocs, hocs⟩ := frag_obj_subject hfrag hmf
    rw [show (⟨n, rdfFirst, ci⟩ : Triple).o = ci from rfl] at hocs
    subst hocs
    have he := herb_encode (hcut (Derives.scmUni
      (fun u hu => Derives.base hu) (Derives.base hm0) hm))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  eqDiffSym := by
    intro x y hxy
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) hxy
    obtain ⟨os, rfl⟩ := frag_obj_subject hfrag hm1
    have he := herb_encode (hcut (Derives.eqDiffSym (Derives.base hm1)))
    rw [toTerm_subjTerm] at he ⊢
    exact he
  pdwToDiff := by
    intro p1 p2 x o1 o2 hd h1 h2
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hd
    have hs0 : s0 = Subject.iri p1 := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri p2 := hy0.symm
    subst ho0
    have hnp1 : rlReservedIri p1 = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    have hnp2 : rlReservedIri p2 = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm0))
    obtain ⟨sx, oo1, hm1, rfl, rfl⟩ := herb_decode hnp1 h1
    obtain ⟨sx2, oo2, hm2, hx2, rfl⟩ := herb_decode hnp2 h2
    have hsx : sx2 = sx := subjTerm_injective hx2.symm
    subst hsx
    obtain ⟨os1, rfl⟩ := frag_obj_subject hfrag hm1
    by_cases heq : os1.toTerm = o2
    · exfalso
      rw [← heq] at hm2
      exact hcons (Clash.prpPdw hm0 hm1 hm2)
    · have he := herb_encode (hcut (Derives.pdwToDiff (Derives.base hm0)
        (Derives.base hm1) (Derives.base hm2) heq))
      rw [toTerm_subjTerm]
      exact he
  caxDwToDiff := by
    intro c1 c2 x y hd h1 h2
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hd
    have hs0 : s0 = Subject.iri c1 := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri c2 := hy0.symm
    subst ho0
    obtain ⟨sx, ox, hm1, rfl, hox⟩ := herb_decode (by decide) h1
    have ho1 : ox = Term.iri c1 := hox.symm
    subst ho1
    obtain ⟨sy, oy, hm2, rfl, hoy⟩ := herb_decode (by decide) h2
    have ho2 : oy = Term.iri c2 := hoy.symm
    subst ho2
    by_cases heq : sx = sy
    · exfalso
      subst heq
      exact hcons (Clash.caxDw hm0 hm1 hm2)
    · have he := herb_encode (hcut (Derives.caxDwToDiff (Derives.base hm0)
        (Derives.base hm1) (Derives.base hm2) heq))
      rw [toTerm_subjTerm] at he
      exact he
  fpDiffToDiff := by
    intro p y1 y2 x1 x2 hdecl h1 h2 hdiff
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlFunctionalProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨sy1, ox1, hm1, rfl, rfl⟩ := herb_decode hnp h1
    obtain ⟨sy2, ox2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    obtain ⟨sx1, od, hmd, hxd, hyd⟩ := herb_decode (by decide) hdiff
    have hm1' : (⟨sy1, p, sx1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, ← hxd]
      exact hm1
    have hmd' : (⟨sx1, owlDifferentFrom, x2⟩ : Triple) ∈ c := by
      rw [hyd]
      exact hmd
    by_cases heq : sy1 = sy2
    · exfalso
      subst heq
      have hsame := hcut (Derives.prpFp (Derives.base hm0)
        (Derives.base hm1') (Derives.base hm2))
      exact hcons (Clash.eqDiff1 hsame hmd')
    · have he := herb_encode (hcut (Derives.fpDiffToDiff (Derives.base hm0)
        (Derives.base hm1') (Derives.base hm2) (Derives.base hmd') heq))
      rw [toTerm_subjTerm] at he
      exact he
  ifpDiffToDiff := by
    intro p x1 x2 y1 y2 hdecl h1 h2 hdiff
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlInverseFunctionalProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨sx1, oy1, hm1, rfl, rfl⟩ := herb_decode hnp h1
    obtain ⟨sx2, oy2, hm2, rfl, rfl⟩ := herb_decode hnp h2
    obtain ⟨sx1', od, hmd, hxd, hyd⟩ := herb_decode (by decide) hdiff
    have hsx1 : sx1 = sx1' := subjTerm_injective hxd
    subst hsx1
    have hmd' : (⟨sx1, owlDifferentFrom, sx2.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hyd]
      exact hmd
    obtain ⟨oy1s, rfl⟩ := frag_obj_subject hfrag hm1
    by_cases heq : oy1s.toTerm = y2
    · exfalso
      rw [← heq] at hm2
      have hsame := hcut (Derives.prpIfp (Derives.base hm0)
        (Derives.base hm1) (Derives.base hm2))
      exact hcons (Clash.eqDiff1 hsame hmd')
    · have he := herb_encode (hcut (Derives.ifpDiffToDiff (Derives.base hm0)
        (Derives.base hm1) (Derives.base hm2) (Derives.base hmd') heq))
      rw [toTerm_subjTerm]
      exact he
  chainToTrans := by
    intro p l l' h0 hf1 hr1 hf2 hr2
    obtain ⟨s0, o0, hm0, hx0, rfl⟩ := herb_decode (by decide) h0
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    obtain ⟨n1, of1, hm1, hx1, hy1⟩ := herb_decode (by decide) hf1
    have hof1 : of1 = Term.iri p := hy1.symm
    subst hof1
    obtain ⟨n1', or1, hm2, hx1', rfl⟩ := herb_decode (by decide) hr1
    have hn1 : n1' = n1 := by
      apply subjTerm_injective
      rw [← hx1', ← hx1]
    subst hn1
    obtain ⟨n2, of2, hm3, hx2, hy2⟩ := herb_decode (by decide) hf2
    have hof2 : of2 = Term.iri p := hy2.symm
    subst hof2
    obtain ⟨n2', or2, hm4, hx2', hy4⟩ := herb_decode (by decide) hr2
    have hn2 : n2' = n2 := by
      apply subjTerm_injective
      rw [← hx2', ← hx2]
    subst hn2
    have hor2 : or2 = Term.iri rdfNil := hy4.symm
    subst hor2
    have hm2' : (⟨n1', rdfRest, n2'.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, ← hx2]
      exact hm2
    have hlist : ListDenotes c (subjTerm n1') [Term.iri p, Term.iri p] := by
      rw [← toTerm_subjTerm]
      refine ListDenotes.cons
        (toTerm_ne_nil (frag_not_nil_cons hfrag hm1 (Or.inl rfl)))
        hm1 hm2' ?_
      exact ListDenotes.cons
        (toTerm_ne_nil (frag_not_nil_cons hfrag hm3 (Or.inl rfl)))
        hm3 hm4 ListDenotes.nil
    have hm0' : (⟨Subject.iri p, owlPropertyChainAxiom,
        subjTerm n1'⟩ : Triple) ∈ c := by
      rw [← hx1]
      exact hm0
    exact herb_encode (hcut (Derives.chainToTrans
      (fun u hu => Derives.base hu) (Derives.base hm0') hlist))
  prpRflS := by
    intro p j q y hdecl hocc
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlReflexiveProperty := hy0.symm
    subst ho0
    have hind : j ∈ iriIndividuals c := by
      have h' : rlHerbIext c q (Term.iri j) y := hocc
      rcases h' with ⟨t, ht, -, hx, -⟩ | ⟨-, hm⟩ | ⟨-, hta⟩
      · exact iriIndividuals_of_subj ht (subjTerm_iri hx.symm)
      · obtain ⟨t0, ht0, hjt⟩ := listMember_head_backed hm
        rw [toTerm_subjTerm] at hjt
        exact iriIndividuals_of_subj ht0 (subjTerm_iri hjt.symm)
      · obtain ⟨ys, cs, hne, hj, hld, hty⟩ := hta
        rw [toTerm_subjTerm] at hj
        have hys : ys = Subject.iri j := subjTerm_iri hj.symm
        subst hys
        cases hty with
        | nil => exact absurd rfl hne
        | cons hm1 _ => exact iriIndividuals_of_subj hm1 rfl
    exact herb_encode (hcut (Derives.prpRfl (fun u hu => Derives.base hu)
      (Derives.base hm0) hind))
  prpRflO := by
    intro p j q x hdecl hocc
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlReflexiveProperty := hy0.symm
    subst ho0
    have hind : j ∈ iriIndividuals c := by
      have h' : rlHerbIext c q x (Term.iri j) := hocc
      rcases h' with ⟨t, ht, -, -, hy⟩ | ⟨-, hm⟩ | ⟨-, hta⟩
      · exact iriIndividuals_of_obj ht hy.symm
      · obtain ⟨n, hmf⟩ := listMember_object_backed hm
        exact iriIndividuals_of_obj hmf rfl
      · obtain ⟨ys, cs, hne, -, hld, -⟩ := hta
        obtain ⟨t0, ht0, hjt, -⟩ := listDenotes_head_backed hld hne
        rw [toTerm_subjTerm] at hjt
        exact iriIndividuals_of_subj ht0 (subjTerm_iri hjt.symm)
    exact herb_encode (hcut (Derives.prpRfl (fun u hu => Derives.base hu)
      (Derives.base hm0) hind))
  xsdAxioms := by
    intro p hpm w hw a pr b hax x hx
    have hnp : rlReservedIri p = false := dpp_nonres p hpm
    obtain ⟨sx, ow, hm1, rfl, how⟩ := herb_decode hnp hx
    have how' : ow = Term.iri w := how.symm
    subst how'
    have hdx : drivesXsdAxioms ⟨sx, p, Term.iri w⟩ = true := by
      simp [drivesXsdAxioms, hw, hpm]
    exact herb_encode (hcut (Derives.xsdAxioms (Derives.base hm1) hdx hax))
  dtRangeIntersect := by
    intro d1 d2 d3 hlic pd h1 h2
    obtain ⟨s1, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) h1
    have ho1 : o1 = Term.iri d1 := hy1.symm
    subst ho1
    obtain ⟨s2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hs2 : s2 = s1 := subjTerm_injective hx2.symm
    subst hs2
    have ho2 : o2 = Term.iri d2 := hy2.symm
    subst ho2
    exact herb_encode (hcut (Derives.dtRangeIntersect (Derives.base hm1)
      (Derives.base hm2) hlic))
  dtType1Builtin := by
    intro a pr b hax
    exact herb_encode (hcut (Derives.dtType1Builtin hax))
  caxAdcToDw := by
    intro ci cj hne y l hty hmem hlm1 hlm2
    obtain ⟨sy, oadc, hm1, rfl, hoadc⟩ := herb_decode (by decide) hty
    have ho1 : oadc = Term.iri owlAllDisjointClasses := hoadc.symm
    subst ho1
    obtain ⟨sy2, ol, hm2, hx2, rfl⟩ := herb_decode (by decide) hmem
    have hsy : sy2 = sy := subjTerm_injective hx2.symm
    subst hsy
    have hml1 := listMem_decode hfrag hlm1
    have hml2 := listMem_decode hfrag hlm2
    exact herb_encode (hcut (Derives.caxAdcToDw
      (fun u hu => Derives.base hu) (Derives.base hm1) (Derives.base hm2)
      hml1 hml2 hne))
  invFlipDomRng := by
    intro p q cw h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri q := hy1.symm
    subst ho1
    obtain ⟨s2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hs2 : s2 = Subject.iri p := subjTerm_iri hx2.symm
    subst hs2
    have ho2 : o2 = Term.iri cw := hy2.symm
    subst ho2
    exact herb_encode (hcut (Derives.invFlipDomRng (Derives.base hm1)
      (Derives.base hm2)))
  invFlipRngDom := by
    intro p q cw h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri q := hy1.symm
    subst ho1
    obtain ⟨s2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hs2 : s2 = Subject.iri p := subjTerm_iri hx2.symm
    subst hs2
    have ho2 : o2 = Term.iri cw := hy2.symm
    subst ho2
    exact herb_encode (hcut (Derives.invFlipRngDom (Derives.base hm1)
      (Derives.base hm2)))
  invFlipDomRngRev := by
    intro p q cw h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri q := hy1.symm
    subst ho1
    obtain ⟨s2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hs2 : s2 = Subject.iri q := subjTerm_iri hx2.symm
    subst hs2
    have ho2 : o2 = Term.iri cw := hy2.symm
    subst ho2
    exact herb_encode (hcut (Derives.invFlipDomRngRev (Derives.base hm1)
      (Derives.base hm2)))
  invFlipRngDomRev := by
    intro p q cw h1 h2
    obtain ⟨s1, o1, hm1, hx1, hy1⟩ := herb_decode (by decide) h1
    have hs1 : s1 = Subject.iri p := subjTerm_iri hx1.symm
    subst hs1
    have ho1 : o1 = Term.iri q := hy1.symm
    subst ho1
    obtain ⟨s2, o2, hm2, hx2, hy2⟩ := herb_decode (by decide) h2
    have hs2 : s2 = Subject.iri q := subjTerm_iri hx2.symm
    subst hs2
    have ho2 : o2 = Term.iri cw := hy2.symm
    subst ho2
    exact herb_encode (hcut (Derives.invFlipRngDomRev (Derives.base hm1)
      (Derives.base hm2)))
  compDw := by
    intro c0 hguard
    obtain ⟨a, ha⟩ := hguard
    refine ⟨(complementWitness c0).toTerm, herb_compProps hcut hfrag ?_⟩
    rcases ha with ha | ha
    · obtain ⟨s1, o1, hm1, rfl, ho1⟩ := herb_decode (by decide) ha
      have ho1' : o1 = Term.iri c0 := ho1.symm
      subst ho1'
      obtain ⟨⟨w1, hs1⟩, -⟩ := frag_dw hfrag hm1 rfl
      subst hs1
      intro t htm
      exact hcut (Derives.caxDwToComplement (Derives.base hm1)
        (List.mem_append_left _ (List.mem_append_left _ htm)))
    · obtain ⟨s1, o1, hm1, hx1, rfl⟩ := herb_decode (by decide) ha
      have hs1 : s1 = Subject.iri c0 := subjTerm_iri hx1.symm
      subst hs1
      obtain ⟨-, ⟨w1, ho1⟩⟩ := frag_dw hfrag hm1 rfl
      subst ho1
      intro t htm
      exact hcut (Derives.caxDwToComplement (Derives.base hm1)
        (List.mem_append_left _ (List.mem_append_right _ htm)))
  compMqc := by
    intro c0 hguard
    obtain ⟨x, u, y1, y2, pe, hbody⟩ := hguard
    exact absurd hbody.1 (no_literal_object hfrag (by decide))
  minc1 := by
    intro p hdecl
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlObjectProperty := hy0.symm
    subst ho0
    have hlit : (⟨minCard1Witness p, owlMinCardinality,
        Term.literal litNni1⟩ : Triple) ∈ c :=
      hcut (Derives.minCard1Comprehension (Derives.base hm0)
        (by simp [minCard1WitnessTriples]))
    obtain ⟨os, habs⟩ := frag_obj_subject hfrag hlit
    exact absurd habs (by cases os <;> simp [Subject.toTerm])

end HerbConditions

/-! ## The Herbrand model meets every clash-row condition

The falsity-headed rows need no saturation hypothesis: each one decodes
its premises straight back to graph triples and hands them to the
matching `Clash` constructor, which `hcons` refutes. The three
cardinality rows are discharged differently — their `owl:maxCardinality
"0"` premise relates a term to a LITERAL, which fragment clause (a)
forbids, so they hold vacuously in `rlHerb c`. That is a real
restriction on what the completeness direction reaches, recorded as a
boundary row rather than papered over. -/

section HerbClashConditions

variable {c : Graph} (hfrag : RlHerbFrag c) (hcons : ¬ Clash c)
include hfrag hcons

theorem rlHerb_clash_conditions : RlClashConditions (rlHerb c) where
  eqDiff1 := by
    rintro x y ⟨h1, h2⟩
    obtain ⟨s1, o1, hm1, rfl, rfl⟩ := herb_decode (by decide) h1
    obtain ⟨s2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) h2
    have hs : s1 = s2 := subjTerm_injective hx2
    subst hs
    exact hcons (Clash.eqDiff1 hm1 hm2)
  prpIrp := by
    rintro p x ⟨hdecl, hd⟩
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlIrreflexiveProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨sx, ox, hm1, rfl, hy1⟩ := herb_decode hnp hd
    have hm1' : (⟨sx, p, sx.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy1]
      exact hm1
    exact hcons (Clash.prpIrp hm0 hm1')
  prpAsyp := by
    rintro p x y ⟨hdecl, h1, h2⟩
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri owlAsymmetricProperty := hy0.symm
    subst ho0
    have hnp : rlReservedIri p = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    obtain ⟨sx, o1, hm1, rfl, hy1⟩ := herb_decode hnp h1
    obtain ⟨sy, o2, hm2, hx2, hy2⟩ := herb_decode hnp h2
    have hm1' : (⟨sx, p, sy.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, ← hx2, hy1]
      exact hm1
    have hm2' : (⟨sy, p, sx.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy2]
      exact hm2
    exact hcons (Clash.prpAsyp hm0 hm1' hm2')
  prpPdw := by
    rintro p1 p2 x y ⟨hdecl, h1, h2⟩
    obtain ⟨s0, o0, hm0, hx0, hy0⟩ := herb_decode (by decide) hdecl
    have hs0 : s0 = Subject.iri p1 := subjTerm_iri hx0.symm
    subst hs0
    have ho0 : o0 = Term.iri p2 := hy0.symm
    subst ho0
    have hnp1 : rlReservedIri p1 = false :=
      irw_of_subjIri (tin_s (frag_iris hfrag hm0))
    have hnp2 : rlReservedIri p2 = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm0))
    obtain ⟨sx, o1, hm1, rfl, rfl⟩ := herb_decode hnp1 h1
    obtain ⟨sx2, o2, hm2, hx2, rfl⟩ := herb_decode hnp2 h2
    have hs : sx = sx2 := subjTerm_injective hx2
    subst hs
    exact hcons (Clash.prpPdw hm0 hm1 hm2)
  prpNpa1 := by
    rintro p w x y ⟨hsrc, hap, hti, hd⟩
    obtain ⟨si, o2, hm2, rfl, hy2⟩ := herb_decode (by decide) hap
    have ho2 : o2 = Term.iri p := hy2.symm
    subst ho2
    have hnp : rlReservedIri p = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm2))
    obtain ⟨sx, o4, hm4, rfl, rfl⟩ := herb_decode hnp hd
    obtain ⟨si1, o1, hm1, hw1, hx1⟩ := herb_decode (by decide) hsrc
    have e1 : si = si1 := subjTerm_injective hw1
    subst e1
    obtain ⟨si3, o3, hm3, hw3, hy3⟩ := herb_decode (by decide) hti
    have e3 : si = si3 := subjTerm_injective hw3
    subst e3
    have hm1' : (⟨si, owlSourceIndividual, sx.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hx1]
      exact hm1
    have hm3' : (⟨si, owlTargetIndividual, y⟩ : Triple) ∈ c := by
      rw [hy3]
      exact hm3
    exact hcons (Clash.prpNpa1 hm1' hm2 hm3' hm4)
  prpNpa2 := by
    rintro p w x y ⟨hsrc, hap, htv, hd⟩
    obtain ⟨si, o2, hm2, rfl, hy2⟩ := herb_decode (by decide) hap
    have ho2 : o2 = Term.iri p := hy2.symm
    subst ho2
    have hnp : rlReservedIri p = false :=
      irw_of_termIri (tin_o (frag_iris hfrag hm2))
    obtain ⟨sx, o4, hm4, rfl, rfl⟩ := herb_decode hnp hd
    obtain ⟨si1, o1, hm1, hw1, hx1⟩ := herb_decode (by decide) hsrc
    have e1 : si = si1 := subjTerm_injective hw1
    subst e1
    obtain ⟨si3, o3, hm3, hw3, hy3⟩ := herb_decode (by decide) htv
    have e3 : si = si3 := subjTerm_injective hw3
    subst e3
    have hm1' : (⟨si, owlSourceIndividual, sx.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hx1]
      exact hm1
    have hm3' : (⟨si, owlTargetValue, y⟩ : Triple) ∈ c := by
      rw [hy3]
      exact hm3
    exact hcons (Clash.prpNpa2 hm1' hm2 hm3' hm4)
  clsNothing2 := by
    intro x h
    obtain ⟨s1, o1, hm1, -, hy1⟩ := herb_decode (by decide) h
    have ho1 : o1 = Term.iri owlNothing := hy1.symm
    subst ho1
    exact hcons (Clash.clsNothing2 hm1)
  clsCom := by
    rintro c1 c2 x ⟨hdecl, h1, h2⟩
    obtain ⟨sc1, o1, hm0, rfl, rfl⟩ := herb_decode (by decide) hdecl
    obtain ⟨sx, o2, hm1, rfl, hy2⟩ := herb_decode (by decide) h1
    obtain ⟨sx2, o3, hm2, hx3, hy3⟩ := herb_decode (by decide) h2
    have hs : sx = sx2 := subjTerm_injective hx3
    subst hs
    have hm1' : (⟨sx, rdfType, sc1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy2]
      exact hm1
    have hm2' : (⟨sx, rdfType, c2⟩ : Triple) ∈ c := by
      rw [hy3]
      exact hm2
    exact hcons (Clash.clsCom hm0 hm1' hm2')
  clsMaxc1 := by
    rintro p x u y ⟨hmc, -, -, -⟩
    exact absurd hmc (no_literal_object hfrag (by decide))
  clsMaxqc1 := by
    rintro p x u y cq ⟨hmqc, -, -, -, -, -⟩
    exact absurd hmqc (no_literal_object hfrag (by decide))
  clsMaxqc2 := by
    rintro p x u y ⟨hmqc, -, -, -, -⟩
    exact absurd hmqc (no_literal_object hfrag (by decide))
  caxDw := by
    rintro c1 c2 x ⟨hdecl, h1, h2⟩
    obtain ⟨sc1, o1, hm0, rfl, rfl⟩ := herb_decode (by decide) hdecl
    obtain ⟨sx, o2, hm1, rfl, hy2⟩ := herb_decode (by decide) h1
    obtain ⟨sx2, o3, hm2, hx3, hy3⟩ := herb_decode (by decide) h2
    have hs : sx = sx2 := subjTerm_injective hx3
    subst hs
    have hm1' : (⟨sx, rdfType, sc1.toTerm⟩ : Triple) ∈ c := by
      rw [toTerm_subjTerm, hy2]
      exact hm1
    have hm2' : (⟨sx, rdfType, c2⟩ : Triple) ∈ c := by
      rw [hy3]
      exact hm2
    exact hcons (Clash.caxDw hm0 hm1' hm2')
  caxAdc := by
    rintro cc1 cc2 hne y l z ⟨hty, hmem, hl1, hl2, ht1, ht2⟩
    obtain ⟨sy, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) hty
    have ho1 : o1 = Term.iri owlAllDisjointClasses := hy1.symm
    subst ho1
    obtain ⟨sy2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) hmem
    have hsy : sy = sy2 := subjTerm_injective hx2
    subst hsy
    have hlm1 := listMem_decode hfrag hl1
    have hlm2 := listMem_decode hfrag hl2
    obtain ⟨sz, o3, hm3, rfl, hy3⟩ := herb_decode (by decide) ht1
    have ho3 : o3 = Term.iri cc1 := hy3.symm
    subst ho3
    obtain ⟨sz2, o4, hm4, hx4, hy4⟩ := herb_decode (by decide) ht2
    have hsz : sz = sz2 := subjTerm_injective hx4
    subst hsz
    have ho4 : o4 = Term.iri cc2 := hy4.symm
    subst ho4
    have hne' : (Term.iri cc1) ≠ (Term.iri cc2) := by
      intro h
      exact hne (by injection h)
    exact hcons (Clash.caxAdc hm1 hm2 hlm1 hlm2 hne' hm3 hm4)
  eqDiff2 := by
    rintro z1 z2 hne y l ⟨hty, hmem, hl1, hl2, hsame⟩
    obtain ⟨sy, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) hty
    have ho1 : o1 = Term.iri owlAllDifferent := hy1.symm
    subst ho1
    obtain ⟨sy2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) hmem
    have hsy : sy = sy2 := subjTerm_injective hx2
    subst hsy
    have hlm1 := listMem_decode hfrag hl1
    have hlm2 := listMem_decode hfrag hl2
    obtain ⟨sz, o3, hm3, hx3, hy3⟩ := herb_decode (by decide) hsame
    have hsz : sz = Subject.iri z1 := subjTerm_iri hx3.symm
    subst hsz
    have ho3 : o3 = Term.iri z2 := hy3.symm
    subst ho3
    have hne' : (Subject.iri z1).toTerm ≠ (Term.iri z2) := by
      intro he
      apply hne
      have hee : Term.iri z1 = Term.iri z2 := he
      injection hee
    exact hcons (Clash.eqDiff2 (zi := Subject.iri z1) (zj := Term.iri z2)
      hm1 hm2 hlm1 hlm2 hne' hm3)
  eqDiff3 := by
    rintro z1 z2 hne y l ⟨hty, hmem, hl1, hl2, hsame⟩
    obtain ⟨sy, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) hty
    have ho1 : o1 = Term.iri owlAllDifferent := hy1.symm
    subst ho1
    obtain ⟨sy2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) hmem
    have hsy : sy = sy2 := subjTerm_injective hx2
    subst hsy
    have hlm1 := listMem_decode hfrag hl1
    have hlm2 := listMem_decode hfrag hl2
    obtain ⟨sz, o3, hm3, hx3, hy3⟩ := herb_decode (by decide) hsame
    have hsz : sz = Subject.iri z1 := subjTerm_iri hx3.symm
    subst hsz
    have ho3 : o3 = Term.iri z2 := hy3.symm
    subst ho3
    have hne' : (Subject.iri z1).toTerm ≠ (Term.iri z2) := by
      intro he
      apply hne
      have hee : Term.iri z1 = Term.iri z2 := he
      injection hee
    exact hcons (Clash.eqDiff3 (zi := Subject.iri z1) (zj := Term.iri z2)
      hm1 hm2 hlm1 hlm2 hne' hm3)
  prpAdp := by
    rintro p1 p2 hne y l u v ⟨hty, hmem, hl1, hl2, he1, he2⟩
    obtain ⟨sy, o1, hm1, rfl, hy1⟩ := herb_decode (by decide) hty
    have ho1 : o1 = Term.iri owlAllDisjointProperties := hy1.symm
    subst ho1
    obtain ⟨sy2, o2, hm2, hx2, rfl⟩ := herb_decode (by decide) hmem
    have hsy : sy = sy2 := subjTerm_injective hx2
    subst hsy
    have hlm1 := listMem_decode hfrag hl1
    have hlm2 := listMem_decode hfrag hl2
    have hnr1 : rlReservedIri p1 = false :=
      irw_of_termIri (listMember_termIris (fun t ht => frag_iris hfrag ht) hlm1)
    have hnr2 : rlReservedIri p2 = false :=
      irw_of_termIri (listMember_termIris (fun t ht => frag_iris hfrag ht) hlm2)
    obtain ⟨su, ou, hm3, hx3, hy3⟩ := herb_decode hnr1 he1
    obtain ⟨su2, ou2, hm4, hx4, hy4⟩ := herb_decode hnr2 he2
    have hsu : su = su2 := subjTerm_injective (hx3.symm.trans hx4)
    subst hsu
    have hoo : ou = ou2 := hy3.symm.trans hy4
    subst hoo
    exact hcons (Clash.prpAdp (p1 := p1) (p2 := p2)
      hm1 hm2 hlm1 hlm2 hne hm3 hm4)

end HerbClashConditions

/-! ## Decoding a satisfied ground atom back to closure membership

The completeness direction's last step: an atom true in `rlHerb c` at a
NON-RESERVED predicate is a triple of `c`. This is what turns
`liftInterp (rlHerb (closure g fuel)) ⊨ φ` back into a closure
membership fact in `Unified/OwlRlAdequacy.lean`. -/

theorem rlHerb_atom_decode {c : Graph} {s : Subject} {p : WfIri} {o : Term}
    (hp : rlReservedIri p = false)
    (h : (rlHerb c).iext ((rlHerb c).iIri p) (subjTerm s) o) :
    (⟨s, p, o⟩ : Triple) ∈ c := by
  obtain ⟨s', o', hm, hx, hy⟩ := herb_decode hp h
  have hs : s = s' := subjTerm_injective hx
  subst hs
  subst hy
  exact hm

/-- The same at the `TripleHolds` level, under the assignment that
sends every blank-node label to its own term (the Herbrand domain IS
the term algebra, so that assignment is the identity). -/
def herbAssign (c : Graph) : BnodeAssignment (rlHerb c).idom := fun b => .bnode b

theorem denotSubject_herbAssign (c : Graph) (s : Subject) :
    denotSubject (rlHerb c) (herbAssign c) s = subjTerm s := by
  cases s <;> rfl

theorem denotTerm_herbAssign (c : Graph) {o : Term} (h : TermTtFree o) :
    denotTerm (rlHerb c) (herbAssign c) o = o := by
  cases o with
  | iri _ => rfl
  | bnode _ => rfl
  | literal _ => rfl
  | tripleTerm _ _ _ => exact absurd h (by simp [TermTtFree])

theorem rlHerb_triple_decode {c : Graph} {t : Triple}
    (hp : rlReservedIri t.p = false) (htt : TermTtFree t.o)
    (h : TripleHolds (rlHerb c) (herbAssign c) t) : t ∈ c := by
  have h' : (rlHerb c).iext ((rlHerb c).iIri t.p) (subjTerm t.s) t.o := by
    rw [← denotSubject_herbAssign c t.s, ← denotTerm_herbAssign c htt]
    exact h
  have := rlHerb_atom_decode hp h'
  simpa using this

/-! ## Axiom audit -/

#print axioms rlHerb_conditions
#print axioms rlHerb_clash_conditions
#print axioms rlHerb_atom_decode
#print axioms rlHerb_triple_decode

end L4Factoidal.OWL.RL
