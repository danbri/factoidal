/-
L4Factoidal.RDF.EntailmentSimpleRefinement — the simple-entailment
decision procedure is COMPLETE for its specification.

Port of `formal/fstar/RDF.Entailment.Simple.Refinement.fst` (882 lines).

`EntailmentTheorems.lean` already has the soundness half:
`simpleEntails g h = true → SimpleEntails g h`, read off the
certificate. This module supplies the other half —
`SimpleEntails g h → simpleEntails g h = true` — and joins the two into
`simpleEntails_iff_spec`.

## What differs from the F* source, and why

The F* result is UNCONDITIONALLY complete and CONDITIONALLY sound: its
soundness carries a `graph_exact` side condition, and
`simple_entails_not_sound_unconditionally` is a machine-checked witness
that the condition cannot be dropped. The cause is named in that
module's banner: the shipping `literal_eq` is strictly coarser than
literal term equality, because it folds language-tag case and compares
two `rdf:XMLLiteral`-typed literals by exclusive canonical XML.

This tree's `literalStrictEq` is `==` on `Literal`, whose `BEq` comes
from `DecidableEq`. It IS literal term equality, so both halves hold
unconditionally here and there is no side condition to state. The
coarser comparisons live in the regime variants (`literalValueEq D`),
which are separate functions with a model-theoretic specification this
tree does not port. Reporting the F* side condition as if it applied
here would name a restriction the Lean statement does not carry.

## The engine gap this port found

Completeness is FALSE for the `matchObject` this tree shipped before
2026-08-23: its object arm bound a top-level blank node but fell
straight to `termMatch` for an RDF 1.2 triple term, and `termMatch`
compares a triple term's subject and interior object by identity. So
`_:a p <<( x q _:b )>>` matched only a premise carrying the same
interior label. `entailsSimple_tripleTerm_interior_bnode` below is the
witness that decided `false` before the fix. The F* `match_term`
(`RDF.Entailment.Simple.fst:94`) always recursed; the port did not, and
the theorems here could not have been stated against the old arm.

## Shape of the completeness proof

Two properties of the backtracking search, proved separately:

1. **It terminates in success.** Given a witness substitution `σ`, the
   route through the candidate triples that `σ` picks out succeeds, so
   `List.findSome?` returns SOME mapping. It need not return the one
   `σ` describes — a different candidate may be tried first — which is
   why this half claims only `isSome`.
2. **Whatever it returns, certifies.** `searchInstance` threads a
   mapping that only ever GROWS (a label is bound once, when first met,
   and never rebound), so each triple's match survives to the end and
   `instanceCert` re-checks it successfully.

Together they give `entailsWith = true`. Splitting them is what avoids
having to prove the search finds a particular mapping, which is false.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.Entailment
import L4Factoidal.RDF.EntailmentTheorems

namespace L4Factoidal.RDF.SimpleRefinement

open L4Factoidal.RDF

/-! ## Mapping order

`Mapping` is an association list and `Mapping.lookup` reads the FIRST
entry for a label, so a prepend can shadow. The search never prepends a
label it already holds, so the mappings it produces stand in the
extension order below, where an existing answer is never displaced. -/

/-- `m2` answers every lookup `m1` answers, with the same term. -/
def Extends (m2 m1 : Mapping) : Prop :=
  ∀ b t, m1.lookup b = some t → m2.lookup b = some t

/-- Every binding agrees with the substitution `σ`. -/
def Compat (σ : BNodeId → Term) (m : Mapping) : Prop :=
  ∀ b t, m.lookup b = some t → σ b = t

theorem Extends.refl (m : Mapping) : Extends m m := fun _ _ h => h

theorem Extends.trans {m3 m2 m1 : Mapping}
    (h32 : Extends m3 m2) (h21 : Extends m2 m1) : Extends m3 m1 :=
  fun b t h => h32 b t (h21 b t h)

theorem Compat.nil (σ : BNodeId → Term) : Compat σ [] := by
  intro b t h; simp [Mapping.lookup] at h

theorem lookup_cons_self (b : BNodeId) (t : Term) (m : Mapping) :
    Mapping.lookup ((b, t) :: m) b = some t := by
  simp [Mapping.lookup]

theorem lookup_cons_other {b b' : BNodeId} (t : Term) (m : Mapping)
    (hne : b' ≠ b) : Mapping.lookup ((b, t) :: m) b' = m.lookup b' := by
  have : (b == b') = false := by
    simp only [beq_eq_false_iff_ne]; exact Ne.symm hne
  simp [Mapping.lookup, List.find?, this]

/-- Prepending a label the mapping does not hold cannot displace an
answer, so the result extends it. -/
theorem Extends.cons {m : Mapping} {b : BNodeId} (t : Term)
    (hnew : m.lookup b = none) : Extends ((b, t) :: m) m := by
  intro b' t' h
  by_cases hb : b' = b
  · subst hb; rw [hnew] at h; exact absurd h (by simp)
  · rw [lookup_cons_other t m hb]; exact h

theorem Compat.cons {σ : BNodeId → Term} {m : Mapping} {b : BNodeId} {t : Term}
    (hc : Compat σ m) (hb : σ b = t) : Compat σ ((b, t) :: m) := by
  intro b' t' h
  by_cases hbb : b' = b
  · subst hbb; rw [lookup_cons_self] at h; cases h; exact hb
  · rw [lookup_cons_other t m hbb] at h; exact hc b' t' h

/-- What a mapping's function does on a label it holds. -/
theorem toFun_of_lookup {m : Mapping} {b : BNodeId} {t : Term}
    (h : m.lookup b = some t) : m.toFun b = t := by
  simp [Mapping.toFun, h]


/-! ## The matchers are complete

Each matcher, handed a substitution that already explains the candidate,
succeeds and returns a mapping that still agrees with that substitution.
Two hypotheses stand in for the F* source's `leq_reflexive` and
`bnd_total`: the literal comparison accepts a literal against itself,
and the bindability test accepts every term. Simple entailment supplies
both. -/

/-- A term matches itself when the literal comparison is reflexive. -/
theorem termMatch_refl {leq : Literal → Literal → Bool}
    (hleq : ∀ l, leq l l = true) : ∀ t : Term, termMatch leq t t = true := by
  intro t
  induction t with
  | iri i => simp [termMatch]
  | bnode b => simp [termMatch]
  | literal l => simp [termMatch, hleq]
  | tripleTerm s p o ih => simp [termMatch, ih]

/-- A term that a subject-position substitution accepts is that
subject, read as a term. -/
theorem toSubject?_eq {t : Term} {s : Subject} (h : t.toSubject? = some s) :
    t = s.toTerm := by
  cases t <;> simp [Term.toSubject?] at h <;> subst h <;> rfl

theorem matchSubject_complete {σ : BNodeId → Term} {m : Mapping}
    {ps gs : Subject} (hc : Compat σ m) (h : ps.instance? σ = some gs) :
    ∃ m1, matchSubject m ps gs = some m1 ∧ Compat σ m1 ∧ Extends m1 m := by
  cases ps with
  | iri i =>
      simp only [Subject.instance?, Option.some.injEq] at h
      subst h
      exact ⟨m, by simp [matchSubject], hc, Extends.refl m⟩
  | bnode b =>
      simp only [Subject.instance?] at h
      have hsb : σ b = gs.toTerm := toSubject?_eq h
      cases hl : m.lookup b with
      | some t =>
          have ht : σ b = t := hc b t hl
          have : t = gs.toTerm := by rw [← ht, hsb]
          exact ⟨m, by simp [matchSubject, hl, this], hc, Extends.refl m⟩
      | none =>
          refine ⟨(b, gs.toTerm) :: m, by simp [matchSubject, hl], ?_, ?_⟩
          · exact hc.cons hsb
          · exact Extends.cons _ hl

theorem matchObject_complete {leq : Literal → Literal → Bool}
    {bindable : Term → Bool} (hleq : ∀ l, leq l l = true)
    (hbnd : ∀ t, bindable t = true) :
    ∀ (ho go : Term) (m : Mapping) (σ : BNodeId → Term), Compat σ m →
      ho.instance? σ = some go →
      ∃ m1, matchObject leq bindable m ho go = some m1 ∧
            Compat σ m1 ∧ Extends m1 m := by
  intro ho
  induction ho with
  | iri i =>
      intro go m σ hc h
      simp only [Term.instance?, Option.some.injEq] at h
      subst h
      exact ⟨m, by simp [matchObject, termMatch], hc, Extends.refl m⟩
  | literal l =>
      intro go m σ hc h
      simp only [Term.instance?, Option.some.injEq] at h
      subst h
      exact ⟨m, by simp [matchObject, termMatch, hleq], hc, Extends.refl m⟩
  | bnode b =>
      intro go m σ hc h
      simp only [Term.instance?, Option.some.injEq] at h
      cases hl : m.lookup b with
      | some t =>
          have ht : σ b = t := hc b t hl
          have : t = go := by rw [← ht, h]
          exact ⟨m, by simp [matchObject, hl, this], hc, Extends.refl m⟩
      | none =>
          refine ⟨(b, go) :: m, by simp [matchObject, hl, hbnd], ?_, ?_⟩
          · exact hc.cons h
          · exact Extends.cons _ hl
  | tripleTerm ps pp po ih =>
      intro go m σ hc h
      simp only [Term.instance?] at h
      cases hs : ps.instance? σ with
      | none => rw [hs] at h; simp at h
      | some ps' =>
        cases ho' : po.instance? σ with
        | none => rw [hs, ho'] at h; simp at h
        | some po' =>
          rw [hs, ho'] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨m1, hm1, hc1, he1⟩ := matchSubject_complete hc hs
          obtain ⟨m2, hm2, hc2, he2⟩ := ih po' m1 σ hc1 ho'
          exact ⟨m2, by simp [matchObject, hm1, hm2], hc2, he2.trans he1⟩


/-! ## Part 1 — the search terminates in success

`List.findSome?` returns the first candidate that yields `some`. The
route the witness substitution picks out is one such candidate, so the
search returns SOMETHING; which mapping it returns is not claimed, and
is not what the certificate needs. -/

theorem findSome?_isSome_of_mem {α β : Type} {f : α → Option β} {l : List α}
    {a : α} (ha : a ∈ l) (hf : (f a).isSome = true) :
    (l.findSome? f).isSome = true := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      simp only [List.findSome?]
      cases hx : f x with
      | some v => simp
      | none =>
          simp only []
          rcases List.mem_cons.mp ha with rfl | hmem
          · rw [hx] at hf; simp at hf
          · exact ih hmem

/-- The three components an instance step relates. -/
theorem instance?_parts {σ : BNodeId → Term} {t t' : Triple}
    (h : t.instance? σ = some t') :
    t.s.instance? σ = some t'.s ∧ t.o.instance? σ = some t'.o ∧ t'.p = t.p := by
  simp only [Triple.instance?] at h
  cases hs : t.s.instance? σ with
  | none => rw [hs] at h; simp at h
  | some s' =>
      cases ho : t.o.instance? σ with
      | none => rw [hs, ho] at h; simp at h
      | some o' =>
          rw [hs, ho] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl⟩

theorem searchInstance_isSome {leq : Literal → Literal → Bool}
    {bindable : Term → Bool} (hleq : ∀ l, leq l l = true)
    (hbnd : ∀ t, bindable t = true) (g : Graph) :
    ∀ (hs : List Triple) (m : Mapping) (σ : BNodeId → Term), Compat σ m →
      (∀ t ∈ hs, ∃ t', t.instance? σ = some t' ∧ t' ∈ g) →
      (searchInstance leq bindable g hs m).isSome = true := by
  intro hs
  induction hs with
  | nil => intro m σ _ _; simp [searchInstance]
  | cons t rest ih =>
      intro m σ hc hall
      obtain ⟨t', ht', hmem⟩ := hall t (List.mem_cons_self)
      obtain ⟨hsub, hobj, hp⟩ := instance?_parts ht'
      obtain ⟨m1, hm1, hc1, _⟩ := matchSubject_complete hc hsub
      obtain ⟨m2, hm2, hc2, _⟩ :=
        matchObject_complete hleq hbnd t.o t'.o m1 σ hc1 hobj
      have hrest : (searchInstance leq bindable g rest m2).isSome = true :=
        ih m2 σ hc2 (fun u hu => hall u (List.mem_cons_of_mem _ hu))
      simp only [searchInstance]
      refine findSome?_isSome_of_mem hmem ?_
      have hpne : (t'.p != t.p) = false := by simp [hp]
      simp only [hpne, Bool.false_eq_true, if_false, hm1, hm2]
      exact hrest


/-! ## Part 2 — whatever the search returns, certifies

Each matcher's success is stated for EVERY later mapping, not only for
the one it returns. That is what carries a step's match past the
bindings the remaining triples add, and it is why no separate
"the label stays bound" invariant is needed. -/

/-- A subject read back from its own term view. -/
theorem toSubject?_toTerm (s : Subject) : s.toTerm.toSubject? = some s := by
  cases s <;> rfl

theorem matchSubject_sound {m m1 : Mapping} {ps gs : Subject}
    (h : matchSubject m ps gs = some m1) :
    Extends m1 m ∧ ∀ m', Extends m' m1 → ps.instance? m'.toFun = some gs := by
  cases ps with
  | iri i =>
      cases gs with
      | bnode b => simp [matchSubject] at h
      | iri j =>
          simp only [matchSubject] at h
          by_cases hij : (i == j) = true
          · rw [if_pos hij] at h
            simp only [Option.some.injEq] at h
            subst h
            have : i = j := eq_of_beq hij
            subst this
            exact ⟨Extends.refl m, fun _ _ => rfl⟩
          · rw [if_neg hij] at h; simp at h
  | bnode b =>
      simp only [matchSubject] at h
      cases hl : m.lookup b with
      | some t =>
          simp only [hl] at h
          by_cases ht : (t == gs.toTerm) = true
          · rw [if_pos ht] at h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨Extends.refl m, fun m' he => ?_⟩
            have hb : m'.toFun b = gs.toTerm := by
              rw [toFun_of_lookup (he b t hl)]; exact eq_of_beq ht
            simp only [Subject.instance?, hb, toSubject?_toTerm]
          · rw [if_neg ht] at h; simp at h
      | none =>
          simp only [hl] at h
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨Extends.cons _ hl, fun m' he => ?_⟩
          have hb : m'.toFun b = gs.toTerm :=
            toFun_of_lookup (he b _ (lookup_cons_self b gs.toTerm m))
          simp only [Subject.instance?, hb, toSubject?_toTerm]

theorem matchObject_sound {leq : Literal → Literal → Bool}
    {bindable : Term → Bool} (hleq : ∀ l, leq l l = true) :
    ∀ (ho go : Term) (m m1 : Mapping),
      matchObject leq bindable m ho go = some m1 →
      Extends m1 m ∧ ∀ m', Extends m' m1 →
        ∃ go', ho.instance? m'.toFun = some go' ∧ termMatch leq go go' = true := by
  intro ho
  induction ho with
  | bnode b =>
      intro go m m1 h
      simp only [matchObject] at h
      cases hl : m.lookup b with
      | some t =>
          simp only [hl] at h
          by_cases ht : (t == go) = true
          · rw [if_pos ht] at h
            simp only [Option.some.injEq] at h
            subst h
            have htg : t = go := eq_of_beq ht
            subst htg
            refine ⟨Extends.refl m, fun m' he => ⟨t, ?_, termMatch_refl hleq t⟩⟩
            simp only [Term.instance?, toFun_of_lookup (he b t hl)]
          · rw [if_neg ht] at h; simp at h
      | none =>
          simp only [hl] at h
          cases hb : bindable go with
          | false => rw [hb] at h; simp at h
          | true =>
              rw [hb] at h
              simp only [if_true, Option.some.injEq] at h
              subst h
              refine ⟨Extends.cons _ hl, fun m' he => ⟨go, ?_, termMatch_refl hleq go⟩⟩
              have : m'.lookup b = some go := he b go (lookup_cons_self b go m)
              simp only [Term.instance?, toFun_of_lookup this]
  | iri i =>
      intro go m m1 h
      simp only [matchObject] at h
      cases hm : termMatch leq go (Term.iri i) with
      | false => rw [hm] at h; simp at h
      | true =>
          rw [hm] at h
          simp only [if_true, Option.some.injEq] at h
          subst h
          refine ⟨Extends.refl m, fun m' _ => ⟨.iri i, rfl, ?_⟩⟩
          cases go <;> simp only [termMatch] at hm ⊢ <;> simp_all
  | literal l =>
      intro go m m1 h
      simp only [matchObject] at h
      cases hm : termMatch leq go (Term.literal l) with
      | false => rw [hm] at h; simp at h
      | true =>
          rw [hm] at h
          simp only [if_true, Option.some.injEq] at h
          subst h
          exact ⟨Extends.refl m, fun m' _ => ⟨.literal l, rfl, hm⟩⟩
  | tripleTerm ps pp po ih =>
      intro go m m1 h
      cases go with
      | tripleTerm gs gp go1 =>
          simp only [matchObject] at h
          by_cases hpp : (pp == gp) = true
          · have hppe : pp = gp := eq_of_beq hpp
            subst hppe
            simp only [beq_self_eq_true, if_true] at h
            cases hs : matchSubject m ps gs with
            | none => simp only [hs] at h; simp at h
            | some ma =>
                simp only [hs] at h
                obtain ⟨hea, hsa⟩ := matchSubject_sound hs
                obtain ⟨heb, hsb⟩ := ih go1 ma m1 h
                refine ⟨heb.trans hea, fun m' he => ?_⟩
                obtain ⟨go', hgo, hmt⟩ := hsb m' he
                refine ⟨.tripleTerm gs pp go', ?_, ?_⟩
                · simp only [Term.instance?, hsa m' (he.trans heb), hgo]
                · simp only [termMatch, hmt, beq_self_eq_true, Bool.and_true]
          · rw [if_neg hpp] at h; simp at h
      | iri _ => simp [matchObject, termMatch] at h
      | bnode _ => simp [matchObject, termMatch] at h
      | literal _ => simp [matchObject, termMatch] at h

theorem findSome?_eq_some_mem {α β : Type} {f : α → Option β} {l : List α}
    {b : β} (h : l.findSome? f = some b) : ∃ a, a ∈ l ∧ f a = some b := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons x xs ih =>
      simp only [List.findSome?] at h
      cases hx : f x with
      | some v =>
          rw [hx] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨x, List.mem_cons_self, hx⟩
      | none =>
          rw [hx] at h
          obtain ⟨a, ha, hfa⟩ := ih h
          exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩

theorem searchInstance_certifies {leq : Literal → Literal → Bool}
    {bindable : Term → Bool} (hleq : ∀ l, leq l l = true) (g : Graph) :
    ∀ (hs : List Triple) (m m' : Mapping),
      searchInstance leq bindable g hs m = some m' →
      Extends m' m ∧ ∀ t ∈ hs, ∃ u, u ∈ g ∧ ∃ t'',
        t.instance? m'.toFun = some t'' ∧ tripleMatch leq u t'' = true := by
  intro hs
  induction hs with
  | nil =>
      intro m m' h
      simp only [searchInstance, Option.some.injEq] at h
      subst h
      exact ⟨Extends.refl _, by intro t ht; cases ht⟩
  | cons t rest ih =>
      intro m m' h
      simp only [searchInstance] at h
      obtain ⟨u, humem, hfu⟩ := findSome?_eq_some_mem h
      by_cases hp : (u.p != t.p) = true
      · rw [if_pos hp] at hfu; simp at hfu
      · rw [if_neg hp] at hfu
        have hpe : u.p = t.p := by simpa using hp
        cases hs1 : matchSubject m t.s u.s with
        | none => simp only [hs1] at hfu; simp at hfu
        | some m1 =>
            simp only [hs1] at hfu
            cases ho1 : matchObject leq bindable m1 t.o u.o with
            | none => simp only [ho1] at hfu; simp at hfu
            | some m2 =>
                simp only [ho1] at hfu
                obtain ⟨he1, hsa⟩ := matchSubject_sound hs1
                obtain ⟨he2, hob⟩ := matchObject_sound hleq t.o u.o m1 m2 ho1
                obtain ⟨he3, hrest⟩ := ih m2 m' hfu
                refine ⟨he3.trans (he2.trans he1), ?_⟩
                intro t0 ht0
                rcases List.mem_cons.mp ht0 with rfl | hmem
                · refine ⟨u, humem, ?_⟩
                  have hsub : t0.s.instance? m'.toFun = some u.s :=
                    hsa m' (he3.trans he2)
                  obtain ⟨go', hgo, hmt⟩ := hob m' he3
                  refine ⟨⟨u.s, t0.p, go'⟩, ?_, ?_⟩
                  · simp only [Triple.instance?, hsub, hgo]
                  · simp only [tripleMatch, hmt, beq_self_eq_true, Bool.and_true,
                               hpe]
                · exact hrest t0 hmem


/-! ## The two halves joined -/

theorem entailsWith_complete {leq : Literal → Literal → Bool}
    {bindable : Term → Bool} (hleq : ∀ l, leq l l = true)
    (hbnd : ∀ t, bindable t = true) {g h : Graph}
    (hspec : ∃ σ : BNodeId → Term, ∀ t ∈ h, ∃ t', t.instance? σ = some t' ∧ t' ∈ g) :
    entailsWith leq bindable g h = true := by
  obtain ⟨σ, hall⟩ := hspec
  have hsome : (searchInstance leq bindable g h []).isSome = true :=
    searchInstance_isSome hleq hbnd g h [] σ (Compat.nil σ) hall
  cases hsr : searchInstance leq bindable g h [] with
  | none => rw [hsr] at hsome; simp at hsome
  | some m' =>
      obtain ⟨_, hcert⟩ := searchInstance_certifies hleq g h [] m' hsr
      simp only [entailsWith, hsr, instanceCert]
      refine List.all_eq_true.mpr ?_
      intro t ht
      obtain ⟨u, humem, t'', hinst, hmatch⟩ := hcert t ht
      simp only [hinst]
      exact List.any_eq_true.mpr ⟨u, humem, hmatch⟩

/-- **Completeness** (RDF 1.1 Semantics §5.2, the interpolation lemma,
read left to right). If some instance of `h` is a subgraph of `g`, the
decision procedure says so. Unconditional: no restriction on the
literals of either graph, because `literalStrictEq` IS literal term
equality. -/
theorem simpleEntails_complete {g h : Graph} (hs : SimpleEntails g h) :
    simpleEntails g h = true :=
  entailsWith_complete (fun l => by simp [literalStrictEq])
    (fun _ => rfl) hs

/-- **The refinement result.** The decision procedure and the
specification agree on every pair of graphs. Soundness is
`simpleEntails_sound` (`EntailmentTheorems.lean`); completeness is
above. -/
theorem simpleEntails_iff_spec (g h : Graph) :
    simpleEntails g h = true ↔ SimpleEntails g h :=
  ⟨simpleEntails_sound, simpleEntails_complete⟩

/-! ## The engine gap this port found, pinned

Premise `a p <<( a p c )>>`; conclusion `a p <<( a p _:b )>>`. The
substitution `_:b ↦ c` turns the conclusion into the premise triple, so
the pair stands in the simple entailment relation. Before `matchObject`
recursed into triple terms the procedure answered `false` on it. -/

private def gapIriA : WfIri := ⟨"http://example.org/a", by decide⟩
private def gapIriP : WfIri := ⟨"http://example.org/p", by decide⟩
private def gapIriC : WfIri := ⟨"http://example.org/c", by decide⟩

private def gapPremise : Graph :=
  [⟨.iri gapIriA, gapIriP, .tripleTerm (.iri gapIriA) gapIriP (.iri gapIriC)⟩]

private def gapConclusion : Graph :=
  [⟨.iri gapIriA, gapIriP, .tripleTerm (.iri gapIriA) gapIriP (.bnode "b")⟩]

/-! The substitution witnesses the relation. -/
#guard (gapConclusion.head?.map (fun t => t.instance? (fun _ => .iri gapIriC)))
         == some (gapPremise.head?)

/-! And the procedure now agrees. -/
#guard simpleEntails gapPremise gapConclusion == true

theorem entailsSimple_tripleTerm_interior_bnode :
    simpleEntails gapPremise gapConclusion = true := by decide

/-! ## Axiom audit -/

#print axioms matchSubject_complete
#print axioms matchObject_complete
#print axioms searchInstance_isSome
#print axioms matchSubject_sound
#print axioms matchObject_sound
#print axioms searchInstance_certifies
#print axioms simpleEntails_complete
#print axioms simpleEntails_iff_spec
#print axioms entailsSimple_tripleTerm_interior_bnode

end L4Factoidal.RDF.SimpleRefinement
