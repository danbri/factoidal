/-
L4Factoidal.RDF.EntailmentTheorems — the simple-entailment decision
procedure is sound for its specification.

`simpleEntails_sound`: if `simpleEntails g h = true` then
`SimpleEntails g h` (RDF 1.1 Semantics §5.2) — some instance of `h` is
a subgraph of `g`. As in `IsomorphismTheorems.lean`, nothing is needed
about the SEARCH: the answer is `true` only when `instanceCert` passes,
and the certificate is read off directly as the witness `σ :=
Mapping.toFun m`.

The strict literal comparison `literalStrictEq` is `==` on `Literal`,
whose `BEq` comes from `DecidableEq` (lawful — pitfall 1 of the
skill), so a `termMatch` under it is propositional equality
(`termMatch_strict_eq`). The regime variants (`literalValueEq D`) are
deliberately NOT given a soundness theorem: their specification is
model-theoretic (D-interpretations) and is not ported.

No `sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.Entailment

namespace L4Factoidal.RDF

/-- Under strict literal identity, a term match is equality. -/
theorem termMatch_strict_eq : ∀ {u t : Term},
    termMatch literalStrictEq u t = true → u = t := by
  intro u
  induction u with
  | iri i =>
    intro t h; cases t <;> simp_all [termMatch, Subtype.ext_iff]
  | bnode b =>
    intro t h; cases t <;> simp_all [termMatch]
  | literal l =>
    intro t h
    cases t <;> simp only [termMatch] at h <;> try simp at h
    simp only [literalStrictEq, beq_iff_eq] at h
    rw [Subtype.ext h]
  | tripleTerm s p o ih =>
    intro t h
    cases t <;> simp only [termMatch, Bool.and_eq_true, beq_iff_eq] at h <;> try simp at h
    obtain ⟨⟨hs, hp⟩, ho⟩ := h
    rw [hs, hp, ih ho]

/-- Under strict literal identity, a triple match is equality. -/
theorem tripleMatch_strict_eq {u t : Triple}
    (h : tripleMatch literalStrictEq u t = true) : u = t := by
  simp only [tripleMatch, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  have ho' := termMatch_strict_eq ho
  cases u; cases t
  simp_all

/-- The certificate, under strict identity, yields the witness. -/
theorem instanceCert_strict_sound {m : Mapping} {g h : Graph}
    (hc : instanceCert literalStrictEq m g h = true) : SimpleEntails g h := by
  refine ⟨m.toFun, ?_⟩
  intro t ht
  simp only [instanceCert, List.all_eq_true] at hc
  have := hc t ht
  revert this
  cases hinst : t.instance? m.toFun with
  | none => intro h'; simp at h'
  | some t' =>
    intro h'
    simp only [List.any_eq_true] at h'
    obtain ⟨u, hu, hm⟩ := h'
    exact ⟨t', rfl, tripleMatch_strict_eq hm ▸ hu⟩

/-- **Soundness of `simpleEntails`** (RDF 1.1 Semantics §5.2). -/
theorem simpleEntails_sound {g h : Graph} (hd : simpleEntails g h = true) :
    SimpleEntails g h := by
  unfold simpleEntails entailsWith at hd
  revert hd
  cases searchInstance literalStrictEq (fun _ => true) g h [] with
  | none => intro hd; simp at hd
  | some m => intro hd; exact instanceCert_strict_sound hd

/-- Reflexivity of the specification: every graph simply entails
itself (the identity instance). -/
theorem SimpleEntails.refl (g : Graph) : SimpleEntails g g := by
  refine ⟨fun b => .bnode b, ?_⟩
  intro t ht
  refine ⟨t, ?_, ht⟩
  obtain ⟨s, p, o⟩ := t
  have hs : s.instance? (fun b => Term.bnode b) = some s := by
    cases s <;> simp [Subject.instance?, Term.toSubject?]
  have ho : ∀ o : Term, o.instance? (fun b => Term.bnode b) = some o := by
    intro o
    induction o with
    | iri _ => simp [Term.instance?]
    | bnode _ => simp [Term.instance?]
    | literal _ => simp [Term.instance?]
    | tripleTerm s' _ o' ih =>
      have hs' : s'.instance? (fun b => Term.bnode b) = some s' := by
        cases s' <;> simp [Subject.instance?, Term.toSubject?]
      simp [Term.instance?, hs', ih]
  simp [Triple.instance?, hs, ho]

end L4Factoidal.RDF
