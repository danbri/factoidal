/-
L4Factoidal.Unified.Theory — the unified LBase/IKL theory layer:
schemas, schema satisfaction, schema-relative entailment.

Stage 1 of https://github.com/danbri/factoidal/issues/598, per the
design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §2.2. The
model theory underneath is `L4Factoidal.CL.Semantics` (ISO/IEC 24707
§6.2/§6.3 interpretations with the IKL proposition domain); this
module adds the LBase §2.4 notion of an axiom SCHEMA — a possibly
infinite set of sentences — and entailment relative to a schema plus a
class of interpretations.

Everything here is `Prop`-level and fuel-free: the theory layer states
relations, it does not decide them. The decision procedures stay on
the native side (`RDF.Entailment` etc.); `Unified.RdfAdequacy`
connects the two by theorem.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.CL.Semantics

namespace L4Factoidal.Unified

/-- An axiom schema: a (possibly infinite) set of sentences
(LBase §2.4 axiom schemes; the `rdf:_n` families of RDF 1.1 Semantics
need exactly this). -/
abbrev Schema := CL.Sentence → Prop

/-- The interpretation satisfies every sentence of the schema. -/
def SatisfiesSchema (i : CL.Interp) (S : Schema) : Prop :=
  ∀ s, S s → CL.Satisfies i s

/-- Entailment relative to an interpretation-class condition bundle
AND an axiom schema — the extension mechanism of the design document
§2.2. With the trivial bundle and the empty schema this is plain CL
entailment (`entailsSchema_trivial` below). -/
def EntailsSchema (conds : CL.Interp → Prop) (S : Schema)
    (premises : List CL.Sentence) (conclusion : CL.Sentence) : Prop :=
  ∀ i : CL.Interp, conds i → SatisfiesSchema i S →
    CL.SatisfiesAll i premises → CL.Satisfies i conclusion

/-- `Unified.Entails` is `CL.Entails` (design document §4): plain
first-order entailment over every CL interpretation. -/
abbrev Entails : List CL.Sentence → CL.Sentence → Prop := CL.Entails

/-- Satisfaction-equivalence of two premise lists: every
interpretation satisfies the one exactly when it satisfies the other.
Stronger than mutual entailment, and what the scoping lemmas of
`Unified.RdfAdequacy` actually deliver. -/
def EntailEquiv (ps qs : List CL.Sentence) : Prop :=
  ∀ i : CL.Interp, CL.SatisfiesAll i ps ↔ CL.SatisfiesAll i qs

/-! ## Composition of bundles and schemas -/

/-- The empty schema: no axioms. -/
def emptySchema : Schema := fun _ => False

/-- Union of two schemas. -/
def schemaUnion (S1 S2 : Schema) : Schema := fun s => S1 s ∨ S2 s

/-- Conjunction of two condition bundles. -/
def condAnd (c1 c2 : CL.Interp → Prop) : CL.Interp → Prop :=
  fun i => c1 i ∧ c2 i

/-- The trivial condition bundle: every interpretation. -/
def condTrue : CL.Interp → Prop := fun _ => True

/-! ## Basic laws -/

theorem satisfiesSchema_empty (i : CL.Interp) : SatisfiesSchema i emptySchema :=
  fun _ hs => False.elim hs

theorem satisfiesSchema_union_iff (i : CL.Interp) (S1 S2 : Schema) :
    SatisfiesSchema i (schemaUnion S1 S2) ↔
      SatisfiesSchema i S1 ∧ SatisfiesSchema i S2 := by
  constructor
  · intro h
    exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
  · rintro ⟨h1, h2⟩ s hs
    rcases hs with hs | hs
    · exact h1 s hs
    · exact h2 s hs

/-- With the trivial bundle and the empty schema, `EntailsSchema` is
plain CL entailment. -/
theorem entailsSchema_trivial (premises : List CL.Sentence)
    (conclusion : CL.Sentence) :
    EntailsSchema condTrue emptySchema premises conclusion ↔
      Entails premises conclusion := by
  constructor
  · intro h i _ hsat
    exact h i trivial (satisfiesSchema_empty i) hsat
  · intro h i _ _ hsat
    exact h i trivial hsat

/-- Monotonicity: entailment under a bundle and schema survives
strengthening the bundle and enlarging the schema (a smaller
interpretation class entails no less). -/
theorem entailsSchema_mono {conds conds' : CL.Interp → Prop}
    {S S' : Schema} {premises : List CL.Sentence}
    {conclusion : CL.Sentence}
    (hc : ∀ i, conds' i → conds i) (hs : ∀ s, S s → S' s)
    (h : EntailsSchema conds S premises conclusion) :
    EntailsSchema conds' S' premises conclusion := by
  intro i hci hsi hsat
  exact h i (hc i hci) (fun s hss => hsi s (hs s hss)) hsat

theorem EntailEquiv.refl (ps : List CL.Sentence) : EntailEquiv ps ps :=
  fun _ => Iff.rfl

theorem EntailEquiv.symm {ps qs : List CL.Sentence}
    (h : EntailEquiv ps qs) : EntailEquiv qs ps :=
  fun i => (h i).symm

theorem EntailEquiv.trans {ps qs rs : List CL.Sentence}
    (h1 : EntailEquiv ps qs) (h2 : EntailEquiv qs rs) : EntailEquiv ps rs :=
  fun i => (h1 i).trans (h2 i)

/-- Satisfaction-equivalent premise lists entail the same
conclusions — the transfer that lets the merge lemma rewrite premise
lists inside entailment claims. -/
theorem entailEquiv_entails_iff {ps qs : List CL.Sentence}
    (h : EntailEquiv ps qs) (c : CL.Sentence) :
    Entails ps c ↔ Entails qs c := by
  constructor
  · intro he i hT hsat
    exact he i hT ((h i).mpr hsat)
  · intro he i hT hsat
    exact he i hT ((h i).mp hsat)

end L4Factoidal.Unified
