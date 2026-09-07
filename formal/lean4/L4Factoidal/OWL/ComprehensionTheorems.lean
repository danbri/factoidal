/-
L4Factoidal.OWL.ComprehensionTheorems — the specification of the
comprehension / existential-witness layer, and the proof that the
executable layer emits nothing outside it.

`Comprehension.lean` computes; this file says what it is allowed to
compute. The relation is `CompStar`, and `comprehensionLayer_sound` is
the statement the corpus probe rests on: every triple the layer returns
is either a premise or a `CompStar` consequence of premises.

## Why `CompStar` and not `RLRules.Derives`

`Derives` is the OWL 2 RL/RDF rule relation. Its truth-preservation
theorem (`RLSemantics.rl_derives_holds`) concludes at a FIXED blank-node
assignment, extended only at the two labels the RL table's own
comprehension rows mint. The rows here mint six further label families
and rest on OWL 2 RDF-Based Semantics § 8 comprehension conditions that
the RL profile does not assume. Putting them in `Derives` would either
break that theorem or silently widen what the RL profile claims. They
get their own relation, for the same reason `RLRules.ExtClash` is not
`RLRules.Clash`.

## What is proved here, and what is not

PROVED: `comprehensionLayer_sound` — the executable layer is contained
in `CompStar`. This is the obligation that keeps the probe honest about
WHICH rules produced a pass, and it is the same obligation
`RLTheorems.detectClashPlus_sound` discharges for the clash side.

NOT PROVED HERE, and named rather than left to inference: the
MODEL-THEORETIC soundness of `CompStar` itself — that under an
interpretation meeting the § 8 comprehension conditions, and an
assignment extended at the six reserved label families, every
`CompStar base t` holds whenever `base` does. `RLSemantics` carries the
two-family version of that argument (`rlExtend`, `compWitness`,
`minc1Witness`); the six-family version needs a `compExtend` decoding
each label family and one condition per row. Until it lands, each row's
semantic licence is the citation in `Comprehension.lean`'s header table,
which is the standing of the F\* engine's own comprehension layer.
Tracked as the open obligation in
`docs/designissues/2026-09-07-lean-owl-corpus-gap.md`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.Comprehension
import L4Factoidal.OWL.RLTheorems

namespace L4Factoidal.OWL.Comp

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

/-! ## The relation -/

/-- What the layer may derive from `base`.

Each constructor's premises are `CompStar` rather than `∈ base`, so the
relation is closed under the layer's own stratification: a stage that
reads an earlier stage's output reads `CompStar` facts, and its
conclusions are `CompStar` too. `base` alone would not be closed that
way, and the stage-2 witness row genuinely needs it (the restriction
node it fires on is minted by stage 1).

Two constructors carry an executable side condition rather than a
semantic characterisation — `pairwiseDifferent` and
`disjointPropPairs`. In both cases the condition IS the decision, and
the lemma that unpacks it into graph facts follows the constructor.
`RLRules.prpFpLit` uses the same convention and names it the same way. -/
inductive CompStar (base : Graph) : Triple → Prop where
  /-- A premise. -/
  | base {t : Triple} (h : t ∈ base) : CompStar base t
  /-- **comp-uni1** — RDF-Based Semantics § 8.2 at one canonical
  instance per named class, with § 8.1's one-cell spine. -/
  | uni1 {c : WfIri} {t : Triple}
      (hc : CompStar base ⟨Subject.iri c, rdfType, Term.iri owlClass⟩)
      (ht : t ∈ uni1Triples c) : CompStar base t
  /-- **comp-trp-chain** — `TransitiveObjectProperty(P)` and
  `SubObjectPropertyOf(ObjectPropertyChain(P P), P)` have the same
  content (§ 5.10), with § 8.1's two-cell spine. -/
  | trpChain {p : WfIri} {t : Triple}
      (hp : CompStar base ⟨Subject.iri p, rdfType,
        Term.iri owlTransitiveProperty⟩)
      (ht : t ∈ trpChainTriples p) : CompStar base t
  /-- **comp-adf-clique** — pairwise `owl:differentFrom` is what an
  `owl:AllDifferent` node over the same members says (§ 5.7), with
  § 8.1's spine over the member list. The premise is the DECISION
  `pairwiseDifferent`; `pairwiseDifferent_sound` below turns it into the
  graph facts. -/
  | adfClique {g : Graph} {ms : List WfIri} {t : Triple}
      (hg : ∀ u ∈ g, CompStar base u)
      (hpw : pairwiseDifferent g ms = true)
      (ht : t ∈ adfEmission ms) : CompStar base t
  /-- **pdw-diff**, shared value — `IEXT(p1) ∩ IEXT(p2) = ∅` (§ 5.10)
  and one shared value force the two subjects apart. The disjointness
  premise is the DECISION `disjointPropPairs`;
  `mem_disjointPropPairs_cases` below splits it into the asserted
  `owl:propertyDisjointWith` case and the `owl:AllDisjointProperties`
  case. -/
  | pdwSharedValue {g : Graph} {p1 p2 : WfIri} {x y : Subject} {v : Term}
      (hg : ∀ u ∈ g, CompStar base u)
      (hdis : (p1, p2) ∈ disjointPropPairs g)
      (h1 : CompStar base ⟨x, p1, v⟩)
      (h2 : CompStar base ⟨y, p2, v⟩)
      (hne : x ≠ y) : CompStar base ⟨x, owlDifferentFrom, y.toTerm⟩
  /-- **pdw-diff**, shared subject — the same argument on the object
  side. -/
  | pdwSharedSubject {g : Graph} {p1 p2 : WfIri} {x : Subject}
      {o1 o2 : Term} {o1s : Subject}
      (hg : ∀ u ∈ g, CompStar base u)
      (hdis : (p1, p2) ∈ disjointPropPairs g)
      (h1 : CompStar base ⟨x, p1, o1⟩)
      (h2 : CompStar base ⟨x, p2, o2⟩)
      (ho1 : o1 = o1s.toTerm)
      (hne : o1 ≠ o2) : CompStar base ⟨o1s, owlDifferentFrom, o2⟩
  /-- **svf-thing-mat** — `owl:Thing` is the universal class, so any
  `P`-edge puts its subject in `SomeValuesFrom(P, owl:Thing)`, which
  § 8.4 provides. -/
  | svfThingMat {p : WfIri} {x : Subject} {y : Term} {t : Triple}
      (hedge : CompStar base ⟨x, p, y⟩)
      (ht : t ∈ svfThingShape p ++
        [(⟨x, rdfType, Term.bnode (svfThingRestriction p)⟩ : Triple)]) :
      CompStar base t
  /-- **svf-thing-wit** — membership in a `someValuesFrom` restriction
  asserts a successor (§ 5.4); the witness names it. -/
  | svfThingWit {p : WfIri} {r x : Subject}
      (hsvf : CompStar base ⟨r, owlSomeValuesFrom, Term.iri owlThing⟩)
      (honp : CompStar base ⟨r, owlOnProperty, Term.iri p⟩)
      (hty : CompStar base ⟨x, rdfType, r.toTerm⟩) :
      CompStar base ⟨x, p, Term.bnode (svfThingWitnessNode p x)⟩
  /-- **hasself-synth** — a self-loop puts its subject in `HasSelf(P)`
  (§ 5.4), which § 8.4 provides. -/
  | hasSelfSynth {p : WfIri} {x : Subject} {t : Triple}
      (hedge : CompStar base ⟨x, p, x.toTerm⟩)
      (ht : t ∈ hasSelfShape p ++
        [(⟨x, rdfType, Term.bnode (hasSelfRestriction p)⟩ : Triple)]) :
      CompStar base t

/-! ## Unpacking the two executable side conditions -/

/-- `pairwiseDifferent` decides exactly the graph facts its name
claims. -/
theorem pairwiseDifferent_sound {g : Graph} {ms : List WfIri}
    (h : pairwiseDifferent g ms = true) :
    ∀ a ∈ ms, ∀ b ∈ ms, a ≠ b →
      (⟨Subject.iri a, owlDifferentFrom, Term.iri b⟩ : Triple) ∈ g := by
  intro a ha b hb hne
  simp only [pairwiseDifferent, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  have h2 := h a ha b hb
  rcases h2 with h2 | h2
  · exact absurd h2 hne
  · exact mem_of_memB h2

/-! ## The layer is contained in the relation -/

/-- One stage of the layer preserves "every triple is `CompStar`",
given that every triple each row emits from a `CompStar` driving triple
is itself `CompStar`. -/
theorem foldl_addAll_sound {base : Graph} (rows : Triple → List Triple) :
    ∀ (drive : List Triple) (g : Graph),
      (∀ u ∈ g, CompStar base u) →
      (∀ d ∈ drive, ∀ t ∈ rows d, CompStar base t) →
      ∀ t ∈ drive.foldl (fun acc d => addAll acc (rows d)) g,
        CompStar base t := by
  intro drive
  induction drive with
  | nil => intro g hg _ t ht; exact hg t ht
  | cons d ds ih =>
    intro g hg hrows t ht
    refine ih (addAll g (rows d)) ?_ ?_ t ht
    · intro u hu
      rcases mem_addAll_cases _ g hu with hu' | hu'
      · exact hg u hu'
      · exact hrows d (List.mem_cons_self ..) u hu'
    · intro d' hd'; exact hrows d' (List.mem_cons_of_mem _ hd')

/-! ## Row soundness

One lemma per row: everything the row emits from a `CompStar` driving
triple, over a graph whose triples are all `CompStar`, is `CompStar`. -/

theorem compUni1For_sound {base : Graph} {d t : Triple}
    (hd : CompStar base d) (ht : t ∈ compUni1For d) : CompStar base t := by
  simp only [compUni1For] at ht
  split at ht
  case isFalse => cases ht
  case isTrue hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    simp only [List.mem_flatMap] at ht
    obtain ⟨c, hc, ht⟩ := ht
    have hs : d.s = Subject.iri c := mem_subjIri hc
    refine CompStar.uni1 ?_ ht
    have hdd : (⟨Subject.iri c, rdfType, Term.iri owlClass⟩ : Triple) = d := by
      cases d; simp_all
    rw [hdd]; exact hd

theorem compTrpChainFor_sound {base : Graph} {d t : Triple}
    (hd : CompStar base d) (ht : t ∈ compTrpChainFor d) : CompStar base t := by
  simp only [compTrpChainFor] at ht
  split at ht
  case isFalse => cases ht
  case isTrue hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    simp only [List.mem_flatMap] at ht
    obtain ⟨p, hp, ht⟩ := ht
    have hs : d.s = Subject.iri p := mem_subjIri hp
    refine CompStar.trpChain ?_ ht
    have hdd : (⟨Subject.iri p, rdfType,
        Term.iri owlTransitiveProperty⟩ : Triple) = d := by
      cases d; simp_all
    rw [hdd]; exact hd

theorem compAdfCliqueFor_sound {base g : Graph} {d t : Triple}
    (hg : ∀ u ∈ g, CompStar base u) (ht : t ∈ compAdfCliqueFor g d) :
    CompStar base t := by
  simp only [compAdfCliqueFor] at ht
  split at ht
  case isFalse => cases ht
  case isTrue =>
    simp only [List.mem_flatMap] at ht
    obtain ⟨x, _, ht⟩ := ht
    split at ht
    case isTrue => cases ht
    case isFalse hcond =>
      have hpw : pairwiseDifferent g
          (sortIris (dedupIris (x :: diffPartners g x))) = true := by
        cases hb : pairwiseDifferent g
            (sortIris (dedupIris (x :: diffPartners g x))) with
        | true => rfl
        | false => exact absurd (by simp [hb]) hcond
      exact CompStar.adfClique hg hpw ht

theorem svfThingMatFor_sound {base : Graph} {d t : Triple}
    (hd : CompStar base d) (ht : t ∈ svfThingMatFor d) : CompStar base t := by
  simp only [svfThingMatFor] at ht
  split at ht
  case isFalse => cases ht
  case isTrue =>
    refine CompStar.svfThingMat (x := d.s) (p := d.p) (y := d.o) ?_ ?_
    · have : (⟨d.s, d.p, d.o⟩ : Triple) = d := by cases d; rfl
      rw [this]; exact hd
    · exact ht

theorem hasSelfSynthFor_sound {base : Graph} {d t : Triple}
    (hd : CompStar base d) (ht : t ∈ hasSelfSynthFor d) : CompStar base t := by
  simp only [hasSelfSynthFor] at ht
  split at ht
  case isFalse => cases ht
  case isTrue hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    refine CompStar.hasSelfSynth (x := d.s) (p := d.p) ?_ ?_
    · have : (⟨d.s, d.p, d.s.toTerm⟩ : Triple) = d := by
        cases d; simp_all
      rw [this]; exact hd
    · exact ht

theorem svfThingWitFor_sound {base g : Graph} {d t : Triple}
    (hg : ∀ u ∈ g, CompStar base u) (hd : CompStar base d)
    (ht : t ∈ svfThingWitFor g d) : CompStar base t := by
  simp only [svfThingWitFor] at ht
  split at ht
  case isFalse => cases ht
  case isTrue hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    simp only [List.mem_flatMap, List.mem_map] at ht
    obtain ⟨op, hop, p, hp, m, hm, rfl⟩ := ht
    obtain ⟨hopg, hops, hopp⟩ := mem_withSubjPred hop
    obtain ⟨hmg, hmp, hmo⟩ := mem_withPredObj hm
    refine CompStar.svfThingWit (r := d.s) ?_ ?_ ?_
    · have : (⟨d.s, owlSomeValuesFrom, Term.iri owlThing⟩ : Triple) = d := by
        cases d; simp_all
      rw [this]; exact hd
    · exact hg _ (mem_of_parts hopg hops hopp (mem_asIri hp))
    · exact hg _ (mem_of_parts hmg rfl hmp hmo)

theorem pdwDiffFor_sound {base g : Graph} {d t : Triple}
    (hg : ∀ u ∈ g, CompStar base u) (hd : CompStar base d)
    (ht : t ∈ pdwDiffFor g d) : CompStar base t := by
  simp only [pdwDiffFor, List.mem_flatMap] at ht
  obtain ⟨pr, hpr, ht⟩ := ht
  split at ht
  case isTrue => cases ht
  case isFalse hpeq =>
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hpeq
    have hdd : CompStar base ⟨d.s, pr.1, d.o⟩ := by
      have : (⟨d.s, pr.1, d.o⟩ : Triple) = d := by cases d; simp_all
      rw [this]; exact hd
    simp only [List.mem_append, List.mem_filterMap] at ht
    rcases ht with ht | ht
    · obtain ⟨u, hu, hsome⟩ := ht
      obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
      split at hsome
      · cases hsome
      · rename_i hne
        simp only [Option.some.injEq] at hsome
        subst hsome
        exact CompStar.pdwSharedValue hg hpr hdd
          (hg _ (mem_of_parts hug rfl hup huo))
          (by simp only [beq_iff_eq] at hne; exact fun h => hne h.symm)
    · obtain ⟨u, hu, hsome⟩ := ht
      obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
      split at hsome
      · cases hsome
      · rename_i hne
        split at hsome
        · rename_i os rest heq
          simp only [Option.some.injEq] at hsome
          subst hsome
          refine CompStar.pdwSharedSubject (o2 := u.o) hg hpr hdd
            (hg _ (mem_of_parts hug hus hup rfl)) ?_
            (by simp only [beq_iff_eq] at hne; exact fun h => hne h.symm)
          exact mem_asSubject (by rw [heq]; exact List.mem_cons_self ..)
        · cases hsome

/-! ## The layer -/

theorem layerStage1_sound (base : Graph) :
    ∀ t ∈ layerStage1 base, CompStar base t := by
  have hbase : ∀ u ∈ base, CompStar base u := fun _ h => CompStar.base h
  refine foldl_addAll_sound _ base base hbase ?_
  intro d hd t ht
  simp only [stage1For] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact svfThingMatFor_sound (hbase d hd) ht
  · exact hasSelfSynthFor_sound (hbase d hd) ht

theorem layerStage2_sound (base : Graph) :
    ∀ t ∈ layerStage2 base, CompStar base t := by
  have h1 := layerStage1_sound base
  refine foldl_addAll_sound _ _ _ h1 ?_
  intro d hd t ht
  exact svfThingWitFor_sound h1 (h1 d hd) ht

theorem layerStage3_sound (base : Graph) :
    ∀ t ∈ layerStage3 base, CompStar base t := by
  have hbase : ∀ u ∈ base, CompStar base u := fun _ h => CompStar.base h
  refine foldl_addAll_sound _ base _ (layerStage2_sound base) ?_
  intro d hd t ht
  exact pdwDiffFor_sound hbase (hbase d hd) ht

/-- **The layer emits nothing outside the relation.** This is what the
probe's PositiveEntailmentTest pass rests on: a conclusion matched
against `comprehensionLayer` is matched against `base` plus `CompStar`
consequences of `base`, and nothing else. -/
theorem comprehensionLayer_sound (base : Graph) :
    ∀ t ∈ comprehensionLayer base, CompStar base t := by
  have h3 := layerStage3_sound base
  refine foldl_addAll_sound _ _ _ h3 ?_
  intro d hd t ht
  simp only [stage4For] at ht
  rcases List.mem_append.mp ht with ht | ht
  · rcases List.mem_append.mp ht with ht | ht
    · exact compUni1For_sound (h3 d hd) ht
    · exact compTrpChainFor_sound (h3 d hd) ht
  · exact compAdfCliqueFor_sound h3 ht

end L4Factoidal.OWL.Comp
