/-
L4Factoidal.SPARQL.EntailmentRegimeRdfs — SPARQL under the RDFS regime.

Port of `formal/fstar/SPARQL11.EntailmentRegime.RDFS.fst` (1,115 lines):
LAYER 3 of the query-rung reduction, the module that JOINS the other
two. It proves no new entailment content of its own — that is the
design, and the F\* banner says so.

* LAYER 1 is `RDFS.closure_sound` and `RDFS.closure_complete_of_saturated`
  (`RDFS/ClosureTheorems.lean`): the ρdf closure decides `RDFS.Derives`.
* LAYER 2 is `SPARQL.evalBgp_instantiates_into_graph`
  (`SPARQL/BgpRefinement.lean`): a solution of the evaluator, substituted
  back, lands in the graph it ran on.
* LAYER 3, here, composes them AT the graph `RDFS.closure g fuel`.

## The naming

`SPARQL11.Algebra.BGPRefinement`'s banner sets the family rule: a module
belongs to the `SPARQL11.Algebra.*` family when it refines a named
shipping function and MENTIONS NO ENTAILMENT RELATION. This one mentions
`RDFS.Derives` and refines nothing new, so it is named after the W3C
document it discharges a statement of — SPARQL 1.1 Entailment Regimes
(W3C Recommendation 21 March 2013), §2 (a regime redefines BGP matching
only) and §6 (the RDFS regime) — with the regime name last, so a future
D-entailment or OWL-RL regime theorem gets a sibling rather than a
rename.

## What is proved and what is NOT

PROVED, with no side condition: SOUNDNESS. Every answer the shipping
evaluator returns over the ρdf closure is an answer the regime licenses.
Because both layers land at the ENGINE equality `Triple.eqb` rather than
at structural equality, the licensed triple is stated as one that is
`Triple.eqb`-equal to the answer:

    theorem rdfsRegime_bgp_sound … :
      ∀ t ∈ instBgp q mu, ∃ u, RDFS.Derives g u ∧ u.eqb t = true

`rdfsRegime_bgp_sound_exact` sharpens it to `RDFS.Derives g t` on the
fragment where the two equalities coincide — a closure whose literals are
`GraphExact` and an answer triple that is `TripleExact`. That fragment is
the counterpart of the F\* `graph_frag` / `bgp_frag`, reached here as a
COROLLARY of the unconditional theorem rather than as its scope.

NOT PROVED: COMPLETENESS is conditional, on the same gap the F\* module
names. The F\* tree closed its version of that gap in its part 9; this
port does not, and `EvalBgpCompleteAt` below is the named hypothesis, not
a lemma. `rdfsRegime_bgp_complete_conditional` composes correctly and
assumes it; a reader must not read it as an unconditional completeness
result.

## Why saturation is a hypothesis and not a fact

`RDFS.closure` is fuel-bounded. With the fuel exhausted, the closure is
NOT the RDFS closure and the completeness direction is false. Every
completeness statement below therefore carries
`step (closure g fuel) = closure g fuel`, which
`RDFS.closure_saturated_or_underfueled` turns into "the fuel was
enough". Soundness needs no such hypothesis: a short closure derives
less, and less is still sound.
-/
import L4Factoidal.SPARQL.BgpRefinement
import L4Factoidal.RDFS.ClosureTheorems
import L4Factoidal.RDF.EntailmentSimpleSpec

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## The regime relation on a whole answer -/

/-- The RDFS regime licenses a triple, up to the engine equality. The
`∃ u` is not slack in the specification — it is the exact strength both
layers deliver, for the reason `SPARQL.BgpRefinement`'s header gives. -/
def RdfsLicenses (g : Graph) (t : Triple) : Prop :=
  ∃ u, RDFS.Derives g u ∧ u.eqb t = true

theorem RdfsLicenses.of_derives {g : Graph} {t : Triple} (h : RDFS.Derives g t) :
    RdfsLicenses g t := ⟨t, h, by simp⟩

/-! ## Soundness -/

/-- Layer 1, read out of the engine membership layer 2 produces. -/
theorem licenses_of_graphMem_closure {g : Graph} {fuel : Nat} {t : Triple}
    (h : Graph.mem t (RDFS.closure g fuel) = true) : RdfsLicenses g t := by
  obtain ⟨u, hu, hue⟩ := exists_of_graphMem h
  exact ⟨u, RDFS.closure_sound fuel g hu, hue⟩

/-- **Soundness of the RDFS regime at the BGP level.** Every solution
the shipping evaluator returns over the ρdf closure instantiates to
triples the regime licenses from the ORIGINAL graph.

No fragment hypothesis, no saturation hypothesis, no groundness
hypothesis. -/
theorem rdfsRegime_bgp_sound (g : Graph) (q : Bgp) (fuel : Nat) {mu : Binding}
    (h : mu ∈ evalBgp q (RDFS.closure g fuel)) :
    ∀ t ∈ instBgp q mu, RdfsLicenses g t := fun t ht =>
  licenses_of_graphMem_closure
    (evalBgp_instantiates_into_graph q (RDFS.closure g fuel) h t ht)

/-! ### The fragment where the two equalities coincide

`Term.eqb` is coarser than structural equality in exactly one place —
literals, where `rdf:XMLLiteral` compares by canonical XML and language
tags compare case-insensitively. `LitExact` names the literals where it
is not coarser, and on those the existential collapses. -/

/-- Two `LitExact` literals that the engine equality accepts are the
same record. `Literal.eqb` is coarser than record equality in exactly two
places — `rdf:XMLLiteral` lexical forms compare by canonical XML, and
language tags compare case-insensitively — and `LitExact` rules out both.
-/
theorem literalExact_eqb_eq {a b : Literal} (ha : LitExact a) (hb : LitExact b)
    (h : Literal.eqb a b = true) : a = b := by
  obtain ⟨ax, ad, atag, adir⟩ := a
  obtain ⟨bx, bd, btag, bdir⟩ := b
  simp only [LitExact] at ha hb
  simp only [Literal.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hx, hd⟩, hl⟩, hdir⟩ := h
  rw [if_neg (by simp [ha.1])] at hx
  have hx' : ax = bx := by simpa using hx
  subst hx'; subst hd; subst hdir
  cases atag <;> cases btag <;>
    simp_all [langTagOptionEq, langTagEq]

theorem termExact_eqb_eq : ∀ {a b : Term}, TermExact a → TermExact b →
    a.eqb b = true → a = b := by
  intro a
  induction a with
  | iri i => intro b _ _ h; exact (Term.eqb_iri (by rwa [Term.eqb_symm] at h)).symm
  | bnode x => intro b _ _ h; cases b <;> simp_all [Term.eqb]
  | literal l =>
      intro b ha hb h
      cases b with
      | literal m =>
          simp only [Term.eqb] at h
          exact congrArg Term.literal (Subtype.ext (literalExact_eqb_eq ha hb h))
      | iri _ => simp [Term.eqb] at h
      | bnode _ => simp [Term.eqb] at h
      | tripleTerm _ _ _ => simp [Term.eqb] at h
  | tripleTerm s p o ih =>
      intro b ha hb h
      cases b with
      | tripleTerm s' p' o' =>
          simp only [Term.eqb, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hs, hp⟩, ho⟩ := h
          have hoo : o = o' :=
            ih (show TermExact o from ha) (show TermExact o' from hb) ho
          rw [Subject.eqb_eq hs, hp, hoo]
      | iri _ => simp [Term.eqb] at h
      | bnode _ => simp [Term.eqb] at h
      | literal _ => simp [Term.eqb] at h

theorem tripleExact_eqb_eq {a b : Triple} (ha : TripleExact a) (hb : TripleExact b)
    (h : a.eqb b = true) : a = b := by
  simp only [Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  have hss := Subject.eqb_eq hs
  have hoo := termExact_eqb_eq (a := a.o) (b := b.o) ha hb ho
  cases a; cases b
  simp_all

/-- **Soundness on the exact fragment.** Where the closure's literals and
the answer triple are `Exact`, the licensed triple IS the answer.

This is the F\* module's `graph_frag` / `bgp_frag` shape, obtained as a
corollary rather than assumed as a scope. -/
theorem rdfsRegime_bgp_sound_exact (g : Graph) (q : Bgp) (fuel : Nat)
    {mu : Binding} (hex : GraphExact (RDFS.closure g fuel))
    (h : mu ∈ evalBgp q (RDFS.closure g fuel)) :
    ∀ t ∈ instBgp q mu, TripleExact t → RDFS.Derives g t := by
  intro t ht hte
  obtain ⟨u, hu, hue⟩ :=
    exists_of_graphMem (evalBgp_instantiates_into_graph q (RDFS.closure g fuel) h t ht)
  have : u = t := tripleExact_eqb_eq (hex u hu) hte hue
  exact this ▸ RDFS.closure_sound fuel g hu

/-! ## Completeness, conditional on a named gap

The F\* module records the gap as finding BR-4 and later closes it in
its own part 9. This port does NOT close it. `EvalBgpCompleteAt` is a
hypothesis; a theorem taking it is a composition statement, not a
completeness result. -/

/-- THE NAMED GAP: the evaluator returns `mu` whenever `mu`'s
instantiation of `q` sits inside the graph. Not proved anywhere in this
tree. -/
def EvalBgpCompleteAt (q : Bgp) (c : Graph) (mu : Binding) : Prop :=
  (∀ t ∈ instBgp q mu, Graph.mem t c = true) → mu ∈ evalBgp q c

/-- **Completeness, conditional.** With the fuel enough for saturation
and the gap assumed, an answer the regime licenses from `g` is an answer
the evaluator returns over the closure. -/
theorem rdfsRegime_bgp_complete_conditional (g : Graph) (q : Bgp) (fuel : Nat)
    {mu : Binding}
    (hsat : RDFS.step (RDFS.closure g fuel) = RDFS.closure g fuel)
    (hgap : EvalBgpCompleteAt q (RDFS.closure g fuel) mu)
    (hlic : ∀ t ∈ instBgp q mu, RDFS.Derives g t) :
    mu ∈ evalBgp q (RDFS.closure g fuel) :=
  hgap (fun t ht => RDFS.closure_complete_of_saturated hsat (hlic t ht))

/-- The two halves together, under the gap and saturation. M3's target
shape: the evaluator's answer set over the ρdf closure IS the regime's,
on the exact fragment. -/
theorem rdfsRegime_bgp_exact_iff (g : Graph) (q : Bgp) (fuel : Nat)
    {mu : Binding}
    (hsat : RDFS.step (RDFS.closure g fuel) = RDFS.closure g fuel)
    (hgap : EvalBgpCompleteAt q (RDFS.closure g fuel) mu)
    (hex : GraphExact (RDFS.closure g fuel))
    (hall : ∀ t ∈ instBgp q mu, TripleExact t) :
    mu ∈ evalBgp q (RDFS.closure g fuel) ↔
      ∀ t ∈ instBgp q mu, RDFS.Derives g t := by
  constructor
  · intro h t ht
    exact rdfsRegime_bgp_sound_exact g q fuel hex h t ht (hall t ht)
  · exact rdfsRegime_bgp_complete_conditional g q fuel hsat hgap

/-! ## The ASK corollary

SPARQL 1.1 Entailment Regimes §2: "an entailment regime specifies … how
a basic graph pattern BGP is matched", and nothing above BGP matching
changes. So ASK over a BGP is the non-emptiness of the solution sequence
the theorems above characterise, and the algebra layer is INHERITED
rather than reproved. -/

/-- ASK at the BGP level. The F\* module records why this is not spelled
`eval_ask_query`: that entry point builds a SELECTIVE index, and
comparing the two is an index lemma rather than layer-3 content. The same
split holds here — `evalBgp` is the function layer 2 is about. -/
def askBgp (q : Bgp) (h : Graph) : Bool := !(evalBgp q h).isEmpty

theorem askBgp_gives_solution {q : Bgp} {h : Graph} (hask : askBgp q h = true) :
    ∃ mu, mu ∈ evalBgp q h := by
  cases hs : evalBgp q h with
  | nil => rw [askBgp, hs] at hask; simp at hask
  | cons hd _ => exact ⟨hd, by simp⟩

/-- **ASK soundness under the RDFS regime.** A `true` answer over the
closure is an answer the regime licenses: there really is a solution
mapping whose instantiated BGP the original graph licenses. -/
theorem rdfsRegime_ask_sound (g : Graph) (q : Bgp) (fuel : Nat)
    (hask : askBgp q (RDFS.closure g fuel) = true) :
    ∃ mu, ∀ t ∈ instBgp q mu, RdfsLicenses g t := by
  obtain ⟨mu, hmu⟩ := askBgp_gives_solution hask
  exact ⟨mu, rdfsRegime_bgp_sound g q fuel hmu⟩

/-- **ASK completeness, conditional** — the mirror image, carrying the
same named gap and the same saturation hypothesis. -/
theorem rdfsRegime_ask_complete_conditional (g : Graph) (q : Bgp) (fuel : Nat)
    {mu : Binding}
    (hsat : RDFS.step (RDFS.closure g fuel) = RDFS.closure g fuel)
    (hgap : EvalBgpCompleteAt q (RDFS.closure g fuel) mu)
    (hlic : ∀ t ∈ instBgp q mu, RDFS.Derives g t) :
    askBgp q (RDFS.closure g fuel) = true := by
  have h := rdfsRegime_bgp_complete_conditional g q fuel hsat hgap hlic
  cases hs : evalBgp q (RDFS.closure g fuel) with
  | nil => rw [hs] at h; simp at h
  | cons _ _ => simp [askBgp, hs]

/-! ## Pinned behaviour

Every theorem above is an implication about answers. Guards that only
showed the evaluator returning nothing would satisfy all of them and
mean nothing, so each pin below states a POSITIVE count. -/

section Pins

open L4Factoidal.RDFS (rdfType rdfsSubClassOf)

private def exA : WfIri := ⟨"http://example/A", by decide⟩
private def exB : WfIri := ⟨"http://example/B", by decide⟩
private def exS : WfIri := ⟨"http://example/s", by decide⟩

/-- `s rdf:type A` and `A rdfs:subClassOf B`. The regime licenses
`s rdf:type B`; the raw graph does not carry it. -/
private def gSub : Graph :=
  [ { s := .iri exS, p := rdfType, o := .iri exA }
  , { s := .iri exA, p := rdfsSubClassOf, o := .iri exB } ]

private def qTypeB : Bgp :=
  [{ s := .var "x", p := .iri rdfType, o := .iri exB }]

/-! The query returns NOTHING on the raw graph. Without this the pin
below would not show the regime doing any work. -/
#guard (evalBgp qTypeB gSub).isEmpty

/-! And ONE row over the closure. This is the regime's whole content at
the BGP level. -/
#guard (evalBgp qTypeB (RDFS.closure gSub 8)).length == 1

/-! ASK follows the same way. -/
#guard askBgp qTypeB (RDFS.closure gSub 8)
#guard !(askBgp qTypeB gSub)

/-! The soundness theorem's conclusion is about a NON-EMPTY
instantiation: the single solution instantiates to one triple, and that
triple is in the closure. -/
#guard match evalBgp qTypeB (RDFS.closure gSub 8) with
       | mu :: _ => (instBgp qTypeB mu).length == 1
       | []      => false

#guard match evalBgp qTypeB (RDFS.closure gSub 8) with
       | mu :: _ => (instBgp qTypeB mu).all
                      (fun t => Graph.mem t (RDFS.closure gSub 8))
       | []      => false

/-! The regime does NOT answer everything: a class the graph never
mentions still returns nothing over the closure. A soundness theorem
holds vacuously for an engine that answers everything, so this is the
guard that says the engine is not that. -/
private def exC : WfIri := ⟨"http://example/C", by decide⟩

#guard (evalBgp [{ s := .var "x", p := .iri rdfType, o := .iri exC }]
                (RDFS.closure gSub 8)).isEmpty

/-! The fuel matters, and running out is visible: at zero fuel the
closure is the graph, so the query is empty again. This is why every
completeness statement carries a saturation hypothesis. -/
#guard (evalBgp qTypeB (RDFS.closure gSub 0)).isEmpty

end Pins

end L4Factoidal.SPARQL
