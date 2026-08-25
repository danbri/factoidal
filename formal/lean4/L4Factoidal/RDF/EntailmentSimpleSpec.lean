/-
L4Factoidal.RDF.EntailmentSimpleSpec — simple entailment, transcribed
from the specification text and related to the tree's own definition.

Port of `formal/fstar/RDF.Entailment.Simple.Spec.fst` (309 lines).

Baseline: RDF 1.1 Semantics, W3C Recommendation 25 February 2014.

§4, INSTANCE, verbatim:

> Suppose that M is a functional mapping from a set of blank nodes to
> some set of literals, blank nodes and IRIs. Any graph obtained from a
> graph G by replacing some or all of the blank nodes N in G by M(N) is
> an instance of G.

§5.3, the INTERPOLATION LEMMA, verbatim:

> G simply entails a graph E if and only if a subgraph of G is an
> instance of E.

Cross-checked against Hayes, RDF Semantics (2004), which the normative
OWL 2 specifications build on: §0.3 and §2 there say the same up to the
rename of "URI reference" to "IRI". Simple entailment is the stable
part across the two baselines.

## Why a second definition of something the tree already has

`RDF.Entailment` defines `SimpleEntails` through `Triple.instance?`, a
total FUNCTION that computes the substituted triple. That is the right
shape for the decision procedure to be proved against, and it is what
the tree's soundness theorem talks about.

This module states the same relation the way the specification text
states it: a RELATION between a pattern triple and a candidate triple,
one clause per term kind, computing nothing and calling nothing.
`spec_iff_simpleEntails` then proves the two agree.

That is what the second definition buys. Without it, "the decision
procedure is sound" is a statement about a definition this project
wrote; with it, the definition this project wrote is tied to a
transcription a reader can check against the specification's own
sentences, line by line, with no algorithm in the way.

## Version divergences that touch this module

A literal is replaced by ITSELF — term identity, not any value
equality. RDF 1.1 Concepts §3.3 makes two literals term-equal exactly
when lexical form, datatype IRI and language tag compare character by
character. The tree's shipping literal test is deliberately coarser in
two places: it compares language tags case-insensitively, and it
compares two `rdf:XMLLiteral` literals by exclusive canonical XML.
Both are D-entailment behaviours and neither is licensed by SIMPLE
entailment, so `LitExact` below names the literals where those two
branches cannot fire. It is not part of the specification — it is the
side condition a soundness proof needs, kept apart so the specification
stays clean.
-/
import L4Factoidal.RDF.Entailment

namespace L4Factoidal.RDF

/-! ## Instance mappings

A mapping from blank-node labels to terms. Total, which loses nothing:
the specification's "some or all of the blank nodes" is covered because
a mapping may send a label to its own blank node, and `fun b => .bnode b`
is then the identity instance. -/

abbrev BnodeSubst := BNodeId → Term

/-- A subject seen as a term. Injective, with the subject-eligible
terms as its image (RDF 1.1 Concepts §3.1: a subject is an IRI or a
blank node). -/
def subjTerm : Subject → Term
  | .iri i => .iri i
  | .bnode b => .bnode b

/-- `Term.toSubject?` and `subjTerm` are inverse where the first
succeeds. The generalized-RDF side condition of several rule rows
arrives as a `toSubject?` success while the specification states it as
a `subjTerm` equation; this is the bridge. -/
theorem subjTerm_of_toSubject? : ∀ {t : Term} {s : Subject},
    t.toSubject? = some s → subjTerm s = t
  | .iri _, _, h => by simp [Term.toSubject?] at h; subst h; rfl
  | .bnode _, _, h => by simp [Term.toSubject?] at h; subst h; rfl
  | .literal _, _, h => by simp [Term.toSubject?] at h
  | .tripleTerm _ _ _, _, h => by simp [Term.toSubject?] at h

/-- `gs` is the result of replacing the blank nodes of `ps` by `M`, in
subject position: an IRI is not a blank node so it is unchanged; a
blank node `b` becomes `M b`, and that is the subject `gs` exactly when
`M b` is `gs`'s term form. -/
def SubjInst (m : BnodeSubst) : Subject → Subject → Prop
  | .iri i, gs => gs = .iri i
  | .bnode b, gs => m b = subjTerm gs

/-- The same in term (object) position, one clause per term kind. A
literal is replaced by the SAME literal term. A triple term carries
ordinary graph-scoped blank nodes at every depth, so substitution
recurses through it and the predicate IRI is unchanged. -/
def TermInst (m : BnodeSubst) : Term → Term → Prop
  | .bnode b, g => m b = g
  | .iri i, g => g = .iri i
  | .literal l, g => g = .literal l
  | .tripleTerm ps pp po, g =>
      ∃ gs go, g = .tripleTerm gs pp go ∧ SubjInst m ps gs ∧ TermInst m po go

/-- A predicate is an IRI, hence never a blank node, hence unchanged. -/
def TripleInst (m : BnodeSubst) (tb ta : Triple) : Prop :=
  tb.p = ta.p ∧ SubjInst m tb.s ta.s ∧ TermInst m tb.o ta.o

/-! ## The specification

Reading a graph as a SET of triples, "the instance of B under M is a
subgraph of A" says exactly: every triple of B, after substitution, is
a triple of A. One existential over the mapping, then a universal over
B's triples — no ordering, no multiplicity, no search. -/

def SimpleEntailmentSpec (a b : Graph) : Prop :=
  ∃ m : BnodeSubst, ∀ tb ∈ b, ∃ ta ∈ a, TripleInst m tb ta

/-! ## The relational form agrees with the computed one

`Triple.instance?` computes; `TripleInst` relates. Proving them
equivalent is what ties the tree's decision procedure to the
transcription above. -/

theorem subjInst_iff (m : BnodeSubst) (ps gs : Subject) :
    SubjInst m ps gs ↔ Subject.instance? m ps = some gs := by
  cases ps with
  | iri i => simp [SubjInst, Subject.instance?, eq_comm]
  | bnode b =>
      simp only [SubjInst, Subject.instance?]
      constructor
      · intro h; rw [h]; cases gs <;> simp [subjTerm, Term.toSubject?]
      · intro h
        cases hb : m b with
        | iri i => rw [hb] at h; simp [Term.toSubject?] at h; subst h; simp [subjTerm]
        | bnode c => rw [hb] at h; simp [Term.toSubject?] at h; subst h; simp [subjTerm]
        | literal l => rw [hb] at h; simp [Term.toSubject?] at h
        | tripleTerm s p o => rw [hb] at h; simp [Term.toSubject?] at h

theorem termInst_iff (m : BnodeSubst) : ∀ (pat g : Term),
    TermInst m pat g ↔ Term.instance? m pat = some g
  | .bnode b, g => by simp [TermInst, Term.instance?, eq_comm]
  | .iri i, g => by simp [TermInst, Term.instance?, eq_comm]
  | .literal l, g => by simp [TermInst, Term.instance?, eq_comm]
  | .tripleTerm ps pp po, g => by
      simp only [TermInst, Term.instance?]
      constructor
      · rintro ⟨gs, go, rfl, hs, ho⟩
        rw [(subjInst_iff m ps gs).mp hs, (termInst_iff m po go).mp ho]
      · intro h
        cases hs : Subject.instance? m ps with
        | none => rw [hs] at h; simp at h
        | some gs =>
            cases ho : Term.instance? m po with
            | none => rw [hs, ho] at h; simp at h
            | some go =>
                rw [hs, ho] at h
                simp only [Option.some.injEq] at h
                exact ⟨gs, go, h.symm, (subjInst_iff m ps gs).mpr hs,
                       (termInst_iff m po go).mpr ho⟩

theorem tripleInst_iff (m : BnodeSubst) (tb ta : Triple) :
    TripleInst m tb ta ↔ Triple.instance? m tb = some ta := by
  simp only [TripleInst, Triple.instance?]
  constructor
  · rintro ⟨hp, hs, ho⟩
    rw [(subjInst_iff m tb.s ta.s).mp hs, (termInst_iff m tb.o ta.o).mp ho]
    cases ta; simp_all
  · intro h
    cases hs : Subject.instance? m tb.s with
    | none => rw [hs] at h; simp at h
    | some s' =>
        cases ho : Term.instance? m tb.o with
        | none => rw [hs, ho] at h; simp at h
        | some o' =>
            rw [hs, ho] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨rfl, (subjInst_iff m tb.s s').mpr hs, (termInst_iff m tb.o o').mpr ho⟩

/-- **The bridge.** The specification transcribed from §4 and §5.3 and
the tree's own `SimpleEntails` define the same relation. -/
theorem spec_iff_simpleEntails (a b : Graph) :
    SimpleEntailmentSpec a b ↔ SimpleEntails a b := by
  constructor
  · rintro ⟨m, h⟩
    refine ⟨m, fun t ht => ?_⟩
    obtain ⟨ta, hta, hinst⟩ := h t ht
    exact ⟨ta, (tripleInst_iff m t ta).mp hinst, hta⟩
  · rintro ⟨m, h⟩
    refine ⟨m, fun t ht => ?_⟩
    obtain ⟨t', hinst, hmem⟩ := h t ht
    exact ⟨t', hmem, (tripleInst_iff m t t').mpr hinst⟩

/-! ## The literal fragment the soundness side condition needs

Not part of the specification. `LitExact` names the literals where the
tree's two coarser literal branches cannot fire. -/

def LitExact (l : Literal) : Prop :=
  l.datatype ≠ rdfXMLLiteral ∧
  (match l.langTag with
   | none => True
   | some t => t.toLower = t)

def TermExact : Term → Prop
  | .iri _ => True
  | .bnode _ => True
  | .literal l => LitExact l.val
  | .tripleTerm _ _ o => TermExact o

def TripleExact (t : Triple) : Prop := TermExact t.o

def GraphExact (g : Graph) : Prop := ∀ t ∈ g, TripleExact t

/-! ## The ground fragment

No blank node anywhere — subject, object, or any depth of a nested
triple term. A bnode-free pattern triple never drives the decision
procedure's rebind check, which is the one place literal comparison
still routes through the coarser test, so soundness for a ground `b`
needs no side condition on literal content at all. -/

def subjGround : Subject → Bool
  | .iri _ => true
  | .bnode _ => false

def termGround : Term → Bool
  | .iri _ => true
  | .bnode _ => false
  | .literal _ => true
  | .tripleTerm s _ o => subjGround s && termGround o

def tripleGround (t : Triple) : Bool := subjGround t.s && termGround t.o

def GraphGround (g : Graph) : Prop := ∀ t ∈ g, tripleGround t = true

/-! ## Triple-term freedom

The RDF 1.2 quarantine predicate: a triple term has no denotation in
either baseline's model theory, so the model-theoretic side needs it.
The syntactic specification above does not. -/

def TermTtFree : Term → Prop
  | .iri _ => True
  | .bnode _ => True
  | .literal _ => True
  | .tripleTerm _ _ _ => False

def GraphTtFree (g : Graph) : Prop := ∀ t ∈ g, TermTtFree t.o

/-! ## Appendix: the specification's own shape, stated literally

"A subgraph of A is an instance of B" names an intermediate graph — the
instance itself. `InstanceSubgraphForm` spells that out;
`SimpleEntailmentSpec` collapses it, which is the form a refinement
proof can use. The F\* tree proves the two equivalent in a sibling
module, so the collapse is checked and not assumed. It is proved here
too, and the appendix exists so a reader can check the transcription
against the specification's own wording. -/

def IsSubgraph (g h : Graph) : Prop := ∀ t ∈ g, t ∈ h

/-- `gInst` is an instance of `gPat` under `m`, at graph level: every
pattern triple has its image in `gInst`, and every `gInst` triple is
the image of a pattern triple. -/
def IsInstanceOf (m : BnodeSubst) (gInst gPat : Graph) : Prop :=
  (∀ tp ∈ gPat, ∃ ti ∈ gInst, TripleInst m tp ti) ∧
  (∀ ti ∈ gInst, ∃ tp ∈ gPat, TripleInst m tp ti)

def InstanceSubgraphForm (a b : Graph) : Prop :=
  ∃ (m : BnodeSubst) (gInst : Graph), IsSubgraph gInst a ∧ IsInstanceOf m gInst b

/-- The collapse is faithful: the specification's literal shape and the
form a refinement proof uses pick out the same pairs of graphs.

Right to left is immediate. Left to right has to BUILD the intermediate
graph, and the witness is the image of `b` itself — which is why the
proof goes through `List.filterMap`: `Triple.instance? m` is exactly
that image, and `tripleInst_iff` turns it back into the relation. -/
theorem spec_iff_instanceSubgraphForm (a b : Graph) :
    SimpleEntailmentSpec a b ↔ InstanceSubgraphForm a b := by
  constructor
  · rintro ⟨m, h⟩
    refine ⟨m, b.filterMap (Triple.instance? m), ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨tp, htp, hinst⟩ := List.mem_filterMap.mp ht
      obtain ⟨ta, hta, hrel⟩ := h tp htp
      rw [(tripleInst_iff m tp ta).mp hrel] at hinst
      cases hinst
      exact hta
    · intro tp htp
      obtain ⟨ta, _, hrel⟩ := h tp htp
      exact ⟨ta, List.mem_filterMap.mpr ⟨tp, htp, (tripleInst_iff m tp ta).mp hrel⟩, hrel⟩
    · intro ti hti
      obtain ⟨tp, htp, hinst⟩ := List.mem_filterMap.mp hti
      exact ⟨tp, htp, (tripleInst_iff m tp ti).mpr hinst⟩
  · rintro ⟨m, gInst, hsub, hfwd, _⟩
    refine ⟨m, fun tp htp => ?_⟩
    obtain ⟨ti, hti, hrel⟩ := hfwd tp htp
    exact ⟨ti, hsub ti hti, hrel⟩

/-! ## Build-time checks

The theorems above are the deliverable; these pin that the relation is
not vacuous in either direction — it holds where the specification says
it should and fails where it should. -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def a1 : Triple := ⟨.iri (iriW "http://e.org/a"), iriW "http://e.org/p",
                            .iri (iriW "http://e.org/b")⟩
private def bn : Triple := ⟨.bnode "x", iriW "http://e.org/p", .iri (iriW "http://e.org/b")⟩
private def bnObj : Triple := ⟨.iri (iriW "http://e.org/a"), iriW "http://e.org/p", .bnode "y"⟩
private def lit : Triple := ⟨.iri (iriW "http://e.org/a"), iriW "http://e.org/p",
                             .literal (Literal.string "10")⟩

/-! A ground graph entails itself, and a blank-node pattern is entailed
by its instance. -/

#guard simpleEntails [a1] [a1]
#guard simpleEntails [a1] [bn]
#guard simpleEntails [lit] [bnObj]

/-! And the relation is not everywhere true: a blank node in SUBJECT
position cannot become a literal, so a pattern whose subject must map
to one is not entailed. -/

#guard !simpleEntails [a1] [⟨.iri (iriW "http://e.org/z"), iriW "http://e.org/p",
                             .iri (iriW "http://e.org/b")⟩]
#guard !simpleEntails [] [a1]
#guard simpleEntails [a1] []

/-! The ground and triple-term predicates decide what they say they
decide. -/

#guard tripleGround a1
#guard !tripleGround bn
#guard !tripleGround bnObj
#guard tripleGround lit

end Checks

end L4Factoidal.RDF
