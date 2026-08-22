/-
L4Factoidal.OWL.Tableau — model theory and declarative clash calculus
for the fragment covered by the first clash rules of the F* refutation
tableau (`formal/fstar/Tableau.Refute.fst`).

Workstream: rung on https://github.com/danbri/factoidal/issues/466
(folded in from the duplicate track
https://github.com/danbri/factoidal/issues/468 — see that issue for
why the proof home for tableau soundness is Lean: the global inductive
invariants involved are a poor fit for SMT-driven F* automation).

`Interp.sem` is the OWL 2 Direct Semantics class-expression
interpretation function
(https://www.w3.org/TR/owl2-direct-semantics/ Table 5), restricted to:
class names, Boolean connectives, value restrictions
(ObjectAllValuesFrom / ObjectSomeValuesFrom), and UNQUALIFIED
cardinality bounds (ObjectMinCardinality / ObjectMaxCardinality).

NOT ported yet (later rungs, in the order the F* engine grew them):
qualified cardinality, nominals (ObjectOneOf), datatypes, functional
roles, and the SHIQ ≤-rule witness merge. The ∃-witness rule (fresh
individuals) IS here — `exWitness` — with its freshness side condition
stated over `indsOf`; so is the role box (rung 3): subrole axioms and
transitive roles (`RoleAxioms`), with the SHIQ ∀⁺-push rule
`allTransE`.

Cardinality without set theory: OWL says "at least/most n distinct
r-successors". Distinct-successor counting is phrased with plain
`List` + `Pairwise (· ≠ ·)` — no mathlib, per the zero-dependency
rule. A length-n pairwise-distinct list is exactly an n-element
subset witness.

Two layers, mirroring how the F* engine's verdicts decompose:

* `Derives R A φ` — positive facts obtainable from the ABox by
  forward rules against role box `R` (the analogue of `Tableau.fst`'s positive-sound
  materialisation).
* `Refuted R A` — the clash calculus (the analogue of
  `Tableau.Refute.fst`'s `tableau_consistent = Some false`). One
  constructor per clash rule; `disjSplit` is the branching rule. A
  `Refuted` derivation tree IS a clash certificate — the object the
  certificate-checker rung will serialize and check.

Proofs live in `TableauTheorems.lean`; example derivations and the
axiom audit in `TableauTests.lean`.
-/

namespace L4Factoidal.OWL

/-- Role (object property) names. IRIs in the engine; opaque strings
    here, same choice as the prototype and revisitable when this file
    is connected to `L4Factoidal.RDF.Core`'s well-formed IRI subtype. -/
abbrev Role := String

/-- Individual names (ABox constants). No unique-name assumption: two
    names may denote one domain element unless a `diff` assertion
    separates them. -/
abbrev Ind := String

/-- Class expressions. One constructor per OWL construct in scope. -/
inductive Concept where
  | atom    (name : String)          -- class name (IRI)
  | top                              -- owl:Thing
  | bot                              -- owl:Nothing
  | neg     (c : Concept)            -- ObjectComplementOf
  | conj    (c d : Concept)          -- ObjectIntersectionOf (binary)
  | disj    (c d : Concept)          -- ObjectUnionOf (binary)
  | all     (r : Role) (c : Concept) -- ObjectAllValuesFrom
  | ex      (r : Role) (c : Concept) -- ObjectSomeValuesFrom
  | atLeast (n : Nat) (r : Role)     -- ObjectMinCardinality n r
  | atMost  (n : Nat) (r : Role)     -- ObjectMaxCardinality n r
deriving Repr, DecidableEq

/-- An interpretation over a domain `δ`: class extensions and role
    extensions (the OWL 2 Direct Semantics `·^C` and `·^OP` maps). -/
structure Interp (δ : Type) where
  concept : String → δ → Prop
  role    : Role → δ → δ → Prop

/-- `n` pairwise-distinct `r`-successors of `x`, as a list witness. -/
def Interp.succWitness {δ : Type} (I : Interp δ) (r : Role) (x : δ)
    (n : Nat) (l : List δ) : Prop :=
  l.length = n ∧ l.Pairwise (· ≠ ·) ∧ ∀ y ∈ l, I.role r x y

/-- Class-expression semantics — OWL 2 Direct Semantics Table 5,
    restricted to the fragment. -/
def Interp.sem {δ : Type} (I : Interp δ) : Concept → δ → Prop
  | .atom a,      x => I.concept a x
  | .top,         _ => True
  | .bot,         _ => False
  | .neg c,       x => ¬ I.sem c x
  | .conj c d,    x => I.sem c x ∧ I.sem d x
  | .disj c d,    x => I.sem c x ∨ I.sem d x
  | .all r c,     x => ∀ y, I.role r x y → I.sem c y
  | .ex r c,      x => ∃ y, I.role r x y ∧ I.sem c y
  | .atLeast n r, x => ∃ l, I.succWitness r x n l
  | .atMost n r,  x => ¬ ∃ l, I.succWitness r x (n + 1) l

/-- ABox assertions — the ground facts the tableau starts from.
    `diff` is owl:differentFrom, the engine's source of provable
    distinctness for max-cardinality clashes. -/
inductive Assertion where
  | inst (a : Ind) (c : Concept)     -- ClassAssertion
  | rel  (r : Role) (a b : Ind)      -- ObjectPropertyAssertion
  | diff (a b : Ind)                 -- DifferentIndividuals (binary)
deriving Repr, DecidableEq

/-- Satisfaction of one assertion by interpretation `I` and name
    assignment `ν`. -/
def Satisfies {δ : Type} (I : Interp δ) (ν : Ind → δ) : Assertion → Prop
  | .inst a c  => I.sem c (ν a)
  | .rel r a b => I.role r (ν a) (ν b)
  | .diff a b  => ν a ≠ ν b

/-- A model of an ABox satisfies every assertion. -/
def SatAll {δ : Type} (I : Interp δ) (ν : Ind → δ)
    (A : List Assertion) : Prop :=
  ∀ φ ∈ A, Satisfies I ν φ

/-- The role box (rung 3): subrole axioms `r ⊑ s` and transitivity
    declarations — the SHIQ-side context role facts are read against.
    The F* engine keeps the same data in `Tableau.Types.fst`'s
    role-axiom list. -/
structure RoleAxioms where
  subRole : List (Role × Role)   -- pairs (r, s) meaning r ⊑ s
  trans   : List Role            -- roles declared transitive
deriving Repr, DecidableEq

/-- The empty role box — the pre-role-box calculus embeds as this
    instance. -/
def RoleAxioms.empty : RoleAxioms := ⟨[], []⟩

/-- An interpretation respects the role box: subrole inclusion and
    transitivity hold of the role extensions. -/
def RespectsRBox {δ : Type} (I : Interp δ) (R : RoleAxioms) : Prop :=
  (∀ p ∈ R.subRole, ∀ x y, I.role p.1 x y → I.role p.2 x y) ∧
  (∀ r ∈ R.trans, ∀ x y z, I.role r x y → I.role r y z → I.role r x z)

/-- Consistency w.r.t. a role box: some domain, interpretation, and
    assignment respect the role box and model the ABox.
    `TableauTheorems.refuted_not_consistent` refutes exactly this. -/
def Consistent (R : RoleAxioms) (A : List Assertion) : Prop :=
  ∃ (δ : Type) (I : Interp δ) (ν : Ind → δ), RespectsRBox I R ∧ SatAll I ν A

/-- The individual names occurring in an assertion. Concepts in this
    fragment contain no individuals (no nominals, no hasValue), so
    only the assertion-level positions count. -/
def Assertion.inds : Assertion → List Ind
  | .inst a _  => [a]
  | .rel _ a b => [a, b]
  | .diff a b  => [a, b]

/-- The individual names occurring anywhere in an ABox — the set the
    ∃-rule's freshness side condition is stated against. -/
def indsOf (A : List Assertion) : List Ind :=
  A.flatMap Assertion.inds

/-- Forward derivation of facts from an ABox, against a role box.
    Hypothesis, conjunction elimination, the ∀-rule (value restriction
    applied across a known role edge), and the three role-box rules:
    subrole inclusion, transitive composition, and the SHIQ ∀⁺-push
    (a value restriction on a transitive role travels across each edge
    of that role, so it reaches every individual on an r-chain). -/
inductive Derives (R : RoleAxioms) (A : List Assertion) : Assertion → Prop where
  | hyp {φ} : φ ∈ A → Derives R A φ
  | conjE1 {a c d} :
      Derives R A (.inst a (.conj c d)) → Derives R A (.inst a c)
  | conjE2 {a c d} :
      Derives R A (.inst a (.conj c d)) → Derives R A (.inst a d)
  | allE {a b r c} :
      Derives R A (.inst a (.all r c)) → Derives R A (.rel r a b) →
      Derives R A (.inst b c)
  | subRoleE {r s a b} :
      Derives R A (.rel r a b) → (r, s) ∈ R.subRole →
      Derives R A (.rel s a b)
  | transE {r a b e} :
      Derives R A (.rel r a b) → Derives R A (.rel r b e) →
      r ∈ R.trans → Derives R A (.rel r a e)
  | allTransE {a b r c} :
      Derives R A (.inst a (.all r c)) → r ∈ R.trans →
      Derives R A (.rel r a b) →
      Derives R A (.inst b (.all r c))

/-- The clash calculus. A constructor = a clash rule = a certificate
    node. `Prop`-valued for the soundness development; the
    certificate-checker rung re-states it as a `Type` so trees can be
    serialized and checked. -/
inductive Refuted (R : RoleAxioms) : List Assertion → Prop where
  /-- C ⊓ ¬C at one individual. -/
  | clash {A a c} :
      Derives R A (.inst a c) → Derives R A (.inst a (.neg c)) →
      Refuted R A
  /-- owl:Nothing is uninhabited. -/
  | botClash {A a} :
      Derives R A (.inst a .bot) → Refuted R A
  /-- ≥(n+1) r together with ≤n r at one individual (the F* engine's
      C3/C4 count clash). -/
  | minMaxClash {A a n r} :
      Derives R A (.inst a (.atLeast (n + 1) r)) →
      Derives R A (.inst a (.atMost n r)) →
      Refuted R A
  /-- ≤n r refuted by n+1 named successors that are pairwise provably
      distinct via owl:differentFrom (the engine's differentFrom-based
      max-cardinality refutation). -/
  | maxClash {A a n r} (l : List Ind) :
      Derives R A (.inst a (.atMost n r)) →
      l.length = n + 1 →
      l.Pairwise (fun x y => Derives R A (.diff x y) ∨ Derives R A (.diff y x)) →
      (∀ b ∈ l, Derives R A (.rel r a b)) →
      Refuted R A
  /-- Disjunction branching: if both extensions are refuted, the ABox
      is refuted. -/
  | disjSplit {A a c d} :
      Derives R A (.inst a (.disj c d)) →
      Refuted R (.inst a c :: A) →
      Refuted R (.inst a d :: A) →
      Refuted R A
  /-- The ∃-rule: a derived `∃r.C` at `a` licenses a FRESH witness
      individual `x` with an `r`-edge from `a` and membership in `C`;
      if that extension is refuted, so is the ABox. Freshness (`x` not
      named anywhere in `A`) is the whole soundness argument: a model
      of `A` says nothing about `x`, so its assignment can be bent to
      the semantic witness that `∃r.C` guarantees exists. This is the
      rule the F* engine bounds with witness depth caps
      (`Tableau.Refute.fst`, stage (e)). -/
  | exWitness {A a r c} (x : Ind) :
      Derives R A (.inst a (.ex r c)) →
      x ∉ indsOf A →
      Refuted R (.rel r a x :: .inst x c :: A) →
      Refuted R A

end L4Factoidal.OWL
