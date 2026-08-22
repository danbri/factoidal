/- Model theory for the fragment covered by the first clash rules of
   the F* refutation tableau (formal/fstar/Tableau.Refute.fst).

   Experiment tracked in
   https://github.com/danbri/factoidal/issues/468 — Lean 4 is being
   tried as the proof home for tableau soundness, because the global
   inductive invariants involved are a poor fit for SMT-driven F*
   automation.

   Spec correspondence (the review object, per
   docs/review-guide-w3c-semantics.md): `Interp.sem` below is the
   OWL 2 Direct Semantics class-expression interpretation function
   (https://www.w3.org/TR/owl2-direct-semantics/ Table 5), restricted
   to: class names, Boolean connectives, value restrictions
   (ObjectAllValuesFrom / ObjectSomeValuesFrom), and UNQUALIFIED
   cardinality bounds (ObjectMinCardinality / ObjectMaxCardinality).
   Qualified cardinality, nominals, and datatypes are later waves.

   Cardinality without set theory: OWL says "at least/most n distinct
   r-successors". We phrase distinct-successor counting with plain
   `List` + `Pairwise (· ≠ ·)` so the development needs no mathlib —
   a list of length n whose elements are pairwise distinct is exactly
   an n-element subset witness. -/

namespace TableauSound

/-- Role (object property) names. IRIs in the engine; opaque strings here. -/
abbrev Role := String

/-- Individual names (ABox constants). No unique-name assumption:
    two names may denote one domain element unless a `diff` assertion
    separates them. -/
abbrev Ind := String

/-- Class expressions. One constructor per OWL construct in scope. -/
inductive Concept where
  | atom   (name : String)              -- class name (IRI)
  | top                                 -- owl:Thing
  | bot                                 -- owl:Nothing
  | neg    (c : Concept)                -- ObjectComplementOf
  | conj   (c d : Concept)              -- ObjectIntersectionOf (binary)
  | disj   (c d : Concept)              -- ObjectUnionOf (binary)
  | all    (r : Role) (c : Concept)     -- ObjectAllValuesFrom
  | ex     (r : Role) (c : Concept)     -- ObjectSomeValuesFrom
  | atLeast (n : Nat) (r : Role)        -- ObjectMinCardinality n r
  | atMost  (n : Nat) (r : Role)        -- ObjectMaxCardinality n r
deriving Repr, DecidableEq

/-- An interpretation over a domain `δ`: class extensions and role
    extensions. (The OWL 2 Direct Semantics `·^C` and `·^OP` maps.) -/
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

/-- Consistency: some domain, interpretation, and assignment model
    the ABox. The soundness theorem in Calculus.lean refutes exactly
    this. -/
def Consistent (A : List Assertion) : Prop :=
  ∃ (δ : Type) (I : Interp δ) (ν : Ind → δ), SatAll I ν A

end TableauSound
