/-
L4Factoidal.SPARQL.AlgebraSpec — a DECLARATIVE specification of the
SPARQL 1.1 algebra, transcribed from the W3C Recommendation text and
readable against that text without reference to any algorithm.

Port of `formal/fstar/SPARQL11.Algebra.Spec.fst` (834 lines).

Baseline: SPARQL 1.1 Query Language, W3C Recommendation 21 March 2013,
§18.3 (solution-mapping preliminaries), §18.4 (SPARQL Algebra) and
§18.5 (SPARQL Algebra Evaluation Semantics — the multiset semantics).

## Independence, and how it is checkable

This module computes almost nothing and mentions NO function and NO
type of `L4Factoidal.SPARQL.Algebra`. Its only project-internal import
is `L4Factoidal.RDF.Core`, for the RDF term model. That single import
line is the mechanical check, the same one the F\* source states about
its `open` list.

It is the independent statement the shipping evaluator is to be proved
against. The proof itself is `SPARQL11.Algebra.Refinement.fst`, not yet
ported.

## Two layers, kept apart

§18.5 defines each operator twice: once as a SET of solution mappings,
once by a cardinality clause. Part 3 states the set layer, part 4 the
bag layer. Distinct is the reason to keep them apart — its set layer is
"the same elements", so all of its content is in the cardinality
clause, and letting the set layer stand in for the definition would
lose the operator entirely.

## Association lists are the representation, not the meaning

A solution mapping is a partial function; it is carried here as an
association list because that is what the evaluator produces and no
translation layer should sit at the refinement boundary. Two lists
denote one mapping exactly when `SMapEq` holds, and every statement
below is invariant under `SMapEq`. The `congr` lemmas are what check
that.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.SPARQL.AlgebraSpec

open L4Factoidal.RDF

/-! ## Part 1 — solution mappings (§18.3) -/

/-- §18.3 names the variable set V; a variable is its name. -/
abbrev VarName := String

/-- §18.3, "a solution mapping μ is a partial function μ : V → T". -/
abbrev SMap := List (VarName × Term)

/-- dom(μ) — §18.3, "the subset of V where μ is defined". -/
def sdom (mu : SMap) : List VarName := mu.map Prod.fst

/-- μ(v), partial: `none` when `v` is outside dom(μ). -/
def sval (v : VarName) (mu : SMap) : Option Term := mu.lookup v

/-- The empty solution mapping μ₀ of §18.3's note. -/
def smapEmpty : SMap := []

def noRepeats : List VarName → Bool
  | [] => true
  | v :: rest => !rest.contains v && noRepeats rest

/-- Well-formedness of the REPRESENTATION, not of the mapping. A
partial function has at most one value per variable; an association
list can carry several. Statements about `sval` are insensitive to that
(lookup takes the first binding); statements about `sdom` are not. -/
def smapWf (mu : SMap) : Bool := noRepeats (sdom mu)

/-! ### 1.1 Term identity, transcribed

RDF 1.1 Concepts §3.3, literal term equality: the same lexical form
character by character, the same datatype IRI, the same language tag
(NOT case-folded), the same base direction. Written out rather than
delegated to the derived equality, so the transcription can be checked
against the specification text. -/

def litIdEq (l1 l2 : Literal) : Bool :=
  l1.lexicalForm == l2.lexicalForm && l1.datatype == l2.datatype &&
  l1.langTag == l2.langTag && l1.direction == l2.direction

def subjIdEq : Subject → Subject → Bool
  | .iri a, .iri b => a == b
  | .bnode a, .bnode b => a == b
  | _, _ => false

def termIdEq : Term → Term → Bool
  | .iri a, .iri b => a == b
  | .bnode a, .bnode b => a == b
  | .literal a, .literal b => litIdEq a.val b.val
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
      subjIdEq s1 s2 && p1 == p2 && termIdEq o1 o2
  | _, _ => false

theorem litIdEq_sound {l1 l2 : Literal} (h : litIdEq l1 l2 = true) : l1 = l2 := by
  simp only [litIdEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases l1; cases l2; simp_all

theorem subjIdEq_sound : ∀ {s1 s2 : Subject}, subjIdEq s1 s2 = true → s1 = s2 := by
  intro s1 s2 h
  cases s1 <;> cases s2 <;> simp only [subjIdEq, beq_iff_eq] at h <;> try simp at h
  · exact congrArg Subject.iri h
  · exact congrArg Subject.bnode h

theorem termIdEq_sound : ∀ {t1 t2 : Term}, termIdEq t1 t2 = true → t1 = t2 := by
  intro t1
  induction t1 with
  | iri a =>
      intro t2 h
      cases t2 with
      | iri b => exact congrArg Term.iri (Subtype.ext (by simpa [termIdEq] using h))
      | bnode _ => simp [termIdEq] at h
      | literal _ => simp [termIdEq] at h
      | tripleTerm _ _ _ => simp [termIdEq] at h
  | bnode a =>
      intro t2 h
      cases t2 with
      | bnode b => exact congrArg Term.bnode (by simpa [termIdEq] using h)
      | iri _ => simp [termIdEq] at h
      | literal _ => simp [termIdEq] at h
      | tripleTerm _ _ _ => simp [termIdEq] at h
  | literal a =>
      intro t2 h
      cases t2 with
      | literal b =>
          exact congrArg Term.literal (Subtype.ext (litIdEq_sound (by simpa [termIdEq] using h)))
      | iri _ => simp [termIdEq] at h
      | bnode _ => simp [termIdEq] at h
      | tripleTerm _ _ _ => simp [termIdEq] at h
  | tripleTerm s p o ih =>
      intro t2 h
      cases t2 with
      | tripleTerm s2 p2 o2 =>
          simp only [termIdEq, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hs, hp⟩, ho⟩ := h
          rw [subjIdEq_sound hs, hp, ih ho]
      | iri _ => simp [termIdEq] at h
      | bnode _ => simp [termIdEq] at h
      | literal _ => simp [termIdEq] at h

theorem termIdEq_refl : ∀ t : Term, termIdEq t t = true := by
  intro t
  induction t with
  | iri a => simp [termIdEq]
  | bnode a => simp [termIdEq]
  | literal a => simp only [termIdEq, litIdEq, beq_self_eq_true, Bool.and_self]
  | tripleTerm s p o ih => cases s <;> simp [termIdEq, subjIdEq, ih]

theorem termIdEq_complete {t1 t2 : Term} (h : t1 = t2) : termIdEq t1 t2 = true := by
  subst h; exact termIdEq_refl t1

/-! ### 1.2 Equality of mappings, and its decision procedure -/

/-- Two association lists denote the SAME solution mapping when they
agree as partial functions. This — not list equality — is the equality
§18.3 means, and it is what Distinct must use to decide duplicates. -/
def SMapEq (mu1 mu2 : SMap) : Prop := ∀ v, sval v mu1 = sval v mu2

theorem SMapEq.refl (mu : SMap) : SMapEq mu mu := fun _ => rfl

theorem SMapEq.symm {mu1 mu2 : SMap} (h : SMapEq mu1 mu2) : SMapEq mu2 mu1 :=
  fun v => (h v).symm

theorem SMapEq.trans {mu1 mu2 mu3 : SMap}
    (h1 : SMapEq mu1 mu2) (h2 : SMapEq mu2 mu3) : SMapEq mu1 mu3 :=
  fun v => (h1 v).trans (h2 v)

def optTermIdEq : Option Term → Option Term → Bool
  | none, none => true
  | some a, some b => termIdEq a b
  | _, _ => false

def agreesOn : List VarName → SMap → SMap → Bool
  | [], _, _ => true
  | v :: rest, mu1, mu2 =>
      optTermIdEq (sval v mu1) (sval v mu2) && agreesOn rest mu1 mu2

/-- Two mappings agree everywhere exactly when they agree on the union
of their domains, because outside both domains both are `none`. -/
def smapEqb (mu1 mu2 : SMap) : Bool :=
  agreesOn (sdom mu1) mu1 mu2 && agreesOn (sdom mu2) mu1 mu2

theorem sval_none_outside_dom (v : VarName) : ∀ (mu : SMap),
    v ∉ sdom mu → sval v mu = none := by
  intro mu
  induction mu with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro h
      have hne : ¬ (v = p.1) := by
        intro hv; exact h (by simp [sdom, hv])
      have hrest : v ∉ sdom rest := by
        intro hm; exact h (by simp [sdom]; exact Or.inr (by simpa [sdom] using hm))
      simp only [sval, List.lookup]
      have : (v == p.1) = false := by simp [hne]
      simp only [this]
      exact ih hrest

theorem agreesOn_mem : ∀ (vs : List VarName) (mu1 mu2 : SMap) (v : VarName),
    agreesOn vs mu1 mu2 = true → v ∈ vs →
    optTermIdEq (sval v mu1) (sval v mu2) = true := by
  intro vs
  induction vs with
  | nil => intro _ _ _ _ hm; cases hm
  | cons w rest ih =>
      intro mu1 mu2 v h hm
      simp only [agreesOn, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hm with rfl | hr
      · exact h.1
      · exact ih mu1 mu2 v h.2 hr

theorem optTermIdEq_sound {o1 o2 : Option Term} (h : optTermIdEq o1 o2 = true) :
    o1 = o2 := by
  cases o1 <;> cases o2 <;> simp only [optTermIdEq] at h <;> try simp at h
  · rfl
  · rw [termIdEq_sound h]

theorem smapEqb_sound {mu1 mu2 : SMap} (h : smapEqb mu1 mu2 = true) :
    SMapEq mu1 mu2 := by
  simp only [smapEqb, Bool.and_eq_true] at h
  intro v
  by_cases h1 : v ∈ sdom mu1
  · exact optTermIdEq_sound (agreesOn_mem _ mu1 mu2 v h.1 h1)
  · by_cases h2 : v ∈ sdom mu2
    · exact optTermIdEq_sound (agreesOn_mem _ mu1 mu2 v h.2 h2)
    · rw [sval_none_outside_dom v mu1 h1, sval_none_outside_dom v mu2 h2]

theorem agreesOn_of_SMapEq : ∀ (vs : List VarName) (mu1 mu2 : SMap),
    SMapEq mu1 mu2 → agreesOn vs mu1 mu2 = true := by
  intro vs
  induction vs with
  | nil => intro _ _ _; rfl
  | cons v rest ih =>
      intro mu1 mu2 h
      simp only [agreesOn, Bool.and_eq_true]
      refine ⟨?_, ih mu1 mu2 h⟩
      rw [h v]
      cases hv : sval v mu2 with
      | none => rfl
      | some t => simp [optTermIdEq, termIdEq_refl]

theorem smapEqb_complete {mu1 mu2 : SMap} (h : SMapEq mu1 mu2) :
    smapEqb mu1 mu2 = true := by
  simp only [smapEqb, Bool.and_eq_true]
  exact ⟨agreesOn_of_SMapEq _ mu1 mu2 h, agreesOn_of_SMapEq _ mu1 mu2 h⟩


/-! ## Part 2 — compatibility and merge (§18.3) -/

/-- §18.3, Definition: Compatible Mappings, transcribed: "for every
variable v in dom(μ1) and in dom(μ2), μ1(v) = μ2(v)". Stated over
`sval` rather than over the domain lists, so it is automatically
insensitive to the association-list representation. -/
def Compatible (mu1 mu2 : SMap) : Prop :=
  ∀ v t1 t2, sval v mu1 = some t1 → sval v mu2 = some t2 → t1 = t2

/-- The note after the definition, proved rather than asserted: "the
empty solution mapping μ₀ is compatible with any other". -/
theorem compatible_empty_left (mu : SMap) : Compatible smapEmpty mu := by
  intro v t1 t2 h _; simp [sval, smapEmpty] at h

theorem compatible_empty_right (mu : SMap) : Compatible mu smapEmpty := by
  intro v t1 t2 _ h; simp [sval, smapEmpty] at h

/-- "Two solution mappings with disjoint domains are always
compatible." -/
def DomDisjoint (mu1 mu2 : SMap) : Prop :=
  ∀ v, ¬ ((sval v mu1).isSome = true ∧ (sval v mu2).isSome = true)

theorem compatible_of_disjoint {mu1 mu2 : SMap} (h : DomDisjoint mu1 mu2) :
    Compatible mu1 mu2 := by
  intro v t1 t2 h1 h2
  exact absurd ⟨by simp [h1], by simp [h2]⟩ (h v)

/-- Reflexivity is worth stating on its own. The shipping
`sm_compatible` of the F\* evaluator is NOT reflexive on all
association lists (a duplicate-key list defeats it), and this lemma is
what pins that difference on the REPRESENTATION rather than on the
definition. -/
theorem compatible_refl (mu : SMap) : Compatible mu mu := by
  intro v t1 t2 h1 h2; rw [h1] at h2; exact Option.some.inj h2

theorem compatible_symm {mu1 mu2 : SMap} (h : Compatible mu1 mu2) :
    Compatible mu2 mu1 := fun v t1 t2 h1 h2 => (h v t2 t1 h2 h1).symm

/-- Compatibility respects `SMapEq` in each argument — the check that
the definition is about mappings, not about lists. -/
theorem compatible_congr_left {mu1 mu1' mu2 : SMap}
    (h : Compatible mu1 mu2) (he : SMapEq mu1 mu1') : Compatible mu1' mu2 := by
  intro v t1 t2 h1 h2; exact h v t1 t2 ((he v).trans h1) h2

theorem compatible_congr_right {mu1 mu2 mu2' : SMap}
    (h : Compatible mu1 mu2) (he : SMapEq mu2 mu2') : Compatible mu1 mu2' := by
  intro v t1 t2 h1 h2; exact h v t1 t2 h1 ((he v).trans h2)

/-! ### 2.1 merge

§18.3: merge(μ1, μ2) is defined for compatible mappings and is their
union. Stated as a RELATION rather than as a function returning an
association list, so nothing downstream is committed to a particular
list layout. -/

def mergeAt (mu1 mu2 : SMap) (v : VarName) : Option Term :=
  match sval v mu1 with
  | some t => some t
  | none => sval v mu2

def IsMerge (mu1 mu2 mu : SMap) : Prop := ∀ v, sval v mu = mergeAt mu1 mu2 v

/-- A canonical witness, so `IsMerge` is never vacuous: appending is a
merge, because lookup takes the first binding. -/
def mergeCanonical (mu1 mu2 : SMap) : SMap := mu1 ++ mu2

theorem sval_append (v : VarName) : ∀ (mu1 mu2 : SMap),
    sval v (mu1 ++ mu2) =
      (match sval v mu1 with | some t => some t | none => sval v mu2) := by
  intro mu1
  induction mu1 with
  | nil => intro mu2; rfl
  | cons p rest ih =>
      intro mu2
      simp only [sval, List.cons_append, List.lookup]
      cases hv : (v == p.1) with
      | true => simp
      | false => simpa [sval] using ih mu2

theorem mergeCanonical_isMerge (mu1 mu2 : SMap) :
    IsMerge mu1 mu2 (mergeCanonical mu1 mu2) := by
  intro v; simpa [mergeCanonical, mergeAt] using sval_append v mu1 mu2

/-- A merge is determined up to `SMapEq`, so "the" merge is well
defined as a solution mapping even though many lists represent it. -/
theorem merge_unique {mu1 mu2 mu mu' : SMap}
    (h : IsMerge mu1 mu2 mu) (h' : IsMerge mu1 mu2 mu') : SMapEq mu mu' :=
  fun v => (h v).trans (h' v).symm

/-- On COMPATIBLE mappings merge is symmetric: the W3C merge and the
union of Pérez, Arenas and Gutiérrez (2009) agree. -/
theorem merge_comm_compatible {mu1 mu2 mu : SMap}
    (hc : Compatible mu1 mu2) (h : IsMerge mu1 mu2 mu) : IsMerge mu2 mu1 mu := by
  intro v
  rw [h v]
  simp only [mergeAt]
  cases h1 : sval v mu1 with
  | none => cases h2 : sval v mu2 <;> rfl
  | some t1 =>
      cases h2 : sval v mu2 with
      | none => rfl
      | some t2 => rw [hc v t1 t2 h1 h2]

theorem merge_extends_left {mu1 mu2 mu : SMap} {v : VarName} {t : Term}
    (h : IsMerge mu1 mu2 mu) (h1 : sval v mu1 = some t) : sval v mu = some t := by
  rw [h v]; simp [mergeAt, h1]

theorem merge_extends_right {mu1 mu2 mu : SMap} {v : VarName} {t : Term}
    (h : IsMerge mu1 mu2 mu) (hc : Compatible mu1 mu2)
    (h2 : sval v mu2 = some t) : sval v mu = some t := by
  rw [h v]
  simp only [mergeAt]
  cases h1 : sval v mu1 with
  | none => exact h2
  | some t1 => rw [hc v t1 t h1 h2]

theorem merge_dom {mu1 mu2 mu : SMap} (h : IsMerge mu1 mu2 mu) (v : VarName) :
    (sval v mu).isSome = true ↔
      ((sval v mu1).isSome = true ∨ (sval v mu2).isSome = true) := by
  rw [h v]
  simp only [mergeAt]
  cases h1 : sval v mu1 <;> simp

/-- Merge of compatible mappings is compatible with each argument — the
property a Join proof needs when chaining. -/
theorem merge_compatible_left {mu1 mu2 mu : SMap}
    (h : IsMerge mu1 mu2 mu) (_hc : Compatible mu1 mu2) : Compatible mu mu1 := by
  intro v a b ha hb
  rw [h v] at ha
  simp only [mergeAt, hb] at ha
  exact (Option.some.inj ha).symm

/-! ## Part 3 — the algebra operators, SET layer (§18.5)

Solution multisets are carried as lists, because that is what the
evaluator produces. This layer states which mappings a list may
contain, up to `SMapEq`; part 4 states multiplicities. -/

abbrev SMultiset := List SMap

/-- "μ occurs in Ω", up to `SMapEq`, since a list of association lists
represents a multiset of partial functions. -/
def Occurs (mu : SMap) (omega : SMultiset) : Prop :=
  ∃ mu', mu' ∈ omega ∧ SMapEq mu mu'

theorem occurs_of_mem {mu : SMap} {omega : SMultiset} (h : mu ∈ omega) :
    Occurs mu omega := ⟨mu, h, SMapEq.refl mu⟩

/-- Filter is stated PARAMETRICALLY in the expression evaluator,
exactly as §18.5 states it. `FExpr` stands for "expr(μ) has an
effective boolean value of true"; §17's definition of that predicate is
outside this fragment. -/
abbrev FExpr := SMap → Bool

/-- `Filter(expr, Ω) = { μ | μ ∈ Ω and expr(μ) has an EBV of true }`. -/
def InFilter (f : FExpr) (omega : SMultiset) (mu : SMap) : Prop :=
  Occurs mu omega ∧ f mu = true

/-- `Join(Ω1, Ω2) = { merge(μ1, μ2) | μ1 ∈ Ω1, μ2 ∈ Ω2, μ1 and μ2
compatible }`. -/
def InJoin (o1 o2 : SMultiset) (mu : SMap) : Prop :=
  ∃ mu1 mu2, mu1 ∈ o1 ∧ mu2 ∈ o2 ∧ Compatible mu1 mu2 ∧ IsMerge mu1 mu2 mu

/-- Join is commutative at the set layer, because merge is symmetric on
compatible arguments (Pérez et al. 2009, Proposition 1). -/
theorem join_comm {o1 o2 : SMultiset} {mu : SMap} (h : InJoin o1 o2 mu) :
    InJoin o2 o1 mu := by
  obtain ⟨mu1, mu2, h1, h2, hc, hm⟩ := h
  exact ⟨mu2, mu1, h2, h1, compatible_symm hc, merge_comm_compatible hc hm⟩

/-- `Union(Ω1, Ω2) = { μ | μ ∈ Ω1 or μ ∈ Ω2 }`. -/
def InUnion (o1 o2 : SMultiset) (mu : SMap) : Prop :=
  Occurs mu o1 ∨ Occurs mu o2

/-- `Diff(Ω1, Ω2, expr) = { μ | μ ∈ Ω1 such that for all μ' ∈ Ω2,
either μ and μ' are not compatible, or they are compatible and
expr(merge(μ, μ')) has an EBV of false }`. -/
def InDiff (f : FExpr) (o1 o2 : SMultiset) (mu : SMap) : Prop :=
  Occurs mu o1 ∧
  ∀ mu2 ∈ o2, ¬ Compatible mu mu2 ∨ (∀ m, IsMerge mu mu2 m → f m = false)

/-- `LeftJoin(Ω1, Ω2, expr) = Filter(expr, Join(Ω1, Ω2)) ∪
Diff(Ω1, Ω2, expr)`, transcribed as the literal composition of the
three definitions above rather than re-derived, so a reader diffing
against the specification text sees one line. -/
def InLeftJoin (f : FExpr) (o1 o2 : SMultiset) (mu : SMap) : Prop :=
  (InJoin o1 o2 mu ∧ f mu = true) ∨ InDiff f o1 o2 mu

/-- `Minus(Ω1, Ω2) = { μ | μ ∈ Ω1 such that for all μ' ∈ Ω2, either μ
and μ' are not compatible, or dom(μ) and dom(μ') are disjoint }`. -/
def InMinus (o1 o2 : SMultiset) (mu : SMap) : Prop :=
  Occurs mu o1 ∧ ∀ mu2 ∈ o2, ¬ Compatible mu mu2 ∨ DomDisjoint mu mu2

/-- `Extend(μ, var, term) = μ ∪ {(var, term)}` if var ∉ dom(μ);
UNDEFINED if var ∈ dom(μ). The W3C text leaves that case undefined — an
error condition, not a no-op — and what the evaluator does there is one
of the things the refinement proof has to state rather than assume. -/
def IsExtendAt (mu : SMap) (v : VarName) (t : Term) (mu' : SMap) : Prop :=
  sval v mu = none ∧ sval v mu' = some t ∧
  ∀ w, w ≠ v → sval w mu' = sval w mu

/-- The expression evaluator for Extend is partial: an expression may
raise an error (§17.2), and then §18.5's Extend leaves the variable
unbound. -/
abbrev VExpr := SMap → Option Term

/-- `Extend(Ω, var, expr) = { Extend(μ, var, expr(μ)) | μ ∈ Ω }`. -/
def InExtend (ev : VExpr) (v : VarName) (omega : SMultiset) (mu' : SMap) : Prop :=
  ∃ mu, mu ∈ omega ∧
    (match ev mu with
     | some t => (sval v mu = none ∧ IsExtendAt mu v t mu') ∨
                 ((sval v mu).isSome = true ∧ SMapEq mu' mu)
     | none => SMapEq mu' mu)

/-- `Proj(μ, PV)` — "the restriction of μ to the variables in PV". -/
def IsProj (pv : List VarName) (mu mu' : SMap) : Prop :=
  (∀ v ∈ pv, sval v mu' = sval v mu) ∧ (∀ v, v ∉ pv → sval v mu' = none)

/-- `Project(Ω, PV) = { Proj(μ, PV) | μ ∈ Ω }`. -/
def InProject (pv : List VarName) (omega : SMultiset) (mu' : SMap) : Prop :=
  ∃ mu, mu ∈ omega ∧ IsProj pv mu mu'

/-- `Distinct(Ω) = { μ | μ ∈ Ω }` where Card[μ] = 1. The set layer is
just "the same elements"; ALL of Distinct's content is in the
cardinality clause `distinctCardSpec`. Recording both makes the split
explicit rather than letting the set layer stand in for the
definition. -/
def InDistinct (omega : SMultiset) (mu : SMap) : Prop := Occurs mu omega


/-! ## Part 4 — the BAG layer, cardinalities (§18.5, normative) -/

/-- `Card[μ](Ω)` — how many times μ occurs in the multiset Ω, counted
up to `SMapEq` through the decision procedure of part 1.2, so it counts
MAPPINGS and not list layouts. -/
def mult (mu : SMap) (omega : SMultiset) : Nat :=
  (omega.filter (fun m => smapEqb mu m)).length

theorem mult_pos_iff_mem (mu : SMap) : ∀ (omega : SMultiset),
    0 < mult mu omega ↔ ∃ m, m ∈ omega ∧ smapEqb mu m = true := by
  intro omega
  induction omega with
  | nil => simp [mult]
  | cons m rest ih =>
      simp only [mult, List.filter]
      cases hm : smapEqb mu m with
      | true =>
          simp only [List.length_cons, Nat.succ_pos, true_iff]
          exact ⟨m, List.mem_cons_self, hm⟩
      | false =>
          simp only []
          rw [show (rest.filter (fun x => smapEqb mu x)).length = mult mu rest from rfl,
              ih]
          constructor
          · rintro ⟨x, hx, hxe⟩; exact ⟨x, List.mem_cons_of_mem _ hx, hxe⟩
          · rintro ⟨x, hx, hxe⟩
            rcases List.mem_cons.mp hx with rfl | hr
            · rw [hm] at hxe; exact absurd hxe (by simp)
            · exact ⟨x, hr, hxe⟩

/-- The multiplicity of a mapping depends on the MAPPING, not on the
list that represents it. -/
theorem mult_congr {mu mu' : SMap} (h : SMapEq mu mu') : ∀ omega : SMultiset,
    mult mu omega = mult mu' omega := by
  intro omega
  induction omega with
  | nil => rfl
  | cons m rest ih =>
      simp only [mult, List.filter]
      cases hm : smapEqb mu m with
      | true =>
          have hm' : smapEqb mu' m = true :=
            smapEqb_complete (SMapEq.trans (SMapEq.symm h) (smapEqb_sound hm))
          simp only [hm', List.length_cons]
          exact congrArg (· + 1) ih
      | false =>
          have hm' : smapEqb mu' m = false := by
            cases hx : smapEqb mu' m with
            | false => rfl
            | true =>
                have : smapEqb mu m = true :=
                  smapEqb_complete (SMapEq.trans h (smapEqb_sound hx))
                rw [hm] at this; exact absurd this (by simp)
          simp only [hm']
          exact ih

theorem mult_pos_iff_occurs (mu : SMap) (omega : SMultiset) :
    0 < mult mu omega ↔ Occurs mu omega := by
  rw [mult_pos_iff_mem]
  constructor
  · rintro ⟨m, hm, hme⟩; exact ⟨m, hm, smapEqb_sound hme⟩
  · rintro ⟨m, hm, hme⟩; exact ⟨m, hm, smapEqb_complete hme⟩

/-! ### 4.1 the cardinality clauses of §18.5, transcribed -/

/-- "Card[Union(Ω1,Ω2)][μ] = Card[Ω1][μ] + Card[Ω2][μ]". -/
def unionCardSpec (o1 o2 res : SMultiset) : Prop :=
  ∀ mu, mult mu res = mult mu o1 + mult mu o2

/-- "Card[Filter(expr,Ω)][μ] = Card[Ω][μ] if expr(μ) is true, 0
otherwise". -/
def filterCardSpec (f : FExpr) (omega res : SMultiset) : Prop :=
  ∀ mu, mult mu res = (if f mu then mult mu omega else 0)

/-- "Card[Distinct(Ω)][μ] = 1" for every μ occurring in Ω, 0
otherwise — the whole content of Distinct. -/
def distinctCardSpec (omega res : SMultiset) : Prop :=
  ∀ mu, mult mu res = (if 0 < mult mu omega then 1 else 0)

/-- "Card[Project(Ω,PV)][μ] = the sum over μ' ∈ Ω with Proj(μ',PV) = μ
of Card[Ω][μ']" — projection MERGES duplicates without removing them,
so the result multiset has the same total size as the input. -/
def projectCardSpec (pv : List VarName) (omega res : SMultiset) : Prop :=
  res.length = omega.length ∧ ∀ mu, Occurs mu res ↔ InProject pv omega mu

/-- "Card[Minus(Ω1,Ω2)][μ] = Card[Ω1][μ]" for a retained μ, 0
otherwise — Minus never duplicates and never merges. -/
def minusCardSpec (o1 o2 res : SMultiset) : Prop :=
  (∀ mu, InMinus o1 o2 mu → mult mu res = mult mu o1) ∧
  (∀ mu, ¬ InMinus o1 o2 mu → mult mu res = 0)

/-! ## Part 5 — BGP matching (§18.3.1 / §18.5)

Stated over an ABSTRACT pattern type and an abstract instantiation
function, so this module stays independent of the shipping abstract
syntax. The refinement proof instantiates `tp` with the evaluator's
triple pattern, `gtriple` with `RDF.Triple`, and `inst` with the
shipping instantiation.

`inst mu p` is μ(p): the triple obtained by replacing every variable of
p by its μ-image. It is PARTIAL — a pattern whose subject variable is
bound to a literal has no instance, because an RDF subject is never a
literal — and that partiality is why the statement below is relational
rather than functional. -/

/-- Simple-entailment BGP matching, §18.3.1 specialised: μ is a
solution of BGP against G exactly when μ(BGP) is a subgraph of G and
dom(μ) = var(BGP), with Card[μ] = 1 for each such μ. -/
def BgpSol {tp gtriple : Type}
    (inst : SMap → tp → Option gtriple) (patvars : tp → List VarName)
    (b : List tp) (g : List gtriple) (mu : SMap) : Prop :=
  (∀ p ∈ b, ∃ t, inst mu p = some t ∧ t ∈ g) ∧
  (∀ v, (sval v mu).isSome = true ↔ ∃ p, p ∈ b ∧ v ∈ patvars p)

/-- The empty BGP has exactly the empty solution — §18.5's base case,
and the check that `BgpSol` is not vacuous. -/
theorem bgp_empty {tp gtriple : Type}
    (inst : SMap → tp → Option gtriple) (patvars : tp → List VarName)
    (g : List gtriple) : BgpSol inst patvars [] g smapEmpty := by
  constructor
  · intro p hp; cases hp
  · intro v
    constructor
    · intro h; simp [sval, smapEmpty] at h
    · rintro ⟨p, hp, -⟩; cases hp

/-! ## Build-time checks -/

private def vX : VarName := "x"
private def vY : VarName := "y"
private def tA : Term := .iri ⟨"http://example.org/a", by decide⟩
private def tB : Term := .iri ⟨"http://example.org/b", by decide⟩

/-! Lookup takes the FIRST binding, which is what makes appending a
merge. -/
#guard sval vX [(vX, tA), (vX, tB)] == some tA
#guard sval vY [(vX, tA)] == none

/-! A duplicate-key list is a badly formed REPRESENTATION even though
it denotes a perfectly good mapping. -/
#guard smapWf [(vX, tA), (vX, tB)] == false
#guard smapWf [(vX, tA), (vY, tB)] == true

/-! Two different lists denoting one mapping. -/
#guard smapEqb [(vX, tA), (vX, tB)] [(vX, tA)] == true
#guard smapEqb [(vX, tA)] [(vX, tB)] == false

/-! Multiplicity counts mappings, not layouts: the two lists below are
one mapping, so it is counted twice. -/
#guard mult [(vX, tA)] [[(vX, tA)], [(vX, tA), (vX, tB)], [(vX, tB)]] == 2

/-! ## Axiom audit -/

#print axioms termIdEq_sound
#print axioms smapEqb_sound
#print axioms smapEqb_complete
#print axioms compatible_refl
#print axioms mergeCanonical_isMerge
#print axioms merge_comm_compatible
#print axioms merge_compatible_left
#print axioms join_comm
#print axioms mult_congr
#print axioms mult_pos_iff_occurs
#print axioms bgp_empty

end L4Factoidal.SPARQL.AlgebraSpec
