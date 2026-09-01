/-
L4Factoidal.SPARQL.SharedSubjectTripleRefinement -- semantic reference for
the narrow persisted three-predicate shared-subject plan.

The persisted query harness may choose any of the three predicate fragments as
its physical driver and use SRI2/OLI2/HashMap structures to obtain the other
two fragments.  That is deliberately outside this module.  This module owns
only the pure List meaning: one driver row combines with every object value of
the other two predicate fragments for the same RDF subject.

The reference is separate from the Harness so a later theorem states an RDF
and SPARQL claim, rather than an implementation accident of local files or
`Std.HashMap`.
-/
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.SPARQL.AlgebraSpec

namespace L4Factoidal.SPARQL.SharedSubjectTripleRefinement

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.AlgebraSpec

/-- The rows belonging to one constant predicate, in their input order. -/
def predicateFragment (predicate : WfIri) (graph : Graph) : Graph :=
  graph.filter (fun triple => triple.p == predicate)

/-- The object sequence for one RDF subject, retaining graph order and every
physical occurrence.  Retaining occurrences is required by SPARQL bag
semantics: duplicate RDF rows and multiple property values are not sets. -/
def objectsForSubject (subject : Subject) : Graph → List Term
  | [] => []
  | triple :: rest =>
      if triple.s == subject then triple.o :: objectsForSubject subject rest
      else objectsForSubject subject rest

/-- A concrete solution mapping for a three-predicate BGP.  The association
list order is the ordinary left-to-right BGP binding order: the third object
was bound last, then the second, then the first, then the shared subject.
This makes the reference suitable for comparison with `evalBgp`; a fast plan
which chooses a different physical driver must establish mapping equivalence.
-/
def sharedSubjectBinding (subjectVar firstVar secondVar thirdVar : VarName)
    (subject : Subject) (firstObject secondObject thirdObject : Term) : Binding :=
  [(thirdVar, thirdObject), (secondVar, secondObject), (firstVar, firstObject),
    (subjectVar, subject.toTerm)]

/-- Pure reference result for a syntactically ordered three-pattern BGP.
`drivers` supplies the first predicate fragment.  For each driver row, the
two target fragments contribute their complete same-subject object sequences,
so the nested loops retain the required Cartesian-product multiplicity. -/
def sharedSubjectTripleSolutions (subjectVar firstVar secondVar thirdVar : VarName)
    (drivers firstTargets secondTargets : Graph) : SolutionSeq :=
  drivers.flatMap fun driver =>
    (objectsForSubject driver.s firstTargets).flatMap fun firstObject =>
      (objectsForSubject driver.s secondTargets).map fun secondObject =>
        sharedSubjectBinding subjectVar firstVar secondVar thirdVar driver.s
          driver.o firstObject secondObject

/-- Bag equivalence of solution sequences, using the already-established
mapping equality rather than association-list layout equality. -/
def BagEquivalent (left right : SolutionSeq) : Prop :=
  ∀ mapping, mult mapping left = mult mapping right

theorem predicateFragment_nil (predicate : WfIri) :
    predicateFragment predicate [] = [] := by
  rfl

theorem objectsForSubject_nil (subject : Subject) :
    objectsForSubject subject [] = [] := by
  rfl

theorem objectsForSubject_cons_same (subject : Subject) (triple : Triple) (rest : Graph)
    (h : triple.s == subject) :
    objectsForSubject subject (triple :: rest) =
      triple.o :: objectsForSubject subject rest := by
  simp [objectsForSubject, h]

theorem objectsForSubject_cons_other (subject : Subject) (triple : Triple) (rest : Graph)
    (h : triple.s ≠ subject) :
    objectsForSubject subject (triple :: rest) = objectsForSubject subject rest := by
  simp [objectsForSubject, h]

theorem sharedSubjectBinding_lookup_third
    (subjectVar firstVar secondVar thirdVar : VarName)
    (subject : Subject) (firstObject secondObject thirdObject : Term) :
    (sharedSubjectBinding subjectVar firstVar secondVar thirdVar subject
      firstObject secondObject thirdObject).lookup thirdVar = some thirdObject := by
  simp [sharedSubjectBinding, Binding.lookup]

theorem sharedSubjectBinding_lookup_first
    (subjectVar firstVar secondVar thirdVar : VarName)
    (subject : Subject) (firstObject secondObject thirdObject : Term)
    (hThird : thirdVar ≠ firstVar) (hSecond : secondVar ≠ firstVar) :
    (sharedSubjectBinding subjectVar firstVar secondVar thirdVar subject
      firstObject secondObject thirdObject).lookup firstVar = some firstObject := by
  simp [sharedSubjectBinding, Binding.lookup, hThird, hSecond]

theorem sharedSubjectBinding_lookup_subject
    (subjectVar firstVar secondVar thirdVar : VarName)
    (subject : Subject) (firstObject secondObject thirdObject : Term)
    (hThird : thirdVar ≠ subjectVar) (hSecond : secondVar ≠ subjectVar)
    (hFirst : firstVar ≠ subjectVar) :
    (sharedSubjectBinding subjectVar firstVar secondVar thirdVar subject
      firstObject secondObject thirdObject).lookup subjectVar = some subject.toTerm := by
  simp [sharedSubjectBinding, Binding.lookup, hThird, hSecond, hFirst]

theorem sharedSubjectTripleSolutions_no_drivers
    (subjectVar firstVar secondVar thirdVar : VarName) (firstTargets secondTargets : Graph) :
    sharedSubjectTripleSolutions subjectVar firstVar secondVar thirdVar [] firstTargets secondTargets = [] := by
  rfl

theorem sharedSubjectTripleSolutions_no_first_targets
    (subjectVar firstVar secondVar thirdVar : VarName) (drivers secondTargets : Graph) :
    sharedSubjectTripleSolutions subjectVar firstVar secondVar thirdVar drivers [] secondTargets = [] := by
  simp [sharedSubjectTripleSolutions, objectsForSubject]

/-- Matching the first shared-subject pattern from the empty mapping either
    rejects a predicate mismatch or produces exactly the two bindings the
    reference construction expects. -/
theorem tpMatch_first (subjectVar objectVar : VarName) (predicate : WfIri)
    (triple : Triple) (hVars : subjectVar ≠ objectVar) :
    tpMatch
        { s := .var subjectVar, p := .iri predicate, o := .var objectVar }
        triple [] =
      if predicate == triple.p then
        some [(objectVar, triple.o), (subjectVar, triple.s.toTerm)]
      else none := by
  cases hp : predicate == triple.p <;>
    simp [tpMatch, tryBindSubject, tryBindTerm, Binding.lookup, Binding.bind,
      hp, hVars]

/-- Filtering a predicate fragment exposes the same one-row decision used by
    the triple-pattern matcher.  Keeping this lemma explicit avoids relying on
    the implementation shape of subtype `BEq` in the evaluator proof. -/
theorem predicateFragment_cons (predicate : WfIri) (triple : Triple) (rest : Graph) :
    predicateFragment predicate (triple :: rest) =
      if triple.p == predicate then triple :: predicateFragment predicate rest
      else predicateFragment predicate rest := by
  unfold predicateFragment
  cases h : triple.p == predicate with
  | false =>
      have hne : triple.p ≠ predicate := by
        intro heq
        subst predicate
        simp at h
      have hneVal : triple.p.val ≠ predicate.val := fun heq =>
        hne (Subtype.ext heq)
      simp [hneVal]
  | true =>
      have heq : triple.p = predicate := beq_iff_eq.mp h
      subst predicate
      simp

/-- The first triple-pattern scan is exactly a predicate-fragment scan with
    the subject and object variables bound in evaluator order. -/
theorem evalTP_first (subjectVar objectVar : VarName) (predicate : WfIri)
    (graph : Graph) (hVars : subjectVar ≠ objectVar) :
    evalTP
        { s := .var subjectVar, p := .iri predicate, o := .var objectVar }
        graph [] =
      (predicateFragment predicate graph).map fun triple =>
        [(objectVar, triple.o), (subjectVar, triple.s.toTerm)] := by
  induction graph with
  | nil => rfl
  | cons triple rest ih =>
      have ih' :
          List.filterMap
              (fun t => tpMatch
                { s := .var subjectVar, p := .iri predicate, o := .var objectVar }
                t []) rest =
            (predicateFragment predicate rest).map fun t =>
              [(objectVar, t.o), (subjectVar, t.s.toTerm)] := by
        simpa only [evalTP] using ih
      have hp : (predicate == triple.p) = (triple.p == predicate) := by
        exact BEq.comm
      simp only [evalTP, List.filterMap_cons]
      rw [tpMatch_first subjectVar objectVar predicate triple hVars, ih', hp,
        predicateFragment_cons]
      cases h : triple.p == predicate <;> simp

private theorem Subject.toTerm_injective : Function.Injective Subject.toTerm := by
  intro left right h
  cases left <;> cases right <;> simp_all [Subject.toTerm]

/-- For subjects, engine term equality collapses to structural subject
    equality.  The reversed comparison is the orientation used by
    `tryBindSubject` versus `objectsForSubject`. -/
theorem subjectToTerm_eqb_rev (expected actual : Subject) :
    expected.toTerm.eqb actual.toTerm = (actual == expected) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have heqTerm : expected.toTerm = actual.toTerm :=
      Term.eqb_eq_of_toSubject (x := actual) h (by cases actual <;> rfl)
    exact beq_iff_eq.mpr (Subject.toTerm_injective heqTerm).symm
  · intro h
    have heq : actual = expected := beq_iff_eq.mp h
    subst actual
    exact Term.eqb_refl _

/-- Once the shared subject is bound and the next object variable is fresh, a
    later triple-pattern step is precisely a same-subject predicate scan. -/
theorem tpMatch_freshObject (subjectVar objectVar : VarName)
    (predicate : WfIri) (subject : Subject) (seed : Binding)
    (triple : Triple)
    (hSubject : seed.lookup subjectVar = some subject.toTerm)
    (hObject : seed.lookup objectVar = none) :
    tpMatch
        { s := .var subjectVar, p := .iri predicate, o := .var objectVar }
        triple seed =
      if triple.s == subject && predicate == triple.p then
        some ((objectVar, triple.o) :: seed)
      else none := by
  cases triple with
  | mk tripleSubject triplePredicate tripleObject =>
      cases hs : tripleSubject == subject <;>
        cases hp : predicate == triplePredicate <;>
        simp [tpMatch, tryBindSubject, tryBindTerm, Binding.bind,
          subjectToTerm_eqb_rev, hs, hp, hSubject, hObject]

/-- The full graph scan for a later pattern is list-equal to mapping over the
    same-subject objects of its predicate fragment. -/
theorem evalTP_freshObject (subjectVar objectVar : VarName)
    (predicate : WfIri) (subject : Subject) (seed : Binding)
    (graph : Graph)
    (hSubject : seed.lookup subjectVar = some subject.toTerm)
    (hObject : seed.lookup objectVar = none) :
    evalTP
        { s := .var subjectVar, p := .iri predicate, o := .var objectVar }
        graph seed =
      (objectsForSubject subject (predicateFragment predicate graph)).map
        (fun object => (objectVar, object) :: seed) := by
  induction graph with
  | nil => rfl
  | cons triple rest ih =>
      have ih' :
          List.filterMap
              (fun t => tpMatch
                { s := .var subjectVar, p := .iri predicate, o := .var objectVar }
                t seed) rest =
            (objectsForSubject subject (predicateFragment predicate rest)).map
              (fun object => (objectVar, object) :: seed) := by
        simpa only [evalTP] using ih
      have hp : (predicate == triple.p) = (triple.p == predicate) := by
        exact BEq.comm
      simp only [evalTP, List.filterMap_cons]
      rw [tpMatch_freshObject subjectVar objectVar predicate subject seed triple
        hSubject hObject, ih', hp, predicateFragment_cons]
      cases hs : triple.s == subject <;> cases hpred : triple.p == predicate <;>
        simp [objectsForSubject, hs]

/-- Stronger than the planned bag theorem: with the syntactically first
    predicate as driver, the direct three-fragment construction is exactly
    list-equal to left-to-right `evalBgp`.  Predicate distinctness is not a
    semantic requirement; it belongs only to the persisted planner admission.
    The four output variables must be pairwise distinct so every later match
    is a fresh binding rather than a repeated-variable equality constraint. -/
theorem sharedSubjectTripleSolutions_eq_evalBgp
    (subjectVar firstVar secondVar thirdVar : VarName)
    (p1 p2 p3 : WfIri) (graph : Graph)
    (hSubjectFirst : subjectVar ≠ firstVar)
    (hSubjectSecond : subjectVar ≠ secondVar)
    (hSubjectThird : subjectVar ≠ thirdVar)
    (hFirstSecond : firstVar ≠ secondVar)
    (hFirstThird : firstVar ≠ thirdVar)
    (hSecondThird : secondVar ≠ thirdVar) :
    sharedSubjectTripleSolutions subjectVar firstVar secondVar thirdVar
        (predicateFragment p1 graph) (predicateFragment p2 graph)
        (predicateFragment p3 graph) =
      evalBgp
        [{ s := .var subjectVar, p := .iri p1, o := .var firstVar },
         { s := .var subjectVar, p := .iri p2, o := .var secondVar },
         { s := .var subjectVar, p := .iri p3, o := .var thirdVar }] graph := by
  unfold evalBgp
  simp only [evalBgpFrom, Binding.empty]
  rw [evalTP_first subjectVar firstVar p1 graph hSubjectFirst]
  simp only [List.flatMap_map]
  unfold sharedSubjectTripleSolutions
  apply congrArg (fun f => List.flatMap f (predicateFragment p1 graph))
  funext driver
  rw [evalTP_freshObject subjectVar secondVar p2 driver.s
    [(firstVar, driver.o), (subjectVar, driver.s.toTerm)] graph
    (by simp [Binding.lookup, Ne.symm hSubjectFirst])
    (by simp [Binding.lookup, hFirstSecond, hSubjectSecond])]
  simp only [List.flatMap_map]
  apply congrArg (fun f => List.flatMap f
    (objectsForSubject driver.s (predicateFragment p2 graph)))
  funext firstObject
  rw [evalTP_freshObject subjectVar thirdVar p3 driver.s
    [(secondVar, firstObject), (firstVar, driver.o),
      (subjectVar, driver.s.toTerm)] graph
    (by simp [Binding.lookup, Ne.symm hSubjectSecond, Ne.symm hSubjectFirst])
    (by simp [Binding.lookup, hSecondThird, hFirstThird, hSubjectThird])]
  simp [sharedSubjectBinding]

/-- The exact theorem immediately discharges the intended multiset-level
    refinement statement used by a physical planner. -/
theorem sharedSubjectTriple_bag_refines_evalBgp
    (subjectVar firstVar secondVar thirdVar : VarName)
    (p1 p2 p3 : WfIri) (graph : Graph)
    (hSubjectFirst : subjectVar ≠ firstVar)
    (hSubjectSecond : subjectVar ≠ secondVar)
    (hSubjectThird : subjectVar ≠ thirdVar)
    (hFirstSecond : firstVar ≠ secondVar)
    (hFirstThird : firstVar ≠ thirdVar)
    (hSecondThird : secondVar ≠ thirdVar) :
    BagEquivalent
      (sharedSubjectTripleSolutions subjectVar firstVar secondVar thirdVar
        (predicateFragment p1 graph) (predicateFragment p2 graph)
        (predicateFragment p3 graph))
      (evalBgp
        [{ s := .var subjectVar, p := .iri p1, o := .var firstVar },
         { s := .var subjectVar, p := .iri p2, o := .var secondVar },
         { s := .var subjectVar, p := .iri p3, o := .var thirdVar }] graph) := by
  unfold BagEquivalent
  intro mapping
  rw [sharedSubjectTripleSolutions_eq_evalBgp subjectVar firstVar secondVar
    thirdVar p1 p2 p3 graph hSubjectFirst hSubjectSecond hSubjectThird
    hFirstSecond hFirstThird hSecondThird]

/-!
The remaining physical bridge is intentionally separate: prove that the
Merkle-verified SRI2 fragments and the executable HashMap grouping denote the
three `predicateFragment` lists above, including multiplicity.  If the planner
chooses a predicate other than `p1` as driver, it must additionally use a
bag-preserving BGP permutation theorem rather than claiming list equality.
-/

namespace Audit

#print axioms sharedSubjectTripleSolutions_eq_evalBgp
#print axioms sharedSubjectTriple_bag_refines_evalBgp

end Audit

end L4Factoidal.SPARQL.SharedSubjectTripleRefinement
