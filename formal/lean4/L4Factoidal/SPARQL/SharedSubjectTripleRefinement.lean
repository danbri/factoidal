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

/-
The next theorem belongs here once the two physical bridges are available.

  theorem sharedSubjectTriple_bag_refines_evalBgp
      (subjectVar firstVar secondVar thirdVar : VarName)
      (p1 p2 p3 : WfIri) (graph : Graph)
      (hPreds : p1 != p2 /\ p1 != p3 /\ p2 != p3)
      (hVars : subjectVar != firstVar /\ subjectVar != secondVar /\
        subjectVar != thirdVar /\ firstVar != secondVar /\
        firstVar != thirdVar /\ secondVar != thirdVar) :
      BagEquivalent
        (sharedSubjectTripleSolutions subjectVar firstVar secondVar thirdVar
          (predicateFragment p1 graph) (predicateFragment p2 graph)
          (predicateFragment p3 graph))
        (evalBgp
          [{ s := .var subjectVar, p := .iri p1, o := .var firstVar },
           { s := .var subjectVar, p := .iri p2, o := .var secondVar },
           { s := .var subjectVar, p := .iri p3, o := .var thirdVar }] graph)

The later persisted implementation also needs an agreement theorem from its
HashMap/SRI2-selected fragments to these `predicateFragment` Lists.  The
semantic theorem above intentionally does not assume file reads, Merkle
verification, or a particular driver choice.
-/

end L4Factoidal.SPARQL.SharedSubjectTripleRefinement
