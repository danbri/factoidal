/-
L4Factoidal.SPARQL.SharedSubjectTriple -- executable core for the narrow
three-predicate, shared-subject physical plan.

This module contains only typed RDF/SPARQL data transformations.  File I/O,
Merkle verification, SRI2 range reads, query admission, and SELECT modifiers
remain outside it.  Keeping both the simple List reference and the production
HashMap grouping here gives the refinement layer a real executable target
without making the runtime harness depend on proof modules.
-/
import L4Factoidal.SPARQL.Algebra
import Std.Data.HashMap

namespace L4Factoidal.SPARQL.SharedSubjectTriple

open L4Factoidal.RDF
open L4Factoidal.SPARQL

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
was bound last, then the second, then the first, then the shared subject. -/
def sharedSubjectBinding (subjectVar firstVar secondVar thirdVar : VarName)
    (subject : Subject) (firstObject secondObject thirdObject : Term) : Binding :=
  [(thirdVar, thirdObject), (secondVar, secondObject), (firstVar, firstObject),
    (subjectVar, subject.toTerm)]

/-- Simple List reference for a syntactically ordered three-pattern BGP. -/
def sharedSubjectTripleSolutions (subjectVar firstVar secondVar thirdVar : VarName)
    (drivers firstTargets secondTargets : Graph) : SolutionSeq :=
  drivers.flatMap fun driver =>
    (objectsForSubject driver.s firstTargets).flatMap fun firstObject =>
      (objectsForSubject driver.s secondTargets).map fun secondObject =>
        sharedSubjectBinding subjectVar firstVar secondVar thirdVar driver.s
          driver.o firstObject secondObject

/-- Production grouping used after SRI2 has selected exact predicate
fragments.  Values are consed while folding left, so each subject bucket is in
reverse fragment order.  The direct plan promises bag semantics, not this
incidental bucket order. -/
def objectsBySubjectStep
    (indexed : Std.HashMap Subject (List Term)) (triple : Triple) :
    Std.HashMap Subject (List Term) :=
  indexed.insert triple.s (triple.o :: indexed.getD triple.s [])

def objectsBySubject (triples : Graph) : Std.HashMap Subject (List Term) :=
  triples.foldl objectsBySubjectStep ∅

/-- Production Cartesian-product finisher.  It keeps every physical row and
therefore every duplicate.  `driverVar`, `leftVar`, and `rightVar` describe
the optimizer's chosen physical order; solution-map equality ignores the
association-list layout. -/
def subjectTripleSolutions (subjectVar driverVar leftVar rightVar : VarName)
    (drivers lefts rights : Graph) : SolutionSeq :=
  let leftBySubject := objectsBySubject lefts
  let rightBySubject := objectsBySubject rights
  drivers.flatMap fun driver =>
    (leftBySubject.getD driver.s []).flatMap fun leftObject =>
      (rightBySubject.getD driver.s []).map fun rightObject =>
        [(rightVar, rightObject), (leftVar, leftObject),
          (driverVar, driver.o), (subjectVar, driver.s.toTerm)]

end L4Factoidal.SPARQL.SharedSubjectTriple
