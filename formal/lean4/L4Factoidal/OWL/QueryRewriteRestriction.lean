/-
L4Factoidal.OWL.QueryRewriteRestriction — layer 4 of the port of
`OWL.QueryRewrite`: recognising restriction class expressions.

Layers 1 to 3 handle the FLAT path — `owl:intersectionOf` and
`owl:unionOf` over named classes. This layer is the classifier the
nested (Phase 4) path needs: given a marker key, which kind of
restriction is it, and is its filler itself a class expression?

The EXPANSION that consumes this classification is not here. In the F\*
source that is `expand_ce_subject`, 460 lines of nested class-expression
rewriting, and CLAUDE.md records the known narrowness that lives in it
(<https://github.com/danbri/factoidal/issues/236>: the N=1 qualified
`CE_MaxCardinality` rewrite emits an anchor triple that MULTIPLIES rows
per P-edge and drops vacuous-truth individuals). So `OWL.QueryRewrite`
stays not covered and no alias was added.

## The discipline this layer encodes

Not every restriction is a rewrite target. The F\* source is explicit,
and the reason is that the OWL-RL closure already handles some shapes
better than a query rewrite can:

* `owl:someValuesFrom` with a NAMED-class filler is NOT a marker — the
  closure's canonical-bnode materialisation is the correct path.
* `owl:someValuesFrom` with a class-expression filler IS a marker.
* `owl:allValuesFrom` is a marker whatever the filler.

`restrictionHasNestedFiller` is what tells those apart, and it is the
only place the three notions of "is a class expression" have to agree:
a flat marker, another restriction, or an `owl:complementOf` bnode.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewritePattern

namespace L4Factoidal.OWL.QueryRewriteCore

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.SPARQL
open L4Factoidal.OWL.RL (owlSomeValuesFrom owlAllValuesFrom owlComplementOf
  owlMinCardinality owlMaxCardinality owlCardinality
  owlMinQualifiedCardinality owlMaxQualifiedCardinality owlQualifiedCardinality
  owlRestriction owlOnProperty owlOnClass owlClass owlIntersectionOf)

/-! ## The restriction kinds -/

inductive Restriction where
  | someValuesFrom
  | allValuesFrom
  | minCardinality
  | maxCardinality
  | exactCardinality
  | complementOf
  deriving DecidableEq, Repr

/-! ## Single-predicate tests -/

def isSvfSubject (b : Bgp) (k : String) : Bool :=
  (bgpFindFirstObj b k owlSomeValuesFrom).isSome

def isAvfSubject (b : Bgp) (k : String) : Bool :=
  (bgpFindFirstObj b k owlAllValuesFrom).isSome

/-- `[ a owl:Class ; owl:complementOf :C ]`. -/
def isComplementOfSubject (b : Bgp) (k : String) : Bool :=
  (bgpFindFirstObj b k owlComplementOf).isSome

def complementOfTarget (b : Bgp) (k : String) : Option PatternTerm :=
  bgpFindFirstObj b k owlComplementOf

/-! ## The cardinality family

Unqualified and qualified forms classify the same way, tried min, max,
exact in that order — as in the F\* source, so a marker carrying more
than one cardinality predicate resolves identically in both trees. -/

def cardSubjectCombinator (b : Bgp) (k : String) : Option Restriction :=
  if (bgpFindFirstObj b k owlMinCardinality).isSome ||
     (bgpFindFirstObj b k owlMinQualifiedCardinality).isSome then
    some .minCardinality
  else if (bgpFindFirstObj b k owlMaxCardinality).isSome ||
          (bgpFindFirstObj b k owlMaxQualifiedCardinality).isSome then
    some .maxCardinality
  else if (bgpFindFirstObj b k owlCardinality).isSome ||
          (bgpFindFirstObj b k owlQualifiedCardinality).isSome then
    some .exactCardinality
  else none

def isCardSubject (b : Bgp) (k : String) : Bool :=
  (cardSubjectCombinator b k).isSome

/-- A restriction marker of any supported kind. -/
def isRestrictionSubject (b : Bgp) (k : String) : Bool :=
  isSvfSubject b k || isAvfSubject b k || isCardSubject b k

/-! ## The filler -/

/-- The filler of the restriction rooted at `k`, with the predicate
that supplied it. `someValuesFrom` is tried first, as in the F\*
source. -/
def restrictionFiller (b : Bgp) (k : String) : Option (PatternTerm × Restriction) :=
  match bgpFindFirstObj b k owlSomeValuesFrom with
  | some f => some (f, .someValuesFrom)
  | none =>
      match bgpFindFirstObj b k owlAllValuesFrom with
      | some f => some (f, .allValuesFrom)
      | none => none

/-- Is the filler itself a class expression? Three ways to be one: a
flat marker, another restriction, or a complement bnode. A named IRI
filler is none of them, which is what keeps the someValuesFrom case
out of the rewrite. -/
def restrictionHasNestedFiller (b : Bgp) (k : String) : Bool :=
  match restrictionFiller b k with
  | none => false
  | some (filler, _) =>
      match markerKey filler with
      | none => false
      | some kf =>
          (findFlatMarkers b).any (fun e => e.1 == kf) ||
          isRestrictionSubject b kf ||
          isComplementOfSubject b kf

/-- The rewrite-target discipline, as one predicate.
`someValuesFrom` earns a marker only with a class-expression filler;
`allValuesFrom` always does. -/
def isRewriteTargetRestriction (b : Bgp) (k : String) : Bool :=
  if isAvfSubject b k then true
  else if isSvfSubject b k then restrictionHasNestedFiller b k
  else false

/-! ## What the classifier guarantees -/

/-- A named-class `someValuesFrom` filler is NOT a rewrite target. This
is the discipline the F\* source states in prose, and the case
`simple2` depends on: the closure's canonical-bnode materialisation
handles it, and a query rewrite would compete with that. -/
theorem svf_namedFiller_not_target {b : Bgp} {k : String} {i : WfIri}
    (hsvf : bgpFindFirstObj b k owlSomeValuesFrom = some (.iri i))
    (havf : isAvfSubject b k = false) :
    isRewriteTargetRestriction b k = false := by
  simp only [isRewriteTargetRestriction, havf, if_false,
             restrictionHasNestedFiller, restrictionFiller, hsvf,
             markerKey, if_true]
  simp [isSvfSubject, hsvf]

/-- The three cardinality answers are mutually exclusive by
construction — the `else if` chain cannot report two. Stated because a
later edit that turns it into three independent tests would be able
to. -/
theorem cardSubjectCombinator_min {b : Bgp} {k : String}
    (h : (bgpFindFirstObj b k owlMinCardinality).isSome = true) :
    cardSubjectCombinator b k = some .minCardinality := by
  simp [cardSubjectCombinator, h]

/-! ## Build-time checks -/

private def cA : WfIri := ⟨"http://example.org/A", by decide⟩
private def cP : WfIri := ⟨"http://example.org/p", by decide⟩

/-! `[ a owl:Restriction ; owl:onProperty :p ; owl:someValuesFrom :A ]` —
a NAMED filler, so not a rewrite target. -/
private def svfNamed : Bgp :=
  [ { s := .bnode "r", p := .iri rdfType, o := .iri owlRestriction },
    { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlSomeValuesFrom, o := .iri cA } ]

#guard isSvfSubject svfNamed "r" == true
#guard isRestrictionSubject svfNamed "r" == true
#guard restrictionHasNestedFiller svfNamed "r" == false
#guard isRewriteTargetRestriction svfNamed "r" == false

/-! The same shape with `owl:allValuesFrom` IS a target, named filler
and all. -/
private def avfNamed : Bgp :=
  [ { s := .bnode "r", p := .iri owlAllValuesFrom, o := .iri cA } ]
#guard isRewriteTargetRestriction avfNamed "r" == true

/-! A someValuesFrom whose filler is a flat intersection bnode IS a
target — the `simple5` / `simple8` shape. -/
private def svfNested : Bgp :=
  [ { s := .bnode "r", p := .iri owlSomeValuesFrom, o := .bnode "c" },
    { s := .bnode "c", p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest, o := .iri rdfNil } ]
#guard restrictionHasNestedFiller svfNested "r" == true
#guard isRewriteTargetRestriction svfNested "r" == true

/-! Cardinality classification, qualified and unqualified. -/
private def maxCard : Bgp :=
  [ { s := .bnode "r", p := .iri owlMaxQualifiedCardinality,
      o := .literal (Literal.string "1") },
    { s := .bnode "r", p := .iri owlOnClass, o := .iri cA } ]
#guard cardSubjectCombinator maxCard "r" == some Restriction.maxCardinality
#guard isCardSubject maxCard "r" == true
#guard isRestrictionSubject maxCard "r" == true

private def exactCard : Bgp :=
  [ { s := .bnode "r", p := .iri owlCardinality,
      o := .literal (Literal.string "2") } ]
#guard cardSubjectCombinator exactCard "r" == some Restriction.exactCardinality

/-! A complement bnode is recognised, and its target recovered. -/
private def compl : Bgp :=
  [ { s := .bnode "n", p := .iri rdfType, o := .iri owlClass },
    { s := .bnode "n", p := .iri owlComplementOf, o := .iri cA } ]
#guard isComplementOfSubject compl "n" == true
#guard complementOfTarget compl "n" == some (PatternTerm.iri cA)
#guard isRestrictionSubject compl "n" == false

/-! Nothing fires on a marker-free BGP. -/
#guard isRestrictionSubject [{ s := .var "x", p := .iri cP, o := .var "y" }] "r" == false

/-! ## Axiom audit -/

#print axioms svf_namedFiller_not_target
#print axioms cardSubjectCombinator_min

end L4Factoidal.OWL.QueryRewriteCore
