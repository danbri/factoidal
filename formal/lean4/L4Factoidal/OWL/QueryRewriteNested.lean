/-
L4Factoidal.OWL.QueryRewriteNested — layer 7 of the port of
`OWL.QueryRewrite`: nested markers, the nested BGP rewrite, and
`rewriteQuery`.

Layers 1 to 5 built the pieces — marker keys, collection walking, the
flat rewrite, the union ladder, the restriction classifier, the
recursive class-expression expander. Layer 6 added join normalisation.
This layer is the part that finds markers ANYWHERE in a BGP, including
inside another marker's filler, and the top-level entry point the
evaluator calls.

## One marker type, two Lean types

The F* `ce_combinator` is a single type carrying the flat combinators
(`CE_Intersect`, `CE_Union`) and the restriction family
(`CE_SomeValuesFrom`, the cardinality kinds, `CE_ComplementOf`). The
Lean layers split it: `CeCombinator` for the flat pair,
`Restriction` for the rest. `MarkerKind` puts them back together for
the marker list, which is what needs both.

## What the marker search does

`findMarkers` runs three passes, in the F* order:

1. `findFlatMarkersAcc` — the `owl:intersectionOf` / `owl:unionOf`
   markers.
2. `addRestrictionMarkersAcc` — one pass over the BGP adding
   restriction subjects. `owl:someValuesFrom` is added ONLY when its
   filler is itself nested, because a named filler is already handled
   by the closure. `owl:allValuesFrom` and `owl:complementOf` are added
   unconditionally; the F* source gives the reason for complement —
   the closure has no canonical materialisation for class complement,
   so the rewriter is the only path.
3. `addInnerRestrictionsAcc` — a fuelled transitive walk from the
   restriction markers found in pass 2 into their fillers, so an inner
   restriction's bookkeeping is stripped as well.

Fuel is the BGP length plus one in both passes that take it, matching
the F* source.

## The residue rule, and the OR that has to stay an OR

`isNestedBookkeeping` strips a triple when its subject is a marker and
its predicate is class-expression meta, OR when its subject is on some
marker's `rdf:first`/`rdf:rest` chain. The F* source records why the
second test is not an `else if`: a nested class expression can have the
parser reuse one blank node as BOTH a marker and a list cell, and an
`else if` would leave one of its two roles unstripped. The port keeps
the `||`, and `bookkeeping_or_is_not_elseif` pins the case where the
two differ so a later edit cannot quietly make it an `else if`.

## Scope

`rewritePatternNested` descends every group-graph-pattern constructor
except `subSelect`, exactly as the F* `rewrite_ggp` does. Sub-select
bodies are not rewritten in either tree.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewriteJoins
import L4Factoidal.OWL.QueryRewriteExpand
import L4Factoidal.OWL.QueryRewritePattern

namespace L4Factoidal.OWL.QueryRewriteNested

open L4Factoidal.RDF
open L4Factoidal.RDFS (rdfType rdfFirst rdfRest rdfNil)
open L4Factoidal.SPARQL
open L4Factoidal.OWL.QueryRewriteCore
open L4Factoidal.OWL.RL (owlIntersectionOf owlUnionOf owlComplementOf
  owlSomeValuesFrom owlAllValuesFrom owlOnProperty owlOnClass owlClass
  owlRestriction owlMinCardinality owlMaxCardinality owlCardinality
  owlMinQualifiedCardinality owlMaxQualifiedCardinality
  owlQualifiedCardinality)

/-! ## 1. One marker kind -/

/-- The F* `ce_combinator`, rebuilt from the two Lean types that split
it. -/
inductive MarkerKind where
  | flat (c : CeCombinator)
  | restriction (r : Restriction)
  deriving DecidableEq, Repr

abbrev MarkerList := List (String × MarkerKind)

def markerListHas (acc : MarkerList) (k : String) : Bool :=
  acc.any (fun kv => kv.1 == k)

/-- Predicate-level cardinality classifier. Unqualified and qualified
forms classify together, tried min, max, exact — the F* order. -/
def combinatorOfCardPred (p : WfIri) : Option Restriction :=
  if p == owlMinCardinality || p == owlMinQualifiedCardinality then
    some .minCardinality
  else if p == owlMaxCardinality || p == owlMaxQualifiedCardinality then
    some .maxCardinality
  else if p == owlCardinality || p == owlQualifiedCardinality then
    some .exactCardinality
  else none

/-! ## 2. Pass 2 — restriction subjects in this BGP -/

def addRestrictionMarkersAcc (b : Bgp) : Bgp → MarkerList → MarkerList
  | [], acc => acc
  | tp :: rest, acc =>
      let keep (kind : Option (String × MarkerKind)) : MarkerList :=
        match kind with
        | none => acc
        | some (k, c) => if markerListHas acc k then acc else acc ++ [(k, c)]
      let next : MarkerList :=
        match subjectMarkerKey tp.s, tp.p with
        | some k, .iri p =>
            if p == owlSomeValuesFrom then
              if restrictionHasNestedFiller b k then
                keep (some (k, .restriction .someValuesFrom))
              else acc
            else if p == owlAllValuesFrom then
              keep (some (k, .restriction .allValuesFrom))
            else if p == owlComplementOf then
              keep (some (k, .restriction .complementOf))
            else
              match combinatorOfCardPred p with
              | some c => keep (some (k, .restriction c))
              | none => acc
        | _, _ => acc
      addRestrictionMarkersAcc b rest next

/-! ## 3. Pass 3 — inner restrictions, transitively

A named-class filler ends the walk; a blank-node filler that is itself
a restriction is marked and pushed back on the work list. -/

def addInnerRestrictionsAcc (b : Bgp) : List String → MarkerList → Nat → MarkerList
  | _, acc, 0 => acc
  | [], acc, _ => acc
  | k :: rest, acc, n + 1 =>
      match restrictionFiller b k with
      | none => addInnerRestrictionsAcc b rest acc n
      | some (filler, _) =>
          match markerKey filler with
          | none => addInnerRestrictionsAcc b rest acc n
          | some kf =>
              if markerListHas acc kf then
                addInnerRestrictionsAcc b rest acc n
              else if isSvfSubject b kf then
                addInnerRestrictionsAcc b (rest ++ [kf])
                  (acc ++ [(kf, .restriction .someValuesFrom)]) n
              else if isAvfSubject b kf then
                addInnerRestrictionsAcc b (rest ++ [kf])
                  (acc ++ [(kf, .restriction .allValuesFrom)]) n
              else if isComplementOfSubject b kf then
                -- no further walk: a complement target is a class term,
                -- not a chain head
                addInnerRestrictionsAcc b rest
                  (acc ++ [(kf, .restriction .complementOf)]) n
              else addInnerRestrictionsAcc b rest acc n

/-! ## 4. All markers -/

def flatMarkersAsKinds (b : Bgp) : MarkerList :=
  (findFlatMarkers b).map (fun kc => (kc.1, MarkerKind.flat kc.2))

/-- The work list for pass 3: the someValuesFrom and allValuesFrom keys
pass 2 added. Cardinality and complement markers are not chased, as in
the F* source. -/
def restrictionWorkKeys (ms : MarkerList) : List String :=
  ms.foldl (fun acc km =>
    match km.2 with
    | .restriction .someValuesFrom => acc ++ [km.1]
    | .restriction .allValuesFrom => acc ++ [km.1]
    | _ => acc) []

def findMarkers (b : Bgp) : MarkerList :=
  let withRestrictions := addRestrictionMarkersAcc b b (flatMarkersAsKinds b)
  addInnerRestrictionsAcc b (restrictionWorkKeys withRestrictions)
    withRestrictions (b.length + 1)

/-! ## 5. Top-level markers and the residue rule -/

def collectTopMarkersAcc (markers : MarkerList) : Bgp → List String → List String
  | [], acc => acc.reverse
  | tp :: rest, acc =>
      match tp.p with
      | .iri p =>
          if p == rdfType then
            match markerKey tp.o with
            | some k =>
                if markerListHas markers k && !acc.contains k then
                  collectTopMarkersAcc markers rest (k :: acc)
                else collectTopMarkersAcc markers rest acc
            | none => collectTopMarkersAcc markers rest acc
          else collectTopMarkersAcc markers rest acc
      | _ => collectTopMarkersAcc markers rest acc

def collectTopMarkers (b : Bgp) (markers : MarkerList) : List String :=
  collectTopMarkersAcc markers b []

/-- `?x rdf:type m` where `m` is one of the top-level markers. -/
def isAnyTopConsumer (topMarkers : List String) (tp : TriplePattern) : Bool :=
  match tp.p, markerKey tp.o with
  | .iri p, some k => p == rdfType && topMarkers.contains k
  | _, _ => false

/-- Every class-expression meta predicate that is stripped when its
subject is a marker. -/
def isCeMetaPred (p : WfIri) (o : PatternTerm) : Bool :=
  p == owlIntersectionOf || p == owlUnionOf || p == owlComplementOf ||
  p == owlOnProperty || p == owlSomeValuesFrom || p == owlAllValuesFrom ||
  p == owlMinCardinality || p == owlMaxCardinality || p == owlCardinality ||
  p == owlMinQualifiedCardinality || p == owlMaxQualifiedCardinality ||
  p == owlQualifiedCardinality || p == owlOnClass ||
  (p == rdfType && (match o with
                    | .iri oi => oi == owlClass || oi == owlRestriction
                    | _ => false))

/-- A bookkeeping triple of ANY marker, nested ones included.

The two tests are joined with `||`, never `else if`. A nested class
expression can have one blank node serve as both a marker and a list
cell, and an `else if` leaves one of the two roles unstripped. -/
def isNestedBookkeeping (markers : MarkerList) (allChainKeys : List String)
    (tp : TriplePattern) : Bool :=
  match subjectMarkerKey tp.s, tp.p with
  | some sk, .iri p =>
      let isMarker := markerListHas markers sk
      let isOnChain := allChainKeys.contains sk
      let markerMeta := isMarker && isCeMetaPred p tp.o
      let chainMeta := isOnChain && (p == rdfFirst || p == rdfRest)
      markerMeta || chainMeta
  | _, _ => false

/-- The union of every marker's `rdf:first`/`rdf:rest` chain keys. -/
def allChainKeysForMarkers (b : Bgp) (markers : MarkerList) : List String :=
  markers.foldl (fun acc km =>
    let headOpt :=
      match bgpFindFirstObj b km.1 owlIntersectionOf with
      | some h => some h
      | none => bgpFindFirstObj b km.1 owlUnionOf
    match headOpt with
    | none => acc
    | some hd =>
        (collectionChainKeys b hd).foldl
          (fun a c => if a.contains c then a else a ++ [c]) acc) []

/-! ## 6. The nested BGP rewrite -/

def nestedResidue (markers : MarkerList) (chainKeys : List String)
    (topMarkers : List String) (b : Bgp) : Bgp :=
  b.foldl (fun acc tp =>
    if isNestedBookkeeping markers chainKeys tp then acc
    else if isAnyTopConsumer topMarkers tp then acc
    else acc ++ [tp]) []

def nestedConsumerPatterns (b : Bgp) (topMarkers : List String) (fuel : Nat) :
    List QueryPattern :=
  b.foldl (fun acc tp =>
    if isAnyTopConsumer topMarkers tp then
      acc ++ [expandCeSubject b tp.s tp.o fuel]
    else acc) []

/-- Stitch the residue and the consumer expansions. Two BGPs coalesce
into one, which is what keeps `paper-sparqldl-Q2` a single BGP join. -/
def stitchNested (base : QueryPattern) (parts : List QueryPattern) : QueryPattern :=
  parts.foldl (fun acc g =>
    match acc, g with
    | .empty, _ => g
    | .bgp ba, .bgp bg => .bgp (ba ++ bg)
    | _, _ => .join acc g) base

def rewriteBgpNested (b : Bgp) : QueryPattern :=
  match findMarkers b with
  | [] => .bgp b
  | markers =>
      match collectTopMarkers b markers with
      -- markers exist but none is consumed by a `?x rdf:type m`
      -- triple, so there is nothing safe to rewrite: fall through to
      -- the flat rewriter, which also leaves the BGP alone
      | [] => rewriteBgpFlat b
      | topMarkers =>
          let chainKeys := allChainKeysForMarkers b markers
          let residue := nestedResidue markers chainKeys topMarkers b
          let consumers := nestedConsumerPatterns b topMarkers (markers.length + 1)
          match consumers with
          | [] => if residue.isEmpty then .empty else .bgp residue
          | _ =>
              stitchNested (if residue.isEmpty then .empty else .bgp residue) consumers

/-! ## 7. The recursion, and the entry point -/

def rewritePatternNested : QueryPattern → QueryPattern
  | .bgp b => rewriteBgpNested b
  | .join a b => .join (rewritePatternNested a) (rewritePatternNested b)
  | .leftJoin a b e => .leftJoin (rewritePatternNested a) (rewritePatternNested b) e
  | .filter e a => .filter e (rewritePatternNested a)
  | .union a b => .union (rewritePatternNested a) (rewritePatternNested b)
  | .minus a b => .minus (rewritePatternNested a) (rewritePatternNested b)
  | .graph gt a => .graph gt (rewritePatternNested a)
  | .lateral a b => .lateral (rewritePatternNested a) (rewritePatternNested b)
  | .bind e v a => .bind e v (rewritePatternNested a)
  | .values vs rs => .values vs rs
  | .service i s a => .service i s (rewritePatternNested a)
  | .serviceVar v s a => .serviceVar v s (rewritePatternNested a)
  -- sub-select bodies are not descended into, as in the F* source
  | .subSelect q => .subSelect q
  | .propertyPath s pp o => .propertyPath s pp o
  | .empty => .empty

/-- Normalise joins first, then rewrite. The order matters: the parser
splits a BGP at every period, so without the normalisation pass a
marker and its list chain sit in different leaves and the rewriter
finds nothing.

DISTINCT for `owl:unionOf` set semantics is applied locally at each
union emission site, not as a top-level modifier, so a query with no
class expression keeps bag semantics. -/
def rewriteQueryPattern (p : QueryPattern) : QueryPattern :=
  rewritePatternNested (QueryRewriteJoins.normaliseJoins p)

/-! ## 8. Facts -/

/-- A BGP with no marker is returned unchanged. -/
theorem rewriteBgpNested_noMarker (b : Bgp) (h : findMarkers b = []) :
    rewriteBgpNested b = .bgp b := by
  simp only [rewriteBgpNested, h]

/-- The empty pattern is a fixed point of the whole entry point. -/
theorem rewriteQueryPattern_empty : rewriteQueryPattern .empty = .empty := rfl

/-- A sub-select body is untouched by the entry point. -/
theorem rewriteQueryPattern_subSelect (q : Query) :
    rewriteQueryPattern (.subSelect q) = .subSelect q := rfl

/-- UNION structure survives the recursion. -/
theorem rewritePatternNested_union (a b : QueryPattern) :
    rewritePatternNested (.union a b)
      = .union (rewritePatternNested a) (rewritePatternNested b) := rfl

/-- Nothing is stripped when the marker list and the chain list are
both empty, so a BGP with no class expression keeps every triple. -/
theorem isNestedBookkeeping_nil (tp : TriplePattern) :
    isNestedBookkeeping [] [] tp = false := by
  simp only [isNestedBookkeeping, markerListHas, List.any_nil,
             List.contains_nil, Bool.false_and, Bool.or_self]
  split <;> rfl

theorem isAnyTopConsumer_nil (tp : TriplePattern) :
    isAnyTopConsumer [] tp = false := by
  simp only [isAnyTopConsumer, List.contains_nil, Bool.and_false]
  split <;> rfl

theorem nestedResidue_nil (b : Bgp) : nestedResidue [] [] [] b = b := by
  have step : ∀ (l : Bgp) (acc : Bgp),
      l.foldl (fun acc tp =>
        if isNestedBookkeeping [] [] tp then acc
        else if isAnyTopConsumer [] tp then acc
        else acc ++ [tp]) acc = acc ++ l := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons tp rest ih =>
        intro acc
        rw [List.foldl_cons,
            if_neg (by simp [isNestedBookkeeping_nil]),
            if_neg (by simp [isAnyTopConsumer_nil]),
            ih (acc ++ [tp])]
        simp
  simpa [nestedResidue] using step b []

/-! ## Build-time checks -/

private def cA : WfIri := ⟨"http://example.org/A", by decide⟩
private def cB : WfIri := ⟨"http://example.org/B", by decide⟩
private def cP : WfIri := ⟨"http://example.org/p", by decide⟩

/-- `?x a [ owl:intersectionOf (:A :B) ]`, as the parser leaves it. -/
private def bgpIntersect : Bgp :=
  [ { s := .var "x", p := .iri rdfType, o := .bnode bnodeVarPrefix },
    { s := .bnode bnodeVarPrefix, p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil } ]

/-- A plain BGP with no class expression. -/
private def bgpPlain : Bgp :=
  [ { s := .var "x", p := .iri cP, o := .var "y" } ]

/-! A BGP with no marker survives untouched. -/
#guard findMarkers bgpPlain == ([] : MarkerList)
#guard (match rewriteBgpNested bgpPlain with | .bgp b => b.length | _ => 0) == 1

/-! An intersection marker is found, and its list cells are chain keys,
so the bookkeeping is stripped rather than left in the residue. -/
#guard (findMarkers bgpIntersect).length == 1
#guard (collectTopMarkers bgpIntersect (findMarkers bgpIntersect)).length == 1
#guard (allChainKeysForMarkers bgpIntersect (findMarkers bgpIntersect)).length == 2
#guard (nestedResidue (findMarkers bgpIntersect)
          (allChainKeysForMarkers bgpIntersect (findMarkers bgpIntersect))
          (collectTopMarkers bgpIntersect (findMarkers bgpIntersect))
          bgpIntersect).length == 0

/-! The cardinality classifier keeps qualified and unqualified together
and resolves min before max before exact. -/
#guard combinatorOfCardPred owlMinCardinality == some Restriction.minCardinality
#guard combinatorOfCardPred owlMinQualifiedCardinality == some Restriction.minCardinality
#guard combinatorOfCardPred owlMaxQualifiedCardinality == some Restriction.maxCardinality
#guard combinatorOfCardPred owlQualifiedCardinality == some Restriction.exactCardinality
#guard combinatorOfCardPred owlOnProperty == (none : Option Restriction)

/-! The residue rule's `||` is not an `else if`. One blank node that is
BOTH a marker and a list cell has its chain triple stripped; an
`else if` on `isMarker` would keep it, because `rdf:first` is not a
class-expression meta predicate. -/
private def dualRoleTriple : TriplePattern :=
  { s := .bnode "d", p := .iri rdfFirst, o := .iri cA }

#guard isNestedBookkeeping [("d", .flat .intersect)] ["d"] dualRoleTriple == true
#guard isNestedBookkeeping [("d", .flat .intersect)] [] dualRoleTriple == false
#guard isCeMetaPred rdfFirst (.iri cA) == false

/-! ## Axiom audit -/

#print axioms rewriteBgpNested_noMarker
#print axioms isNestedBookkeeping_nil
#print axioms nestedResidue_nil
#print axioms rewriteQueryPattern_subSelect

end L4Factoidal.OWL.QueryRewriteNested
