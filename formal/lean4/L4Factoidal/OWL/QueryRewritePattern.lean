/-
L4Factoidal.OWL.QueryRewritePattern — layer 3 of the port of
`OWL.QueryRewrite`: the UNION ladder, the marker scan, and the
`QueryPattern` traversal that ties layers 1 and 2 to a whole query.

With this the FLAT path (Phase 3 in the F\* source — `owl:intersectionOf`
and `owl:unionOf` over named classes) is complete. Phase 4's nested
class expressions and the restriction combinators
(`owl:someValuesFrom`, `owl:allValuesFrom`, the cardinality family,
`owl:complementOf`) are not here, so `OWL.QueryRewrite` remains not
covered and no alias was added.

## Why the union branch is wrapped in a DISTINCT sub-select

SPARQL `UNION` is bag-semantic; OWL `unionOf` is set-theoretic. One `?x`
matching two operands would contribute two rows. `wrapDistinctOverPattern`
puts a `SELECT * DISTINCT { … }` around the ladder so the CE-expanded
portion dedupes without forcing DISTINCT on the user's outer
projection — which would break bag-semantic queries that never
mentioned OWL at all.

The F\* source is emphatic about the placement, and CLAUDE.md repeats
it: the wrap belongs at the CE-emission site, and the internal-variable
strip belongs at the FINAL projection only. `SPARQL/RewriteVarStrip.lean`
proves the second half of that (`strip_inside_join_admits_spurious_row`).

**Only wrap 2+ branches.** A zero-branch union collapses to `empty` and
a one-branch union to the BGP itself; neither can duplicate, so wrapping
would add dead AST. `buildUnionPattern` follows the F\* source in
special-casing both.

## What is proved

`unionLadder_leaves`: the ladder contains exactly the branches it was
given, so no branch is dropped and none is invented. That is the
property a left-deep fold can silently get wrong.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewriteFlat
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.OWL.QueryRewriteCore

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.SPARQL
open L4Factoidal.OWL.RL (owlIntersectionOf owlUnionOf owlClass)

/-! ## One union branch -/

/-- The shared residue, plus one `rdf:type operand` triple for each
consumer subject. -/
def buildUnionBranch (residue : Bgp) (consumers : List TriplePattern)
    (op : PatternTerm) : Bgp :=
  residue ++ consumers.map (fun tp => { s := tp.s, p := .iri rdfType, o := op })

/-! ## The ladder -/

/-- Stitch branches into a left-deep `union` tree. -/
def unionLadder (acc : QueryPattern) : List QueryPattern → QueryPattern
  | [] => acc
  | br :: rest => unionLadder (.union acc br) rest

/-- The leaves of a left-deep ladder, in order. -/
def ladderLeaves : QueryPattern → List QueryPattern
  | .union l r => ladderLeaves l ++ [r]
  | p => [p]

/-- **The ladder keeps exactly its branches.** A left-deep fold is easy
to write so that it drops the head or re-associates; this says it does
neither. -/
theorem unionLadder_leaves (acc : QueryPattern) :
    ∀ branches : List QueryPattern,
      ladderLeaves (unionLadder acc branches) = ladderLeaves acc ++ branches
  | [] => by simp [unionLadder]
  | br :: rest => by
      simp only [unionLadder, unionLadder_leaves (.union acc br) rest,
                 ladderLeaves, List.append_assoc, List.cons_append,
                 List.nil_append]

/-! ## The DISTINCT wrapper -/

/-- `SELECT * DISTINCT { p }`. -/
def wrapDistinctOverPattern (p : QueryPattern) : QueryPattern :=
  .subSelect (mkQuery (.select .all) p (modifier := { distinct := true }))

/-- Assemble branch BGPs into a pattern. Zero branches collapse to
`empty`, one to the BGP itself, and only 2+ get the ladder and the
wrapper. -/
def buildUnionPattern : List Bgp → QueryPattern
  | [] => .empty
  | [b] => .bgp b
  | b :: rest =>
      wrapDistinctOverPattern (unionLadder (.bgp b) (rest.map QueryPattern.bgp))

/-! ## Finding the markers

A key is a flat class-expression marker when the BGP carries
`(m owl:intersectionOf _)` or `(m owl:unionOf _)`. The combinator says
which. -/

inductive CeCombinator where
  | intersect
  | union
  deriving DecidableEq, Repr

def combinatorOfPredFlat (p : WfIri) : Option CeCombinator :=
  if p == owlIntersectionOf then some .intersect
  else if p == owlUnionOf then some .union
  else none

/-- Markers in the order the BGP mentions them, without duplicates. -/
def findFlatMarkersAcc : Bgp → List (String × CeCombinator) →
    List (String × CeCombinator)
  | [], acc => acc.reverse
  | tp :: rest, acc =>
      match subjectMarkerKey tp.s, tp.p with
      | some k, .iri p =>
          match combinatorOfPredFlat p with
          | some c =>
              if acc.any (fun e => e.1 == k) then findFlatMarkersAcc rest acc
              else findFlatMarkersAcc rest ((k, c) :: acc)
          | none => findFlatMarkersAcc rest acc
      | _, _ => findFlatMarkersAcc rest acc

def findFlatMarkers (b : Bgp) : List (String × CeCombinator) :=
  findFlatMarkersAcc b []

/-! ## Rewriting one BGP for one marker -/

/-- One intersection marker, applied in place. The BGP stays a BGP:
only a union escalates out of one. -/
def rewriteBgpOneIntersection (k : String) (b : Bgp) : Bgp :=
  match extractFlatIntersection b k with
  | none => b
  | some operands =>
      let chain :=
        match bgpFindFirstObj b k owlIntersectionOf with
        | some listHead => collectionChainKeys b listHead
        | none => []
      rewriteBgpIntersection k chain operands b

/-- One union marker. This is where the BGP becomes a union ladder. -/
def rewriteBgpOneUnion (k : String) (b : Bgp) : QueryPattern :=
  match extractFlatUnion b k with
  | none => .bgp b
  | some operands =>
      let chain :=
        match bgpFindFirstObj b k owlUnionOf with
        | some listHead => collectionChainKeys b listHead
        | none => []
      let residue := rewriteBgpStripMarker k chain b
      let consumers := rewriteBgpCollectConsumers k b
      buildUnionPattern (operands.map (buildUnionBranch residue consumers))

/-- EVERY intersection marker, in order, then the FIRST union marker.

The first Lean version of this function applied only the first marker
of either kind, so a BGP carrying two intersection markers, or an
intersection followed by a union, was rewritten differently from the F*
tree. The F* source's own comment states the order -- "Apply all
intersection markers first (in order), then the first union marker" --
and remaining union markers in one BGP are left for the nested pass. -/
def rewriteBgpFlat (b : Bgp) : QueryPattern :=
  let markers := findFlatMarkers b
  let interKeys := markers.foldl (fun acc kc =>
    match kc.2 with | .intersect => acc ++ [kc.1] | _ => acc) []
  let unionKeys := markers.foldl (fun acc kc =>
    match kc.2 with | .union => acc ++ [kc.1] | _ => acc) []
  let bAfterInter := interKeys.foldl (fun cur k => rewriteBgpOneIntersection k cur) b
  match unionKeys with
  | [] => .bgp bAfterInter
  | k :: _ => rewriteBgpOneUnion k bAfterInter

/-! ## The traversal

Structure-preserving: every constructor is rebuilt from its rewritten
children, and only `bgp` nodes can change. That is what lets the
rewriter run unconditionally, which the F\* banner asserts and this
definition makes checkable. -/

def rewritePattern : QueryPattern → QueryPattern
  | .bgp b => rewriteBgpFlat b
  | .join l r => .join (rewritePattern l) (rewritePattern r)
  | .leftJoin l r c => .leftJoin (rewritePattern l) (rewritePattern r) c
  | .filter c p => .filter c (rewritePattern p)
  | .union l r => .union (rewritePattern l) (rewritePattern r)
  | .minus l r => .minus (rewritePattern l) (rewritePattern r)
  | .graph n p => .graph n (rewritePattern p)
  | .lateral l r => .lateral (rewritePattern l) (rewritePattern r)
  | .bind e v p => .bind e v (rewritePattern p)
  | .service e s p => .service e s (rewritePattern p)
  | .serviceVar v s p => .serviceVar v s (rewritePattern p)
  -- A sub-select carries a whole Query; rewriting inside it needs the
  -- Query-level pass, which is where the F* source puts it too.
  | .subSelect q => .subSelect q
  | .values vs rs => .values vs rs
  | .propertyPath s p o => .propertyPath s p o
  | .empty => .empty

/-- A pattern with no flat marker anywhere is returned unchanged. This
is the "safe to apply unconditionally" claim, for the fragment the
traversal can reach. -/
theorem rewritePattern_bgp_noMarker (b : Bgp) (h : findFlatMarkers b = []) :
    rewritePattern (.bgp b) = .bgp b := by
  simp only [rewritePattern, rewriteBgpFlat, h, List.foldl_nil]

/-! ## Build-time checks -/

private def cA : WfIri := ⟨"http://example.org/A", by decide⟩
private def cB : WfIri := ⟨"http://example.org/B", by decide⟩
private def cP : WfIri := ⟨"http://example.org/p", by decide⟩

private def interBgp2 : Bgp :=
  [ { s := .var "x",    p := .iri rdfType, o := .bnode "c" },
    { s := .bnode "c",  p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil },
    { s := .var "x",    p := .iri cP,       o := .var "y" } ]

private def unionBgp2 : Bgp :=
  [ { s := .var "x",    p := .iri rdfType, o := .bnode "c" },
    { s := .bnode "c",  p := .iri owlUnionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil },
    { s := .var "x",    p := .iri cP,       o := .var "y" } ]

#guard findFlatMarkers interBgp2 == [("c", CeCombinator.intersect)]
#guard findFlatMarkers unionBgp2 == [("c", CeCombinator.union)]

/-! Intersection: one BGP, three triples, no marker left. -/
#guard (match rewriteBgpFlat interBgp2 with
        | .bgp out => out.length == 3
        | _ => false)

/-! Union: a DISTINCT sub-select over a two-branch ladder. -/
#guard (match rewriteBgpFlat unionBgp2 with
        | .subSelect _ => true
        | _ => false)

/-! Both branches survive the ladder, in order. -/
#guard (ladderLeaves (unionLadder (.bgp [])
          [QueryPattern.bgp interBgp2, QueryPattern.bgp unionBgp2])).length == 3

/-! A marker-free BGP is untouched, and so is a pattern built over it. -/
private def plainBgp2 : Bgp := [{ s := .var "x", p := .iri cP, o := .var "y" }]
#guard findFlatMarkers plainBgp2 == []
#guard (match rewriteBgpFlat plainBgp2 with
        | .bgp out => out == plainBgp2
        | _ => false)
#guard (match rewritePattern (.join (.bgp plainBgp2) .empty) with
        | .join (.bgp out) .empty => out == plainBgp2
        | _ => false)

/-! One branch is NOT wrapped — wrapping would be dead AST. -/
#guard (match buildUnionPattern [plainBgp2] with
        | .bgp _ => true
        | _ => false)
#guard (match buildUnionPattern [] with
        | .empty => true
        | _ => false)

/-! ## Axiom audit -/

#print axioms unionLadder_leaves
#print axioms rewritePattern_bgp_noMarker

end L4Factoidal.OWL.QueryRewriteCore
