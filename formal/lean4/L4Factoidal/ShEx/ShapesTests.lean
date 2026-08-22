/-
L4Factoidal.ShEx.ShapesTests — build-time checks for shape
satisfaction, with the EXTRA-vs-CLOSED separation pinned.
-/
import L4Factoidal.ShEx.Shapes

namespace L4Factoidal.ShEx
open L4Factoidal.RDF

private def iriT (s : String) : Term :=
  if h : isIri s then .iri ⟨s, h⟩ else .bnode "invalid"
private def litT (s : String) : Term := .literal (Literal.string s)

private def P : String := "http://ex/p"
private def Q : String := "http://ex/q"

private def tcP (min max : Int) (ve : Option ShapeExpr) : TripleExpr :=
  .tripleConstraint (.mk none false P ve min max [] [])

private def shape (closed : Bool) (extra : List String) (te : Option TripleExpr) : Shape :=
  .mk closed extra te [] [] []

private def arcP (v : Term) : Arc := ⟨P, v, false⟩
private def arcQ (v : Term) : Arc := ⟨Q, v, false⟩

-- Cardinality over the neighbourhood.
#guard satisfiesShape (shape false [] (some (tcP 1 1 none))) [arcP (litT "x")]
#guard !(satisfiesShape (shape false [] (some (tcP 1 1 none))) [])
#guard !(satisfiesShape (shape false [] (some (tcP 1 1 none)))
           [arcP (litT "x"), arcP (litT "y")])
#guard satisfiesShape (shape false [] (some (tcP 1 (-1) none)))
         [arcP (litT "x"), arcP (litT "y")]   -- unbounded

-- A valueExpr filters which arcs the constraint can take.
private def onlyIri : ShapeExpr := .nodeConstraint { nodeKind := some .iri }
#guard satisfiesShape (shape false [] (some (tcP 1 1 (some onlyIri))))
         [arcP (iriT "http://ex/a")]
#guard !(satisfiesShape (shape false [] (some (tcP 1 1 (some onlyIri))))
           [arcP (litT "x")])

-- CLOSED bounds only UNMENTIONED predicates.
#guard satisfiesShape (shape false [] (some (tcP 1 1 none)))
         [arcP (litT "x"), arcQ (litT "y")]          -- open: q tolerated
#guard !(satisfiesShape (shape true [] (some (tcP 1 1 none)))
           [arcP (litT "x"), arcQ (litT "y")])       -- closed: q forbidden
#guard satisfiesShape (shape true [] (some (tcP 1 1 none))) [arcP (litT "x")]

-- EXTRA tolerates LEFTOVER arcs on a MENTIONED predicate — the arcs
-- the constraint could not take because its valueExpr failed.
#guard satisfiesShape (shape false [P] (some (tcP 1 1 (some onlyIri))))
         [arcP (iriT "http://ex/a"), arcP (litT "leftover")]
-- ...and WITHOUT extra, that same leftover fails, even though the
-- shape is OPEN. This is the distinction the F* module records as a
-- real bug when conflated: `closed` never grants leftover tolerance.
#guard !(satisfiesShape (shape false [] (some (tcP 1 1 (some onlyIri))))
           [arcP (iriT "http://ex/a"), arcP (litT "leftover")])

-- EXTRA works regardless of `closed`.
#guard satisfiesShape (shape true [P] (some (tcP 1 1 (some onlyIri))))
         [arcP (iriT "http://ex/a"), arcP (litT "leftover")]

-- A shape with no expression: closed means nothing may be present.
#guard satisfiesShape (shape false [] none) [arcP (litT "x")]
#guard !(satisfiesShape (shape true [] none) [arcP (litT "x")])
#guard satisfiesShape (shape true [] none) []

-- EachOf requires every branch; OneOf takes the first satisfied one.
private def eachPQ : TripleExpr :=
  .eachOf (.mk none [tcP 1 1 none, .tripleConstraint (.mk none false Q none 1 1 [] [])]
             none none [] [])
#guard satisfiesShape (shape false [] (some eachPQ)) [arcP (litT "x"), arcQ (litT "y")]
#guard !(satisfiesShape (shape false [] (some eachPQ)) [arcP (litT "x")])

private def onePQ : TripleExpr :=
  .oneOf (.mk none [tcP 1 1 none, .tripleConstraint (.mk none false Q none 1 1 [] [])]
            none none [] [])
#guard satisfiesShape (shape false [Q] (some onePQ)) [arcP (litT "x"), arcQ (litT "y")]

-- Neighbourhood construction picks up forward and inverse arcs.
private def g : List Triple :=
  [⟨.iri ⟨"http://ex/n", by decide⟩, ⟨P, by decide⟩, litT "v"⟩]
#guard (neighbourhood g (iriT "http://ex/n")).length == 1
#guard (neighbourhood g (litT "v")).any (·.inverse)

-- Mentioned predicates drive the CLOSED test.
#guard mentionedPredicates (tcP 1 1 none) == [P]
#guard (mentionedPredicates eachPQ).length == 2

end L4Factoidal.ShEx
