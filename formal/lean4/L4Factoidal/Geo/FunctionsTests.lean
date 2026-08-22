/-
L4Factoidal.Geo.FunctionsTests — the geof: extension functions,
exercised exactly as the SPARQL evaluator would call them.
-/
import L4Factoidal.Geo.Functions

namespace L4Factoidal.Geo
open L4Factoidal.SPARQL

/-- Build a `geo:wktLiteral` argument the way the evaluator presents
    one. The datatype IRI is well-formed by `rfl`, the Lean
    counterpart of F*'s `assert_norm`. -/
private def wktLit (s : String) : EvalResult :=
  .term (.literal ⟨⟨s, ⟨wktLiteralIri, by rfl⟩, none, none⟩, by rfl⟩)

private def sq : String := "POLYGON((0 0,4 0,4 4,0 4,0 0))"

#guard extFns (geofNs ++ "sfWithin") [wktLit "POINT(2 2)", wktLit sq]
       == some (.bool true)
#guard extFns (geofNs ++ "sfWithin") [wktLit "POINT(9 9)", wktLit sq]
       == some (.bool false)

-- A boundary point INTERSECTS but is not WITHIN (Simple Features).
#guard extFns (geofNs ++ "sfIntersects") [wktLit "POINT(0 0)", wktLit sq]
       == some (.bool true)
#guard extFns (geofNs ++ "sfWithin") [wktLit "POINT(0 0)", wktLit sq]
       == some (.bool false)
#guard extFns (geofNs ++ "sfTouches") [wktLit "POINT(0 0)", wktLit sq]
       == some (.bool true)
#guard extFns (geofNs ++ "sfDisjoint") [wktLit "POINT(9 9)", wktLit sq]
       == some (.bool true)

-- Contains is Within with arguments swapped.
#guard extFns (geofNs ++ "sfContains") [wktLit sq, wktLit "POINT(2 2)"]
       == some (.bool true)

-- Equality across decimal scales.
#guard extFns (geofNs ++ "sfEquals") [wktLit "POINT(0.10 0.20)", wktLit "POINT(0.1 0.2)"]
       == some (.bool true)

-- MULTI-GEOMETRIES decompose: a point within ANY member of a
-- multipolygon is within the whole.
#guard extFns (geofNs ++ "sfWithin")
         [wktLit "POINT(2 2)",
          wktLit "MULTIPOLYGON(((0 0,4 0,4 4,0 4,0 0)),((9 9,10 9,10 10,9 9)))"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfIntersects")
         [wktLit "POINT(9.5 9.2)",
          wktLit "MULTIPOLYGON(((0 0,4 0,4 4,0 4,0 0)),((9 9,10 9,10 10,9 9)))"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfDisjoint")
         [wktLit "POINT(100 100)",
          wktLit "MULTIPOLYGON(((0 0,4 0,4 4,0 4,0 0)),((9 9,10 9,10 10,9 9)))"]
       == some (.bool true)

-- A GEOMETRYCOLLECTION decomposes too, including nested ones.
#guard extFns (geofNs ++ "sfIntersects")
         [wktLit "POINT(1 1)",
          wktLit "GEOMETRYCOLLECTION(POINT(5 5),GEOMETRYCOLLECTION(LINESTRING(0 0,2 2)))"]
       == some (.bool true)

-- Linestrings: crossing paths intersect; a point on an endpoint
-- TOUCHES an open curve but a mid-path point does not.
#guard extFns (geofNs ++ "sfIntersects")
         [wktLit "LINESTRING(0 0,2 2)", wktLit "LINESTRING(0 2,2 0)"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfTouches")
         [wktLit "POINT(0 0)", wktLit "LINESTRING(0 0,2 2)"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfTouches")
         [wktLit "POINT(1 1)", wktLit "LINESTRING(0 0,2 2)"]
       == some (.bool false)

-- Reversal-invariant linestring equality (open curves).
#guard extFns (geofNs ++ "sfEquals")
         [wktLit "LINESTRING(0 0,1 1,2 2)", wktLit "LINESTRING(2 2,1 1,0 0)"]
       == some (.bool true)

-- REFUSAL becomes a type error, never a guess: a closed loop written
-- from a different starting vertex is a case the algorithm declines
-- to decide, so the evaluator must raise rather than answer false.
#guard (extFns (geofNs ++ "sfEquals")
         [wktLit "LINESTRING(0 0,1 0,1 1,0 0)",
          wktLit "LINESTRING(1 0,1 1,0 0,1 0)"]).isNone

-- TYPE ERRORS, not `false`: an unknown function, a non-WKT argument,
-- wrong arity, and a cross-CRS pair must all return `none` so the
-- evaluator raises §17.6 rather than silently answering.
#guard (extFns (geofNs ++ "sfNoSuchThing") [wktLit "POINT(0 0)", wktLit sq]).isNone
#guard (extFns "http://example.org/other" [wktLit "POINT(0 0)", wktLit sq]).isNone
#guard (extFns (geofNs ++ "sfWithin") [.num 1, wktLit sq]).isNone
#guard (extFns (geofNs ++ "sfWithin") [wktLit "POINT(0 0)"]).isNone
#guard (extFns (geofNs ++ "sfWithin")
          [wktLit "<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(2 2)",
           wktLit sq]).isNone
-- Unparseable lexical form is a type error too.
#guard (extFns (geofNs ++ "sfWithin") [wktLit "POINT(oops)", wktLit sq]).isNone

end L4Factoidal.Geo
