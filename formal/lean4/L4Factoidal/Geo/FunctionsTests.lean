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
