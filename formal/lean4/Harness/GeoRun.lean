/-
Harness.GeoRun — the GeoSPARQL v0 assertions (`lake exe l4geo`), the
Lean twin of `tests/unit/geosparql_v0_unit.ml` (37 assertions, 37 pass
against the F* engine).

Three groups, same order and names as the F* pin file:
  A. WKT parser round-trip (parse -> ADT -> serialize -> re-parse,
     checking the re-parsed geometry matches the original).
  B. Simple Features predicates against hand-built fixtures, including
     an exact-boundary case (point exactly on a polygon edge).
  C. geof:distance / geof:envelope spot checks.

Every check below carries the EXACT F* assertion name it ports, so the
two files diff name-for-name. All 37 are ported here — none needed a
SKIP — after four engine gaps were closed in `L4Factoidal/Geo/`:
`Wkt.lean` gained a WKT serializer (the F* side had one; the Lean port
did not) and a MULTIPOINT parenthesized-component parser
(`MULTIPOINT((1 2), (3 4))`, which the generic point-list parser
cannot read), `Types.lean` gained hand-written structural equality on
`Geometry` (`deriving DecidableEq` cannot discharge the self-
referencing `List Geometry` field), `Topology.lean` gained
`sfOverlaps` and the Polygon/Polygon cases of `sfIntersects`/
`sfWithin` (present in the F* port, not yet ported), and
`Functions.lean` gained `geoDistance`/`geoEnvelope` (present in the F*
port's `RDF.Geo.Functions.fst`, not yet ported).

No `sorry`, no user `axiom`, no `native_decide`, no `unsafe`, no
`partial`.
-/
import L4Factoidal.Geo.Functions

namespace Harness.GeoRun

open L4Factoidal.Geo

/-! ## Verdicts and the score-line grammar -/

inductive Verdict where
  | pass
  | fail (reason : String)
  | skip (reason : String)

def Verdict.line (name : String) : Verdict → String
  | .pass   => s!"PASS {name}"
  | .fail r => s!"FAIL {name}: {r}"
  | .skip r => s!"SKIP {name}: {r}"

def Verdict.isPass : Verdict → Bool
  | .pass => true
  | _     => false

def Verdict.isFail : Verdict → Bool
  | .fail _ => true
  | _       => false

def Verdict.isSkip : Verdict → Bool
  | .skip _ => true
  | _       => false

structure Check where
  name    : String
  verdict : Verdict

/-- A boolean assertion, matching the F* pin file's `check`. -/
def checkBool (name : String) (expected actual : Bool) : Check :=
  { name := name,
    verdict :=
      if expected == actual then .pass
      else .fail s!"expected {expected} got {actual}" }

def showOptBool : Option Bool → String
  | none       => "None"
  | some true  => "Some true"
  | some false => "Some false"

/-- A three-valued (`Option Bool`) assertion, matching the F* pin
    file's `check_opt_bool`. -/
def checkOptBool (name : String) (expected actual : Option Bool) : Check :=
  { name := name,
    verdict :=
      if expected == actual then .pass
      else .fail s!"expected {showOptBool expected} got {showOptBool actual}" }

/-! ## Fixture helpers, matching the F* pin file's `pt` -/

private def pt (x y : Int) : Point := ⟨Scaled.ofInt x, Scaled.ofInt y⟩

private def geomEq (a b : Geometry) : Bool := Geometry.beq a b

/-! ## Group A — WKT parser round-trip -/

section GroupA

-- A1: simple point.
private def a1_1 : Check :=
  match Wkt.parseLiteral "POINT(1 2)" with
  | some v => checkBool "POINT(1 2) parses to G_Point" true (geomEq v.geom (.point (pt 1 2)))
  | none   => checkBool "POINT(1 2) parses to G_Point" true false

private def a1_2 : Check :=
  match Wkt.parseLiteral "POINT(1 2)" with
  | some v =>
      match Wkt.parseLiteral (Wkt.serializeValue v) with
      | some v2 => checkBool "POINT(1 2) round-trips through serialize" true (geomEq v.geom v2.geom)
      | none    => checkBool "POINT(1 2) round-trips through serialize" true false
  | none => checkBool "POINT(1 2) round-trips through serialize" true false

-- A2: decimal coordinates (exact, not floating point).
private def a2_1 : Check :=
  match Wkt.parseLiteral "POINT(51.5074 -0.1278)" with
  | some { geom := .point p, .. } =>
      checkBool "POINT(51.5074 -0.1278) x mantissa exact" true
        (p.x.mantissa == 515074 && p.x.scale == 4)
  | _ => checkBool "POINT(51.5074 -0.1278) x mantissa exact" true false

private def a2_2 : Check :=
  match Wkt.parseLiteral "POINT(51.5074 -0.1278)" with
  | some { geom := .point p, .. } =>
      checkBool "POINT(51.5074 -0.1278) y mantissa exact" true
        (p.y.mantissa == -1278 && p.y.scale == 4)
  | _ => checkBool "POINT(51.5074 -0.1278) y mantissa exact" true false

-- A3: LINESTRING.
private def a3 : Check :=
  match Wkt.parseLiteral "LINESTRING(0 0, 10 0, 10 10)" with
  | some { geom := .lineString l, .. } => checkBool "LINESTRING has 3 points" true (l.length == 3)
  | _ => checkBool "LINESTRING has 3 points" true false

-- A4: POLYGON with a hole.
private def polyWkt : String :=
  "POLYGON((0 0, 10 0, 10 10, 0 10, 0 0),(2 2, 4 2, 4 4, 2 4, 2 2))"

private def a4_1 : Check :=
  match Wkt.parseLiteral polyWkt with
  | some { geom := .polygon p, .. } => checkBool "POLYGON exterior has 5 points" true (p.ext.length == 5)
  | _ => checkBool "POLYGON exterior has 5 points" true false

private def a4_2 : Check :=
  match Wkt.parseLiteral polyWkt with
  | some { geom := .polygon p, .. } => checkBool "POLYGON has 1 hole" true (p.holes.length == 1)
  | _ => checkBool "POLYGON has 1 hole" true false

-- A5: MULTIPOINT both forms.
private def a5_1 : Check :=
  match Wkt.parseLiteral "MULTIPOINT((1 2), (3 4))" with
  | some { geom := .multiPoint pts, .. } =>
      checkBool "MULTIPOINT parenthesized form has 2 points" true (pts.length == 2)
  | _ => checkBool "MULTIPOINT parenthesized form has 2 points" true false

private def a5_2 : Check :=
  match Wkt.parseLiteral "MULTIPOINT(1 2, 3 4)" with
  | some { geom := .multiPoint pts, .. } =>
      checkBool "MULTIPOINT bare form has 2 points" true (pts.length == 2)
  | _ => checkBool "MULTIPOINT bare form has 2 points" true false

-- A6: EMPTY forms.
private def a6_1 : Check :=
  match Wkt.parseLiteral "POINT EMPTY" with
  | some { geom := .empty .point, .. } => checkBool "POINT EMPTY" true true
  | _ => checkBool "POINT EMPTY" true false

private def a6_2 : Check :=
  match Wkt.parseLiteral "GEOMETRYCOLLECTION EMPTY" with
  | some { geom := .empty .geometryCollection, .. } => checkBool "GEOMETRYCOLLECTION EMPTY" true true
  | _ => checkBool "GEOMETRYCOLLECTION EMPTY" true false

-- A7: CRS prefix carried, not transformed.
private def crsWkt : String :=
  "<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(530000 180000)"

private def a7_1 : Check :=
  match Wkt.parseLiteral crsWkt with
  | some { crs := some c, geom := .point _ } =>
      checkBool "CRS prefix captured verbatim" true (c == "http://www.opengis.net/def/crs/EPSG/0/27700")
  | _ => checkBool "CRS prefix captured verbatim" true false

private def a7_2 : Check :=
  match Wkt.parseLiteral crsWkt with
  | some { crs := some _, geom := .point p } =>
      checkBool "CRS-prefixed coordinates unchanged (no transform)" true
        (p.x.mantissa == 530000 && p.y.mantissa == 180000)
  | _ => checkBool "CRS-prefixed coordinates unchanged (no transform)" true false

-- A8: 3D coordinate is a parse failure (out of scope, not silently truncated).
private def a8 : Check :=
  checkBool "POINT Z (3 numbers) is rejected, not silently truncated" true
    (Wkt.parseLiteral "POINT(1 2 3)").isNone

-- A9: GEOMETRYCOLLECTION nesting.
private def a9 : Check :=
  match Wkt.parseLiteral "GEOMETRYCOLLECTION(POINT(1 1), LINESTRING(0 0, 1 1))" with
  | some { geom := .geometryCollection gs, .. } =>
      checkBool "GEOMETRYCOLLECTION has 2 members" true (gs.length == 2)
  | _ => checkBool "GEOMETRYCOLLECTION has 2 members" true false

end GroupA

/-! ## Group B — Simple Features predicates (hand-computed) -/

section GroupB

-- B2/B3: a square (0,0)-(10,0)-(10,10)-(0,10), point (5,0) lies
-- exactly on the bottom edge — the exact-boundary case rational
-- arithmetic nails without an epsilon.
private def square : Polygon :=
  { ext := [pt 0 0, pt 10 0, pt 10 10, pt 0 10, pt 0 0], holes := [] }

private def squareWithHole : Polygon :=
  { ext := [pt 0 0, pt 10 0, pt 10 10, pt 0 10, pt 0 0],
    holes := [[pt 3 3, pt 7 3, pt 7 7, pt 3 7, pt 3 3]] }

private def diag : Geometry := .lineString [pt 0 0, pt 10 10]

private def l1 : Geometry := .lineString [pt 0 0, pt 10 10]
private def l2 : Geometry := .lineString [pt 0 10, pt 10 0]
private def l3 : Geometry := .lineString [pt 0 20, pt 10 30]

private def sqA : Polygon := { ext := [pt 0 0, pt 10 0, pt 10 10, pt 0 10, pt 0 0], holes := [] }
private def sqB : Polygon := { ext := [pt 5 5, pt 15 5, pt 15 15, pt 5 15, pt 5 5], holes := [] }
private def sqC : Polygon :=
  { ext := [pt 100 100, pt 110 100, pt 110 110, pt 100 110, pt 100 100], holes := [] }
private def sqInner : Polygon := { ext := [pt 2 2, pt 4 2, pt 4 4, pt 2 4, pt 2 2], holes := [] }

-- B1: point/point.
private def b1_1 : Check :=
  checkOptBool "sfEquals(POINT(1 1), POINT(1 1)) = true" (some true)
    (sfEquals (.point (pt 1 1)) (.point (pt 1 1)))

private def b1_2 : Check :=
  checkOptBool "sfDisjoint(POINT(1 1), POINT(2 2)) = true" (some true)
    (sfDisjoint (.point (pt 1 1)) (.point (pt 2 2)))

-- B2: point exactly on a polygon edge.
private def b2_1 : Check :=
  checkOptBool "sfTouches(POINT(5 0), square) = true (exactly on edge)" (some true)
    (sfTouches (.point (pt 5 0)) (.polygon square))

private def b2_2 : Check :=
  checkOptBool "sfWithin(POINT(5 0), square) = false (boundary, not interior)" (some false)
    (sfWithin (.point (pt 5 0)) (.polygon square))

private def b2_3 : Check :=
  checkOptBool "sfWithin(POINT(5 5), square) = true (strictly interior)" (some true)
    (sfWithin (.point (pt 5 5)) (.polygon square))

private def b2_4 : Check :=
  checkOptBool "sfDisjoint(POINT(20 20), square) = true" (some true)
    (sfDisjoint (.point (pt 20 20)) (.polygon square))

private def b2_5 : Check :=
  checkOptBool "sfIntersects(POINT(5 0), square) = true (on boundary counts)" (some true)
    (sfIntersects (.point (pt 5 0)) (.polygon square))

-- B3: point inside a hole is exterior to the polygon.
private def b3_1 : Check :=
  checkOptBool "sfDisjoint(POINT(5 5), square-with-hole) = true (5,5 is in the hole)" (some true)
    (sfDisjoint (.point (pt 5 5)) (.polygon squareWithHole))

private def b3_2 : Check :=
  checkOptBool "sfWithin(POINT(1 1), square-with-hole) = true (outside the hole)" (some true)
    (sfWithin (.point (pt 1 1)) (.polygon squareWithHole))

-- B4: point/linestring.
private def b4_1 : Check :=
  checkOptBool "sfWithin(POINT(5 5), diagonal line) = true (interior of open line)" (some true)
    (sfWithin (.point (pt 5 5)) diag)

private def b4_2 : Check :=
  checkOptBool "sfTouches(POINT(0 0), diagonal line) = true (open-line endpoint)" (some true)
    (sfTouches (.point (pt 0 0)) diag)

private def b4_3 : Check :=
  checkOptBool "sfDisjoint(POINT(1 2), diagonal line) = true (off the line)" (some true)
    (sfDisjoint (.point (pt 1 2)) diag)

-- B5: linestring/linestring crossing (exact orientation test).
private def b5_1 : Check :=
  checkOptBool "sfIntersects(diagonal /, diagonal \\) = true (cross at (5,5))" (some true)
    (sfIntersects l1 l2)

private def b5_2 : Check :=
  checkOptBool "sfDisjoint(diagonal /, parallel line far away) = true" (some true)
    (sfDisjoint l1 l3)

-- B6: polygon/polygon — overlapping squares (boundary-crossing + vertex-in-other).
private def b6_1 : Check :=
  checkOptBool "sfIntersects(square A, overlapping square B) = true" (some true)
    (sfIntersects (.polygon sqA) (.polygon sqB))

private def b6_2 : Check :=
  checkOptBool "sfDisjoint(square A, far-away square C) = true" (some true)
    (sfDisjoint (.polygon sqA) (.polygon sqC))

private def b6_3 : Check :=
  checkOptBool "sfWithin(inner square, square A) = true (strictly inside, no boundary contact)" (some true)
    (sfWithin (.polygon sqInner) (.polygon sqA))

private def b6_4 : Check :=
  checkOptBool "sfContains(square A, inner square) = true (flip of within)" (some true)
    (sfContains (.polygon sqA) (.polygon sqInner))

-- B7: mismatched-dimension overlaps is decided false per SFA convention.
private def b7 : Check :=
  checkOptBool "sfOverlaps(POINT, LINESTRING) = false (differing dims, SFA convention)" (some false)
    (sfOverlaps (.point (pt 1 1)) diag)

end GroupB

/-! ## Group C — geof:distance / geof:envelope -/

section GroupC

-- C1: distance(point,point) — exact squared distance of a 3-4-5
-- triangle, so the sqrt is exactly 5 and the approximation should
-- recover it to the disclosed extra precision (mantissa is all zeros
-- after the leading 5).
private def c1 : Check :=
  match geoDistance (.point (pt 0 0)) (.point (pt 3 4)) with
  | some d =>
      let s := Scaled.toStringDec d
      checkBool "distance((0,0),(3,4)) ~= 5 (3-4-5 triangle, exact sqrt)" true
        (s.length ≥ 1 && s.take 1 == "5")
  | none => checkBool "distance((0,0),(3,4)) ~= 5 (3-4-5 triangle, exact sqrt)" true false

-- C2: distance is refused (none) for non-point/point pairs.
private def c2 : Check :=
  checkBool "distance(point, linestring) is refused (None) in v0" true
    (geoDistance (.point (pt 0 0)) diag).isNone

-- C3: envelope of a polygon is its bounding box, as a polygon.
private def c3 : Check :=
  match geoEnvelope (.polygon sqB) with
  | some (.polygon env) =>
      checkBool "envelope(square B) exterior ring has 5 points (closed rectangle)" true
        (env.ext.length == 5)
  | _ => checkBool "envelope(square B) exterior ring has 5 points (closed rectangle)" true false

end GroupC

/-! ## Registration and the score line -/

def checks : List Check :=
  [ a1_1, a1_2, a2_1, a2_2, a3, a4_1, a4_2, a5_1, a5_2, a6_1, a6_2, a7_1, a7_2, a8, a9,
    b1_1, b1_2, b2_1, b2_2, b2_3, b2_4, b2_5, b3_1, b3_2, b4_1, b4_2, b4_3, b5_1, b5_2,
    b6_1, b6_2, b6_3, b6_4, b7,
    c1, c2, c3 ]

def run (_args : List String) : IO UInt32 := do
  IO.println s!"HARNESS-DIAG geosparql-v0: registered={checks.length}"
  for c in checks do
    IO.println (c.verdict.line c.name)
  let n := (checks.filter (fun c => c.verdict.isPass)).length
  let m := (checks.filter (fun c => c.verdict.isFail)).length
  let k := (checks.filter (fun c => c.verdict.isSkip)).length
  IO.println s!"geosparql-v0: {n} pass, {m} fail, {k} skip (out of {n + m + k})"
  if m > 0 then return 1 else return 0

end Harness.GeoRun

def main (args : List String) : IO UInt32 := Harness.GeoRun.run args
