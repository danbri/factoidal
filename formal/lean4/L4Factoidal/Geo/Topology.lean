/-
L4Factoidal.Geo.Topology — the exact geometric kernel, ported from
`formal/fstar/RDF.Geo.Topology.fst`.

Everything here is DIVISION-FREE and float-free. The orientation
determinant decides left/right/collinear with one subtraction of two
products, so segment intersection and point-in-polygon are exact over
`Scaled`. Computing an actual intersection coordinate would need
division and would leave the exact-decimal world; the F* port avoids
it for the same reason and this port follows.

Simple Features convention followed throughout: a shared boundary
point IS an intersection, so all the tests below are on CLOSED
geometries.

CALLER-SIDE ASSUMPTION, unchanged from the F* module: ray-casting
point-in-polygon (`ringClass`) is meaningful only for a SIMPLE,
non-self-intersecting ring. Segment intersection itself needs no such
assumption — it is exact for any two segments.
-/
import L4Factoidal.Geo.BBox

namespace L4Factoidal.Geo

/-- The orientation determinant of the triangle `a b c`:
    `(b-a) × (c-a)`. Positive = counter-clockwise, zero = collinear,
    negative = clockwise. -/
def orient (a b c : Point) : Scaled :=
  Scaled.sub
    (Scaled.mul (Scaled.sub b.x a.x) (Scaled.sub c.y a.y))
    (Scaled.mul (Scaled.sub b.y a.y) (Scaled.sub c.x a.x))

def orientSign (a b c : Point) : Int :=
  let o := orient a b c
  if Scaled.lt o Scaled.zero then -1 else if Scaled.eq o Scaled.zero then 0 else 1

/-- Is `p` inside the closed bounding box of segment `[a,b]`?
    Necessary but not sufficient for "on segment"; combined with
    collinearity it becomes exact, which is the only way it is used. -/
def inSegBBox (p a b : Point) : Bool :=
  Scaled.le (Scaled.min a.x b.x) p.x && Scaled.le p.x (Scaled.max a.x b.x) &&
  Scaled.le (Scaled.min a.y b.y) p.y && Scaled.le p.y (Scaled.max a.y b.y)

/-- Exact point-on-closed-segment test. -/
def pointOnSegment (p a b : Point) : Bool :=
  orientSign a b p == 0 && inSegBBox p a b

/-- Exact segment intersection (proper or improper), by the standard
    four-orientation algorithm. Decidable for ANY two segments. -/
def segmentsIntersect (a b c d : Point) : Bool :=
  let o1 := orientSign a b c
  let o2 := orientSign a b d
  let o3 := orientSign c d a
  let o4 := orientSign c d b
  if o1 != o2 && o3 != o4 then true
  else
    (o1 == 0 && inSegBBox c a b) || (o2 == 0 && inSegBBox d a b) ||
    (o3 == 0 && inSegBBox a c d) || (o4 == 0 && inSegBBox b c d)

/-- Is `p` on any edge of the path? -/
def pointOnPath (p : Point) : List Point → Bool
  | []          => false
  | [_]         => false
  | a :: b :: rest => pointOnSegment p a b || pointOnPath p (b :: rest)

/-- Does segment `[a,b]` meet any edge of the path? -/
def segmentCrossesPath (a b : Point) : List Point → Bool
  | []          => false
  | [_]         => false
  | c :: d :: rest => segmentsIntersect a b c d || segmentCrossesPath a b (d :: rest)

/-- Do two paths meet anywhere? -/
def pathCrossesPath : List Point → List Point → Bool
  | [], _           => false
  | [_], _          => false
  | a :: b :: rest, other =>
      segmentCrossesPath a b other || pathCrossesPath (b :: rest) other

/-- Crossing count for the ray from `p` going in +x. Uses the
    orientation sign rather than an intersection coordinate, so no
    division is needed: an edge straddling the horizontal line
    `y = p.y` crosses to the right of `p` exactly when it runs upward
    with `orient > 0` or downward with `orient < 0`. -/
def rayCrossCount (p : Point) : List Point → Nat
  | []          => 0
  | [_]         => 0
  | a :: b :: rest =>
      let straddles := Scaled.gt a.y p.y != Scaled.gt b.y p.y
      let crosses :=
        if !straddles then false
        else
          let o := orientSign a b p
          (Scaled.lt a.y b.y && o > 0) || (Scaled.gt a.y b.y && o < 0)
      (if crosses then 1 else 0) + rayCrossCount p (b :: rest)

/-- Where a point sits relative to a geometry. -/
inductive PtClass where
  | interior | boundary | exterior
deriving Repr, DecidableEq

/-- Point against a single ring: on the boundary, or inside by odd
    crossing parity. Assumes a simple ring (see the module header). -/
def ringClass (p : Point) (r : Ring) : PtClass :=
  if pointOnPath p r then .boundary
  else if rayCrossCount p r % 2 == 1 then .interior
  else .exterior

def pointInAnyHoleInterior (p : Point) : List Ring → Bool
  | []      => false
  | h :: hs => (ringClass p h == .interior) || pointInAnyHoleInterior p hs

def pointOnAnyRing (p : Point) : List Ring → Bool
  | []      => false
  | r :: rs => pointOnPath p r || pointOnAnyRing p rs

/-- Point against a polygon with holes: boundary of the exterior ring
    or of any hole is boundary; inside the exterior but inside a hole
    is exterior. -/
def polygonClass (p : Point) (poly : Polygon) : PtClass :=
  if pointOnPath p poly.ext || pointOnAnyRing p poly.holes then .boundary
  else match ringClass p poly.ext with
    | .interior => if pointInAnyHoleInterior p poly.holes then .exterior else .interior
    | c         => c

/-- `sfEquals` on points: coordinate equality across scales. -/
def pointEquals (p q : Point) : Bool := Point.eq p q

/-- `sfDisjoint` for point vs polygon. -/
def pointDisjointPolygon (p : Point) (poly : Polygon) : Bool :=
  polygonClass p poly == .exterior

/-- `sfIntersects` for point vs polygon — the negation, per Simple
    Features (boundary counts as intersecting). -/
def pointIntersectsPolygon (p : Point) (poly : Polygon) : Bool :=
  !(pointDisjointPolygon p poly)

/-- `sfWithin` for point vs polygon: interior only. A point on the
    boundary is NOT within, per Simple Features. -/
def pointWithinPolygon (p : Point) (poly : Polygon) : Bool :=
  polygonClass p poly == .interior

/-- `sfTouches` for point vs polygon: boundary only. -/
def pointTouchesPolygon (p : Point) (poly : Polygon) : Bool :=
  polygonClass p poly == .boundary

end L4Factoidal.Geo
