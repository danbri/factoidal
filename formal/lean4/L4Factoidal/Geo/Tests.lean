/-
L4Factoidal.Geo.Tests — build-time checks for the GeoSPARQL port.
Every `#guard` evaluates during elaboration, so a wrong answer is a
build error.
-/
import L4Factoidal.Geo.Topology

namespace L4Factoidal.Geo

-- Exact decimals: scale differences must not change a value.
#guard Scaled.eq ⟨1, 1⟩ ⟨10, 2⟩          -- 0.1 = 0.10
#guard Scaled.eq (Scaled.add ⟨1, 1⟩ ⟨2, 1⟩) ⟨3, 1⟩   -- 0.1 + 0.2 = 0.3
#guard !(Scaled.eq ⟨1, 1⟩ ⟨2, 1⟩)
#guard Scaled.lt ⟨-5, 0⟩ ⟨1, 3⟩          -- -5 < 0.001
#guard Scaled.eq (Scaled.mul ⟨5, 1⟩ ⟨2, 1⟩) ⟨1, 1⟩   -- 0.5 * 0.2 = 0.1 exactly
#guard Scaled.eq (Scaled.sub ⟨3, 1⟩ ⟨1, 1⟩) ⟨2, 1⟩

-- The float trap this port exists to avoid: 0.1 + 0.2 = 0.3 exactly.
#guard Scaled.cmp (Scaled.add ⟨1, 1⟩ ⟨2, 1⟩) ⟨3, 1⟩ == 0

-- Points compare across scales.
#guard Point.eq ⟨⟨1, 1⟩, ⟨2, 1⟩⟩ ⟨⟨10, 2⟩, ⟨20, 2⟩⟩

-- Bounding boxes.
private def p00 : Point := ⟨Scaled.ofInt 0, Scaled.ofInt 0⟩
private def p11 : Point := ⟨Scaled.ofInt 1, Scaled.ofInt 1⟩
private def p22 : Point := ⟨Scaled.ofInt 2, Scaled.ofInt 2⟩

#guard (BBox.ofPoints [p00, p11]).isSome
#guard (BBox.ofPoints []).isNone
#guard match BBox.ofPoints [p00, p11] with
       | some b => Scaled.eq b.xmin (Scaled.ofInt 0) && Scaled.eq b.xmax (Scaled.ofInt 1)
       | none => false

-- An empty geometry has no box; a collection takes the union.
#guard (BBox.ofGeometry (.empty .point)).isNone
#guard match BBox.ofGeometry (.geometryCollection [.point p00, .point p22]) with
       | some b => Scaled.eq b.xmax (Scaled.ofInt 2) && Scaled.eq b.ymin (Scaled.ofInt 0)
       | none => false

-- Overlap is inclusive: boxes sharing only an edge DO overlap, per
-- Simple Features (a shared boundary point is an intersection).
#guard BBox.overlaps (BBox.ofPoint p00) (BBox.ofPoint p00)
#guard BBox.overlaps ⟨Scaled.ofInt 0, Scaled.ofInt 0, Scaled.ofInt 1, Scaled.ofInt 1⟩
                     ⟨Scaled.ofInt 1, Scaled.ofInt 1, Scaled.ofInt 2, Scaled.ofInt 2⟩
#guard !(BBox.overlaps ⟨Scaled.ofInt 0, Scaled.ofInt 0, Scaled.ofInt 1, Scaled.ofInt 1⟩
                       ⟨Scaled.ofInt 2, Scaled.ofInt 2, Scaled.ofInt 3, Scaled.ofInt 3⟩)

-- CRS matching: absent means CRS84, so it matches the explicit IRI.
#guard sameCrs none none
#guard sameCrs none (some crs84)
#guard !(sameCrs (some "http://example.org/crs/other") none)

-- Orientation: counter-clockwise, clockwise, collinear.
#guard orientSign p00 (Point.mk (Scaled.ofInt 1) (Scaled.ofInt 0))
                      (Point.mk (Scaled.ofInt 0) (Scaled.ofInt 1)) == 1
#guard orientSign p00 (Point.mk (Scaled.ofInt 0) (Scaled.ofInt 1))
                      (Point.mk (Scaled.ofInt 1) (Scaled.ofInt 0)) == -1
#guard orientSign p00 p11 p22 == 0

-- A point on a segment, and one off it.
#guard pointOnSegment p11 p00 p22
#guard !(pointOnSegment (Point.mk (Scaled.ofInt 1) (Scaled.ofInt 2)) p00 p22)

-- Crossing segments; touching-at-endpoint counts (Simple Features).
#guard segmentsIntersect p00 p22 (Point.mk (Scaled.ofInt 0) (Scaled.ofInt 2))
                                 (Point.mk (Scaled.ofInt 2) (Scaled.ofInt 0))
#guard segmentsIntersect p00 p11 p11 p22
#guard !(segmentsIntersect p00 (Point.mk (Scaled.ofInt 1) (Scaled.ofInt 0))
                           (Point.mk (Scaled.ofInt 0) (Scaled.ofInt 1))
                           (Point.mk (Scaled.ofInt 1) (Scaled.ofInt 1)))

-- The unit square, closed (WKT rings repeat the first point).
private def unitSquare : Ring :=
  [p00, Point.mk (Scaled.ofInt 2) (Scaled.ofInt 0), p22,
   Point.mk (Scaled.ofInt 0) (Scaled.ofInt 2), p00]

#guard ringClass p11 unitSquare == PtClass.interior
#guard ringClass p00 unitSquare == PtClass.boundary
#guard ringClass (Point.mk (Scaled.ofInt 3) (Scaled.ofInt 3)) unitSquare == PtClass.exterior

-- Simple Features: a boundary point INTERSECTS but is not WITHIN.
private def square : Polygon := ⟨unitSquare, []⟩
#guard pointIntersectsPolygon p00 square
#guard !(pointWithinPolygon p00 square)
#guard pointTouchesPolygon p00 square
#guard pointWithinPolygon p11 square

-- A hole punches the interior back out to exterior.
private def holed : Polygon :=
  ⟨[Point.mk (Scaled.ofInt 0) (Scaled.ofInt 0),
    Point.mk (Scaled.ofInt 6) (Scaled.ofInt 0),
    Point.mk (Scaled.ofInt 6) (Scaled.ofInt 6),
    Point.mk (Scaled.ofInt 0) (Scaled.ofInt 6),
    Point.mk (Scaled.ofInt 0) (Scaled.ofInt 0)],
   [[Point.mk (Scaled.ofInt 2) (Scaled.ofInt 2),
     Point.mk (Scaled.ofInt 4) (Scaled.ofInt 2),
     Point.mk (Scaled.ofInt 4) (Scaled.ofInt 4),
     Point.mk (Scaled.ofInt 2) (Scaled.ofInt 4),
     Point.mk (Scaled.ofInt 2) (Scaled.ofInt 2)]]⟩
#guard polygonClass (Point.mk (Scaled.ofInt 3) (Scaled.ofInt 3)) holed == PtClass.exterior
#guard polygonClass (Point.mk (Scaled.ofInt 1) (Scaled.ofInt 1)) holed == PtClass.interior
#guard polygonClass (Point.mk (Scaled.ofInt 2) (Scaled.ofInt 3)) holed == PtClass.boundary

-- Exactness: a point on a segment at a fine scale is still ON it,
-- where floating point would drift.
#guard pointOnSegment ⟨⟨1, 1⟩, ⟨1, 1⟩⟩ p00 p22

-- The pre-filter soundness theorem and its ordering foundation.
#print axioms Scaled.le_trans
#print axioms disjoint_bbox_no_shared_point
#print axioms contains_ofPoint
#print axioms overlaps_self

end L4Factoidal.Geo
