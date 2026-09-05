/-
L4Factoidal.Geo.BBox — axis-aligned bounding boxes, ported from
`formal/fstar/RDF.Geo.BBox.fst`.

Bounding boxes are the cheap filter in front of the topology
predicates: if two boxes are disjoint, the geometries cannot
intersect, so the expensive test is skipped. That soundness direction
is proved below (`disjoint_bbox_no_shared_point`) rather than assumed
— an unsound filter would silently drop query answers.

An EMPTY geometry has no box, hence `Option`.
-/
import L4Factoidal.Geo.Order

namespace L4Factoidal.Geo

/-- An axis-aligned bounding box. -/
structure BBox where
  xmin : Scaled
  ymin : Scaled
  xmax : Scaled
  ymax : Scaled
deriving Repr, DecidableEq, Inhabited

def BBox.ofPoint (p : Point) : BBox := ⟨p.x, p.y, p.x, p.y⟩

def BBox.union (a b : BBox) : BBox :=
  ⟨Scaled.min a.xmin b.xmin, Scaled.min a.ymin b.ymin,
   Scaled.max a.xmax b.xmax, Scaled.max a.ymax b.ymax⟩

def BBox.unionOpt : Option BBox → Option BBox → Option BBox
  | none,   b      => b
  | a,      none   => a
  | some a, some b => some (a.union b)

def BBox.ofPoints (ps : List Point) : Option BBox :=
  ps.foldl (fun acc p => BBox.unionOpt acc (some (BBox.ofPoint p))) none

def BBox.ofRings (rs : List Ring) : Option BBox :=
  rs.foldl (fun acc r => BBox.unionOpt acc (BBox.ofPoints r)) none

def BBox.ofPolygon (p : Polygon) : Option BBox := BBox.ofPoints p.ext

def BBox.ofPolygons (ps : List Polygon) : Option BBox :=
  ps.foldl (fun acc p => BBox.unionOpt acc (BBox.ofPolygon p)) none

mutual

/-- Bounding box of a geometry. Recursive through collections. -/
def BBox.ofGeometry : Geometry → Option BBox
  | .point p           => some (BBox.ofPoint p)
  | .lineString ps     => BBox.ofPoints ps
  | .polygon poly      => BBox.ofPolygon poly
  | .multiPoint ps     => BBox.ofPoints ps
  | .multiLineString ls => ls.foldl (fun acc l => BBox.unionOpt acc (BBox.ofPoints l)) none
  | .multiPolygon ps   => BBox.ofPolygons ps
  | .geometryCollection gs => BBox.ofGeometries gs
  | .empty _           => none

/-- Bounding box of a list of geometries. Mutual with `ofGeometry` so
    the structural recursion through `geometryCollection` is visible
    to the termination checker (a `foldl` over the sublist hides it). -/
def BBox.ofGeometries : List Geometry → Option BBox
  | []      => none
  | g :: gs => BBox.unionOpt (BBox.ofGeometry g) (BBox.ofGeometries gs)
end

/-- A point lies inside a box (inclusive on all four edges). -/
def BBox.contains (b : BBox) (p : Point) : Bool :=
  Scaled.le b.xmin p.x && Scaled.le p.x b.xmax &&
  Scaled.le b.ymin p.y && Scaled.le p.y b.ymax

/-- Two boxes overlap (inclusive: touching edges count as overlap,
    matching the Simple Features convention that a shared boundary
    point is an intersection). -/
def BBox.overlaps (a b : BBox) : Bool :=
  Scaled.le a.xmin b.xmax && Scaled.le b.xmin a.xmax &&
  Scaled.le a.ymin b.ymax && Scaled.le b.ymin a.ymax

/-- A point always lies in its own bounding box. -/
theorem contains_ofPoint (p : Point) : (BBox.ofPoint p).contains p = true := by
  simp [BBox.ofPoint, BBox.contains, Scaled.le, Scaled.cmp, Scaled.align]

/-- A box always overlaps itself (it is non-empty by construction). -/
theorem overlaps_self (p : Point) :
    (BBox.ofPoint p).overlaps (BBox.ofPoint p) = true := by
  simp [BBox.ofPoint, BBox.overlaps, Scaled.le, Scaled.cmp, Scaled.align]

/-- SOUNDNESS OF THE PRE-FILTER. If two boxes do not overlap, no
    point lies in both — so a disjoint-box pair may safely skip the
    topology test. Without this, a disjoint-box shortcut could
    silently drop query answers.

    The argument is four applications of `Scaled.le_trans`: a point
    inside both boxes chains each box's min under the other box's max,
    which is exactly the four conjuncts of `overlaps`. -/
theorem disjoint_bbox_no_shared_point (a b : BBox) (p : Point)
    (h : a.overlaps b = false) : ¬ (a.contains p = true ∧ b.contains p = true) := by
  intro ⟨ha, hb⟩
  simp only [BBox.contains, Bool.and_eq_true] at ha hb
  obtain ⟨⟨⟨hax1, hax2⟩, hay1⟩, hay2⟩ := ha
  obtain ⟨⟨⟨hbx1, hbx2⟩, hby1⟩, hby2⟩ := hb
  have h1 : Scaled.le a.xmin b.xmax = true := Scaled.le_trans hax1 hbx2
  have h2 : Scaled.le b.xmin a.xmax = true := Scaled.le_trans hbx1 hax2
  have h3 : Scaled.le a.ymin b.ymax = true := Scaled.le_trans hay1 hby2
  have h4 : Scaled.le b.ymin a.ymax = true := Scaled.le_trans hby1 hay2
  rw [BBox.overlaps, h1, h2, h3, h4] at h
  simp at h

end L4Factoidal.Geo
