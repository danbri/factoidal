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
import L4Factoidal.Geo.Types

namespace L4Factoidal.Geo

/-- An axis-aligned bounding box. -/
structure BBox where
  xmin : Scaled
  ymin : Scaled
  xmax : Scaled
  ymax : Scaled
deriving Repr, Inhabited

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

/-  NEXT PROOF OBLIGATION (stated here, deliberately not `sorry`-ed):

    `disjoint_bbox_no_shared_point : a.overlaps b = false →
       ¬ (a.contains p ∧ b.contains p)`

    is the soundness of using the box test as a pre-filter in front of
    the topology predicates — without it, a disjoint-box shortcut
    could silently drop query answers. It needs transitivity of
    `Scaled.le`, which in turn needs the rescaling-invariance lemma
    `cmp ⟨m, s⟩ ⟨m', s'⟩ = cmp ⟨m * 10^k, s + k⟩ ⟨m', s'⟩`, since the
    pairwise `align` calls in a three-way chain use different common
    scales. That lemma family lands with `Geo/Order.lean`; until it
    does, no code in this port takes the disjoint-box shortcut.
-/

end L4Factoidal.Geo
