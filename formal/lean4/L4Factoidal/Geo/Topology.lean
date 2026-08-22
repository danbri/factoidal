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

/-! ## Curve and area helpers -/

/-- Is `[a,b]` a sub-segment of `[c,d]`? Both endpoints collinear with
    `cd` and inside its box. -/
def segmentSubsegOf (a b c d : Point) : Bool :=
  orientSign c d a == 0 && orientSign c d b == 0 &&
  inSegBBox a c d && inSegBBox b c d

def segmentSubsegOfAny (a b : Point) : List Point → Bool
  | []          => false
  | [_]         => false
  | c :: d :: rest => segmentSubsegOf a b c d || segmentSubsegOfAny a b (d :: rest)

/-- Every edge of `inner` lies inside a SINGLE edge of `outer`.
    Sufficient but NOT complete for point-set containment: it misses
    an inner edge covered by two or more collinear outer edges across
    a bend. That incompleteness is why the caller below returns
    `Option Bool` rather than `Bool`. -/
def pathWithinPathByEdges : List Point → List Point → Bool
  | [], _  => true
  | [_], _ => true
  | a :: b :: rest, outer =>
      segmentSubsegOfAny a b outer && pathWithinPathByEdges (b :: rest) outer

def allPointsOnPath : List Point → List Point → Bool
  | [], _       => true
  | p :: rest, outer => pointOnPath p outer && allPointsOnPath rest outer

/-- THREE-VALUED line-within-line. `some true` when the per-edge check
    succeeds; `some false` only when some vertex of `inner` is not
    even on `outer` (certain non-containment); otherwise `none` —
    REFUSED rather than guessed. Refusing is the whole point: a
    `false` here would be indistinguishable from a real negative
    answer to a query. -/
def pathWithinPath (inner outer : List Point) : Option Bool :=
  if pathWithinPathByEdges inner outer then some true
  else if !(allPointsOnPath inner outer) then some false
  else none

def listPointEq : List Point → List Point → Bool
  | [], []           => true
  | x :: xs, y :: ys => Point.eq x y && listPointEq xs ys
  | _, _             => false

/-- Is the path a closed loop? -/
def isClosedLine (l : List Point) : Bool :=
  match l, l.getLast? with
  | p :: _, some q => Point.eq p q && l.length ≥ 2
  | _, _ => false

/-- THREE-VALUED linestring equality. Reversal-invariant equality is a
    COMPLETE invariant for OPEN curves — their two endpoints are
    geometrically distinguished. For CLOSED loops of equal length a
    sequence mismatch does NOT prove inequality (the same loop can be
    listed from any starting vertex), so that case is refused. -/
def linestringEquals (l1 l2 : List Point) : Option Bool :=
  if listPointEq l1 l2 || listPointEq l1 l2.reverse then some true
  else if isClosedLine l1 && isClosedLine l2 && l1.length == l2.length then none
  else some false

def allPointsEqTo (pts : List Point) (p : Point) : Bool :=
  pts.all (fun q => Point.eq q p)

/-- Does a linestring meet a polygon? Either a vertex is non-exterior
    or an edge crosses the boundary. -/
def lineIntersectsPolygon (l : List Point) (poly : Polygon) : Bool :=
  l.any (fun p => polygonClass p poly != .exterior) ||
  segmentCrossesRings l (poly.ext :: poly.holes)
where
  segmentCrossesRings : List Point → List Ring → Bool
  | l, rings => rings.any (fun r => pathCrossesPath l r)

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

/-! ## Base-kind predicate dispatch

Point / LineString / Polygon / Empty only. `Multi*` and
`GeometryCollection` are decomposed before reaching these, exactly as
the F* module does. Every result is `Option Bool`: `none` means the
ported algorithm REFUSES to decide, never that the answer is false. -/

/-- `sfEquals` over the base kinds. -/
def sfEqualsBase : Geometry → Geometry → Option Bool
  | .empty k1, .empty k2 => some (k1 == k2)
  | .empty _, _ => some false
  | _, .empty _ => some false
  | .point p1, .point p2 => some (Point.eq p1 p2)
  | .point _, _ => some false
  | _, .point _ => some false
  | .lineString l1, .lineString l2 => linestringEquals l1 l2
  | .lineString _, _ => some false
  | _, .lineString _ => some false
  | _, _ => none

/-- `sfIntersects` over the base kinds. -/
def sfIntersectsBase : Geometry → Geometry → Option Bool
  | .empty _, _ => some false
  | _, .empty _ => some false
  | .point p1, .point p2 => some (Point.eq p1 p2)
  | .point p, .lineString l => some (pointOnPath p l)
  | .lineString l, .point p => some (pointOnPath p l)
  | .point p, .polygon poly => some (polygonClass p poly != .exterior)
  | .polygon poly, .point p => some (polygonClass p poly != .exterior)
  | .lineString l1, .lineString l2 => some (pathCrossesPath l1 l2)
  | .lineString l, .polygon poly => some (lineIntersectsPolygon l poly)
  | .polygon poly, .lineString l => some (lineIntersectsPolygon l poly)
  | _, _ => none

/-- `sfWithin` over the base kinds. An empty geometry is within
    anything; nothing non-empty is within an empty one. -/
def sfWithinBase : Geometry → Geometry → Option Bool
  | .empty _, _ => some true
  | _, .empty _ => some false
  | .point p1, .point p2 => some (Point.eq p1 p2)
  | .point p, .lineString l =>
      if !(pointOnPath p l) then some false
      else if isClosedLine l then some true
      else match l, l.getLast? with
        | first :: _, some last => some (!(Point.eq p first) && !(Point.eq p last))
        | _, _ => some true
  | .lineString l, .point p => some (allPointsEqTo l p)
  | .point p, .polygon poly => some (polygonClass p poly == .interior)
  | .polygon _, .point _ => some false
  | .lineString l1, .lineString l2 => pathWithinPath l1 l2
  | _, _ => none

/-- `sfTouches` over the base kinds: the geometries meet, but only at
    boundaries — their interiors are disjoint. Two equal points share
    an interior, so points never touch points. A point touches a
    linestring exactly at an endpoint of an OPEN curve. Pairs outside
    the ported fragment are REFUSED, not guessed. -/
def sfTouchesBase : Geometry → Geometry → Option Bool
  | .empty _, _ => some false
  | _, .empty _ => some false
  | .point _, .point _ => some false
  | .point p, .polygon poly => some (polygonClass p poly == .boundary)
  | .polygon poly, .point p => some (polygonClass p poly == .boundary)
  | .point p, .lineString l =>
      if isClosedLine l then some false
      else match l, l.getLast? with
        | first :: _, some last => some (Point.eq p first || Point.eq p last)
        | _, _ => some false
  | .lineString l, .point p =>
      if isClosedLine l then some false
      else match l, l.getLast? with
        | first :: _, some last => some (Point.eq p first || Point.eq p last)
        | _, _ => some false
  | _, _ => none

/-! ## Multi* / GeometryCollection decomposition

`Multi*` and `GeometryCollection` are decomposed into base components
before the base predicates see them. The combinators are three-valued
(Kleene): a REFUSAL anywhere blocks a definite `false` but never
blocks a definite `true`, because one witness settles an existential
regardless of what the refused components would have said. -/

/-- Three-valued OR: `some true` if any component says true, `some
    false` only if EVERY component definitely says false, else
    refused. -/
def combineExists (rs : List (Option Bool)) : Option Bool :=
  if rs.any (· == some true) then some true
  else if rs.all (· == some false) then some false
  else none

/-- Three-valued AND: `some false` if any component definitely says
    false, `some true` only if every component definitely says true,
    else refused. -/
def combineForall (rs : List (Option Bool)) : Option Bool :=
  if rs.any (· == some false) then some false
  else if rs.all (· == some true) then some true
  else none

/-- The base geometries a value decomposes into. `GeometryCollection`
    nests, so this recurses; `Multi*` do not. -/
partial def components : Geometry → List Geometry
  | .multiPoint ps      => ps.map .point
  | .multiLineString ls => ls.map .lineString
  | .multiPolygon ps    => ps.map .polygon
  | .geometryCollection gs => gs.flatMap components
  | g => [g]

/-- Is this a compound value needing decomposition? -/
def isCompound : Geometry → Bool
  | .multiPoint _ | .multiLineString _ | .multiPolygon _
  | .geometryCollection _ => true
  | _ => false

/-- `sfIntersects`: two geometries meet if ANY component pair meets. -/
def sfIntersects (g1 g2 : Geometry) : Option Bool :=
  if !(isCompound g1) && !(isCompound g2) then sfIntersectsBase g1 g2
  else
    combineExists
      ((components g1).flatMap (fun a => (components g2).map (sfIntersectsBase a)))

/-- `sfDisjoint` is the negation of `sfIntersects`, propagating the
    refusal rather than turning it into an answer. -/
def sfDisjoint (g1 g2 : Geometry) : Option Bool :=
  (sfIntersects g1 g2).map (!·)

/-- `sfWithin`: EVERY component of the left must be within SOME
    component of the right. -/
def sfWithin (g1 g2 : Geometry) : Option Bool :=
  if !(isCompound g1) && !(isCompound g2) then sfWithinBase g1 g2
  else
    combineForall
      ((components g1).map (fun a =>
        combineExists ((components g2).map (sfWithinBase a))))

/-- `sfContains` is `sfWithin` with the arguments swapped. -/
def sfContains (g1 g2 : Geometry) : Option Bool := sfWithin g2 g1

/-- `sfTouches` over full geometries. -/
def sfTouches (g1 g2 : Geometry) : Option Bool :=
  if !(isCompound g1) && !(isCompound g2) then sfTouchesBase g1 g2
  else
    combineExists
      ((components g1).flatMap (fun a => (components g2).map (sfTouchesBase a)))

/-- `sfEquals`: mutual containment for compounds; the base test
    otherwise. -/
def sfEquals (g1 g2 : Geometry) : Option Bool :=
  if !(isCompound g1) && !(isCompound g2) then sfEqualsBase g1 g2
  else match sfWithin g1 g2, sfWithin g2 g1 with
    | some true, some true   => some true
    | some false, _          => some false
    | _, some false          => some false
    | _, _                   => none

end L4Factoidal.Geo
