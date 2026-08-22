/-
L4Factoidal.Geo.Types — the GeoSPARQL geometry model, ported from
`formal/fstar/RDF.Geo.Types.fst`.

Spec: GeoSPARQL 1.1 (https://docs.ogc.org/is/22-047r1/22-047r1.html),
geometry literals in WKT (Simple Features, ISO 19125-1).

Coordinates are EXACT decimals, not floats: a `Scaled` is a mantissa
and a decimal scale, so `0.1` is `⟨1, 1⟩` and never a binary
approximation. Topology predicates compare coordinates for equality,
and float equality would make `sfEquals` depend on parse rounding —
the same reason the F* side chose `geo_scaled`.

CRS handling matches the F* port: `none` means the default CRS
(CRS84 / EPSG:4326 long-lat, the WKT convention for un-prefixed
literals); a `some crs` literal carries its CRS opaquely. No CRS
TRANSFORMS are performed — cross-CRS predicate calls are refused at
the dispatch site rather than silently assuming identity.
-/

namespace L4Factoidal.Geo

/-- An exact decimal: `mantissa * 10^(-scale)`. -/
structure Scaled where
  mantissa : Int
  scale    : Nat
deriving Repr, DecidableEq, Inhabited

namespace Scaled

/-- `10 ^ n`, always positive. -/
def pow10 : Nat → Nat
  | 0     => 1
  | n + 1 => 10 * pow10 n

theorem pow10_pos : ∀ n, 0 < pow10 n
  | 0     => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (by decide) (pow10_pos n)

def ofInt (i : Int) : Scaled := ⟨i, 0⟩
def zero : Scaled := ofInt 0

/-- Bring two decimals to a common scale, returning the two rescaled
    mantissas and that scale. -/
def align (a b : Scaled) : Int × Int × Nat :=
  let s := max a.scale b.scale
  (a.mantissa * (pow10 (s - a.scale) : Int),
   b.mantissa * (pow10 (s - b.scale) : Int), s)

def add (a b : Scaled) : Scaled :=
  let (x, y, s) := align a b; ⟨x + y, s⟩

def neg (a : Scaled) : Scaled := ⟨-a.mantissa, a.scale⟩

def sub (a b : Scaled) : Scaled :=
  let (x, y, s) := align a b; ⟨x - y, s⟩

def mul (a b : Scaled) : Scaled :=
  ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩

/-- Three-way comparison at a common scale. -/
def cmp (a b : Scaled) : Int :=
  let (x, y, _) := align a b
  if x < y then -1 else if x = y then 0 else 1

def eq (a b : Scaled) : Bool := cmp a b == 0
def lt (a b : Scaled) : Bool := cmp a b < 0
def le (a b : Scaled) : Bool := cmp a b ≤ 0
def gt (a b : Scaled) : Bool := cmp a b > 0
def ge (a b : Scaled) : Bool := cmp a b ≥ 0

def min (a b : Scaled) : Scaled := if le a b then a else b
def max (a b : Scaled) : Scaled := if ge a b then a else b
def abs (a : Scaled) : Scaled := if lt a zero then neg a else a

end Scaled

/-- A planar point. `x` is longitude/easting, `y` latitude/northing —
    WKT axis order, which for CRS84 is long-lat. -/
structure Point where
  x : Scaled
  y : Scaled
deriving Repr, DecidableEq, Inhabited

/-- Point equality is coordinate equality at a common scale, so
    `0.10` and `0.1` denote the same point. -/
def Point.eq (p q : Point) : Bool :=
  Scaled.eq p.x q.x && Scaled.eq p.y q.y

/-- A ring or open path. Closed rings repeat the first point as the
    last, per the WKT convention; the type does not enforce it. -/
abbrev Ring := List Point

structure Polygon where
  ext   : Ring
  holes : List Ring
deriving Repr, DecidableEq, Inhabited

inductive Kind where
  | point | lineString | polygon
  | multiPoint | multiLineString | multiPolygon
  | geometryCollection
deriving Repr, DecidableEq, Inhabited

inductive Geometry where
  | point              (p : Point)
  | lineString         (ps : List Point)
  | polygon            (poly : Polygon)
  | multiPoint         (ps : List Point)
  | multiLineString    (ls : List (List Point))
  | multiPolygon       (ps : List Polygon)
  | geometryCollection (gs : List Geometry)
  | empty              (k : Kind)
deriving Repr, Inhabited

def Geometry.kind : Geometry → Kind
  | .point _              => .point
  | .lineString _         => .lineString
  | .polygon _            => .polygon
  | .multiPoint _         => .multiPoint
  | .multiLineString _    => .multiLineString
  | .multiPolygon _       => .multiPolygon
  | .geometryCollection _ => .geometryCollection
  | .empty k              => k

/-- A parsed `geo:wktLiteral`: the geometry plus its optional CRS IRI.
    `none` = default CRS84. -/
structure WktValue where
  crs  : Option String
  geom : Geometry
deriving Repr, Inhabited

/-- The GeoSPARQL namespace. -/
def geoNs : String := "http://www.opengis.net/ont/geosparql#"

/-- The `geo:wktLiteral` datatype IRI. -/
def wktLiteralIri : String := geoNs ++ "wktLiteral"

/-- The default CRS URI for un-prefixed WKT literals (CRS84). -/
def crs84 : String := "http://www.opengis.net/def/crs/OGC/1.3/CRS84"

/-- Two literals are comparable only within one CRS: `none` means
    CRS84, so it matches an explicit CRS84 IRI. -/
def sameCrs (a b : Option String) : Bool :=
  match a, b with
  | none, none => true
  | none, some c | some c, none => c == crs84
  | some c, some d => c == d

end L4Factoidal.Geo
