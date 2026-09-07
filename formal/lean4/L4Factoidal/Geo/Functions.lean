/-
L4Factoidal.Geo.Functions — the GeoSPARQL SPARQL extension functions,
ported from `formal/fstar/RDF.Geo.Functions.fst`.

GeoSPARQL 1.1 §9 defines its topology predicates as SPARQL functions
named by IRI (`geof:sfIntersects`, …). SPARQL 1.1 §17.6 already gives
those an extension point, and the Lean evaluator exposes it as an
ordinary field: `EvalEnv.ext : String → List EvalResult → Option
EvalResult`. So this module needs NO change to the evaluator — it
builds a function table that a caller installs:

    { EvalEnv.empty with ext := Geo.extFns }

That is the purity doctrine paying off. The F* side reaches the same
functions through a registry the evaluator consults; here the table is
an argument, so nothing global is mutated and the evaluator stays a
total function of explicit inputs.

CRS RULE, inherited: v0 performs NO coordinate transforms. Two
literals in different CRSes produce a type error rather than a
silently wrong answer computed as if the coordinates were comparable.
-/
import L4Factoidal.Geo.Wkt
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.Geo

open L4Factoidal.SPARQL

/-- The `geof:` function namespace. -/
def geofNs : String := "http://www.opengis.net/def/function/geosparql/"

/-- Pull a WKT value out of an argument: it must be a literal typed
    `geo:wktLiteral` whose lexical form parses. Anything else is a
    type error, per §17.6. -/
def wktArg : EvalResult → Option WktValue
  | .term (.literal l) =>
      if l.val.datatype.val == wktLiteralIri then Wkt.parseLiteral l.val.lexicalForm
      else none
  | _ => none

/-- Apply a general geometry predicate to two parsed literals with
    the CRS guard. A REFUSAL from the predicate (`none`) becomes a
    §17.6 type error, exactly like a bad argument — the evaluator must
    never see a guessed boolean. -/
def geoPredicate (f : Geometry → Geometry → Option Bool)
    (a b : EvalResult) : Option EvalResult := do
  let va ← wktArg a
  let vb ← wktArg b
  if !(sameCrs va.crs vb.crs) then none
  else (f va.geom vb.geom).map EvalResult.bool

/-- The function table. Install as `EvalEnv.ext`. Unregistered IRIs
    fall through to `none`, which the evaluator turns into the §17.6
    type error — never into `false`, which would silently change
    query answers. -/
def extFns (iri : String) (args : List EvalResult) : Option EvalResult :=
  if !(iri.startsWith geofNs) then none
  else
    let name := iri.drop geofNs.length
    match args with
    | [a, b] =>
        if name == "sfEquals" then geoPredicate sfEquals a b
        else if name == "sfWithin" then geoPredicate sfWithin a b
        else if name == "sfContains" then geoPredicate sfContains a b
        else if name == "sfIntersects" then geoPredicate sfIntersects a b
        else if name == "sfDisjoint" then geoPredicate sfDisjoint a b
        else if name == "sfTouches" then geoPredicate sfTouches a b
        else none
    | _ => none

/-! ## `geof:distance` and `geof:envelope`

Ported from `RDF.Geo.Functions.fst`'s `geo_distance`/`geo_envelope`.
Both are "cheap" geometry functions the evaluator can also install
through `extFns` above, but the pin file exercises them directly, so
they are plain functions rather than registry entries. -/

/-- `floor(sqrt n)` by binary search, fuel-bounded by `n + 2` (a
    generous, easy-to-see bound: the search halves its range each
    round, so it converges in `O(log n)` rounds well inside that fuel
    via the early `lo ≥ hi` exit). Structural on the fuel argument, so
    no `partial` is needed — the same shape as `Scaled.pow10` above. -/
def isqrtSearch : Nat → Nat → Nat → Nat → Nat
  | _,        lo, _,  0        => lo
  | n,        lo, hi, fuel + 1 =>
      if lo ≥ hi then lo
      else
        let mid := (lo + hi + 1) / 2
        if mid * mid ≤ n then isqrtSearch n mid hi fuel
        else isqrtSearch n lo (mid - 1) fuel

def isqrt (n : Nat) : Nat :=
  if n == 0 then 0 else isqrtSearch n 0 (n + 1) (n + 2)

/-- Extra decimal digits of precision `geoSqrtApprox` discloses beyond
    the input's own scale. -/
def geoDistancePrecisionExtraDigits : Nat := 9

def geoDistanceSquared (p1 p2 : Point) : Scaled :=
  let dx := Scaled.sub p1.x p2.x
  let dy := Scaled.sub p1.y p2.y
  Scaled.add (Scaled.mul dx dx) (Scaled.mul dy dy)

/-- `floor(sqrt v)` of a nonnegative `Scaled`, to
    `geoDistancePrecisionExtraDigits` extra decimal digits beyond the
    input's own scale. This is the ONE inexact step anywhere in the
    GeoSPARQL v0 surface — an under-approximation (never rounded or
    over-approximated), computed by the pure integer `isqrt` above, so
    the disclosed inexactness is exactly one documented
    `floor(sqrt(...))` call, not a black box. -/
def geoSqrtApprox (v : Scaled) : Scaled :=
  let s := v.scale
  let outScale := s + geoDistancePrecisionExtraDigits
  let shift : Nat := outScale + outScale - s
  let m : Nat := (if v.mantissa < 0 then 0 else v.mantissa).toNat
  let arg : Nat := m * Scaled.pow10 shift
  { mantissa := (isqrt arg : Int), scale := outScale }

/-- `geof:distance(g1,g2)`: the exact squared distance and a disclosed
    approximate square root for point/point; refused (`none`) for
    every other geometry-kind pair — v0 scope limits the exact-
    arithmetic distance function to point/point. -/
def geoDistance (g1 g2 : Geometry) : Option Scaled :=
  match g1, g2 with
  | .point p1, .point p2 => some (geoSqrtApprox (geoDistanceSquared p1 p2))
  | _, _ => none

/-- The bounding box as a closed rectangular exterior ring, no holes. -/
def bboxToPolygon (b : BBox) : Polygon :=
  { ext := [ ⟨b.xmin, b.ymin⟩, ⟨b.xmax, b.ymin⟩, ⟨b.xmax, b.ymax⟩,
             ⟨b.xmin, b.ymax⟩, ⟨b.xmin, b.ymin⟩ ],
    holes := [] }

/-- `geof:envelope(g)`: the geometry's bounding box as a rectangular
    polygon — exact, no approximation involved at all. -/
def geoEnvelope (g : Geometry) : Option Geometry :=
  match BBox.ofGeometry g with
  | none   => none
  | some b => some (.polygon (bboxToPolygon b))

end L4Factoidal.Geo
