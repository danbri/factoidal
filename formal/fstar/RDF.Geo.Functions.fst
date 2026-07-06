module RDF.Geo.Functions

open FStar.String
open FStar.List.Tot
open FStar.Mul
open RDF.Geo.Types
open RDF.Geo.BBox

(* ================================================================ *)
(* GeoSPARQL v0 "cheap" geometry functions: geof:distance and         *)
(* geof:envelope. Pure F*, no assume vals, no host CG library.        *)
(*                                                                    *)
(* geof:distance (point/point only in v0 — see module header of      *)
(* RDF.Geo.Topology.fst for the same "decided vs refused" discipline) *)
(* computes an EXACT rational squared distance, then takes a          *)
(* disclosed *approximate* square root to produce an xsd:double        *)
(* lexical value. This is the ONE inexact step anywhere in the         *)
(* GeoSPARQL v0 surface (per the plan's option-A recommendation) —      *)
(* the square root itself is computed by a pure-F* integer-square-      *)
(* root (`isqrt`, a standard binary-search algorithm, not an `assume    *)
(* val`), scaled to 9 extra decimal digits beyond the input's own       *)
(* precision and then FLOORED (an under-approximation, never rounded    *)
(* or over-approximated) — so the disclosed inexactness is exactly one   *)
(* documented floor(sqrt(...)) call, not a black box.                    *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(* Pure-F* integer square root (floor), binary search.                *)
(* ---------------------------------------------------------------- *)

let rec isqrt_search (n : nat) (lo hi : nat) (fuel : nat) : Tot nat (decreases fuel) =
  if fuel = 0 then lo
  else if lo >= hi then lo
  else
    let mid = (lo + hi + 1) / 2 in
    if mid * mid <= n then isqrt_search n mid hi (fuel - 1)
    else isqrt_search n lo (mid - 1) (fuel - 1)

// floor(sqrt(n)). fuel = n+2 is a generous, easy-to-verify bound (binary
// search converges in O(log n) actual iterations via the `lo >= hi`
// early exit — the oversized nominal fuel costs nothing at runtime).
let isqrt (n : nat) : nat =
  if n = 0 then 0 else isqrt_search n 0 (n + 1) (n + 2)

(* ---------------------------------------------------------------- *)
(* geof:distance — point/point exact squared distance, then a         *)
(* disclosed approximate sqrt to a geo_scaled (9 extra decimal          *)
(* digits of precision beyond the input coordinates' own scale).       *)
(* ---------------------------------------------------------------- *)

let geo_distance_precision_extra_digits : nat = 9

let geo_distance_squared (p1 p2 : geo_point) : geo_scaled =
  let dx = gs_sub p1.gp_x p2.gp_x in
  let dy = gs_sub p1.gp_y p2.gp_y in
  gs_add (gs_mul dx dx) (gs_mul dy dy)

// floor(sqrt(value)) of a nonnegative geo_scaled, to
// `geo_distance_precision_extra_digits` extra decimal digits beyond
// the input's own scale — see module header for why this is exact
// integer arithmetic (isqrt) all the way down to the single disclosed
// floor(sqrt(...)) step.
let geo_sqrt_approx (v : geo_scaled) : geo_scaled =
  let s = v.gs_scale in
  let out_scale = s + geo_distance_precision_extra_digits in
  let shift : nat = out_scale + out_scale - s in  // = s + 2*extra_digits, always >= 0
  let m = (if v.gs_mantissa < 0 then 0 else v.gs_mantissa) in
  let arg = m * geo_pow10 shift in
  { gs_mantissa = isqrt arg; gs_scale = out_scale }

// geof:distance(g1,g2): Some (approximate xsd:double lexical form) for
// point/point; None (refused, not the "decided vs refused" table's
// intersects/within kind of refusal but a genuine "not implemented
// for this geometry-kind pair in v0" — the plan's scope explicitly
// limits the exact-arithmetic distance function to point/point) for
// every other kind combination.
let geo_distance (g1 g2 : geo_geometry) : option geo_scaled =
  match g1, g2 with
  | G_Point p1, G_Point p2 -> Some (geo_sqrt_approx (geo_distance_squared p1 p2))
  | _, _ -> None

(* ---------------------------------------------------------------- *)
(* geof:envelope — the geometry's bounding box as a rectangular       *)
(* polygon (exact; no approximation involved at all).                 *)
(* ---------------------------------------------------------------- *)

let geo_envelope (g : geo_geometry) : option geo_geometry =
  match RDF.Geo.BBox.geo_bbox_of_geometry g with
  | None -> None
  | Some b -> Some (G_Polygon (geo_bbox_to_polygon b))
