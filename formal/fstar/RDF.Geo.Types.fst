module RDF.Geo.Types

open FStar.String
open FStar.List.Tot
open FStar.Mul
open RDF.Term

(* ================================================================ *)
(* GeoSPARQL v0 — geometry ADT + exact-rational coordinate type      *)
(*                                                                    *)
(* Pure F*, option-A of docs/designissues/2026-05-07-                *)
(* geosparql-fstar-investigation.md: coordinates are EXACT rationals,*)
(* no floating point, no host CG library, no new assume vals.        *)
(*                                                                    *)
(* Coordinates are represented as `geo_scaled` — mantissa / 10^scale,*)
(* the SAME idiom SPARQL11.Algebra's parse_to_scaled/scaled_cmp and  *)
(* XPath.Eval's xpath_number already use for exact decimal values —  *)
(* rather than introducing a second (numerator, denominator) fraction*)
(* representation. Every WKT coordinate literal is a decimal string, *)
(* hence exactly representable this way, and +, -, * on two such      *)
(* values stay exact and closed (scale adds under multiplication,     *)
(* aligns under add/sub). Division is never needed by any predicate   *)
(* in this v0 slice; the one inexact step in the whole GeoSPARQL v0   *)
(* surface is geof:distance's final square root, documented at its    *)
(* definition site in RDF.Geo.Functions.fst, not here.                *)
(*                                                                    *)
(* This module does NOT import SPARQL11.Algebra (parsers/geo types   *)
(* sit below the algebra layer in the dependency graph — mirroring   *)
(* Parser.NTriples/Parser.Turtle, which depend on RDF.Graph.Executable*)
(* but not on SPARQL11.Algebra). SPARQL11.Algebra depends on this     *)
(* module, not the other way around.                                 *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(* Exact scaled-decimal rationals                                    *)
(* ---------------------------------------------------------------- *)

// value = gs_mantissa / 10^gs_scale
type geo_scaled = { gs_mantissa : int; gs_scale : nat }

let rec geo_pow10 (n : nat) : Tot (r:nat{r > 0}) (decreases n) =
  if n = 0 then 1 else 10 * geo_pow10 (n - 1)

let gs_of_int (i : int) : geo_scaled = { gs_mantissa = i; gs_scale = 0 }
let gs_zero : geo_scaled = gs_of_int 0

// Align two scaled values to a common scale, returning the two
// aligned mantissas plus the common scale used.
let gs_align (a b : geo_scaled) : (int & int & nat) =
  if a.gs_scale = b.gs_scale then (a.gs_mantissa, b.gs_mantissa, a.gs_scale)
  else if a.gs_scale < b.gs_scale then
    (a.gs_mantissa * geo_pow10 (b.gs_scale - a.gs_scale), b.gs_mantissa, b.gs_scale)
  else
    (a.gs_mantissa, b.gs_mantissa * geo_pow10 (a.gs_scale - b.gs_scale), a.gs_scale)

let gs_add (a b : geo_scaled) : geo_scaled =
  let (am, bm, sc) = gs_align a b in { gs_mantissa = am + bm; gs_scale = sc }

let gs_sub (a b : geo_scaled) : geo_scaled =
  let (am, bm, sc) = gs_align a b in { gs_mantissa = am - bm; gs_scale = sc }

let gs_neg (a : geo_scaled) : geo_scaled = { gs_mantissa = (0 - a.gs_mantissa); gs_scale = a.gs_scale }

let gs_mul (a b : geo_scaled) : geo_scaled =
  { gs_mantissa = a.gs_mantissa * b.gs_mantissa; gs_scale = a.gs_scale + b.gs_scale }

// Three-way compare: -1 / 0 / 1
let gs_cmp (a b : geo_scaled) : int =
  let (am, bm, _) = gs_align a b in
  if am < bm then -1 else if am > bm then 1 else 0

let gs_eq (a b : geo_scaled) : bool = gs_cmp a b = 0
let gs_lt (a b : geo_scaled) : bool = gs_cmp a b < 0
let gs_le (a b : geo_scaled) : bool = gs_cmp a b <= 0
let gs_gt (a b : geo_scaled) : bool = gs_cmp a b > 0
let gs_ge (a b : geo_scaled) : bool = gs_cmp a b >= 0

let gs_sign (a : geo_scaled) : int =
  if a.gs_mantissa < 0 then -1 else if a.gs_mantissa > 0 then 1 else 0

let gs_min (a b : geo_scaled) : geo_scaled = if gs_le a b then a else b
let gs_max (a b : geo_scaled) : geo_scaled = if gs_ge a b then a else b

let gs_abs (a : geo_scaled) : geo_scaled =
  if a.gs_mantissa < 0 then gs_neg a else a

// Format a scaled value back to a plain decimal string, e.g.
// {gs_mantissa=515074; gs_scale=4} -> "51.5074", {gs_mantissa=3; gs_scale=0} -> "3".
let rec geo_zeros (n : nat) : Tot string (decreases n) =
  if n = 0 then "" else "0" ^ geo_zeros (n - 1)

let geo_pad_left_zeros (s : string) (target : nat) : string =
  let len = String.length s in
  if len >= target then s else geo_zeros (target - len) ^ s

let gs_to_string (a : geo_scaled) : string =
  if a.gs_scale = 0 then string_of_int a.gs_mantissa
  else
    let is_neg = a.gs_mantissa < 0 in
    let av = (if is_neg then 0 - a.gs_mantissa else a.gs_mantissa) in
    let p = geo_pow10 a.gs_scale in
    let int_part = av / p in
    let frac_part = av - (int_part * p) in
    let frac_str = geo_pad_left_zeros (string_of_int frac_part) a.gs_scale in
    (if is_neg then "-" else "") ^ string_of_int int_part ^ "." ^ frac_str

(* ---------------------------------------------------------------- *)
(* Geometry ADT — 2D only (v0 scope excludes Z/M coordinates and     *)
(* CRS transforms per the plan's "out of scope" section).            *)
(* ---------------------------------------------------------------- *)

type geo_point = { gp_x : geo_scaled; gp_y : geo_scaled }

// A ring or open path is just a list of points in order (closed rings
// repeat the first point as the last, per WKT convention; not
// enforced by the type — see geo_wf_ring below).
type geo_ring = list geo_point

type geo_polygon = { gpoly_ext : geo_ring; gpoly_holes : list geo_ring }

type geo_kind =
  | GK_Point | GK_LineString | GK_Polygon
  | GK_MultiPoint | GK_MultiLineString | GK_MultiPolygon
  | GK_GeometryCollection

type geo_geometry =
  | G_Point              : geo_point -> geo_geometry
  | G_LineString         : list geo_point -> geo_geometry
  | G_Polygon            : geo_polygon -> geo_geometry
  | G_MultiPoint         : list geo_point -> geo_geometry
  | G_MultiLineString    : list (list geo_point) -> geo_geometry
  | G_MultiPolygon       : list geo_polygon -> geo_geometry
  | G_GeometryCollection : list geo_geometry -> geo_geometry
  | G_Empty              : geo_kind -> geo_geometry

// A parsed WKT literal: the geometry plus its (optional) CRS IRI.
// `None` means "default CRS" (CRS84 / EPSG:4326 long-lat, as per the
// GeoSPARQL/WKT convention for un-prefixed literals). A `Some crs`
// literal carries the CRS opaquely: v0 does NOT transform between
// CRSes (per the plan's explicit out-of-scope), so cross-CRS
// predicate calls are refused (documented at the predicate dispatch
// site in RDF.Geo.Topology.fst) rather than silently assuming
// identity.
type geo_wkt_value = { gw_crs : option string; gw_geom : geo_geometry }

let geo_kind_of (g : geo_geometry) : geo_kind =
  match g with
  | G_Point _ -> GK_Point
  | G_LineString _ -> GK_LineString
  | G_Polygon _ -> GK_Polygon
  | G_MultiPoint _ -> GK_MultiPoint
  | G_MultiLineString _ -> GK_MultiLineString
  | G_MultiPolygon _ -> GK_MultiPolygon
  | G_GeometryCollection _ -> GK_GeometryCollection
  | G_Empty k -> k

(* ---------------------------------------------------------------- *)
(* geo:wktLiteral datatype IRI + CRS84 default                       *)
(* ---------------------------------------------------------------- *)

let geo_ns : string = "http://www.opengis.net/ont/geosparql#"

let geo_wktLiteral : wf_iri =
  assert_norm (is_iri "http://www.opengis.net/ont/geosparql#wktLiteral");
  "http://www.opengis.net/ont/geosparql#wktLiteral"

// Not itself a term-position IRI (it's a function-namespace prefix,
// concatenated with a local name before ever being used as a term),
// so it stays a plain string rather than `wf_iri`.
let geof_ns : string = "http://www.opengis.net/def/function/geosparql/"

let geo_crs84 : wf_iri =
  assert_norm (is_iri "http://www.opengis.net/def/crs/OGC/1.3/CRS84");
  "http://www.opengis.net/def/crs/OGC/1.3/CRS84"

(* ---------------------------------------------------------------- *)
(* Well-formedness predicates                                        *)
(*                                                                    *)
(* A ring is well-formed when it has at least 4 points and is closed  *)
(* (first point equals last point). A polygon is well-formed when     *)
(* its exterior ring and every hole ring are well-formed. These are   *)
(* the minimal OGC well-formedness checks v0 relies on before running *)
(* any topological predicate on a polygon — self-intersection is NOT  *)
(* checked (the "simple, non-self-intersecting" assumption documented *)
(* throughout RDF.Geo.Topology.fst is a caller obligation, not         *)
(* verified here).                                                    *)
(* ---------------------------------------------------------------- *)

let geo_point_eq (a b : geo_point) : bool =
  gs_eq a.gp_x b.gp_x && gs_eq a.gp_y b.gp_y

let rec geo_last_point (pts : list geo_point) : Tot (option geo_point) (decreases pts) =
  match pts with
  | [] -> None
  | [p] -> Some p
  | _ :: rest -> geo_last_point rest

let geo_wf_ring (r : geo_ring) : bool =
  if List.Tot.length r < 4 then false
  else
    match r, geo_last_point r with
    | first :: _, Some last -> geo_point_eq first last
    | _, _ -> false

let geo_wf_linestring (l : list geo_point) : bool = List.Tot.length l >= 2

let geo_wf_polygon (p : geo_polygon) : bool =
  geo_wf_ring p.gpoly_ext && List.Tot.for_all geo_wf_ring p.gpoly_holes

// A linestring is "closed" (a loop) when it has >=1 point and its
// first point equals its last (per OGC: the boundary of a closed
// curve is empty; the boundary of an open curve is its two endpoints).
let geo_is_closed_line (l : list geo_point) : bool =
  match l, geo_last_point l with
  | first :: _, Some last -> geo_point_eq first last
  | _, _ -> false

let rec geo_wf_geometry (g : geo_geometry) : Tot bool (decreases g) =
  match g with
  | G_Point _ -> true
  | G_LineString l -> geo_wf_linestring l
  | G_Polygon p -> geo_wf_polygon p
  | G_MultiPoint _ -> true
  | G_MultiLineString ls -> List.Tot.for_all geo_wf_linestring ls
  | G_MultiPolygon ps -> List.Tot.for_all geo_wf_polygon ps
  | G_GeometryCollection gs -> geo_wf_geometry_list gs
  | G_Empty _ -> true
and geo_wf_geometry_list (gs : list geo_geometry) : Tot bool (decreases gs) =
  match gs with
  | [] -> true
  | g :: rest -> geo_wf_geometry g && geo_wf_geometry_list rest

(* ---------------------------------------------------------------- *)
(* Generic option-bool combinators used throughout the predicate      *)
(* layer for decomposing Multi*/GeometryCollection geometries into    *)
(* their components: "exists a true" / "all true", each correctly     *)
(* short-circuiting to a decided answer and falling back to `None`    *)
(* (undecided) only when no component pair settles the question.      *)
(* ---------------------------------------------------------------- *)

let rec geo_combine_exists (xs : list (option bool)) : Tot (option bool) (decreases xs) =
  match xs with
  | [] -> Some false
  | Some true :: _ -> Some true
  | Some false :: rest -> geo_combine_exists rest
  | None :: rest ->
    (match geo_combine_exists rest with
     | Some true -> Some true
     | _ -> None)

let rec geo_combine_forall (xs : list (option bool)) : Tot (option bool) (decreases xs) =
  match xs with
  | [] -> Some true
  | Some false :: _ -> Some false
  | Some true :: rest -> geo_combine_forall rest
  | None :: rest ->
    (match geo_combine_forall rest with
     | Some false -> Some false
     | _ -> None)
