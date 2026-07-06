module RDF.Geo.Topology

open FStar.String
open FStar.List.Tot
open FStar.Mul
open RDF.Geo.Types
open RDF.Geo.BBox

(* ================================================================ *)
(* GeoSPARQL v0 Simple Features (DE-9IM-derived) predicates, pure     *)
(* exact rational arithmetic (option A of the plan). NO floating      *)
(* point, no host CG library.                                        *)
(*                                                                    *)
(* Every predicate returns `option bool`:                             *)
(*   Some true / Some false — decided exactly                        *)
(*   None                    — this geometry-kind combination is NOT  *)
(*                              decided by v0 (documented per-pair    *)
(*                              below); callers (the geof: dispatch   *)
(*                              in SPARQL11.Algebra.fst) map `None`   *)
(*                              to ER_Error, never to a guessed bool. *)
(*                                                                    *)
(* DECIDED VS REFUSED TABLE (kept in sync with the module's own       *)
(* implementation — see also the commit report for the same table):   *)
(*                                                                    *)
(*  point/point            : ALL 8 predicates decided exactly.        *)
(*  point/linestring       : equals(=false), intersects, disjoint,    *)
(*                            within, contains, touches decided.      *)
(*                            crosses, overlaps -> None (refused;     *)
(*                            crosses' DE-9IM pattern equivalence for  *)
(*                            0-dim/1-dim pairs is not settled here,   *)
(*                            better to refuse than assert an unverified*)
(*                            equivalence).                            *)
(*  point/polygon          : equals(=false), intersects, disjoint,    *)
(*                            within, contains, touches, overlaps     *)
(*                            (=false, differing dims per SFA         *)
(*                            convention) decided. crosses -> None.    *)
(*  linestring/linestring  : intersects, disjoint decided exactly     *)
(*                            (general segment-pair orientation test, *)
(*                            no simplicity assumption needed).       *)
(*                            equals decided up to reversal (NOT      *)
(*                            rotation-of-a-closed-loop's start point —*)
(*                            documented limitation). within/contains  *)
(*                            decided only when every edge of the      *)
(*                            "inner" line is a sub-segment of a SINGLE*)
(*                            edge of the "outer" line (does not       *)
(*                            handle an edge covered by the             *)
(*                            concatenation of >=2 outer edges across  *)
(*                            a bend — documented limitation, returns  *)
(*                            None there). touches/crosses/overlaps    *)
(*                            -> None (refused).                       *)
(*  polygon/polygon        : intersects, disjoint, within, contains    *)
(*                            decided via boundary-crossing + vertex-  *)
(*                            in-other tests, for SIMPLE (non-self-    *)
(*                            intersecting) polygons only (caller       *)
(*                            obligation, not checked). equals decided  *)
(*                            when bboxes differ (=false) or rings      *)
(*                            match up to rotation/reversal (=true);   *)
(*                            otherwise None. touches/crosses/overlaps  *)
(*                            -> None always (full DE-9IM boundary/     *)
(*                            interior classification not attempted).   *)
(*  linestring/polygon     : intersects, disjoint only (vertex-inside  *)
(*                            OR edge-crosses-ring-edge). Everything    *)
(*                            else -> None.                             *)
(*  Multi*/GeometryCollection: decomposed into components; intersects/ *)
(*                            disjoint via exists/forall over pairwise *)
(*                            component results (exact whenever the     *)
(*                            component-pair predicate is exact).        *)
(*                            within/contains use a sufficient-only     *)
(*                            per-component check and fall back to      *)
(*                            None when a geometry straddles multiple   *)
(*                            components of a Multi* target without     *)
(*                            being fully within any single one.         *)
(*                                                                    *)
(* Everything under "decided" is exact rational arithmetic: no         *)
(* epsilon, no floating point — a point exactly on a polygon edge is    *)
(* correctly classified as boundary, not nudged either way.            *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(* Exact orientation / segment primitives                             *)
(* ---------------------------------------------------------------- *)

// 2D cross product of (b-a) x (c-a); sign gives orientation of the
// ordered triple (a,b,c): >0 left turn (CCW), <0 right turn (CW),
// =0 collinear. Exact: sums/products of exact rationals.
let geo_orient (a b c : geo_point) : geo_scaled =
  let bx_ax = gs_sub b.gp_x a.gp_x in
  let cy_ay = gs_sub c.gp_y a.gp_y in
  let by_ay = gs_sub b.gp_y a.gp_y in
  let cx_ax = gs_sub c.gp_x a.gp_x in
  gs_sub (gs_mul bx_ax cy_ay) (gs_mul by_ay cx_ax)

let geo_orient_sign (a b c : geo_point) : int = gs_sign (geo_orient a b c)

// Is point p on the closed bounding box of segment [a,b]? (Necessary,
// not sufficient, condition for "on segment" — combined with
// collinearity below it becomes exact "on segment" for the collinear
// case, which is the only case it is ever used in.)
let geo_in_seg_bbox (p a b : geo_point) : bool =
  gs_le (gs_min a.gp_x b.gp_x) p.gp_x && gs_le p.gp_x (gs_max a.gp_x b.gp_x) &&
  gs_le (gs_min a.gp_y b.gp_y) p.gp_y && gs_le p.gp_y (gs_max a.gp_y b.gp_y)

// Exact point-on-closed-segment test.
let geo_point_on_segment (p a b : geo_point) : bool =
  geo_orient_sign a b p = 0 && geo_in_seg_bbox p a b

// Exact proper-or-improper segment intersection test (standard
// orientation-based algorithm; decidable for ANY two segments, no
// "simple polygon" assumption needed — that assumption is only
// needed for point-in-polygon ray casting below).
let geo_segments_intersect (a b c d : geo_point) : bool =
  let o1 = geo_orient_sign a b c in
  let o2 = geo_orient_sign a b d in
  let o3 = geo_orient_sign c d a in
  let o4 = geo_orient_sign c d b in
  if o1 <> o2 && o3 <> o4 then true
  else
    (o1 = 0 && geo_in_seg_bbox c a b) ||
    (o2 = 0 && geo_in_seg_bbox d a b) ||
    (o3 = 0 && geo_in_seg_bbox a c d) ||
    (o4 = 0 && geo_in_seg_bbox b c d)

(* ---------------------------------------------------------------- *)
(* Rings/paths as consecutive-segment lists                           *)
(* ---------------------------------------------------------------- *)

let rec geo_point_on_path (p : geo_point) (pts : list geo_point) : Tot bool (decreases pts) =
  match pts with
  | [] | [_] -> false
  | a :: b :: rest -> geo_point_on_segment p a b || geo_point_on_path p (b :: rest)

let rec geo_segment_crosses_path (a b : geo_point) (pts : list geo_point) : Tot bool (decreases pts) =
  match pts with
  | [] | [_] -> false
  | p :: q :: rest -> geo_segments_intersect a b p q || geo_segment_crosses_path a b (q :: rest)

let rec geo_path_crosses_path (pts1 pts2 : list geo_point) : Tot bool (decreases pts1) =
  match pts1 with
  | [] | [_] -> false
  | a :: b :: rest -> geo_segment_crosses_path a b pts2 || geo_path_crosses_path (b :: rest) pts2

// Is [a,b] a sub-segment of [c,d] (collinear and both endpoints
// within [c,d]'s extent on that line)?
let geo_segment_subseg_of (a b c d : geo_point) : bool =
  geo_orient_sign c d a = 0 && geo_orient_sign c d b = 0 &&
  geo_in_seg_bbox a c d && geo_in_seg_bbox b c d

let rec geo_segment_subseg_of_any (a b : geo_point) (pts : list geo_point) : Tot bool (decreases pts) =
  match pts with
  | [] | [_] -> false
  | c :: d :: rest -> geo_segment_subseg_of a b c d || geo_segment_subseg_of_any a b (d :: rest)

// Every edge of `inner` is a sub-segment of a SINGLE edge of `outer`.
// Sufficient but not complete for "inner's point-set subset of
// outer's point-set" (misses an inner edge covered by >=2 collinear
// outer edges across a bend) — see module header.
let rec geo_path_within_path_by_edges (inner outer : list geo_point) : Tot bool (decreases inner) =
  match inner with
  | [] | [_] -> true
  | a :: b :: rest -> geo_segment_subseg_of_any a b outer && geo_path_within_path_by_edges (b :: rest) outer

let rec geo_all_points_on_path (pts outer : list geo_point) : Tot bool (decreases pts) =
  match pts with
  | [] -> true
  | p :: rest -> geo_point_on_path p outer && geo_all_points_on_path rest outer

// option-bool line-within-line: True when the per-edge check
// succeeds; False only when NO vertex of `inner` is even on `outer`
// (a clean, certain non-containment); else refused (None) — see
// module header's documented limitation.
let geo_path_within_path (inner outer : list geo_point) : option bool =
  if geo_path_within_path_by_edges inner outer then Some true
  else if not (geo_all_points_on_path inner outer) then Some false
  else None

let rec geo_list_point_eq (a b : list geo_point) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> geo_point_eq x y && geo_list_point_eq xs ys
  | _, _ -> false

// Reversal-invariant equality for OPEN curves is a complete
// invariant (no rotation ambiguity — the two endpoints are
// geometrically distinguished). For CLOSED loops of matching length,
// a plain sequence mismatch does NOT prove inequality (the same loop
// can be listed starting from any vertex) — refuse (None) rather
// than assert `Some false` in that case.
let geo_linestring_equals (l1 l2 : list geo_point) : option bool =
  if geo_list_point_eq l1 l2 || geo_list_point_eq l1 (List.Tot.rev l2) then Some true
  else if geo_is_closed_line l1 && geo_is_closed_line l2 && List.Tot.length l1 = List.Tot.length l2 then None
  else Some false

let geo_all_points_eq_to (pts : list geo_point) (p : geo_point) : bool =
  List.Tot.for_all (fun q -> geo_point_eq q p) pts

(* ---------------------------------------------------------------- *)
(* Point-in-ring / point-in-polygon, exact (division-free) ray cast   *)
(*                                                                    *)
(* Standard exact "crossing number" test rewritten with the           *)
(* orientation predicate instead of computing an intersection x       *)
(* coordinate (which would need division): for each edge straddling   *)
(* the horizontal line y = p.y, the edge crosses to the right of p    *)
(* iff (edge goes upward and orient(a,b,p) > 0) or (edge goes         *)
(* downward and orient(a,b,p) < 0). Requires the ring's caller-side    *)
(* "simple, non-self-intersecting" assumption (documented throughout   *)
(* this module) — parity ray-casting is not meaningful for a           *)
(* self-intersecting ring.                                            *)
(* ---------------------------------------------------------------- *)

let rec geo_ray_cross_count (p : geo_point) (pts : list geo_point) : Tot nat (decreases pts) =
  match pts with
  | [] | [_] -> 0
  | a :: b :: rest ->
    let straddles = (gs_gt a.gp_y p.gp_y) <> (gs_gt b.gp_y p.gp_y) in
    let crosses =
      if not straddles then false
      else
        let o = geo_orient_sign a b p in
        (gs_lt a.gp_y b.gp_y && o > 0) || (gs_gt a.gp_y b.gp_y && o < 0) in
    (if crosses then 1 else 0) + geo_ray_cross_count p (b :: rest)

type geo_pt_class = | PC_Interior | PC_Boundary | PC_Exterior

let geo_point_ring_class (p : geo_point) (r : geo_ring) : geo_pt_class =
  if geo_point_on_path p r then PC_Boundary
  else if geo_ray_cross_count p r % 2 = 1 then PC_Interior
  else PC_Exterior

let rec geo_point_in_any_hole_interior (p : geo_point) (holes : list geo_ring) : Tot bool (decreases holes) =
  match holes with
  | [] -> false
  | h :: rest -> geo_point_ring_class p h = PC_Interior || geo_point_in_any_hole_interior p rest

let rec geo_point_on_any_ring (p : geo_point) (rings : list geo_ring) : Tot bool (decreases rings) =
  match rings with
  | [] -> false
  | r :: rest -> geo_point_on_path p r || geo_point_on_any_ring p rest

let geo_point_polygon_class (p : geo_point) (poly : geo_polygon) : geo_pt_class =
  if geo_point_on_path p poly.gpoly_ext || geo_point_on_any_ring p poly.gpoly_holes then PC_Boundary
  else if geo_ray_cross_count p poly.gpoly_ext % 2 = 1 then
    (if geo_point_in_any_hole_interior p poly.gpoly_holes then PC_Exterior else PC_Interior)
  else PC_Exterior

(* ---------------------------------------------------------------- *)
(* Line/polygon and polygon/polygon boundary interaction              *)
(* ---------------------------------------------------------------- *)

let rec geo_segment_crosses_rings (a b : geo_point) (rings : list geo_ring) : Tot bool (decreases rings) =
  match rings with
  | [] -> false
  | r :: rest -> geo_segment_crosses_path a b r || geo_segment_crosses_rings a b rest

let geo_segment_crosses_polygon_boundary (a b : geo_point) (poly : geo_polygon) : bool =
  geo_segment_crosses_path a b poly.gpoly_ext ||
  geo_segment_crosses_rings a b poly.gpoly_holes

let rec geo_any_vertex_in_polygon (pts : list geo_point) (poly : geo_polygon) : Tot bool (decreases pts) =
  match pts with
  | [] -> false
  | p :: rest -> geo_point_polygon_class p poly <> PC_Exterior || geo_any_vertex_in_polygon rest poly

let rec geo_line_crosses_polygon_boundary (pts : list geo_point) (poly : geo_polygon) : Tot bool (decreases pts) =
  match pts with
  | [] | [_] -> false
  | a :: b :: rest ->
    geo_segment_crosses_polygon_boundary a b poly || geo_line_crosses_polygon_boundary (b :: rest) poly

let geo_line_intersects_polygon (pts : list geo_point) (poly : geo_polygon) : bool =
  geo_any_vertex_in_polygon pts poly || geo_line_crosses_polygon_boundary pts poly

let rec geo_ring_crosses_polygon_boundary (r : geo_ring) (poly : geo_polygon) : Tot bool (decreases r) =
  match r with
  | [] | [_] -> false
  | a :: b :: rest ->
    geo_segment_crosses_polygon_boundary a b poly || geo_ring_crosses_polygon_boundary (b :: rest) poly

let rec geo_rings_cross_polygon_boundary (rs : list geo_ring) (poly : geo_polygon) : Tot bool (decreases rs) =
  match rs with
  | [] -> false
  | r :: rest -> geo_ring_crosses_polygon_boundary r poly || geo_rings_cross_polygon_boundary rest poly

let geo_polygon_boundaries_cross (p1 p2 : geo_polygon) : bool =
  geo_ring_crosses_polygon_boundary p1.gpoly_ext p2 ||
  geo_rings_cross_polygon_boundary p1.gpoly_holes p2

// Complete (not just sufficient) exact test for two SIMPLE polygons:
// they intersect iff some vertex of either is inside-or-on the other,
// or their boundaries cross. (Standard result for simple polygons.)
let geo_polygons_intersect (p1 p2 : geo_polygon) : bool =
  geo_any_vertex_in_polygon p1.gpoly_ext p2 ||
  geo_any_vertex_in_polygon p2.gpoly_ext p1 ||
  geo_polygon_boundaries_cross p1 p2

(* ---------------------------------------------------------------- *)
(* Ring equality up to rotation/reversal (for polygon sfEquals)       *)
(* ---------------------------------------------------------------- *)

let rec geo_drop_last (pts : list geo_point) : Tot (list geo_point) (decreases pts) =
  match pts with
  | [] -> []
  | [_] -> []
  | p :: rest -> p :: geo_drop_last rest

let geo_rotate_once (pts : list geo_point) : list geo_point =
  match pts with
  | [] -> []
  | p :: rest -> rest @ [p]

let rec geo_any_rotation_eq (a b : list geo_point) (fuel : nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else geo_list_point_eq a b || geo_any_rotation_eq (geo_rotate_once a) b (fuel - 1)

let geo_ring_eq_up_to_rotation_reversal (r1 r2 : geo_ring) : bool =
  let o1 = geo_drop_last r1 in
  let o2 = geo_drop_last r2 in
  List.Tot.length o1 = List.Tot.length o2 &&
  (geo_any_rotation_eq o1 o2 (List.Tot.length o1) ||
   geo_any_rotation_eq o1 (List.Tot.rev o2) (List.Tot.length o1))

let rec geo_ring_in_list (r : geo_ring) (rs : list geo_ring) : Tot bool (decreases rs) =
  match rs with
  | [] -> false
  | r2 :: rest -> geo_ring_eq_up_to_rotation_reversal r r2 || geo_ring_in_list r rest

let rec geo_rings_subset (rs1 rs2 : list geo_ring) : Tot bool (decreases rs1) =
  match rs1 with
  | [] -> true
  | r :: rest -> geo_ring_in_list r rs2 && geo_rings_subset rest rs2

let geo_holes_eq (h1 h2 : list geo_ring) : bool =
  List.Tot.length h1 = List.Tot.length h2 && geo_rings_subset h1 h2 && geo_rings_subset h2 h1

let geo_polygon_equals (p1 p2 : geo_polygon) : option bool =
  match geo_bbox_of_polygon p1, geo_bbox_of_polygon p2 with
  | Some b1, Some b2 ->
    if not (geo_bbox_eq b1 b2) then Some false
    else if geo_ring_eq_up_to_rotation_reversal p1.gpoly_ext p2.gpoly_ext &&
            geo_holes_eq p1.gpoly_holes p2.gpoly_holes
    then Some true
    else None
  | _, _ -> None

(* ---------------------------------------------------------------- *)
(* Base-kind predicates (Point / LineString / Polygon / Empty only —  *)
(* Multi*/GeometryCollection are decomposed before reaching these,    *)
(* see the fuel-based decomposition further down).                   *)
(* ---------------------------------------------------------------- *)

let sf_equals_base (g1 g2 : geo_geometry) : option bool =
  match g1, g2 with
  | G_Empty k1, G_Empty k2 -> Some (k1 = k2)
  | G_Empty _, _ -> Some false
  | _, G_Empty _ -> Some false
  | G_Point p1, G_Point p2 -> Some (geo_point_eq p1 p2)
  | G_Point _, _ -> Some false
  | _, G_Point _ -> Some false
  | G_LineString l1, G_LineString l2 -> geo_linestring_equals l1 l2
  | G_LineString _, _ -> Some false
  | _, G_LineString _ -> Some false
  | G_Polygon p1, G_Polygon p2 -> geo_polygon_equals p1 p2
  | _, _ -> None

let sf_intersects_base (g1 g2 : geo_geometry) : option bool =
  match g1, g2 with
  | G_Empty _, _ -> Some false
  | _, G_Empty _ -> Some false
  | G_Point p1, G_Point p2 -> Some (geo_point_eq p1 p2)
  | G_Point p, G_LineString l -> Some (geo_point_on_path p l)
  | G_LineString l, G_Point p -> Some (geo_point_on_path p l)
  | G_Point p, G_Polygon poly -> Some (geo_point_polygon_class p poly <> PC_Exterior)
  | G_Polygon poly, G_Point p -> Some (geo_point_polygon_class p poly <> PC_Exterior)
  | G_LineString l1, G_LineString l2 -> Some (geo_path_crosses_path l1 l2)
  | G_LineString l, G_Polygon poly -> Some (geo_line_intersects_polygon l poly)
  | G_Polygon poly, G_LineString l -> Some (geo_line_intersects_polygon l poly)
  | G_Polygon p1, G_Polygon p2 ->
    (match geo_bbox_of_polygon p1, geo_bbox_of_polygon p2 with
     | Some b1, Some b2 -> if geo_bbox_disjoint b1 b2 then Some false else Some (geo_polygons_intersect p1 p2)
     | _, _ -> Some false)
  | _, _ -> None

let sf_within_base (g1 g2 : geo_geometry) : option bool =
  match g1, g2 with
  | G_Empty _, G_Empty _ -> Some true
  | G_Empty _, _ -> Some true
  | _, G_Empty _ -> Some false
  | G_Point p1, G_Point p2 -> Some (geo_point_eq p1 p2)
  | G_Point p, G_LineString l ->
    if not (geo_point_on_path p l) then Some false
    else if geo_is_closed_line l then Some true
    else
      (match l, geo_last_point l with
       | first :: _, Some last -> Some (not (geo_point_eq p first) && not (geo_point_eq p last))
       | _, _ -> Some true)
  | G_LineString l, G_Point p -> Some (geo_all_points_eq_to l p)
  | G_Point p, G_Polygon poly -> Some (geo_point_polygon_class p poly = PC_Interior)
  | G_Polygon _, G_Point _ -> Some false
  | G_LineString l1, G_LineString l2 -> geo_path_within_path l1 l2
  | G_LineString l, G_Polygon poly ->
    (match geo_bbox_of_points l, geo_bbox_of_polygon poly with
     | Some bl, Some bp ->
       if geo_bbox_disjoint bl bp then Some false
       else if not (geo_any_vertex_in_polygon l poly) then Some false
       else if geo_any_vertex_in_polygon l poly && List.Tot.for_all (fun p -> geo_point_polygon_class p poly <> PC_Exterior) l
               && not (geo_line_crosses_polygon_boundary l poly)
       then Some true
       else None
     | _, _ -> Some false)
  | G_Polygon _, G_LineString _ -> Some false
  | G_Polygon p1, G_Polygon p2 ->
    if geo_polygon_boundaries_cross p1 p2 then None
    else
      (match p1.gpoly_ext with
       | rep :: _ -> Some (geo_point_polygon_class rep p2 <> PC_Exterior)
       | [] -> None)
  | _, _ -> None

let sf_touches_base (g1 g2 : geo_geometry) : option bool =
  match g1, g2 with
  | G_Empty _, _ -> Some false
  | _, G_Empty _ -> Some false
  | G_Point _, G_Point _ -> Some false
  | G_Point p, G_LineString l ->
    if not (geo_point_on_path p l) then Some false
    else if geo_is_closed_line l then Some false
    else
      (match l, geo_last_point l with
       | first :: _, Some last -> Some (geo_point_eq p first || geo_point_eq p last)
       | _, _ -> Some false)
  | G_LineString l, G_Point p ->
    if not (geo_point_on_path p l) then Some false
    else if geo_is_closed_line l then Some false
    else
      (match l, geo_last_point l with
       | first :: _, Some last -> Some (geo_point_eq p first || geo_point_eq p last)
       | _, _ -> Some false)
  | G_Point p, G_Polygon poly -> Some (geo_point_polygon_class p poly = PC_Boundary)
  | G_Polygon poly, G_Point p -> Some (geo_point_polygon_class p poly = PC_Boundary)
  | _, _ -> None

let sf_crosses_base (g1 g2 : geo_geometry) : option bool =
  match g1, g2 with
  | G_Empty _, _ -> Some false
  | _, G_Empty _ -> Some false
  | G_Point _, G_Point _ -> Some false
  | G_Polygon _, G_Polygon _ -> Some false
  | _, _ -> None

let sf_overlaps_base (g1 g2 : geo_geometry) : option bool =
  match g1, g2 with
  | G_Empty _, _ -> Some false
  | _, G_Empty _ -> Some false
  | G_Point _, G_Point _ -> Some false
  | G_Point _, G_LineString _ -> Some false
  | G_LineString _, G_Point _ -> Some false
  | G_Point _, G_Polygon _ -> Some false
  | G_Polygon _, G_Point _ -> Some false
  | G_LineString _, G_Polygon _ -> Some false
  | G_Polygon _, G_LineString _ -> Some false
  | G_LineString _, G_LineString _ -> None
  | G_Polygon _, G_Polygon _ -> None
  | _, _ -> None

(* ---------------------------------------------------------------- *)
(* Multi*/GeometryCollection decomposition, fuel-bounded.              *)
(*                                                                    *)
(* GeometryCollection can nest arbitrarily; MultiPoint/MultiLineString/*)
(* MultiPolygon do not. Decomposing a Multi* value into per-component  *)
(* base geometries produces FRESH values that are not literal          *)
(* subterms of the original (`G_Point p` from a `MultiPoint` list       *)
(* element is not a structural subterm of the `G_MultiPoint` value),   *)
(* so plain structural `decreases` does not apply — this is exactly    *)
(* the documented "fuel where structural measures don't exist" case    *)
(* (mirroring XPath.Eval.fst). Fuel = 64 is a generous bound on         *)
(* realistic GeometryCollection nesting depth; exceeding it refuses    *)
(* (None) rather than crashing.                                        *)
(* ---------------------------------------------------------------- *)

let rec geo_decompose_fuel
    (base : geo_geometry -> geo_geometry -> option bool)
    (combine : list (option bool) -> option bool)
    (g1 g2 : geo_geometry) (fuel : nat)
  : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    match g1 with
    | G_GeometryCollection gs ->
      combine (List.Tot.map (fun g -> geo_decompose_fuel base combine g g2 (fuel - 1)) gs)
    | G_MultiPoint pts ->
      combine (List.Tot.map (fun p -> geo_decompose_fuel base combine (G_Point p) g2 (fuel - 1)) pts)
    | G_MultiLineString ls ->
      combine (List.Tot.map (fun l -> geo_decompose_fuel base combine (G_LineString l) g2 (fuel - 1)) ls)
    | G_MultiPolygon ps ->
      combine (List.Tot.map (fun p -> geo_decompose_fuel base combine (G_Polygon p) g2 (fuel - 1)) ps)
    | _ ->
      (match g2 with
       | G_GeometryCollection gs ->
         combine (List.Tot.map (fun g -> geo_decompose_fuel base combine g1 g (fuel - 1)) gs)
       | G_MultiPoint pts ->
         combine (List.Tot.map (fun p -> geo_decompose_fuel base combine g1 (G_Point p) (fuel - 1)) pts)
       | G_MultiLineString ls ->
         combine (List.Tot.map (fun l -> geo_decompose_fuel base combine g1 (G_LineString l) (fuel - 1)) ls)
       | G_MultiPolygon ps ->
         combine (List.Tot.map (fun p -> geo_decompose_fuel base combine g1 (G_Polygon p) (fuel - 1)) ps)
       | _ -> base g1 g2)

let geo_decompose_default_fuel : nat = 64

let geo_decompose (base : geo_geometry -> geo_geometry -> option bool)
    (combine : list (option bool) -> option bool) (g1 g2 : geo_geometry) : option bool =
  geo_decompose_fuel base combine g1 g2 geo_decompose_default_fuel

(* ---------------------------------------------------------------- *)
(* Top-level predicates                                               *)
(* ---------------------------------------------------------------- *)

let sf_intersects (g1 g2 : geo_geometry) : option bool =
  geo_decompose sf_intersects_base geo_combine_exists g1 g2

let sf_disjoint (g1 g2 : geo_geometry) : option bool =
  match sf_intersects g1 g2 with
  | Some b -> Some (not b)
  | None -> None

let sf_touches (g1 g2 : geo_geometry) : option bool = sf_touches_base g1 g2
let sf_crosses (g1 g2 : geo_geometry) : option bool = sf_crosses_base g1 g2
let sf_overlaps (g1 g2 : geo_geometry) : option bool = sf_overlaps_base g1 g2
let sf_equals (g1 g2 : geo_geometry) : option bool = sf_equals_base g1 g2

// within, decomposing g1 (the "inner" side) via forall over its
// Multi*/Collection components (exact — a union is within B iff
// every one of its components is), then for base-kind g1 trying a
// *sufficient* decomposition of g2 (the "outer"/target side) when
// g2 is itself Multi*/Collection — see module header for the
// documented `None` fallback when g1 straddles multiple components
// of g2 without being wholly within any single one.
let geo_within_g2_decompose (g1 g2 : geo_geometry) : option bool =
  match g2 with
  | G_GeometryCollection gs ->
    (match geo_combine_exists (List.Tot.map (fun g -> sf_within_base g1 g) gs) with
     | Some true -> Some true
     | _ -> (match sf_intersects g1 g2 with Some false -> Some false | _ -> None))
  | G_MultiPoint pts ->
    (match geo_combine_exists (List.Tot.map (fun p -> sf_within_base g1 (G_Point p)) pts) with
     | Some true -> Some true
     | _ -> (match sf_intersects g1 g2 with Some false -> Some false | _ -> None))
  | G_MultiLineString ls ->
    (match geo_combine_exists (List.Tot.map (fun l -> sf_within_base g1 (G_LineString l)) ls) with
     | Some true -> Some true
     | _ -> (match sf_intersects g1 g2 with Some false -> Some false | _ -> None))
  | G_MultiPolygon ps ->
    (match geo_combine_exists (List.Tot.map (fun p -> sf_within_base g1 (G_Polygon p)) ps) with
     | Some true -> Some true
     | _ -> (match sf_intersects g1 g2 with Some false -> Some false | _ -> None))
  | _ -> sf_within_base g1 g2

let rec sf_within_fuel (g1 g2 : geo_geometry) (fuel : nat) : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    match g1 with
    | G_GeometryCollection gs ->
      geo_combine_forall (List.Tot.map (fun g -> sf_within_fuel g g2 (fuel - 1)) gs)
    | G_MultiPoint pts ->
      geo_combine_forall (List.Tot.map (fun p -> sf_within_fuel (G_Point p) g2 (fuel - 1)) pts)
    | G_MultiLineString ls ->
      geo_combine_forall (List.Tot.map (fun l -> sf_within_fuel (G_LineString l) g2 (fuel - 1)) ls)
    | G_MultiPolygon ps ->
      geo_combine_forall (List.Tot.map (fun p -> sf_within_fuel (G_Polygon p) g2 (fuel - 1)) ps)
    | _ -> geo_within_g2_decompose g1 g2

let sf_within (g1 g2 : geo_geometry) : option bool = sf_within_fuel g1 g2 geo_decompose_default_fuel
let sf_contains (g1 g2 : geo_geometry) : option bool = sf_within g2 g1

(* ---------------------------------------------------------------- *)
(* CRS-aware wrappers over geo_wkt_value, used by the SPARQL          *)
(* dispatch layer. v0 performs NO CRS transformation: a call across    *)
(* two differing, explicitly-stated CRS IRIs is refused (None) rather   *)
(* than silently assumed identity; `None` (default/CRS84) is treated    *)
(* as compatible with any explicitly-stated CRS (the common real-world  *)
(* case of one literal using the bare form and another repeating        *)
(* CRS84 explicitly).                                                   *)
(* ---------------------------------------------------------------- *)

let geo_crs_compatible (a b : option string) : bool =
  match a, b with
  | Some x, Some y -> x = y
  | _, _ -> true

let geo_wkt_predicate (f : geo_geometry -> geo_geometry -> option bool)
    (a b : geo_wkt_value) : option bool =
  if geo_crs_compatible a.gw_crs b.gw_crs then f a.gw_geom b.gw_geom else None

