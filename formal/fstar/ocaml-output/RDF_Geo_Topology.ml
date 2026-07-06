open Prims
let geo_orient (a : RDF_Geo_Types.geo_point) (b : RDF_Geo_Types.geo_point)
  (c : RDF_Geo_Types.geo_point) : RDF_Geo_Types.geo_scaled=
  let bx_ax = RDF_Geo_Types.gs_sub b.RDF_Geo_Types.gp_x a.RDF_Geo_Types.gp_x in
  let cy_ay = RDF_Geo_Types.gs_sub c.RDF_Geo_Types.gp_y a.RDF_Geo_Types.gp_y in
  let by_ay = RDF_Geo_Types.gs_sub b.RDF_Geo_Types.gp_y a.RDF_Geo_Types.gp_y in
  let cx_ax = RDF_Geo_Types.gs_sub c.RDF_Geo_Types.gp_x a.RDF_Geo_Types.gp_x in
  RDF_Geo_Types.gs_sub (RDF_Geo_Types.gs_mul bx_ax cy_ay)
    (RDF_Geo_Types.gs_mul by_ay cx_ax)
let geo_orient_sign (a : RDF_Geo_Types.geo_point)
  (b : RDF_Geo_Types.geo_point) (c : RDF_Geo_Types.geo_point) : Prims.int=
  RDF_Geo_Types.gs_sign (geo_orient a b c)
let geo_in_seg_bbox (p : RDF_Geo_Types.geo_point)
  (a : RDF_Geo_Types.geo_point) (b : RDF_Geo_Types.geo_point) : Prims.bool=
  (((RDF_Geo_Types.gs_le
       (RDF_Geo_Types.gs_min a.RDF_Geo_Types.gp_x b.RDF_Geo_Types.gp_x)
       p.RDF_Geo_Types.gp_x)
      &&
      (RDF_Geo_Types.gs_le p.RDF_Geo_Types.gp_x
         (RDF_Geo_Types.gs_max a.RDF_Geo_Types.gp_x b.RDF_Geo_Types.gp_x)))
     &&
     (RDF_Geo_Types.gs_le
        (RDF_Geo_Types.gs_min a.RDF_Geo_Types.gp_y b.RDF_Geo_Types.gp_y)
        p.RDF_Geo_Types.gp_y))
    &&
    (RDF_Geo_Types.gs_le p.RDF_Geo_Types.gp_y
       (RDF_Geo_Types.gs_max a.RDF_Geo_Types.gp_y b.RDF_Geo_Types.gp_y))
let geo_point_on_segment (p : RDF_Geo_Types.geo_point)
  (a : RDF_Geo_Types.geo_point) (b : RDF_Geo_Types.geo_point) : Prims.bool=
  ((geo_orient_sign a b p) = Prims.int_zero) && (geo_in_seg_bbox p a b)
let geo_segments_intersect (a : RDF_Geo_Types.geo_point)
  (b : RDF_Geo_Types.geo_point) (c : RDF_Geo_Types.geo_point)
  (d : RDF_Geo_Types.geo_point) : Prims.bool=
  let o1 = geo_orient_sign a b c in
  let o2 = geo_orient_sign a b d in
  let o3 = geo_orient_sign c d a in
  let o4 = geo_orient_sign c d b in
  if (o1 <> o2) && (o3 <> o4)
  then true
  else
    ((((o1 = Prims.int_zero) && (geo_in_seg_bbox c a b)) ||
        ((o2 = Prims.int_zero) && (geo_in_seg_bbox d a b)))
       || ((o3 = Prims.int_zero) && (geo_in_seg_bbox a c d)))
      || ((o4 = Prims.int_zero) && (geo_in_seg_bbox b c d))
let rec geo_point_on_path (p : RDF_Geo_Types.geo_point)
  (pts : RDF_Geo_Types.geo_point Prims.list) : Prims.bool=
  match pts with
  | [] -> false
  | uu___::[] -> false
  | a::b::rest ->
      (geo_point_on_segment p a b) || (geo_point_on_path p (b :: rest))
let rec geo_segment_crosses_path (a : RDF_Geo_Types.geo_point)
  (b : RDF_Geo_Types.geo_point) (pts : RDF_Geo_Types.geo_point Prims.list) :
  Prims.bool=
  match pts with
  | [] -> false
  | uu___::[] -> false
  | p::q::rest ->
      (geo_segments_intersect a b p q) ||
        (geo_segment_crosses_path a b (q :: rest))
let rec geo_path_crosses_path (pts1 : RDF_Geo_Types.geo_point Prims.list)
  (pts2 : RDF_Geo_Types.geo_point Prims.list) : Prims.bool=
  match pts1 with
  | [] -> false
  | uu___::[] -> false
  | a::b::rest ->
      (geo_segment_crosses_path a b pts2) ||
        (geo_path_crosses_path (b :: rest) pts2)
let geo_segment_subseg_of (a : RDF_Geo_Types.geo_point)
  (b : RDF_Geo_Types.geo_point) (c : RDF_Geo_Types.geo_point)
  (d : RDF_Geo_Types.geo_point) : Prims.bool=
  ((((geo_orient_sign c d a) = Prims.int_zero) &&
      ((geo_orient_sign c d b) = Prims.int_zero))
     && (geo_in_seg_bbox a c d))
    && (geo_in_seg_bbox b c d)
let rec geo_segment_subseg_of_any (a : RDF_Geo_Types.geo_point)
  (b : RDF_Geo_Types.geo_point) (pts : RDF_Geo_Types.geo_point Prims.list) :
  Prims.bool=
  match pts with
  | [] -> false
  | uu___::[] -> false
  | c::d::rest ->
      (geo_segment_subseg_of a b c d) ||
        (geo_segment_subseg_of_any a b (d :: rest))
let rec geo_path_within_path_by_edges
  (inner : RDF_Geo_Types.geo_point Prims.list)
  (outer : RDF_Geo_Types.geo_point Prims.list) : Prims.bool=
  match inner with
  | [] -> true
  | uu___::[] -> true
  | a::b::rest ->
      (geo_segment_subseg_of_any a b outer) &&
        (geo_path_within_path_by_edges (b :: rest) outer)
let rec geo_all_points_on_path (pts : RDF_Geo_Types.geo_point Prims.list)
  (outer : RDF_Geo_Types.geo_point Prims.list) : Prims.bool=
  match pts with
  | [] -> true
  | p::rest ->
      (geo_point_on_path p outer) && (geo_all_points_on_path rest outer)
let geo_path_within_path (inner : RDF_Geo_Types.geo_point Prims.list)
  (outer : RDF_Geo_Types.geo_point Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  if geo_path_within_path_by_edges inner outer
  then FStar_Pervasives_Native.Some true
  else
    if Prims.op_Negation (geo_all_points_on_path inner outer)
    then FStar_Pervasives_Native.Some false
    else FStar_Pervasives_Native.None
let rec geo_list_point_eq (a : RDF_Geo_Types.geo_point Prims.list)
  (b : RDF_Geo_Types.geo_point Prims.list) : Prims.bool=
  match (a, b) with
  | ([], []) -> true
  | (x::xs, y::ys) ->
      (RDF_Geo_Types.geo_point_eq x y) && (geo_list_point_eq xs ys)
  | (uu___, uu___1) -> false
let geo_linestring_equals (l1 : RDF_Geo_Types.geo_point Prims.list)
  (l2 : RDF_Geo_Types.geo_point Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  if
    (geo_list_point_eq l1 l2) ||
      (geo_list_point_eq l1 (FStar_List_Tot_Base.rev l2))
  then FStar_Pervasives_Native.Some true
  else
    if
      ((RDF_Geo_Types.geo_is_closed_line l1) &&
         (RDF_Geo_Types.geo_is_closed_line l2))
        &&
        ((FStar_List_Tot_Base.length l1) = (FStar_List_Tot_Base.length l2))
    then FStar_Pervasives_Native.None
    else FStar_Pervasives_Native.Some false
let geo_all_points_eq_to (pts : RDF_Geo_Types.geo_point Prims.list)
  (p : RDF_Geo_Types.geo_point) : Prims.bool=
  FStar_List_Tot_Base.for_all (fun q -> RDF_Geo_Types.geo_point_eq q p) pts
let rec geo_ray_cross_count (p : RDF_Geo_Types.geo_point)
  (pts : RDF_Geo_Types.geo_point Prims.list) : Prims.nat=
  match pts with
  | [] -> Prims.int_zero
  | uu___::[] -> Prims.int_zero
  | a::b::rest ->
      let straddles =
        (RDF_Geo_Types.gs_gt a.RDF_Geo_Types.gp_y p.RDF_Geo_Types.gp_y) <>
          (RDF_Geo_Types.gs_gt b.RDF_Geo_Types.gp_y p.RDF_Geo_Types.gp_y) in
      let crosses =
        if Prims.op_Negation straddles
        then false
        else
          (let o = geo_orient_sign a b p in
           ((RDF_Geo_Types.gs_lt a.RDF_Geo_Types.gp_y b.RDF_Geo_Types.gp_y)
              && (o > Prims.int_zero))
             ||
             ((RDF_Geo_Types.gs_gt a.RDF_Geo_Types.gp_y b.RDF_Geo_Types.gp_y)
                && (o < Prims.int_zero))) in
      (if crosses then Prims.int_one else Prims.int_zero) +
        (geo_ray_cross_count p (b :: rest))
type geo_pt_class =
  | PC_Interior 
  | PC_Boundary 
  | PC_Exterior 
let uu___is_PC_Interior (projectee : geo_pt_class) : Prims.bool=
  match projectee with | PC_Interior -> true | uu___ -> false
let uu___is_PC_Boundary (projectee : geo_pt_class) : Prims.bool=
  match projectee with | PC_Boundary -> true | uu___ -> false
let uu___is_PC_Exterior (projectee : geo_pt_class) : Prims.bool=
  match projectee with | PC_Exterior -> true | uu___ -> false
let geo_point_ring_class (p : RDF_Geo_Types.geo_point)
  (r : RDF_Geo_Types.geo_ring) : geo_pt_class=
  if geo_point_on_path p r
  then PC_Boundary
  else
    if ((mod) (geo_ray_cross_count p r) (Prims.of_int (2))) = Prims.int_one
    then PC_Interior
    else PC_Exterior
let rec geo_point_in_any_hole_interior (p : RDF_Geo_Types.geo_point)
  (holes : RDF_Geo_Types.geo_ring Prims.list) : Prims.bool=
  match holes with
  | [] -> false
  | h::rest ->
      ((geo_point_ring_class p h) = PC_Interior) ||
        (geo_point_in_any_hole_interior p rest)
let rec geo_point_on_any_ring (p : RDF_Geo_Types.geo_point)
  (rings : RDF_Geo_Types.geo_ring Prims.list) : Prims.bool=
  match rings with
  | [] -> false
  | r::rest -> (geo_point_on_path p r) || (geo_point_on_any_ring p rest)
let geo_point_polygon_class (p : RDF_Geo_Types.geo_point)
  (poly : RDF_Geo_Types.geo_polygon) : geo_pt_class=
  if
    (geo_point_on_path p poly.RDF_Geo_Types.gpoly_ext) ||
      (geo_point_on_any_ring p poly.RDF_Geo_Types.gpoly_holes)
  then PC_Boundary
  else
    if
      ((mod) (geo_ray_cross_count p poly.RDF_Geo_Types.gpoly_ext)
         (Prims.of_int (2)))
        = Prims.int_one
    then
      (if geo_point_in_any_hole_interior p poly.RDF_Geo_Types.gpoly_holes
       then PC_Exterior
       else PC_Interior)
    else PC_Exterior
let rec geo_segment_crosses_rings (a : RDF_Geo_Types.geo_point)
  (b : RDF_Geo_Types.geo_point) (rings : RDF_Geo_Types.geo_ring Prims.list) :
  Prims.bool=
  match rings with
  | [] -> false
  | r::rest ->
      (geo_segment_crosses_path a b r) ||
        (geo_segment_crosses_rings a b rest)
let geo_segment_crosses_polygon_boundary (a : RDF_Geo_Types.geo_point)
  (b : RDF_Geo_Types.geo_point) (poly : RDF_Geo_Types.geo_polygon) :
  Prims.bool=
  (geo_segment_crosses_path a b poly.RDF_Geo_Types.gpoly_ext) ||
    (geo_segment_crosses_rings a b poly.RDF_Geo_Types.gpoly_holes)
let rec geo_any_vertex_in_polygon (pts : RDF_Geo_Types.geo_point Prims.list)
  (poly : RDF_Geo_Types.geo_polygon) : Prims.bool=
  match pts with
  | [] -> false
  | p::rest ->
      ((geo_point_polygon_class p poly) <> PC_Exterior) ||
        (geo_any_vertex_in_polygon rest poly)
let rec geo_line_crosses_polygon_boundary
  (pts : RDF_Geo_Types.geo_point Prims.list)
  (poly : RDF_Geo_Types.geo_polygon) : Prims.bool=
  match pts with
  | [] -> false
  | uu___::[] -> false
  | a::b::rest ->
      (geo_segment_crosses_polygon_boundary a b poly) ||
        (geo_line_crosses_polygon_boundary (b :: rest) poly)
let geo_line_intersects_polygon (pts : RDF_Geo_Types.geo_point Prims.list)
  (poly : RDF_Geo_Types.geo_polygon) : Prims.bool=
  (geo_any_vertex_in_polygon pts poly) ||
    (geo_line_crosses_polygon_boundary pts poly)
let rec geo_ring_crosses_polygon_boundary (r : RDF_Geo_Types.geo_ring)
  (poly : RDF_Geo_Types.geo_polygon) : Prims.bool=
  match r with
  | [] -> false
  | uu___::[] -> false
  | a::b::rest ->
      (geo_segment_crosses_polygon_boundary a b poly) ||
        (geo_ring_crosses_polygon_boundary (b :: rest) poly)
let rec geo_rings_cross_polygon_boundary
  (rs : RDF_Geo_Types.geo_ring Prims.list) (poly : RDF_Geo_Types.geo_polygon)
  : Prims.bool=
  match rs with
  | [] -> false
  | r::rest ->
      (geo_ring_crosses_polygon_boundary r poly) ||
        (geo_rings_cross_polygon_boundary rest poly)
let geo_polygon_boundaries_cross (p1 : RDF_Geo_Types.geo_polygon)
  (p2 : RDF_Geo_Types.geo_polygon) : Prims.bool=
  (geo_ring_crosses_polygon_boundary p1.RDF_Geo_Types.gpoly_ext p2) ||
    (geo_rings_cross_polygon_boundary p1.RDF_Geo_Types.gpoly_holes p2)
let geo_polygons_intersect (p1 : RDF_Geo_Types.geo_polygon)
  (p2 : RDF_Geo_Types.geo_polygon) : Prims.bool=
  ((geo_any_vertex_in_polygon p1.RDF_Geo_Types.gpoly_ext p2) ||
     (geo_any_vertex_in_polygon p2.RDF_Geo_Types.gpoly_ext p1))
    || (geo_polygon_boundaries_cross p1 p2)
let rec geo_drop_last (pts : RDF_Geo_Types.geo_point Prims.list) :
  RDF_Geo_Types.geo_point Prims.list=
  match pts with
  | [] -> []
  | uu___::[] -> []
  | p::rest -> p :: (geo_drop_last rest)
let geo_rotate_once (pts : RDF_Geo_Types.geo_point Prims.list) :
  RDF_Geo_Types.geo_point Prims.list=
  match pts with | [] -> [] | p::rest -> FStar_List_Tot_Base.op_At rest [p]
let rec geo_any_rotation_eq (a : RDF_Geo_Types.geo_point Prims.list)
  (b : RDF_Geo_Types.geo_point Prims.list) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (geo_list_point_eq a b) ||
      (geo_any_rotation_eq (geo_rotate_once a) b (fuel - Prims.int_one))
let geo_ring_eq_up_to_rotation_reversal (r1 : RDF_Geo_Types.geo_ring)
  (r2 : RDF_Geo_Types.geo_ring) : Prims.bool=
  let o1 = geo_drop_last r1 in
  let o2 = geo_drop_last r2 in
  ((FStar_List_Tot_Base.length o1) = (FStar_List_Tot_Base.length o2)) &&
    ((geo_any_rotation_eq o1 o2 (FStar_List_Tot_Base.length o1)) ||
       (geo_any_rotation_eq o1 (FStar_List_Tot_Base.rev o2)
          (FStar_List_Tot_Base.length o1)))
let rec geo_ring_in_list (r : RDF_Geo_Types.geo_ring)
  (rs : RDF_Geo_Types.geo_ring Prims.list) : Prims.bool=
  match rs with
  | [] -> false
  | r2::rest ->
      (geo_ring_eq_up_to_rotation_reversal r r2) || (geo_ring_in_list r rest)
let rec geo_rings_subset (rs1 : RDF_Geo_Types.geo_ring Prims.list)
  (rs2 : RDF_Geo_Types.geo_ring Prims.list) : Prims.bool=
  match rs1 with
  | [] -> true
  | r::rest -> (geo_ring_in_list r rs2) && (geo_rings_subset rest rs2)
let geo_holes_eq (h1 : RDF_Geo_Types.geo_ring Prims.list)
  (h2 : RDF_Geo_Types.geo_ring Prims.list) : Prims.bool=
  (((FStar_List_Tot_Base.length h1) = (FStar_List_Tot_Base.length h2)) &&
     (geo_rings_subset h1 h2))
    && (geo_rings_subset h2 h1)
let geo_polygon_equals (p1 : RDF_Geo_Types.geo_polygon)
  (p2 : RDF_Geo_Types.geo_polygon) :
  Prims.bool FStar_Pervasives_Native.option=
  match ((RDF_Geo_BBox.geo_bbox_of_polygon p1),
          (RDF_Geo_BBox.geo_bbox_of_polygon p2))
  with
  | (FStar_Pervasives_Native.Some b1, FStar_Pervasives_Native.Some b2) ->
      if Prims.op_Negation (RDF_Geo_BBox.geo_bbox_eq b1 b2)
      then FStar_Pervasives_Native.Some false
      else
        if
          (geo_ring_eq_up_to_rotation_reversal p1.RDF_Geo_Types.gpoly_ext
             p2.RDF_Geo_Types.gpoly_ext)
            &&
            (geo_holes_eq p1.RDF_Geo_Types.gpoly_holes
               p2.RDF_Geo_Types.gpoly_holes)
        then FStar_Pervasives_Native.Some true
        else FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let sf_equals_base (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match (g1, g2) with
  | (RDF_Geo_Types.G_Empty k1, RDF_Geo_Types.G_Empty k2) ->
      FStar_Pervasives_Native.Some (k1 = k2)
  | (RDF_Geo_Types.G_Empty uu___, uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, RDF_Geo_Types.G_Empty uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point p1, RDF_Geo_Types.G_Point p2) ->
      FStar_Pervasives_Native.Some (RDF_Geo_Types.geo_point_eq p1 p2)
  | (RDF_Geo_Types.G_Point uu___, uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, RDF_Geo_Types.G_Point uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_LineString l1, RDF_Geo_Types.G_LineString l2) ->
      geo_linestring_equals l1 l2
  | (RDF_Geo_Types.G_LineString uu___, uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, RDF_Geo_Types.G_LineString uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Polygon p1, RDF_Geo_Types.G_Polygon p2) ->
      geo_polygon_equals p1 p2
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let sf_intersects_base (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match (g1, g2) with
  | (RDF_Geo_Types.G_Empty uu___, uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, RDF_Geo_Types.G_Empty uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point p1, RDF_Geo_Types.G_Point p2) ->
      FStar_Pervasives_Native.Some (RDF_Geo_Types.geo_point_eq p1 p2)
  | (RDF_Geo_Types.G_Point p, RDF_Geo_Types.G_LineString l) ->
      FStar_Pervasives_Native.Some (geo_point_on_path p l)
  | (RDF_Geo_Types.G_LineString l, RDF_Geo_Types.G_Point p) ->
      FStar_Pervasives_Native.Some (geo_point_on_path p l)
  | (RDF_Geo_Types.G_Point p, RDF_Geo_Types.G_Polygon poly) ->
      FStar_Pervasives_Native.Some
        ((geo_point_polygon_class p poly) <> PC_Exterior)
  | (RDF_Geo_Types.G_Polygon poly, RDF_Geo_Types.G_Point p) ->
      FStar_Pervasives_Native.Some
        ((geo_point_polygon_class p poly) <> PC_Exterior)
  | (RDF_Geo_Types.G_LineString l1, RDF_Geo_Types.G_LineString l2) ->
      FStar_Pervasives_Native.Some (geo_path_crosses_path l1 l2)
  | (RDF_Geo_Types.G_LineString l, RDF_Geo_Types.G_Polygon poly) ->
      FStar_Pervasives_Native.Some (geo_line_intersects_polygon l poly)
  | (RDF_Geo_Types.G_Polygon poly, RDF_Geo_Types.G_LineString l) ->
      FStar_Pervasives_Native.Some (geo_line_intersects_polygon l poly)
  | (RDF_Geo_Types.G_Polygon p1, RDF_Geo_Types.G_Polygon p2) ->
      (match ((RDF_Geo_BBox.geo_bbox_of_polygon p1),
               (RDF_Geo_BBox.geo_bbox_of_polygon p2))
       with
       | (FStar_Pervasives_Native.Some b1, FStar_Pervasives_Native.Some b2)
           ->
           if RDF_Geo_BBox.geo_bbox_disjoint b1 b2
           then FStar_Pervasives_Native.Some false
           else FStar_Pervasives_Native.Some (geo_polygons_intersect p1 p2)
       | (uu___, uu___1) -> FStar_Pervasives_Native.Some false)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let sf_within_base (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match (g1, g2) with
  | (RDF_Geo_Types.G_Empty uu___, RDF_Geo_Types.G_Empty uu___1) ->
      FStar_Pervasives_Native.Some true
  | (RDF_Geo_Types.G_Empty uu___, uu___1) ->
      FStar_Pervasives_Native.Some true
  | (uu___, RDF_Geo_Types.G_Empty uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point p1, RDF_Geo_Types.G_Point p2) ->
      FStar_Pervasives_Native.Some (RDF_Geo_Types.geo_point_eq p1 p2)
  | (RDF_Geo_Types.G_Point p, RDF_Geo_Types.G_LineString l) ->
      if Prims.op_Negation (geo_point_on_path p l)
      then FStar_Pervasives_Native.Some false
      else
        if RDF_Geo_Types.geo_is_closed_line l
        then FStar_Pervasives_Native.Some true
        else
          (match (l, (RDF_Geo_Types.geo_last_point l)) with
           | (first::uu___2, FStar_Pervasives_Native.Some last) ->
               FStar_Pervasives_Native.Some
                 ((Prims.op_Negation (RDF_Geo_Types.geo_point_eq p first)) &&
                    (Prims.op_Negation (RDF_Geo_Types.geo_point_eq p last)))
           | (uu___2, uu___3) -> FStar_Pervasives_Native.Some true)
  | (RDF_Geo_Types.G_LineString l, RDF_Geo_Types.G_Point p) ->
      FStar_Pervasives_Native.Some (geo_all_points_eq_to l p)
  | (RDF_Geo_Types.G_Point p, RDF_Geo_Types.G_Polygon poly) ->
      FStar_Pervasives_Native.Some
        ((geo_point_polygon_class p poly) = PC_Interior)
  | (RDF_Geo_Types.G_Polygon uu___, RDF_Geo_Types.G_Point uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_LineString l1, RDF_Geo_Types.G_LineString l2) ->
      geo_path_within_path l1 l2
  | (RDF_Geo_Types.G_LineString l, RDF_Geo_Types.G_Polygon poly) ->
      (match ((RDF_Geo_BBox.geo_bbox_of_points l),
               (RDF_Geo_BBox.geo_bbox_of_polygon poly))
       with
       | (FStar_Pervasives_Native.Some bl, FStar_Pervasives_Native.Some bp)
           ->
           if RDF_Geo_BBox.geo_bbox_disjoint bl bp
           then FStar_Pervasives_Native.Some false
           else
             if Prims.op_Negation (geo_any_vertex_in_polygon l poly)
             then FStar_Pervasives_Native.Some false
             else
               if
                 ((geo_any_vertex_in_polygon l poly) &&
                    (FStar_List_Tot_Base.for_all
                       (fun p ->
                          (geo_point_polygon_class p poly) <> PC_Exterior) l))
                   &&
                   (Prims.op_Negation
                      (geo_line_crosses_polygon_boundary l poly))
               then FStar_Pervasives_Native.Some true
               else FStar_Pervasives_Native.None
       | (uu___, uu___1) -> FStar_Pervasives_Native.Some false)
  | (RDF_Geo_Types.G_Polygon uu___, RDF_Geo_Types.G_LineString uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Polygon p1, RDF_Geo_Types.G_Polygon p2) ->
      if geo_polygon_boundaries_cross p1 p2
      then FStar_Pervasives_Native.None
      else
        (match p1.RDF_Geo_Types.gpoly_ext with
         | rep::uu___1 ->
             FStar_Pervasives_Native.Some
               ((geo_point_polygon_class rep p2) <> PC_Exterior)
         | [] -> FStar_Pervasives_Native.None)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let sf_touches_base (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match (g1, g2) with
  | (RDF_Geo_Types.G_Empty uu___, uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, RDF_Geo_Types.G_Empty uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point uu___, RDF_Geo_Types.G_Point uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point p, RDF_Geo_Types.G_LineString l) ->
      if Prims.op_Negation (geo_point_on_path p l)
      then FStar_Pervasives_Native.Some false
      else
        if RDF_Geo_Types.geo_is_closed_line l
        then FStar_Pervasives_Native.Some false
        else
          (match (l, (RDF_Geo_Types.geo_last_point l)) with
           | (first::uu___2, FStar_Pervasives_Native.Some last) ->
               FStar_Pervasives_Native.Some
                 ((RDF_Geo_Types.geo_point_eq p first) ||
                    (RDF_Geo_Types.geo_point_eq p last))
           | (uu___2, uu___3) -> FStar_Pervasives_Native.Some false)
  | (RDF_Geo_Types.G_LineString l, RDF_Geo_Types.G_Point p) ->
      if Prims.op_Negation (geo_point_on_path p l)
      then FStar_Pervasives_Native.Some false
      else
        if RDF_Geo_Types.geo_is_closed_line l
        then FStar_Pervasives_Native.Some false
        else
          (match (l, (RDF_Geo_Types.geo_last_point l)) with
           | (first::uu___2, FStar_Pervasives_Native.Some last) ->
               FStar_Pervasives_Native.Some
                 ((RDF_Geo_Types.geo_point_eq p first) ||
                    (RDF_Geo_Types.geo_point_eq p last))
           | (uu___2, uu___3) -> FStar_Pervasives_Native.Some false)
  | (RDF_Geo_Types.G_Point p, RDF_Geo_Types.G_Polygon poly) ->
      FStar_Pervasives_Native.Some
        ((geo_point_polygon_class p poly) = PC_Boundary)
  | (RDF_Geo_Types.G_Polygon poly, RDF_Geo_Types.G_Point p) ->
      FStar_Pervasives_Native.Some
        ((geo_point_polygon_class p poly) = PC_Boundary)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let sf_crosses_base (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match (g1, g2) with
  | (RDF_Geo_Types.G_Empty uu___, uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, RDF_Geo_Types.G_Empty uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point uu___, RDF_Geo_Types.G_Point uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Polygon uu___, RDF_Geo_Types.G_Polygon uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let sf_overlaps_base (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match (g1, g2) with
  | (RDF_Geo_Types.G_Empty uu___, uu___1) ->
      FStar_Pervasives_Native.Some false
  | (uu___, RDF_Geo_Types.G_Empty uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point uu___, RDF_Geo_Types.G_Point uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point uu___, RDF_Geo_Types.G_LineString uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_LineString uu___, RDF_Geo_Types.G_Point uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Point uu___, RDF_Geo_Types.G_Polygon uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Polygon uu___, RDF_Geo_Types.G_Point uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_LineString uu___, RDF_Geo_Types.G_Polygon uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_Polygon uu___, RDF_Geo_Types.G_LineString uu___1) ->
      FStar_Pervasives_Native.Some false
  | (RDF_Geo_Types.G_LineString uu___, RDF_Geo_Types.G_LineString uu___1) ->
      FStar_Pervasives_Native.None
  | (RDF_Geo_Types.G_Polygon uu___, RDF_Geo_Types.G_Polygon uu___1) ->
      FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let rec geo_decompose_fuel
  (base :
    RDF_Geo_Types.geo_geometry ->
      RDF_Geo_Types.geo_geometry -> Prims.bool FStar_Pervasives_Native.option)
  (combine :
    Prims.bool FStar_Pervasives_Native.option Prims.list ->
      Prims.bool FStar_Pervasives_Native.option)
  (g1 : RDF_Geo_Types.geo_geometry) (g2 : RDF_Geo_Types.geo_geometry)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match g1 with
     | RDF_Geo_Types.G_GeometryCollection gs ->
         combine
           (FStar_List_Tot_Base.map
              (fun g ->
                 geo_decompose_fuel base combine g g2 (fuel - Prims.int_one))
              gs)
     | RDF_Geo_Types.G_MultiPoint pts ->
         combine
           (FStar_List_Tot_Base.map
              (fun p ->
                 geo_decompose_fuel base combine (RDF_Geo_Types.G_Point p) g2
                   (fuel - Prims.int_one)) pts)
     | RDF_Geo_Types.G_MultiLineString ls ->
         combine
           (FStar_List_Tot_Base.map
              (fun l ->
                 geo_decompose_fuel base combine
                   (RDF_Geo_Types.G_LineString l) g2 (fuel - Prims.int_one))
              ls)
     | RDF_Geo_Types.G_MultiPolygon ps ->
         combine
           (FStar_List_Tot_Base.map
              (fun p ->
                 geo_decompose_fuel base combine (RDF_Geo_Types.G_Polygon p)
                   g2 (fuel - Prims.int_one)) ps)
     | uu___1 ->
         (match g2 with
          | RDF_Geo_Types.G_GeometryCollection gs ->
              combine
                (FStar_List_Tot_Base.map
                   (fun g ->
                      geo_decompose_fuel base combine g1 g
                        (fuel - Prims.int_one)) gs)
          | RDF_Geo_Types.G_MultiPoint pts ->
              combine
                (FStar_List_Tot_Base.map
                   (fun p ->
                      geo_decompose_fuel base combine g1
                        (RDF_Geo_Types.G_Point p) (fuel - Prims.int_one)) pts)
          | RDF_Geo_Types.G_MultiLineString ls ->
              combine
                (FStar_List_Tot_Base.map
                   (fun l ->
                      geo_decompose_fuel base combine g1
                        (RDF_Geo_Types.G_LineString l) (fuel - Prims.int_one))
                   ls)
          | RDF_Geo_Types.G_MultiPolygon ps ->
              combine
                (FStar_List_Tot_Base.map
                   (fun p ->
                      geo_decompose_fuel base combine g1
                        (RDF_Geo_Types.G_Polygon p) (fuel - Prims.int_one))
                   ps)
          | uu___2 -> base g1 g2))
let geo_decompose_default_fuel : Prims.nat= (Prims.of_int (64))
let geo_decompose
  (base :
    RDF_Geo_Types.geo_geometry ->
      RDF_Geo_Types.geo_geometry -> Prims.bool FStar_Pervasives_Native.option)
  (combine :
    Prims.bool FStar_Pervasives_Native.option Prims.list ->
      Prims.bool FStar_Pervasives_Native.option)
  (g1 : RDF_Geo_Types.geo_geometry) (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  geo_decompose_fuel base combine g1 g2 geo_decompose_default_fuel
let sf_intersects (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  geo_decompose sf_intersects_base RDF_Geo_Types.geo_combine_exists g1 g2
let sf_disjoint (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match sf_intersects g1 g2 with
  | FStar_Pervasives_Native.Some b ->
      FStar_Pervasives_Native.Some (Prims.op_Negation b)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let sf_touches (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option= sf_touches_base g1 g2
let sf_crosses (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option= sf_crosses_base g1 g2
let sf_overlaps (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option= sf_overlaps_base g1 g2
let sf_equals (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option= sf_equals_base g1 g2
let geo_within_g2_decompose (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  match g2 with
  | RDF_Geo_Types.G_GeometryCollection gs ->
      (match RDF_Geo_Types.geo_combine_exists
               (FStar_List_Tot_Base.map (fun g -> sf_within_base g1 g) gs)
       with
       | FStar_Pervasives_Native.Some true ->
           FStar_Pervasives_Native.Some true
       | uu___ ->
           (match sf_intersects g1 g2 with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | uu___1 -> FStar_Pervasives_Native.None))
  | RDF_Geo_Types.G_MultiPoint pts ->
      (match RDF_Geo_Types.geo_combine_exists
               (FStar_List_Tot_Base.map
                  (fun p -> sf_within_base g1 (RDF_Geo_Types.G_Point p)) pts)
       with
       | FStar_Pervasives_Native.Some true ->
           FStar_Pervasives_Native.Some true
       | uu___ ->
           (match sf_intersects g1 g2 with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | uu___1 -> FStar_Pervasives_Native.None))
  | RDF_Geo_Types.G_MultiLineString ls ->
      (match RDF_Geo_Types.geo_combine_exists
               (FStar_List_Tot_Base.map
                  (fun l -> sf_within_base g1 (RDF_Geo_Types.G_LineString l))
                  ls)
       with
       | FStar_Pervasives_Native.Some true ->
           FStar_Pervasives_Native.Some true
       | uu___ ->
           (match sf_intersects g1 g2 with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | uu___1 -> FStar_Pervasives_Native.None))
  | RDF_Geo_Types.G_MultiPolygon ps ->
      (match RDF_Geo_Types.geo_combine_exists
               (FStar_List_Tot_Base.map
                  (fun p -> sf_within_base g1 (RDF_Geo_Types.G_Polygon p)) ps)
       with
       | FStar_Pervasives_Native.Some true ->
           FStar_Pervasives_Native.Some true
       | uu___ ->
           (match sf_intersects g1 g2 with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | uu___1 -> FStar_Pervasives_Native.None))
  | uu___ -> sf_within_base g1 g2
let rec sf_within_fuel (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match g1 with
     | RDF_Geo_Types.G_GeometryCollection gs ->
         RDF_Geo_Types.geo_combine_forall
           (FStar_List_Tot_Base.map
              (fun g -> sf_within_fuel g g2 (fuel - Prims.int_one)) gs)
     | RDF_Geo_Types.G_MultiPoint pts ->
         RDF_Geo_Types.geo_combine_forall
           (FStar_List_Tot_Base.map
              (fun p ->
                 sf_within_fuel (RDF_Geo_Types.G_Point p) g2
                   (fuel - Prims.int_one)) pts)
     | RDF_Geo_Types.G_MultiLineString ls ->
         RDF_Geo_Types.geo_combine_forall
           (FStar_List_Tot_Base.map
              (fun l ->
                 sf_within_fuel (RDF_Geo_Types.G_LineString l) g2
                   (fuel - Prims.int_one)) ls)
     | RDF_Geo_Types.G_MultiPolygon ps ->
         RDF_Geo_Types.geo_combine_forall
           (FStar_List_Tot_Base.map
              (fun p ->
                 sf_within_fuel (RDF_Geo_Types.G_Polygon p) g2
                   (fuel - Prims.int_one)) ps)
     | uu___1 -> geo_within_g2_decompose g1 g2)
let sf_within (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option=
  sf_within_fuel g1 g2 geo_decompose_default_fuel
let sf_contains (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  Prims.bool FStar_Pervasives_Native.option= sf_within g2 g1
let geo_crs_compatible (a : Prims.string FStar_Pervasives_Native.option)
  (b : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  match (a, b) with
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) -> x = y
  | (uu___, uu___1) -> true
let geo_wkt_predicate
  (f :
    RDF_Geo_Types.geo_geometry ->
      RDF_Geo_Types.geo_geometry -> Prims.bool FStar_Pervasives_Native.option)
  (a : RDF_Geo_Types.geo_wkt_value) (b : RDF_Geo_Types.geo_wkt_value) :
  Prims.bool FStar_Pervasives_Native.option=
  if geo_crs_compatible a.RDF_Geo_Types.gw_crs b.RDF_Geo_Types.gw_crs
  then f a.RDF_Geo_Types.gw_geom b.RDF_Geo_Types.gw_geom
  else FStar_Pervasives_Native.None
