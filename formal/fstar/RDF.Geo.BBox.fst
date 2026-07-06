module RDF.Geo.BBox

open FStar.String
open FStar.List.Tot
open RDF.Geo.Types

(* ================================================================ *)
(* Axis-aligned bounding boxes over exact rational (geo_scaled)       *)
(* coordinates. Used both as a cheap fast-reject before any exact     *)
(* topological predicate (RDF.Geo.Topology.fst) and to implement       *)
(* geof:envelope (RDF.Geo.Functions.fst).                             *)
(* ================================================================ *)

type geo_bbox = { bb_xmin : geo_scaled; bb_ymin : geo_scaled;
                   bb_xmax : geo_scaled; bb_ymax : geo_scaled }

let geo_bbox_of_point (p : geo_point) : geo_bbox =
  { bb_xmin = p.gp_x; bb_ymin = p.gp_y; bb_xmax = p.gp_x; bb_ymax = p.gp_y }

let geo_bbox_union (a b : geo_bbox) : geo_bbox =
  { bb_xmin = gs_min a.bb_xmin b.bb_xmin;
    bb_ymin = gs_min a.bb_ymin b.bb_ymin;
    bb_xmax = gs_max a.bb_xmax b.bb_xmax;
    bb_ymax = gs_max a.bb_ymax b.bb_ymax }

let rec geo_bbox_of_points_acc (pts : list geo_point) (acc : geo_bbox)
  : Tot geo_bbox (decreases pts) =
  match pts with
  | [] -> acc
  | p :: rest -> geo_bbox_of_points_acc rest (geo_bbox_union acc (geo_bbox_of_point p))

// None for an empty point list (no bbox for the empty geometry forms).
let geo_bbox_of_points (pts : list geo_point) : option geo_bbox =
  match pts with
  | [] -> None
  | p :: rest -> Some (geo_bbox_of_points_acc rest (geo_bbox_of_point p))

let geo_bbox_of_ring (r : geo_ring) : option geo_bbox = geo_bbox_of_points r

let geo_bbox_union_opt (a b : option geo_bbox) : option geo_bbox =
  match a, b with
  | None, x -> x
  | x, None -> x
  | Some ba, Some bb -> Some (geo_bbox_union ba bb)

let rec geo_bbox_of_rings (rs : list geo_ring) : Tot (option geo_bbox) (decreases rs) =
  match rs with
  | [] -> None
  | r :: rest -> geo_bbox_union_opt (geo_bbox_of_ring r) (geo_bbox_of_rings rest)

let geo_bbox_of_polygon (p : geo_polygon) : option geo_bbox = geo_bbox_of_ring p.gpoly_ext

let rec geo_bbox_of_polygons (ps : list geo_polygon) : Tot (option geo_bbox) (decreases ps) =
  match ps with
  | [] -> None
  | p :: rest -> geo_bbox_union_opt (geo_bbox_of_polygon p) (geo_bbox_of_polygons rest)

let rec geo_bbox_of_linestrings (ls : list (list geo_point)) : Tot (option geo_bbox) (decreases ls) =
  match ls with
  | [] -> None
  | l :: rest -> geo_bbox_union_opt (geo_bbox_of_points l) (geo_bbox_of_linestrings rest)

let rec geo_bbox_of_geometry (g : geo_geometry) : Tot (option geo_bbox) (decreases g) =
  match g with
  | G_Point p -> Some (geo_bbox_of_point p)
  | G_LineString l -> geo_bbox_of_points l
  | G_Polygon p -> geo_bbox_of_polygon p
  | G_MultiPoint pts -> geo_bbox_of_points pts
  | G_MultiLineString ls -> geo_bbox_of_linestrings ls
  | G_MultiPolygon ps -> geo_bbox_of_polygons ps
  | G_GeometryCollection gs -> geo_bbox_of_geometry_list gs
  | G_Empty _ -> None
and geo_bbox_of_geometry_list (gs : list geo_geometry) : Tot (option geo_bbox) (decreases gs) =
  match gs with
  | [] -> None
  | g :: rest -> geo_bbox_union_opt (geo_bbox_of_geometry g) (geo_bbox_of_geometry_list rest)

(* ---------------------------------------------------------------- *)
(* BBox relations                                                     *)
(* ---------------------------------------------------------------- *)

let geo_bbox_intersects (a b : geo_bbox) : bool =
  not (gs_gt a.bb_xmin b.bb_xmax || gs_gt b.bb_xmin a.bb_xmax ||
       gs_gt a.bb_ymin b.bb_ymax || gs_gt b.bb_ymin a.bb_ymax)

let geo_bbox_disjoint (a b : geo_bbox) : bool = not (geo_bbox_intersects a b)

// a contains b
let geo_bbox_contains (a b : geo_bbox) : bool =
  gs_le a.bb_xmin b.bb_xmin && gs_ge a.bb_xmax b.bb_xmax &&
  gs_le a.bb_ymin b.bb_ymin && gs_ge a.bb_ymax b.bb_ymax

let geo_bbox_eq (a b : geo_bbox) : bool =
  gs_eq a.bb_xmin b.bb_xmin && gs_eq a.bb_xmax b.bb_xmax &&
  gs_eq a.bb_ymin b.bb_ymin && gs_eq a.bb_ymax b.bb_ymax

// The bbox as a closed rectangular ring, exterior-ring-only polygon
// (for geof:envelope — RDF.Geo.Functions.fst turns this into WKT).
let geo_bbox_to_polygon (b : geo_bbox) : geo_polygon =
  { gpoly_ext = [ { gp_x = b.bb_xmin; gp_y = b.bb_ymin };
                  { gp_x = b.bb_xmax; gp_y = b.bb_ymin };
                  { gp_x = b.bb_xmax; gp_y = b.bb_ymax };
                  { gp_x = b.bb_xmin; gp_y = b.bb_ymax };
                  { gp_x = b.bb_xmin; gp_y = b.bb_ymin } ];
    gpoly_holes = [] }
