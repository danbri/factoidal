open Prims
type geo_bbox =
  {
  bb_xmin: RDF_Geo_Types.geo_scaled ;
  bb_ymin: RDF_Geo_Types.geo_scaled ;
  bb_xmax: RDF_Geo_Types.geo_scaled ;
  bb_ymax: RDF_Geo_Types.geo_scaled }
let __proj__Mkgeo_bbox__item__bb_xmin (projectee : geo_bbox) :
  RDF_Geo_Types.geo_scaled=
  match projectee with | { bb_xmin; bb_ymin; bb_xmax; bb_ymax;_} -> bb_xmin
let __proj__Mkgeo_bbox__item__bb_ymin (projectee : geo_bbox) :
  RDF_Geo_Types.geo_scaled=
  match projectee with | { bb_xmin; bb_ymin; bb_xmax; bb_ymax;_} -> bb_ymin
let __proj__Mkgeo_bbox__item__bb_xmax (projectee : geo_bbox) :
  RDF_Geo_Types.geo_scaled=
  match projectee with | { bb_xmin; bb_ymin; bb_xmax; bb_ymax;_} -> bb_xmax
let __proj__Mkgeo_bbox__item__bb_ymax (projectee : geo_bbox) :
  RDF_Geo_Types.geo_scaled=
  match projectee with | { bb_xmin; bb_ymin; bb_xmax; bb_ymax;_} -> bb_ymax
let geo_bbox_of_point (p : RDF_Geo_Types.geo_point) : geo_bbox=
  {
    bb_xmin = (p.RDF_Geo_Types.gp_x);
    bb_ymin = (p.RDF_Geo_Types.gp_y);
    bb_xmax = (p.RDF_Geo_Types.gp_x);
    bb_ymax = (p.RDF_Geo_Types.gp_y)
  }
let geo_bbox_union (a : geo_bbox) (b : geo_bbox) : geo_bbox=
  {
    bb_xmin = (RDF_Geo_Types.gs_min a.bb_xmin b.bb_xmin);
    bb_ymin = (RDF_Geo_Types.gs_min a.bb_ymin b.bb_ymin);
    bb_xmax = (RDF_Geo_Types.gs_max a.bb_xmax b.bb_xmax);
    bb_ymax = (RDF_Geo_Types.gs_max a.bb_ymax b.bb_ymax)
  }
let rec geo_bbox_of_points_acc (pts : RDF_Geo_Types.geo_point Prims.list)
  (acc : geo_bbox) : geo_bbox=
  match pts with
  | [] -> acc
  | p::rest ->
      geo_bbox_of_points_acc rest (geo_bbox_union acc (geo_bbox_of_point p))
let geo_bbox_of_points (pts : RDF_Geo_Types.geo_point Prims.list) :
  geo_bbox FStar_Pervasives_Native.option=
  match pts with
  | [] -> FStar_Pervasives_Native.None
  | p::rest ->
      FStar_Pervasives_Native.Some
        (geo_bbox_of_points_acc rest (geo_bbox_of_point p))
let geo_bbox_of_ring (r : RDF_Geo_Types.geo_ring) :
  geo_bbox FStar_Pervasives_Native.option= geo_bbox_of_points r
let geo_bbox_union_opt (a : geo_bbox FStar_Pervasives_Native.option)
  (b : geo_bbox FStar_Pervasives_Native.option) :
  geo_bbox FStar_Pervasives_Native.option=
  match (a, b) with
  | (FStar_Pervasives_Native.None, x) -> x
  | (x, FStar_Pervasives_Native.None) -> x
  | (FStar_Pervasives_Native.Some ba, FStar_Pervasives_Native.Some bb) ->
      FStar_Pervasives_Native.Some (geo_bbox_union ba bb)
let rec geo_bbox_of_rings (rs : RDF_Geo_Types.geo_ring Prims.list) :
  geo_bbox FStar_Pervasives_Native.option=
  match rs with
  | [] -> FStar_Pervasives_Native.None
  | r::rest ->
      geo_bbox_union_opt (geo_bbox_of_ring r) (geo_bbox_of_rings rest)
let geo_bbox_of_polygon (p : RDF_Geo_Types.geo_polygon) :
  geo_bbox FStar_Pervasives_Native.option=
  geo_bbox_of_ring p.RDF_Geo_Types.gpoly_ext
let rec geo_bbox_of_polygons (ps : RDF_Geo_Types.geo_polygon Prims.list) :
  geo_bbox FStar_Pervasives_Native.option=
  match ps with
  | [] -> FStar_Pervasives_Native.None
  | p::rest ->
      geo_bbox_union_opt (geo_bbox_of_polygon p) (geo_bbox_of_polygons rest)
let rec geo_bbox_of_linestrings
  (ls : RDF_Geo_Types.geo_point Prims.list Prims.list) :
  geo_bbox FStar_Pervasives_Native.option=
  match ls with
  | [] -> FStar_Pervasives_Native.None
  | l::rest ->
      geo_bbox_union_opt (geo_bbox_of_points l)
        (geo_bbox_of_linestrings rest)
let rec geo_bbox_of_geometry (g : RDF_Geo_Types.geo_geometry) :
  geo_bbox FStar_Pervasives_Native.option=
  match g with
  | RDF_Geo_Types.G_Point p ->
      FStar_Pervasives_Native.Some (geo_bbox_of_point p)
  | RDF_Geo_Types.G_LineString l -> geo_bbox_of_points l
  | RDF_Geo_Types.G_Polygon p -> geo_bbox_of_polygon p
  | RDF_Geo_Types.G_MultiPoint pts -> geo_bbox_of_points pts
  | RDF_Geo_Types.G_MultiLineString ls -> geo_bbox_of_linestrings ls
  | RDF_Geo_Types.G_MultiPolygon ps -> geo_bbox_of_polygons ps
  | RDF_Geo_Types.G_GeometryCollection gs -> geo_bbox_of_geometry_list gs
  | RDF_Geo_Types.G_Empty uu___ -> FStar_Pervasives_Native.None
and geo_bbox_of_geometry_list (gs : RDF_Geo_Types.geo_geometry Prims.list) :
  geo_bbox FStar_Pervasives_Native.option=
  match gs with
  | [] -> FStar_Pervasives_Native.None
  | g::rest ->
      geo_bbox_union_opt (geo_bbox_of_geometry g)
        (geo_bbox_of_geometry_list rest)
let geo_bbox_intersects (a : geo_bbox) (b : geo_bbox) : Prims.bool=
  Prims.op_Negation
    ((((RDF_Geo_Types.gs_gt a.bb_xmin b.bb_xmax) ||
         (RDF_Geo_Types.gs_gt b.bb_xmin a.bb_xmax))
        || (RDF_Geo_Types.gs_gt a.bb_ymin b.bb_ymax))
       || (RDF_Geo_Types.gs_gt b.bb_ymin a.bb_ymax))
let geo_bbox_disjoint (a : geo_bbox) (b : geo_bbox) : Prims.bool=
  Prims.op_Negation (geo_bbox_intersects a b)
let geo_bbox_contains (a : geo_bbox) (b : geo_bbox) : Prims.bool=
  (((RDF_Geo_Types.gs_le a.bb_xmin b.bb_xmin) &&
      (RDF_Geo_Types.gs_ge a.bb_xmax b.bb_xmax))
     && (RDF_Geo_Types.gs_le a.bb_ymin b.bb_ymin))
    && (RDF_Geo_Types.gs_ge a.bb_ymax b.bb_ymax)
let geo_bbox_eq (a : geo_bbox) (b : geo_bbox) : Prims.bool=
  (((RDF_Geo_Types.gs_eq a.bb_xmin b.bb_xmin) &&
      (RDF_Geo_Types.gs_eq a.bb_xmax b.bb_xmax))
     && (RDF_Geo_Types.gs_eq a.bb_ymin b.bb_ymin))
    && (RDF_Geo_Types.gs_eq a.bb_ymax b.bb_ymax)
let geo_bbox_to_polygon (b : geo_bbox) : RDF_Geo_Types.geo_polygon=
  {
    RDF_Geo_Types.gpoly_ext =
      [{ RDF_Geo_Types.gp_x = (b.bb_xmin); RDF_Geo_Types.gp_y = (b.bb_ymin) };
      { RDF_Geo_Types.gp_x = (b.bb_xmax); RDF_Geo_Types.gp_y = (b.bb_ymin) };
      { RDF_Geo_Types.gp_x = (b.bb_xmax); RDF_Geo_Types.gp_y = (b.bb_ymax) };
      { RDF_Geo_Types.gp_x = (b.bb_xmin); RDF_Geo_Types.gp_y = (b.bb_ymax) };
      { RDF_Geo_Types.gp_x = (b.bb_xmin); RDF_Geo_Types.gp_y = (b.bb_ymin) }];
    RDF_Geo_Types.gpoly_holes = []
  }
