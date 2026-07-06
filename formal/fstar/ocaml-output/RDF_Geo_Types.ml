open Prims
type geo_scaled = {
  gs_mantissa: Prims.int ;
  gs_scale: Prims.nat }
let __proj__Mkgeo_scaled__item__gs_mantissa (projectee : geo_scaled) :
  Prims.int= match projectee with | { gs_mantissa; gs_scale;_} -> gs_mantissa
let __proj__Mkgeo_scaled__item__gs_scale (projectee : geo_scaled) :
  Prims.nat= match projectee with | { gs_mantissa; gs_scale;_} -> gs_scale
let rec geo_pow10 (n : Prims.nat) : Prims.nat=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (geo_pow10 (n - Prims.int_one))
let gs_of_int (i : Prims.int) : geo_scaled=
  { gs_mantissa = i; gs_scale = Prims.int_zero }
let gs_zero : geo_scaled= gs_of_int Prims.int_zero
let gs_align (a : geo_scaled) (b : geo_scaled) :
  (Prims.int * Prims.int * Prims.nat)=
  if a.gs_scale = b.gs_scale
  then ((a.gs_mantissa), (b.gs_mantissa), (a.gs_scale))
  else
    if a.gs_scale < b.gs_scale
    then
      ((a.gs_mantissa * (geo_pow10 (b.gs_scale - a.gs_scale))),
        (b.gs_mantissa), (b.gs_scale))
    else
      ((a.gs_mantissa),
        (b.gs_mantissa * (geo_pow10 (a.gs_scale - b.gs_scale))),
        (a.gs_scale))
let gs_add (a : geo_scaled) (b : geo_scaled) : geo_scaled=
  let uu___ = gs_align a b in
  match uu___ with
  | (am, bm, sc) -> { gs_mantissa = (am + bm); gs_scale = sc }
let gs_sub (a : geo_scaled) (b : geo_scaled) : geo_scaled=
  let uu___ = gs_align a b in
  match uu___ with
  | (am, bm, sc) -> { gs_mantissa = (am - bm); gs_scale = sc }
let gs_neg (a : geo_scaled) : geo_scaled=
  { gs_mantissa = (Prims.int_zero - a.gs_mantissa); gs_scale = (a.gs_scale) }
let gs_mul (a : geo_scaled) (b : geo_scaled) : geo_scaled=
  {
    gs_mantissa = (a.gs_mantissa * b.gs_mantissa);
    gs_scale = (a.gs_scale + b.gs_scale)
  }
let gs_cmp (a : geo_scaled) (b : geo_scaled) : Prims.int=
  let uu___ = gs_align a b in
  match uu___ with
  | (am, bm, uu___1) ->
      if am < bm
      then (Prims.of_int (-1))
      else if am > bm then Prims.int_one else Prims.int_zero
let gs_eq (a : geo_scaled) (b : geo_scaled) : Prims.bool=
  (gs_cmp a b) = Prims.int_zero
let gs_lt (a : geo_scaled) (b : geo_scaled) : Prims.bool=
  (gs_cmp a b) < Prims.int_zero
let gs_le (a : geo_scaled) (b : geo_scaled) : Prims.bool=
  (gs_cmp a b) <= Prims.int_zero
let gs_gt (a : geo_scaled) (b : geo_scaled) : Prims.bool=
  (gs_cmp a b) > Prims.int_zero
let gs_ge (a : geo_scaled) (b : geo_scaled) : Prims.bool=
  (gs_cmp a b) >= Prims.int_zero
let gs_sign (a : geo_scaled) : Prims.int=
  if a.gs_mantissa < Prims.int_zero
  then (Prims.of_int (-1))
  else
    if a.gs_mantissa > Prims.int_zero then Prims.int_one else Prims.int_zero
let gs_min (a : geo_scaled) (b : geo_scaled) : geo_scaled=
  if gs_le a b then a else b
let gs_max (a : geo_scaled) (b : geo_scaled) : geo_scaled=
  if gs_ge a b then a else b
let gs_abs (a : geo_scaled) : geo_scaled=
  if a.gs_mantissa < Prims.int_zero then gs_neg a else a
let rec geo_zeros (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then ""
  else Prims.strcat "0" (geo_zeros (n - Prims.int_one))
let geo_pad_left_zeros (s : Prims.string) (target : Prims.nat) :
  Prims.string=
  let len = FStar_String.strlen s in
  if len >= target then s else Prims.strcat (geo_zeros (target - len)) s
let gs_to_string (a : geo_scaled) : Prims.string=
  if a.gs_scale = Prims.int_zero
  then Prims.string_of_int a.gs_mantissa
  else
    (let is_neg = a.gs_mantissa < Prims.int_zero in
     let av =
       if is_neg then Prims.int_zero - a.gs_mantissa else a.gs_mantissa in
     let p = geo_pow10 a.gs_scale in
     let int_part = av / p in
     let frac_part = av - (int_part * p) in
     let frac_str =
       geo_pad_left_zeros (Prims.string_of_int frac_part) a.gs_scale in
     Prims.strcat (if is_neg then "-" else "")
       (Prims.strcat (Prims.string_of_int int_part)
          (Prims.strcat "." frac_str)))
type geo_point = {
  gp_x: geo_scaled ;
  gp_y: geo_scaled }
let __proj__Mkgeo_point__item__gp_x (projectee : geo_point) : geo_scaled=
  match projectee with | { gp_x; gp_y;_} -> gp_x
let __proj__Mkgeo_point__item__gp_y (projectee : geo_point) : geo_scaled=
  match projectee with | { gp_x; gp_y;_} -> gp_y
type geo_ring = geo_point Prims.list
type geo_polygon = {
  gpoly_ext: geo_ring ;
  gpoly_holes: geo_ring Prims.list }
let __proj__Mkgeo_polygon__item__gpoly_ext (projectee : geo_polygon) :
  geo_ring= match projectee with | { gpoly_ext; gpoly_holes;_} -> gpoly_ext
let __proj__Mkgeo_polygon__item__gpoly_holes (projectee : geo_polygon) :
  geo_ring Prims.list=
  match projectee with | { gpoly_ext; gpoly_holes;_} -> gpoly_holes
type geo_kind =
  | GK_Point 
  | GK_LineString 
  | GK_Polygon 
  | GK_MultiPoint 
  | GK_MultiLineString 
  | GK_MultiPolygon 
  | GK_GeometryCollection 
let uu___is_GK_Point (projectee : geo_kind) : Prims.bool=
  match projectee with | GK_Point -> true | uu___ -> false
let uu___is_GK_LineString (projectee : geo_kind) : Prims.bool=
  match projectee with | GK_LineString -> true | uu___ -> false
let uu___is_GK_Polygon (projectee : geo_kind) : Prims.bool=
  match projectee with | GK_Polygon -> true | uu___ -> false
let uu___is_GK_MultiPoint (projectee : geo_kind) : Prims.bool=
  match projectee with | GK_MultiPoint -> true | uu___ -> false
let uu___is_GK_MultiLineString (projectee : geo_kind) : Prims.bool=
  match projectee with | GK_MultiLineString -> true | uu___ -> false
let uu___is_GK_MultiPolygon (projectee : geo_kind) : Prims.bool=
  match projectee with | GK_MultiPolygon -> true | uu___ -> false
let uu___is_GK_GeometryCollection (projectee : geo_kind) : Prims.bool=
  match projectee with | GK_GeometryCollection -> true | uu___ -> false
type geo_geometry =
  | G_Point of geo_point 
  | G_LineString of geo_point Prims.list 
  | G_Polygon of geo_polygon 
  | G_MultiPoint of geo_point Prims.list 
  | G_MultiLineString of geo_point Prims.list Prims.list 
  | G_MultiPolygon of geo_polygon Prims.list 
  | G_GeometryCollection of geo_geometry Prims.list 
  | G_Empty of geo_kind 
let uu___is_G_Point (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_Point _0 -> true | uu___ -> false
let __proj__G_Point__item___0 (projectee : geo_geometry) : geo_point=
  match projectee with | G_Point _0 -> _0
let uu___is_G_LineString (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_LineString _0 -> true | uu___ -> false
let __proj__G_LineString__item___0 (projectee : geo_geometry) :
  geo_point Prims.list= match projectee with | G_LineString _0 -> _0
let uu___is_G_Polygon (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_Polygon _0 -> true | uu___ -> false
let __proj__G_Polygon__item___0 (projectee : geo_geometry) : geo_polygon=
  match projectee with | G_Polygon _0 -> _0
let uu___is_G_MultiPoint (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_MultiPoint _0 -> true | uu___ -> false
let __proj__G_MultiPoint__item___0 (projectee : geo_geometry) :
  geo_point Prims.list= match projectee with | G_MultiPoint _0 -> _0
let uu___is_G_MultiLineString (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_MultiLineString _0 -> true | uu___ -> false
let __proj__G_MultiLineString__item___0 (projectee : geo_geometry) :
  geo_point Prims.list Prims.list=
  match projectee with | G_MultiLineString _0 -> _0
let uu___is_G_MultiPolygon (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_MultiPolygon _0 -> true | uu___ -> false
let __proj__G_MultiPolygon__item___0 (projectee : geo_geometry) :
  geo_polygon Prims.list= match projectee with | G_MultiPolygon _0 -> _0
let uu___is_G_GeometryCollection (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_GeometryCollection _0 -> true | uu___ -> false
let __proj__G_GeometryCollection__item___0 (projectee : geo_geometry) :
  geo_geometry Prims.list=
  match projectee with | G_GeometryCollection _0 -> _0
let uu___is_G_Empty (projectee : geo_geometry) : Prims.bool=
  match projectee with | G_Empty _0 -> true | uu___ -> false
let __proj__G_Empty__item___0 (projectee : geo_geometry) : geo_kind=
  match projectee with | G_Empty _0 -> _0
type geo_wkt_value =
  {
  gw_crs: Prims.string FStar_Pervasives_Native.option ;
  gw_geom: geo_geometry }
let __proj__Mkgeo_wkt_value__item__gw_crs (projectee : geo_wkt_value) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { gw_crs; gw_geom;_} -> gw_crs
let __proj__Mkgeo_wkt_value__item__gw_geom (projectee : geo_wkt_value) :
  geo_geometry= match projectee with | { gw_crs; gw_geom;_} -> gw_geom
let geo_kind_of (g : geo_geometry) : geo_kind=
  match g with
  | G_Point uu___ -> GK_Point
  | G_LineString uu___ -> GK_LineString
  | G_Polygon uu___ -> GK_Polygon
  | G_MultiPoint uu___ -> GK_MultiPoint
  | G_MultiLineString uu___ -> GK_MultiLineString
  | G_MultiPolygon uu___ -> GK_MultiPolygon
  | G_GeometryCollection uu___ -> GK_GeometryCollection
  | G_Empty k -> k
let geo_ns : Prims.string= "http://www.opengis.net/ont/geosparql#"
let geo_wktLiteral : RDF_Term.wf_iri=
  "http://www.opengis.net/ont/geosparql#wktLiteral"
let geof_ns : Prims.string= "http://www.opengis.net/def/function/geosparql/"
let geo_crs84 : RDF_Term.wf_iri=
  "http://www.opengis.net/def/crs/OGC/1.3/CRS84"
let geo_point_eq (a : geo_point) (b : geo_point) : Prims.bool=
  (gs_eq a.gp_x b.gp_x) && (gs_eq a.gp_y b.gp_y)
let rec geo_last_point (pts : geo_point Prims.list) :
  geo_point FStar_Pervasives_Native.option=
  match pts with
  | [] -> FStar_Pervasives_Native.None
  | p::[] -> FStar_Pervasives_Native.Some p
  | uu___::rest -> geo_last_point rest
let geo_wf_ring (r : geo_ring) : Prims.bool=
  if (FStar_List_Tot_Base.length r) < (Prims.of_int (4))
  then false
  else
    (match (r, (geo_last_point r)) with
     | (first::uu___1, FStar_Pervasives_Native.Some last) ->
         geo_point_eq first last
     | (uu___1, uu___2) -> false)
let geo_wf_linestring (l : geo_point Prims.list) : Prims.bool=
  (FStar_List_Tot_Base.length l) >= (Prims.of_int (2))
let geo_wf_polygon (p : geo_polygon) : Prims.bool=
  (geo_wf_ring p.gpoly_ext) &&
    (FStar_List_Tot_Base.for_all geo_wf_ring p.gpoly_holes)
let geo_is_closed_line (l : geo_point Prims.list) : Prims.bool=
  match (l, (geo_last_point l)) with
  | (first::uu___, FStar_Pervasives_Native.Some last) ->
      geo_point_eq first last
  | (uu___, uu___1) -> false
let rec geo_wf_geometry (g : geo_geometry) : Prims.bool=
  match g with
  | G_Point uu___ -> true
  | G_LineString l -> geo_wf_linestring l
  | G_Polygon p -> geo_wf_polygon p
  | G_MultiPoint uu___ -> true
  | G_MultiLineString ls -> FStar_List_Tot_Base.for_all geo_wf_linestring ls
  | G_MultiPolygon ps -> FStar_List_Tot_Base.for_all geo_wf_polygon ps
  | G_GeometryCollection gs -> geo_wf_geometry_list gs
  | G_Empty uu___ -> true
and geo_wf_geometry_list (gs : geo_geometry Prims.list) : Prims.bool=
  match gs with
  | [] -> true
  | g::rest -> (geo_wf_geometry g) && (geo_wf_geometry_list rest)
let rec geo_combine_exists
  (xs : Prims.bool FStar_Pervasives_Native.option Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.Some false
  | (FStar_Pervasives_Native.Some true)::uu___ ->
      FStar_Pervasives_Native.Some true
  | (FStar_Pervasives_Native.Some false)::rest -> geo_combine_exists rest
  | (FStar_Pervasives_Native.None)::rest ->
      (match geo_combine_exists rest with
       | FStar_Pervasives_Native.Some true ->
           FStar_Pervasives_Native.Some true
       | uu___ -> FStar_Pervasives_Native.None)
let rec geo_combine_forall
  (xs : Prims.bool FStar_Pervasives_Native.option Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.Some true
  | (FStar_Pervasives_Native.Some false)::uu___ ->
      FStar_Pervasives_Native.Some false
  | (FStar_Pervasives_Native.Some true)::rest -> geo_combine_forall rest
  | (FStar_Pervasives_Native.None)::rest ->
      (match geo_combine_forall rest with
       | FStar_Pervasives_Native.Some false ->
           FStar_Pervasives_Native.Some false
       | uu___ -> FStar_Pervasives_Native.None)
