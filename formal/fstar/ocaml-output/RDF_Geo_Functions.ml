open Prims
let rec isqrt_search (n : Prims.nat) (lo : Prims.nat) (hi : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then lo
  else
    if lo >= hi
    then lo
    else
      (let mid = ((lo + hi) + Prims.int_one) / (Prims.of_int (2)) in
       if (mid * mid) <= n
       then isqrt_search n mid hi (fuel - Prims.int_one)
       else isqrt_search n lo (mid - Prims.int_one) (fuel - Prims.int_one))
let isqrt (n : Prims.nat) : Prims.nat=
  if n = Prims.int_zero
  then Prims.int_zero
  else
    isqrt_search n Prims.int_zero (n + Prims.int_one)
      (n + (Prims.of_int (2)))
let geo_distance_precision_extra_digits : Prims.nat= (Prims.of_int (9))
let geo_distance_squared (p1 : RDF_Geo_Types.geo_point)
  (p2 : RDF_Geo_Types.geo_point) : RDF_Geo_Types.geo_scaled=
  let dx = RDF_Geo_Types.gs_sub p1.RDF_Geo_Types.gp_x p2.RDF_Geo_Types.gp_x in
  let dy = RDF_Geo_Types.gs_sub p1.RDF_Geo_Types.gp_y p2.RDF_Geo_Types.gp_y in
  RDF_Geo_Types.gs_add (RDF_Geo_Types.gs_mul dx dx)
    (RDF_Geo_Types.gs_mul dy dy)
let geo_sqrt_approx (v : RDF_Geo_Types.geo_scaled) :
  RDF_Geo_Types.geo_scaled=
  let s = v.RDF_Geo_Types.gs_scale in
  let out_scale = s + geo_distance_precision_extra_digits in
  let shift = (out_scale + out_scale) - s in
  let m =
    if v.RDF_Geo_Types.gs_mantissa < Prims.int_zero
    then Prims.int_zero
    else v.RDF_Geo_Types.gs_mantissa in
  let arg = m * (RDF_Geo_Types.geo_pow10 shift) in
  {
    RDF_Geo_Types.gs_mantissa = (isqrt arg);
    RDF_Geo_Types.gs_scale = out_scale
  }
let geo_distance (g1 : RDF_Geo_Types.geo_geometry)
  (g2 : RDF_Geo_Types.geo_geometry) :
  RDF_Geo_Types.geo_scaled FStar_Pervasives_Native.option=
  match (g1, g2) with
  | (RDF_Geo_Types.G_Point p1, RDF_Geo_Types.G_Point p2) ->
      FStar_Pervasives_Native.Some
        (geo_sqrt_approx (geo_distance_squared p1 p2))
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let geo_envelope (g : RDF_Geo_Types.geo_geometry) :
  RDF_Geo_Types.geo_geometry FStar_Pervasives_Native.option=
  match RDF_Geo_BBox.geo_bbox_of_geometry g with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some b ->
      FStar_Pervasives_Native.Some
        (RDF_Geo_Types.G_Polygon (RDF_Geo_BBox.geo_bbox_to_polygon b))
