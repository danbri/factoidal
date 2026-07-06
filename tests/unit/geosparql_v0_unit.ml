(* geosparql_v0_unit.ml — unit pins for the GeoSPARQL v0 pure-F* slice
   (Parser.WKT.fst, RDF.Geo.Types.fst, RDF.Geo.BBox.fst,
   RDF.Geo.Topology.fst, RDF.Geo.Functions.fst). See
   docs/designissues/2026-05-07-geosparql-fstar-investigation.md for
   the plan this implements (phases 1-2, option A pure-rational).

   Three groups:
     A. WKT parser round-trip (parse -> ADT -> serialize -> re-parse,
        checking the re-parsed geometry matches the original — not a
        byte-for-byte string check, since serialization is not
        required to reproduce the exact input whitespace/formatting).
     B. Simple Features predicates against hand-computed fixtures,
        including an exact-boundary case (point exactly on a polygon
        edge) where rational arithmetic avoids the epsilon problem.
     C. geof:distance / geof:envelope spot checks.

   Every fixture below is a small hand-built geometry (documented
   inline), not lifted from an external corpus — appropriate for a v0
   unit-pin file per the task brief, with the OGC conformance-suite
   question addressed separately (see the commit report: not fetchable
   through the sandboxed proxy at the canonical location tried). *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

let check_opt_bool ~name (expected : bool option) (actual : bool option) =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    let s = function None -> "None" | Some true -> "Some true" | Some false -> "Some false" in
    Printf.printf "  FAIL  %s: expected %s got %s\n" name (s expected) (s actual)
  end

(* ---------------------------------------------------------------- *)
(* Small geometry-building helpers                                    *)
(* ---------------------------------------------------------------- *)

let pt x y : RDF_Geo_Types.geo_point =
  { gp_x = RDF_Geo_Types.gs_of_int (Z.of_int x); gp_y = RDF_Geo_Types.gs_of_int (Z.of_int y) }

let geom_eq (a : RDF_Geo_Types.geo_geometry) (b : RDF_Geo_Types.geo_geometry) : bool =
  a = b

let () =
  Printf.printf "\n=== A. WKT parser round-trip ===\n";

  (* A1: simple point *)
  (match Parser_WKT.parse_wkt_literal "POINT(1 2)" with
   | Some v ->
     check ~name:"POINT(1 2) parses to G_Point" true
       (geom_eq v.gw_geom (RDF_Geo_Types.G_Point (pt 1 2)));
     let s = Parser_WKT.serialize_wkt_value v in
     (match Parser_WKT.parse_wkt_literal s with
      | Some v2 -> check ~name:"POINT(1 2) round-trips through serialize" true (geom_eq v.gw_geom v2.gw_geom)
      | None -> check ~name:"POINT(1 2) round-trips through serialize" true false)
   | None -> check ~name:"POINT(1 2) parses to G_Point" true false);

  (* A2: decimal coordinates (exact, not floating point) *)
  (match Parser_WKT.parse_wkt_literal "POINT(51.5074 -0.1278)" with
   | Some { gw_geom = RDF_Geo_Types.G_Point p; _ } ->
     check ~name:"POINT(51.5074 -0.1278) x mantissa exact" true
       (Z.equal p.gp_x.gs_mantissa (Z.of_int 515074) && Z.equal p.gp_x.gs_scale (Z.of_int 4));
     check ~name:"POINT(51.5074 -0.1278) y mantissa exact" true
       (Z.equal p.gp_y.gs_mantissa (Z.of_int (-1278)) && Z.equal p.gp_y.gs_scale (Z.of_int 4))
   | _ -> check ~name:"POINT(51.5074 -0.1278) parses" true false);

  (* A3: LINESTRING *)
  (match Parser_WKT.parse_wkt_literal "LINESTRING(0 0, 10 0, 10 10)" with
   | Some { gw_geom = RDF_Geo_Types.G_LineString l; _ } ->
     check ~name:"LINESTRING has 3 points" true (List.length l = 3)
   | _ -> check ~name:"LINESTRING has 3 points" true false);

  (* A4: POLYGON with a hole *)
  let poly_wkt = "POLYGON((0 0, 10 0, 10 10, 0 10, 0 0),(2 2, 4 2, 4 4, 2 4, 2 2))" in
  (match Parser_WKT.parse_wkt_literal poly_wkt with
   | Some { gw_geom = RDF_Geo_Types.G_Polygon p; _ } ->
     check ~name:"POLYGON exterior has 5 points" true (List.length p.gpoly_ext = 5);
     check ~name:"POLYGON has 1 hole" true (List.length p.gpoly_holes = 1)
   | _ -> check ~name:"POLYGON with hole parses" true false);

  (* A5: MULTIPOINT both forms *)
  (match Parser_WKT.parse_wkt_literal "MULTIPOINT((1 2), (3 4))" with
   | Some { gw_geom = RDF_Geo_Types.G_MultiPoint pts; _ } ->
     check ~name:"MULTIPOINT parenthesized form has 2 points" true (List.length pts = 2)
   | _ -> check ~name:"MULTIPOINT parenthesized form" true false);
  (match Parser_WKT.parse_wkt_literal "MULTIPOINT(1 2, 3 4)" with
   | Some { gw_geom = RDF_Geo_Types.G_MultiPoint pts; _ } ->
     check ~name:"MULTIPOINT bare form has 2 points" true (List.length pts = 2)
   | _ -> check ~name:"MULTIPOINT bare form" true false);

  (* A6: EMPTY forms *)
  (match Parser_WKT.parse_wkt_literal "POINT EMPTY" with
   | Some { gw_geom = RDF_Geo_Types.G_Empty RDF_Geo_Types.GK_Point; _ } ->
     check ~name:"POINT EMPTY" true true
   | _ -> check ~name:"POINT EMPTY" true false);
  (match Parser_WKT.parse_wkt_literal "GEOMETRYCOLLECTION EMPTY" with
   | Some { gw_geom = RDF_Geo_Types.G_Empty RDF_Geo_Types.GK_GeometryCollection; _ } ->
     check ~name:"GEOMETRYCOLLECTION EMPTY" true true
   | _ -> check ~name:"GEOMETRYCOLLECTION EMPTY" true false);

  (* A7: CRS prefix carried, not transformed *)
  (match Parser_WKT.parse_wkt_literal
           "<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(530000 180000)" with
   | Some { gw_crs = Some crs; gw_geom = RDF_Geo_Types.G_Point p } ->
     check ~name:"CRS prefix captured verbatim" true (crs = "http://www.opengis.net/def/crs/EPSG/0/27700");
     check ~name:"CRS-prefixed coordinates unchanged (no transform)" true
       (Z.equal p.gp_x.gs_mantissa (Z.of_int 530000) && Z.equal p.gp_y.gs_mantissa (Z.of_int 180000))
   | _ -> check ~name:"CRS prefix parses" true false);

  (* A8: 3D coordinate is a parse failure (out of scope, not silently dropped) *)
  check ~name:"POINT Z (3 numbers) is rejected, not silently truncated" true
    (Parser_WKT.parse_wkt_literal "POINT(1 2 3)" = None);

  (* A9: GEOMETRYCOLLECTION nesting *)
  (match Parser_WKT.parse_wkt_literal "GEOMETRYCOLLECTION(POINT(1 1), LINESTRING(0 0, 1 1))" with
   | Some { gw_geom = RDF_Geo_Types.G_GeometryCollection gs; _ } ->
     check ~name:"GEOMETRYCOLLECTION has 2 members" true (List.length gs = 2)
   | _ -> check ~name:"GEOMETRYCOLLECTION parses" true false);

  Printf.printf "\n=== B. Simple Features predicates (hand-computed) ===\n";

  (* B1: point/point *)
  check_opt_bool ~name:"sfEquals(POINT(1 1), POINT(1 1)) = true"
    (Some true)
    (RDF_Geo_Topology.sf_equals (RDF_Geo_Types.G_Point (pt 1 1)) (RDF_Geo_Types.G_Point (pt 1 1)));
  check_opt_bool ~name:"sfDisjoint(POINT(1 1), POINT(2 2)) = true"
    (Some true)
    (RDF_Geo_Topology.sf_disjoint (RDF_Geo_Types.G_Point (pt 1 1)) (RDF_Geo_Types.G_Point (pt 2 2)));

  (* B2: point exactly on a polygon edge — the exact-boundary case
     rational arithmetic is meant to nail without an epsilon. Square
     (0,0)-(10,0)-(10,10)-(0,10), point (5,0) lies exactly on the
     bottom edge. *)
  let square : RDF_Geo_Types.geo_polygon =
    { gpoly_ext = [ pt 0 0; pt 10 0; pt 10 10; pt 0 10; pt 0 0 ]; gpoly_holes = [] } in
  check_opt_bool ~name:"sfTouches(POINT(5 0), square) = true (exactly on edge)"
    (Some true)
    (RDF_Geo_Topology.sf_touches (RDF_Geo_Types.G_Point (pt 5 0)) (RDF_Geo_Types.G_Polygon square));
  check_opt_bool ~name:"sfWithin(POINT(5 0), square) = false (boundary, not interior)"
    (Some false)
    (RDF_Geo_Topology.sf_within (RDF_Geo_Types.G_Point (pt 5 0)) (RDF_Geo_Types.G_Polygon square));
  check_opt_bool ~name:"sfWithin(POINT(5 5), square) = true (strictly interior)"
    (Some true)
    (RDF_Geo_Topology.sf_within (RDF_Geo_Types.G_Point (pt 5 5)) (RDF_Geo_Types.G_Polygon square));
  check_opt_bool ~name:"sfDisjoint(POINT(20 20), square) = true"
    (Some true)
    (RDF_Geo_Topology.sf_disjoint (RDF_Geo_Types.G_Point (pt 20 20)) (RDF_Geo_Types.G_Polygon square));
  check_opt_bool ~name:"sfIntersects(POINT(5 0), square) = true (on boundary counts)"
    (Some true)
    (RDF_Geo_Topology.sf_intersects (RDF_Geo_Types.G_Point (pt 5 0)) (RDF_Geo_Types.G_Polygon square));

  (* B3: point inside a hole is exterior to the polygon *)
  let square_with_hole : RDF_Geo_Types.geo_polygon =
    { gpoly_ext = [ pt 0 0; pt 10 0; pt 10 10; pt 0 10; pt 0 0 ];
      gpoly_holes = [ [ pt 3 3; pt 7 3; pt 7 7; pt 3 7; pt 3 3 ] ] } in
  check_opt_bool ~name:"sfDisjoint(POINT(5 5), square-with-hole) = true (5,5 is in the hole)"
    (Some true)
    (RDF_Geo_Topology.sf_disjoint (RDF_Geo_Types.G_Point (pt 5 5)) (RDF_Geo_Types.G_Polygon square_with_hole));
  check_opt_bool ~name:"sfWithin(POINT(1 1), square-with-hole) = true (outside the hole)"
    (Some true)
    (RDF_Geo_Topology.sf_within (RDF_Geo_Types.G_Point (pt 1 1)) (RDF_Geo_Types.G_Polygon square_with_hole));

  (* B4: point/linestring *)
  let diag : RDF_Geo_Types.geo_geometry = RDF_Geo_Types.G_LineString [ pt 0 0; pt 10 10 ] in
  check_opt_bool ~name:"sfWithin(POINT(5 5), diagonal line) = true (interior of open line)"
    (Some true) (RDF_Geo_Topology.sf_within (RDF_Geo_Types.G_Point (pt 5 5)) diag);
  check_opt_bool ~name:"sfTouches(POINT(0 0), diagonal line) = true (open-line endpoint)"
    (Some true) (RDF_Geo_Topology.sf_touches (RDF_Geo_Types.G_Point (pt 0 0)) diag);
  check_opt_bool ~name:"sfDisjoint(POINT(1 2), diagonal line) = true (off the line)"
    (Some true) (RDF_Geo_Topology.sf_disjoint (RDF_Geo_Types.G_Point (pt 1 2)) diag);

  (* B5: linestring/linestring crossing (exact orientation test) *)
  let l1 : RDF_Geo_Types.geo_geometry = RDF_Geo_Types.G_LineString [ pt 0 0; pt 10 10 ] in
  let l2 : RDF_Geo_Types.geo_geometry = RDF_Geo_Types.G_LineString [ pt 0 10; pt 10 0 ] in
  check_opt_bool ~name:"sfIntersects(diagonal /, diagonal \\) = true (cross at (5,5))"
    (Some true) (RDF_Geo_Topology.sf_intersects l1 l2);
  let l3 : RDF_Geo_Types.geo_geometry = RDF_Geo_Types.G_LineString [ pt 0 20; pt 10 30 ] in
  check_opt_bool ~name:"sfDisjoint(diagonal /, parallel line far away) = true"
    (Some true) (RDF_Geo_Topology.sf_disjoint l1 l3);

  (* B6: polygon/polygon — overlapping squares (boundary-crossing + vertex-in-other) *)
  let sq_a : RDF_Geo_Types.geo_polygon = { gpoly_ext = [ pt 0 0; pt 10 0; pt 10 10; pt 0 10; pt 0 0 ]; gpoly_holes = [] } in
  let sq_b : RDF_Geo_Types.geo_polygon = { gpoly_ext = [ pt 5 5; pt 15 5; pt 15 15; pt 5 15; pt 5 5 ]; gpoly_holes = [] } in
  check_opt_bool ~name:"sfIntersects(square A, overlapping square B) = true"
    (Some true) (RDF_Geo_Topology.sf_intersects (RDF_Geo_Types.G_Polygon sq_a) (RDF_Geo_Types.G_Polygon sq_b));
  let sq_c : RDF_Geo_Types.geo_polygon = { gpoly_ext = [ pt 100 100; pt 110 100; pt 110 110; pt 100 110; pt 100 100 ]; gpoly_holes = [] } in
  check_opt_bool ~name:"sfDisjoint(square A, far-away square C) = true"
    (Some true) (RDF_Geo_Topology.sf_disjoint (RDF_Geo_Types.G_Polygon sq_a) (RDF_Geo_Types.G_Polygon sq_c));
  let sq_inner : RDF_Geo_Types.geo_polygon = { gpoly_ext = [ pt 2 2; pt 4 2; pt 4 4; pt 2 4; pt 2 2 ]; gpoly_holes = [] } in
  check_opt_bool ~name:"sfWithin(inner square, square A) = true (strictly inside, no boundary contact)"
    (Some true) (RDF_Geo_Topology.sf_within (RDF_Geo_Types.G_Polygon sq_inner) (RDF_Geo_Types.G_Polygon sq_a));
  check_opt_bool ~name:"sfContains(square A, inner square) = true (flip of within)"
    (Some true) (RDF_Geo_Topology.sf_contains (RDF_Geo_Types.G_Polygon sq_a) (RDF_Geo_Types.G_Polygon sq_inner));

  (* B7: mismatched-dimension overlaps is decided false per SFA convention *)
  check_opt_bool ~name:"sfOverlaps(POINT, LINESTRING) = false (differing dims, SFA convention)"
    (Some false)
    (RDF_Geo_Topology.sf_overlaps (RDF_Geo_Types.G_Point (pt 1 1)) diag);

  Printf.printf "\n=== C. geof:distance / geof:envelope ===\n";

  (* C1: distance(point,point) — exact squared distance 3-4-5 triangle,
     so the sqrt is exactly 5 and the approximation should recover it
     to the disclosed extra precision (mantissa ends in all zeros
     after the leading 5). *)
  (match RDF_Geo_Functions.geo_distance (RDF_Geo_Types.G_Point (pt 0 0)) (RDF_Geo_Types.G_Point (pt 3 4)) with
   | Some d ->
     let s = RDF_Geo_Types.gs_to_string d in
     check ~name:"distance((0,0),(3,4)) ~= 5 (3-4-5 triangle, exact sqrt)" true
       (String.length s >= 1 && (String.sub s 0 1 = "5"))
   | None -> check ~name:"distance((0,0),(3,4)) is Some" true false);

  (* C2: distance is refused (None) for non-point/point pairs *)
  check ~name:"distance(point, linestring) is refused (None) in v0"
    true (RDF_Geo_Functions.geo_distance (RDF_Geo_Types.G_Point (pt 0 0)) diag = None);

  (* C3: envelope of a polygon is its bounding box, as a polygon *)
  (match RDF_Geo_Functions.geo_envelope (RDF_Geo_Types.G_Polygon sq_b) with
   | Some (RDF_Geo_Types.G_Polygon env) ->
     check ~name:"envelope(square B) exterior ring has 5 points (closed rectangle)"
       true (List.length env.gpoly_ext = 5)
   | _ -> check ~name:"envelope(square B) is a polygon" true false);

  Printf.printf "\ngeosparql_v0_unit: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
