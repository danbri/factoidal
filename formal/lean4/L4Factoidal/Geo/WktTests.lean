/-
L4Factoidal.Geo.WktTests — build-time checks for WKT parsing.
-/
import L4Factoidal.Geo.Wkt

namespace L4Factoidal.Geo

private def parseGeom (s : String) : Option Geometry :=
  (Wkt.parseLiteral s).map (·.geom)

-- Points, including negative and fractional coordinates.
#guard match parseGeom "POINT(1 2)" with
       | some (.point p) => Point.eq p ⟨⟨1,0⟩, ⟨2,0⟩⟩
       | _ => false
#guard match parseGeom "POINT (-0.1 51.5)" with
       | some (.point p) => Point.eq p ⟨⟨-1,1⟩, ⟨515,1⟩⟩
       | _ => false
#guard (parseGeom "point(1 2)").isSome        -- case-insensitive tag
#guard match parseGeom "POINT EMPTY" with
       | some (.empty .point) => true
       | _ => false

-- EXACTNESS: 0.1 parses to the exact decimal, so it equals 0.10.
#guard match parseGeom "POINT(0.1 0.2)" with
       | some (.point p) => Point.eq p ⟨⟨10,2⟩, ⟨20,2⟩⟩
       | _ => false

-- LineString and Polygon with a hole.
#guard match parseGeom "LINESTRING(0 0, 1 1, 2 0)" with
       | some (.lineString ps) => ps.length == 3
       | _ => false
#guard match parseGeom "POLYGON((0 0,4 0,4 4,0 4,0 0),(1 1,2 1,2 2,1 2,1 1))" with
       | some (.polygon poly) => poly.ext.length == 5 && poly.holes.length == 1
       | _ => false

-- Multi-geometries and a nested collection.
#guard match parseGeom "MULTIPOINT(0 0, 1 1)" with
       | some (.multiPoint ps) => ps.length == 2
       | _ => false
#guard match parseGeom "MULTIPOLYGON(((0 0,1 0,1 1,0 0)),((2 2,3 2,3 3,2 2)))" with
       | some (.multiPolygon ps) => ps.length == 2
       | _ => false
#guard match parseGeom "GEOMETRYCOLLECTION(POINT(1 2),LINESTRING(0 0,1 1))" with
       | some (.geometryCollection gs) => gs.length == 2
       | _ => false

-- A CRS prefix is captured, and absence means CRS84.
#guard match Wkt.parseLiteral "<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(1 2)" with
       | some v => v.crs == some "http://www.opengis.net/def/crs/EPSG/0/27700"
       | none => false
#guard match Wkt.parseLiteral "POINT(1 2)" with
       | some v => v.crs == none
       | none => false

-- Malformed input fails rather than partially parsing.
#guard (Wkt.parseLiteral "POINT(1 2) trailing").isNone
#guard (Wkt.parseLiteral "POINT(1)").isNone
#guard (Wkt.parseLiteral "NOTAGEOMETRY(1 2)").isNone
#guard (Wkt.parseLiteral "POINT(1 2").isNone
#guard (Wkt.parseLiteral "").isNone

-- Decimal rendering round-trips the exact value.
#guard Scaled.toStringDec ⟨-1, 1⟩ == "-0.1"
#guard Scaled.toStringDec ⟨515, 1⟩ == "51.5"
#guard Scaled.toStringDec ⟨5, 0⟩ == "5"
#guard Scaled.toStringDec ⟨1, 3⟩ == "0.001"

-- Parsed geometry feeds the topology predicates directly.
#guard match parseGeom "POLYGON((0 0,4 0,4 4,0 4,0 0))" with
       | some (.polygon poly) => pointWithinPolygon ⟨⟨2,0⟩, ⟨2,0⟩⟩ poly
       | _ => false

end L4Factoidal.Geo
