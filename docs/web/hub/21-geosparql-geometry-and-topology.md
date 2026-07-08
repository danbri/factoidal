---
title: "GeoSPARQL: geometry, topology, and exact-rational arithmetic"
description: "GeoSPARQL adds geometry literals and topological functions to SPARQL. Factoidal's support is pure exact-rational F* — a point exactly on a polygon edge is decided exactly, with no floating-point epsilon anywhere on the decided path — checked live in your browser."
layout: hub.njk
series: docs-hub
series_order: 21
vocab: geosparql
status: published
tests: tests/hub/post21_test.mjs
---

Everything the series has queried so far has been symbolic: IRIs,
literals, language tags, class membership. GeoSPARQL adds a second kind
of value to the graph — *geometry* — and a set of SPARQL functions that
answer spatial questions about it: is this point inside that polygon,
how far apart are these two places, what is the bounding box of this
shape. The geometry lives in the data as an ordinary typed literal; the
questions are ordinary SPARQL expressions. So a GeoSPARQL query runs
through the same `fn.query` path every other post in this series uses —
no new API surface, just new functions the engine recognises inside a
`FILTER` or a projection.

This post covers Factoidal's GeoSPARQL support: pure F* with no
floating-point arithmetic anywhere on its decided path.
That last part is the reason the post exists: a spatial engine built on
floating-point has to decide, for every "is this point on the edge"
question, how big an epsilon counts as "on". Factoidal decides
those cases with exact rational arithmetic, so a point that lies
*exactly* on a polygon's edge is classified as boundary — not nudged
inside or outside by rounding. The [last cell below](#the-exact-boundary-case)
demonstrates exactly that.

## Geometry literals: `geo:wktLiteral` and WKT

A geometry enters an RDF graph as a literal typed
`geo:wktLiteral`
(`http://www.opengis.net/ont/geosparql#wktLiteral`), whose lexical form
is **WKT** (Well-Known Text) — the OGC's plain-text geometry notation.
A couple of shapes in WKT:

```turtle
"POINT(-0.1278 51.5074)"^^geo:wktLiteral
"POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral
```

`POINT(x y)` is a single coordinate pair; the WKT convention is
`x = longitude, y = latitude`, so a London point reads
`POINT(-0.1278 51.5074)`. `POLYGON((...))` is a closed ring of
coordinates (first and last vertex coincide), with the doubled
parentheses leaving room for interior rings (holes). Factoidal's WKT
parser is itself F* —
[`Parser.WKT.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/Parser.WKT.fst) —
and parses coordinates to exact scaled-decimal rationals, not to
floating-point doubles: `51.5074` is carried as the integer `515074`
with a scale of 4, so no precision is lost at the door.

Here is the dataset the topological cells below run against — three UK
city points and two toy "constituency-ish" bounding-box polygons,
hand-picked so exactly one city sits inside each box and Manchester
sits inside neither:

```observable-js
const GEO_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .

  ex:London a ex:City ; ex:name "London" ;
    ex:hasGeom "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:Manchester a ex:City ; ex:name "Manchester" ;
    ex:hasGeom "POINT(-2.2426 53.4808)"^^geo:wktLiteral .
  ex:Edinburgh a ex:City ; ex:name "Edinburgh" ;
    ex:hasGeom "POINT(-3.1883 55.9533)"^^geo:wktLiteral .

  ex:GreaterLondonArea a ex:Area ; ex:name "Greater London (toy box)" ;
    ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
  ex:ScotlandArea a ex:Area ; ex:name "Scotland (toy box)" ;
    ex:hasGeom "POLYGON((-8 54.5, -1 54.5, -1 60.9, -8 60.9, -8 54.5))"^^geo:wktLiteral .
`;
const dataset = await fn.parse(GEO_TTL);
return dataset.size;
```

Fifteen triples: each of the five subjects carries a type, a name, and
a `geo:wktLiteral` geometry. Nothing here is special-cased for
geometry at parse time — a `geo:wktLiteral` is just a typed literal
like any other until a `geof:` function asks about it.

## Topological predicates: the Simple Features family

The spatial questions come from the OGC **Simple Features** access
model, exposed as SPARQL functions under the
`http://www.opengis.net/def/function/geosparql/` namespace (prefix
`geof:`). Each takes two geometries and returns a boolean:

- `geof:sfWithin(a, b)` — is `a` entirely inside `b`?
- `geof:sfContains(a, b)` — is `b` entirely inside `a`? (the converse
  of `sfWithin`)
- `geof:sfIntersects(a, b)` — do `a` and `b` share any point at all?
- `geof:sfDisjoint(a, b)` — do they share *no* point? (the negation of
  `sfIntersects`)
- `geof:sfTouches(a, b)` — do they meet only on their boundaries,
  without either's interior involved?

Because they return booleans, they sit naturally inside a `FILTER`.
"Which city sits inside which area box" is `geof:sfWithin` over the
cross-product of cities and areas:

```observable-js
const GEO_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .

  ex:London a ex:City ; ex:name "London" ;
    ex:hasGeom "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:Manchester a ex:City ; ex:name "Manchester" ;
    ex:hasGeom "POINT(-2.2426 53.4808)"^^geo:wktLiteral .
  ex:Edinburgh a ex:City ; ex:name "Edinburgh" ;
    ex:hasGeom "POINT(-3.1883 55.9533)"^^geo:wktLiteral .

  ex:GreaterLondonArea a ex:Area ; ex:name "Greater London (toy box)" ;
    ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
  ex:ScotlandArea a ex:Area ; ex:name "Scotland (toy box)" ;
    ex:hasGeom "POLYGON((-8 54.5, -1 54.5, -1 60.9, -8 60.9, -8 54.5))"^^geo:wktLiteral .
`;
const dataset = await fn.parse(GEO_TTL);
const rows = await fn.query(dataset, `
  PREFIX ex:   <http://example.org/>
  PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
  SELECT ?cityName ?areaName WHERE {
    ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?cgeom .
    ?area a ex:Area ; ex:name ?areaName ; ex:hasGeom ?ageom .
    FILTER(geof:sfWithin(?cgeom, ?ageom))
  } ORDER BY ?cityName`);
return pretty(rows);
```

Two pairs survive the filter: Edinburgh's point is inside the Scotland
box, London's is inside the Greater London box. Manchester is inside
neither, so it produces no row. Swapping the argument order and using
`geof:sfContains` — "which area box *contains* London" — is the same
relation read the other way and would return the Greater London box.

### `sfWithin` on a map

A table of `(cityName, areaName)` pairs is the query result; a map of
colored points is the same query result, read visually. The cell below
runs the identical `geof:sfWithin` cross-product query, then hands
every city and area geometry to [Leaflet](https://leafletjs.com/)
(vendored, no CDN — see
[`third_party/leaflet/`](https://github.com/danbri/factoidal/blob/claude/main/third_party/leaflet/PROVENANCE.md))
purely to draw the shapes: **the marker colors are the engine's
`sfWithin` answer**, not a recomputation in JavaScript. Green means the
F\* engine decided that city's point is `sfWithin` one of the two area
polygons; grey means it decided the opposite. London gets a bigger
marker and a fixed label, since it's the pairing the prose above
walked through by hand. There is no tile layer — the two toy boxes and
three city points are drawn as plain vector shapes on a blank
background, so the map needs no network access to render.

```observable-js
const GEO_MAP_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .

  ex:London a ex:City ; ex:name "London" ;
    ex:hasGeom "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:Manchester a ex:City ; ex:name "Manchester" ;
    ex:hasGeom "POINT(-2.2426 53.4808)"^^geo:wktLiteral .
  ex:Edinburgh a ex:City ; ex:name "Edinburgh" ;
    ex:hasGeom "POINT(-3.1883 55.9533)"^^geo:wktLiteral .

  ex:GreaterLondonArea a ex:Area ; ex:name "Greater London (toy box)" ;
    ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
  ex:ScotlandArea a ex:Area ; ex:name "Scotland (toy box)" ;
    ex:hasGeom "POLYGON((-8 54.5, -1 54.5, -1 60.9, -8 60.9, -8 54.5))"^^geo:wktLiteral .
`;

// Tiny WKT -> coordinate parser: POINT and POLYGON only, no full WKT
// library (this post's dataset never uses anything else). Positions
// come out in WKT's own (and GeoJSON's) [lon, lat] order, so a
// POLYGON ring can feed L.geoJSON's coordinates array directly;
// callers that need Leaflet's [lat, lon] point order (L.circleMarker,
// L.latLng, fitBounds) swap explicitly at the call site below.
function wktParse(wkt) {
  const s = wkt.trim();
  let m = /^POINT\s*\(\s*([+-]?[\d.]+)\s+([+-]?[\d.]+)\s*\)$/i.exec(s);
  if (m) return { type: "Point", lon: Number(m[1]), lat: Number(m[2]) };
  m = /^POLYGON\s*\(\s*\(([^)]*)\)\s*\)$/i.exec(s);
  if (m) {
    const ring = m[1].split(",").map((pair) => {
      const parts = pair.trim().split(/\s+/).map(Number);
      return [parts[0], parts[1]]; // [lon, lat]
    });
    return { type: "Polygon", ring };
  }
  throw new Error("wktParse: unrecognized WKT: " + wkt);
}

// The ONLY thing that decides a marker's color: the sfWithin boolean
// the F* engine already computed. No geometry math happens in this
// function or anywhere else in this cell.
function colorForWithin(isWithin) {
  return isWithin ? "#2d6a4f" : "#8a8f98";
}

try {
  const dataset = await fn.parse(GEO_MAP_TTL);

  const areaRows = await fn.query(dataset, `
    PREFIX ex: <http://example.org/>
    SELECT ?areaName ?ageom WHERE {
      ?area a ex:Area ; ex:name ?areaName ; ex:hasGeom ?ageom .
    } ORDER BY ?areaName`);
  const cityRows = await fn.query(dataset, `
    PREFIX ex: <http://example.org/>
    SELECT ?cityName ?cgeom WHERE {
      ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?cgeom .
    } ORDER BY ?cityName`);
  // The exact sfWithin cross-product query from the cell above --
  // this Map of cityName -> areaName IS the query result the map
  // renders; every marker color below is read straight out of it.
  const withinRows = await fn.query(dataset, `
    PREFIX ex:   <http://example.org/>
    PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
    SELECT ?cityName ?areaName WHERE {
      ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?cgeom .
      ?area a ex:Area ; ex:name ?areaName ; ex:hasGeom ?ageom .
      FILTER(geof:sfWithin(?cgeom, ?ageom))
    } ORDER BY ?cityName`);
  const withinArea = new Map(
    withinRows.map((r) => [r.get("cityName").value, r.get("areaName").value])
  );

  const container = document.createElement("div");
  container.className = "hub-leaflet-map";

  const map = L.map(container, { zoomControl: true, attributionControl: false });
  const allLatLngs = [];

  for (const row of areaRows) {
    const name = row.get("areaName").value;
    const geom = wktParse(row.get("ageom").value);
    const geojson = { type: "Polygon", coordinates: [geom.ring] };
    L.geoJSON(geojson, {
      style: { color: "#2d6a4f", weight: 1, fillColor: "#2d6a4f", fillOpacity: 0.08 },
    })
      .bindTooltip(name)
      .addTo(map);
    for (const [lon, lat] of geom.ring) allLatLngs.push([lat, lon]);
  }

  for (const row of cityRows) {
    const name = row.get("cityName").value;
    const geom = wktParse(row.get("cgeom").value);
    const area = withinArea.get(name);
    const isWithin = area !== undefined;
    const latlng = [geom.lat, geom.lon];
    const marker = L.circleMarker(latlng, {
      radius: name === "London" ? 10 : 7,
      color: "#1a1e23",
      weight: name === "London" ? 2 : 1,
      fillColor: colorForWithin(isWithin),
      fillOpacity: 0.9,
    }).addTo(map);
    const label = isWithin
      ? name + " — geof:sfWithin " + area
      : name + " — not sfWithin any area shown";
    marker.bindTooltip(label, name === "London" ? { permanent: true, direction: "top" } : {});
    allLatLngs.push(latlng);
  }

  map.fitBounds(allLatLngs, { padding: [16, 16] });

  // Leaflet needs its container sized AND attached to the document
  // before it can lay out tiles/panes correctly; the runtime attaches
  // this cell's returned node to the page only after this function
  // returns, so invalidateSize() has to run on a later frame.
  const invalidate = () => map.invalidateSize();
  if (typeof requestAnimationFrame === "function") requestAnimationFrame(invalidate);
  else setTimeout(invalidate, 0);

  return container;
} catch (err) {
  return html`<div>map unavailable: ${String((err && err.message) || err)}</div>`;
}
```

Every color on this map came out of the same `FILTER(geof:sfWithin(...))`
call the table above ran: London and Edinburgh render green because
their `(cityName, areaName)` pair is in the engine's result set;
Manchester renders grey because it isn't in either area box. The map
draws the query's answer — it does not re-derive point-in-polygon
membership in JavaScript, and the two toy polygons and three points
are the same WKT literals from the dataset at the top of this post,
run through the tiny parser above rather than a general WKT library.

`geof:sfDisjoint` is the complement of `sfIntersects`: two geometries
that share nothing. "Which cities lie *outside* the Greater London
box":

```observable-js
const GEO_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .

  ex:London a ex:City ; ex:name "London" ;
    ex:hasGeom "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:Manchester a ex:City ; ex:name "Manchester" ;
    ex:hasGeom "POINT(-2.2426 53.4808)"^^geo:wktLiteral .
  ex:Edinburgh a ex:City ; ex:name "Edinburgh" ;
    ex:hasGeom "POINT(-3.1883 55.9533)"^^geo:wktLiteral .

  ex:GreaterLondonArea a ex:Area ; ex:name "Greater London (toy box)" ;
    ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
  ex:ScotlandArea a ex:Area ; ex:name "Scotland (toy box)" ;
    ex:hasGeom "POLYGON((-8 54.5, -1 54.5, -1 60.9, -8 60.9, -8 54.5))"^^geo:wktLiteral .
`;
const dataset = await fn.parse(GEO_TTL);
const rows = await fn.query(dataset, `
  PREFIX ex:   <http://example.org/>
  PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
  SELECT ?cityName WHERE {
    ex:GreaterLondonArea ex:hasGeom ?ageom .
    ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?cgeom .
    FILTER(geof:sfDisjoint(?cgeom, ?ageom))
  } ORDER BY ?cityName`);
return pretty(rows);
```

Edinburgh and Manchester — the two cities the earlier `sfWithin` query
did *not* pair with the Greater London box. London is missing here,
exactly because it is not disjoint from the box it sits inside.

## `geof:distance`: exact squared distance, one disclosed square root

`geof:distance` returns a number, not a boolean, so it goes in the
`SELECT` projection rather than a `FILTER`. It is defined for
point-to-point only. The arithmetic is worth spelling out because it is
where the "exact rational" story meets its one exception:
Factoidal computes the *squared* distance
`(x₁ − x₂)² + (y₁ − y₂)²` exactly — sums and products of exact
rationals, no rounding — and then takes a single, disclosed,
under-approximating integer square root
([`RDF.Geo.Functions.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Geo.Functions.fst)'s
`geo_sqrt_approx`, a pure-F* binary-search `isqrt`, floored, never an
`assume val`) to produce the `xsd:double` result. Every other value on
the decided path is exact; the square root is the one documented
floor(sqrt(...)) step, because a Euclidean distance is generally
irrational and has to land in a `double` eventually.

Ordering the cities by distance from London puts London itself first,
at exactly zero:

```observable-js
const GEO_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .

  ex:London a ex:City ; ex:name "London" ;
    ex:hasGeom "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:Manchester a ex:City ; ex:name "Manchester" ;
    ex:hasGeom "POINT(-2.2426 53.4808)"^^geo:wktLiteral .
  ex:Edinburgh a ex:City ; ex:name "Edinburgh" ;
    ex:hasGeom "POINT(-3.1883 55.9533)"^^geo:wktLiteral .

  ex:GreaterLondonArea a ex:Area ; ex:name "Greater London (toy box)" ;
    ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
  ex:ScotlandArea a ex:Area ; ex:name "Scotland (toy box)" ;
    ex:hasGeom "POLYGON((-8 54.5, -1 54.5, -1 60.9, -8 60.9, -8 54.5))"^^geo:wktLiteral .
`;
const dataset = await fn.parse(GEO_TTL);
const rows = await fn.query(dataset, `
  PREFIX ex:   <http://example.org/>
  PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
  SELECT ?cityName (geof:distance(?g, ?londonGeom) AS ?d) WHERE {
    ex:London ex:hasGeom ?londonGeom .
    ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?g .
  } ORDER BY ?d`);
return pretty(rows);
```

London is `0.00000000000000000` — the squared distance from a point to
itself is exactly zero, and the square root of exact zero is exactly
zero, so there is no floating-point drift on the self-distance case.
Manchester (about 2.89 degrees away) and Edinburgh (about 5.40) follow
in order. The units are raw coordinate degrees here, not metres — the
engine does no CRS-aware geodesic reprojection, a scope boundary the
last section names explicitly.

## `geof:envelope`: the bounding box, exactly

`geof:envelope` returns a geometry rather than a boolean or a number:
the axis-aligned bounding box of its argument, as a rectangular
`POLYGON`. There is no approximation anywhere in it — a bounding box is
just the min/max of the input coordinates, all exact:

```observable-js
const GEO_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .
  ex:London a ex:City ; ex:name "London" ;
    ex:hasGeom "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:GreaterLondonArea a ex:Area ; ex:name "Greater London (toy box)" ;
    ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
`;
const dataset = await fn.parse(GEO_TTL);
const rows = await fn.query(dataset, `
  PREFIX ex:   <http://example.org/>
  PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
  SELECT ?name (geof:envelope(?g) AS ?env) WHERE {
    ?s ex:name ?name ; ex:hasGeom ?g .
  } ORDER BY ?name`);
return pretty(rows);
```

The Greater London box is already axis-aligned, so its envelope is
itself, coordinate for coordinate. The London *point* envelopes to a
degenerate rectangle — all four corners collapsed onto the single
point — which is the correct bounding box of a zero-extent geometry.
Note the result literal comes back typed `geo:wktLiteral`, so an
`envelope` result can feed straight back into another `geof:` call.

## The exact-boundary case

This is the case a floating-point spatial engine has to make a judgment
call about, and the one Factoidal decides exactly. Take the Greater
London box and three points: one lying **exactly** on its bottom edge
(`POINT(0 51.3)`, where `51.3` is the box's south edge), one strictly
inside, and one clearly outside. Run all three against `sfWithin`,
`sfIntersects`, and `sfTouches` at once:

```observable-js
const BOX_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .

  ex:box      ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
  ex:onEdge   ex:label "exactly on the edge (y = 51.3)" ; ex:hasGeom "POINT(0 51.3)"^^geo:wktLiteral .
  ex:interior ex:label "strictly inside"               ; ex:hasGeom "POINT(0 51.5)"^^geo:wktLiteral .
  ex:outside  ex:label "clearly outside"               ; ex:hasGeom "POINT(0 52.0)"^^geo:wktLiteral .
`;
const dataset = await fn.parse(BOX_TTL);
async function rel(pred, node) {
  return fn.query(dataset, `
    PREFIX ex:   <http://example.org/>
    PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
    ASK { ex:box ex:hasGeom ?b . ${node} ex:hasGeom ?p . FILTER(geof:${pred}(?p, ?b)) }`);
}
const cases = [
  ["ex:onEdge",   "exactly on the edge (y = 51.3)"],
  ["ex:interior", "strictly inside"],
  ["ex:outside",  "clearly outside"],
];
const out = [];
for (const [node, label] of cases) {
  out.push({
    point: label,
    sfWithin:     await rel("sfWithin", node),
    sfIntersects: await rel("sfIntersects", node),
    sfTouches:    await rel("sfTouches", node),
  });
}
return pretty(out);
```

Read the top row. The point exactly on the edge is **not within** the
polygon (`sfWithin` false — Simple Features "within" requires the
interior, and the boundary is not the interior), it **intersects** the
polygon (`sfIntersects` true — they share that boundary point), and it
**touches** the polygon (`sfTouches` true — they meet only on the
boundary). All three answers are correct *simultaneously*, and they are
correct because the engine classified the point as lying on the
boundary rather than guessing interior-or-exterior. The interior point
is within and intersects but does not touch; the outside point fails
all three. Under the hood this is a ray-casting point-in-polygon test
rewritten to use an exact orientation predicate (sums and products of
exact rationals, no division), so a point exactly on a polygon edge is
classified as boundary and not nudged either way — a property of the
arithmetic, not a tuning parameter (see
[`RDF.Geo.Topology.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Geo.Topology.fst)).

## Scope: what is decided, what is refused

The scope is deliberately narrow. Every predicate
returns "decided exactly" or "refused" per geometry-kind pair — a
refused pair maps to a SPARQL error, never to a guessed boolean. The
[`RDF.Geo.Topology.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Geo.Topology.fst)
module header carries the full decided-vs-refused table; the shape of
it:

- **point/point** — all eight Simple Features predicates decided.
- **point/polygon** (the pairs this post exercises) —
  `sfWithin`, `sfContains`, `sfIntersects`, `sfDisjoint`, `sfTouches`,
  `sfEquals`, and `sfOverlaps` all decided; `sfCrosses` refused.
- **point/linestring** — most predicates decided; `sfCrosses` and
  `sfOverlaps` refused (their DE-9IM pattern equivalence for a
  0-dimension/1-dimension pair is not settled here, and refusing is
  safer than asserting an unverified equivalence).
- **polygon/polygon**, **linestring/linestring**,
  **linestring/polygon** — `sfIntersects`/`sfDisjoint` (and, for
  simple non-self-intersecting polygons, `sfWithin`/`sfContains`)
  decided, with `sfTouches`/`sfCrosses`/`sfOverlaps` largely refused
  pending a full DE-9IM boundary/interior classification.
- **`geof:distance`** — point/point only; every other kind pair
  refused (not implemented, distinct from a topological refusal).
- **CRS** — no coordinate transformation. A call across two
  *differently* stated CRS IRIs is refused rather than silently
  assumed to be identity; a default/CRS84 geometry is treated as
  compatible with any explicitly stated CRS. Distances are in raw
  coordinate units, not geodesic metres.

The design covers the exact-arithmetic core for the pairs it can
prove and refuses loudly everywhere else, rather than covering the
whole Simple Features matrix approximately. Widening the decided set —
`sfCrosses`/`sfOverlaps` for mixed-dimension pairs, a full DE-9IM
classifier, CRS-aware geodesic distance — would extend it, on the same
no-floating-point-on-the-decided-path discipline the boundary cell
above demonstrates.

## What's next

That closes the vocabulary tour the series set out to give. The full
map of published posts, each with its central vocabulary and pinning
test file, is in the
[series plan](../../designissues/2026-07-05-docs-hub-plan/); the
[performance hub](../perf/) covers the runtime-vs-runtime side of the
same engine.

Every live cell above is pinned in
[`tests/hub/post21_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post21_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn` adapter.
