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
sits inside neither. It is named once, below, and every cell in this
section that needs it references `GEO_TTL` by name instead of
repeating it:

```observable-js
GEO_TTL = `
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
`
```

```observable-js
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
const dataset = await fn.parse(GEO_TTL);
const rows = await fn.query(dataset, `# Which city sits inside which area box: cross product of cities and
# areas, kept only where the city's point is sfWithin the area's polygon.
  PREFIX ex:   <http://example.org/>
  PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
  SELECT ?cityName ?areaName WHERE {
    ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?cgeom .
    ?area a ex:Area ; ex:name ?areaName ; ex:hasGeom ?ageom .
    # keep the pair only if the city point lies within the area polygon
    FILTER(geof:sfWithin(?cgeom, ?ageom))
  } ORDER BY ?cityName`);
return pretty(rows);
```

Two pairs survive the filter: Edinburgh's point is inside the Scotland
box, London's is inside the Greater London box. Manchester is inside
neither, so it produces no row. Swapping the argument order and using
`geof:sfContains` — "which area box *contains* London" — is the same
relation read the other way and would return the Greater London box.

### `sfWithin` at borough scale: a live choropleth

The three-city, two-toy-box example above proves the mechanism; this
one scales it up to something that reads as a real place. The
dataset is the real 33 London boroughs (32 boroughs + the City of
London) and the River Thames, vendored as GeoJSON under
[`docs/web/hub/assets/geo/`](https://github.com/danbri/factoidal/blob/claude/main/docs/web/hub/assets/geo/PROVENANCE.md)
(ONS Open Geography boundaries, OGL v3; a Natural Earth river line,
public domain — see that directory's `PROVENANCE.md` for the exact
services, licences, and the Douglas-Peucker simplification that keeps
the total under 70 KB), plus sixteen well-known London landmarks
written directly into this cell as WKT points. The cell converts every
borough polygon and every landmark point to a `geo:wktLiteral`,
`fn.parse`s the result, and runs **one** SPARQL query:

```sparql
# Which landmark points are sfWithin which borough polygon.
SELECT ?boroughName ?landmarkName WHERE {
  ?borough   a ex:Borough  ; ex:name ?boroughName  ; ex:hasGeom ?bgeom .
  ?landmark  a ex:Landmark ; ex:name ?landmarkName ; ex:hasGeom ?lgeom .
  # keep the pair only if the landmark point lies within the borough polygon
  FILTER(geof:sfWithin(?lgeom, ?bgeom))
}
```

— "which landmark points are `sfWithin` which borough polygon", the
same point/polygon `sfWithin` relation the three-city example used,
just run over 33 × 16 candidate pairs instead of 3 × 2. **Every
borough's fill color is that query's row count for that borough** (0
landmarks = the palette's lightest shade, 3+ = its darkest — the scale
`landmarkColor()` below defines); **clicking a borough opens a popup
listing exactly the `?landmarkName` rows this query returned for it**,
plus a second, equally live fact — whether `geof:sfIntersects` decided
the Thames' `LineString` crosses that borough's polygon — read from a
second small query. Nothing about a borough's appearance or popup
content is computed by re-deriving geometry in JavaScript; both come
straight out of query results. `sfWithin` and `sfIntersects` are both
fully decided (never refused) for every pair this cell asks about —
point/polygon `sfWithin` is decided unconditionally, and multi-polygon
component decomposition (several boroughs are OGC `MultiPolygon`s,
not simple `Polygon`s) falls back to `None` only when no component
settles the question, which never happens for a point that is
genuinely inside or outside every part — see
[`RDF.Geo.Topology.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Geo.Topology.fst)'s
decided-vs-refused table, also summarized in the
["Scope"](#scope-what-is-decided-what-is-refused) section below.

The map itself has three layers, same-origin only:

1. **Boroughs** (`L.geoJSON`, the vendored polygon file) — fill color
   from the choropleth query above, a thin outline, a click handler
   that builds the popup from that borough's rows.
2. **The Thames** (`L.geoJSON`, the vendored line file) — a plain blue
   line, drawn for orientation ("this reads as London"), not itself a
   query result.
3. **Landmarks** (`L.circleMarker`, one per named point) — small dark
   dots with a name tooltip; the *input* the choropleth query ran
   over, not its output.

No raster tile layer, no CDN — the strict page's
Content-Security-Policy (visible in this page's `<head>`, task #105)
sets `img-src`/`connect-src` to `'self'` only, so a tile request
literally cannot succeed here, and every marker uses `L.circleMarker`/
`L.geoJSON` rather than Leaflet's default `L.Icon` (whose PNG assets
are deliberately not vendored — see
[`third_party/leaflet/PROVENANCE.md`](https://github.com/danbri/factoidal/blob/claude/main/third_party/leaflet/PROVENANCE.md)).
A **fullscreen** control (top-right, native
[Fullscreen API](https://developer.mozilla.org/en-US/docs/Web/API/Fullscreen_API),
no plugin) makes the choropleth easier to read on a small viewport. On
this page's [live-mode twin](../../hub-live/21-geosparql-geometry-and-topology/)
— same cell source, `data-hub-mode="live"` on `<body>` instead of
`"strict"` — a fourth, non-CDN-restricted layer becomes available: a
real OpenStreetMap raster basemap underneath the vector layers above,
toggleable via a layer control, with its own required attribution
line. The strict page you're reading now never adds it.

```observable-js
// Sixteen well-known London landmarks, hand-picked to land in several
// different boroughs (Westminster and Greenwich get two each; Richmond
// upon Thames gets three) so the choropleth below actually has a
// range of counts to show, not just "0 or 1". These are the cell's
// INPUT data, same status as the three cities/two toy boxes in the
// examples above -- ordinary asserted facts, not a query result. A
// landmark deliberately placed near a borough boundary can land on
// either side of it after this post's Douglas-Peucker simplification
// of the borough polygons (see assets/geo/PROVENANCE.md) -- that is
// the engine reporting exactly what the (simplified) vendored geometry
// says, not a bug; none of the sixteen below are boundary-adjacent
// enough for that to matter.
const LANDMARKS = [
  ["Big Ben", -0.1246, 51.5007],
  ["Buckingham Palace", -0.1419, 51.5014],
  ["Canary Wharf", -0.0235, 51.5054],
  ["The Shard", -0.0865, 51.5045],
  ["Greenwich Observatory", -0.0005, 51.4769],
  ["The O2", 0.0032, 51.5030],
  ["Wembley Stadium", -0.2795, 51.5560],
  ["Emirates Stadium", -0.1084, 51.5549],
  ["Kew Gardens", -0.2955, 51.4787],
  ["Hampton Court Palace", -0.3367, 51.4035],
  ["Twickenham Stadium", -0.3419, 51.4560],
  ["Alexandra Palace", -0.1310, 51.5941],
  ["Heathrow Airport", -0.4543, 51.4700],
  ["Kensington Palace", -0.1877, 51.5052],
  ["Battersea Power Station", -0.1439, 51.4816],
  ["Camden Market", -0.1461, 51.5416],
];

// GeoJSON -> WKT, one direction only (no round trip needed -- Leaflet
// renders the fetched GeoJSON objects directly; WKT is only for the
// SPARQL literals this cell constructs). Matches Parser.WKT.fst's
// nesting exactly: a ring is "(x y, x y, ...)"; a polygon body is
// "(ring, hole, ...)"; MULTIPOLYGON wraps a comma list of polygon
// bodies in one more pair of parens.
function ringToWkt(ring) {
  return "(" + ring.map(([lon, lat]) => lon + " " + lat).join(", ") + ")";
}
function polygonCoordsToWkt(coordinates) {
  return "(" + coordinates.map(ringToWkt).join(", ") + ")";
}
function geomToWkt(geom) {
  if (geom.type === "Polygon") return "POLYGON" + polygonCoordsToWkt(geom.coordinates);
  if (geom.type === "MultiPolygon")
    return "MULTIPOLYGON(" + geom.coordinates.map(polygonCoordsToWkt).join(", ") + ")";
  if (geom.type === "LineString")
    return "LINESTRING(" + geom.coordinates.map(([lon, lat]) => lon + " " + lat).join(", ") + ")";
  throw new Error("geomToWkt: unsupported geometry type " + geom.type);
}

// Choropleth color scale: landmark COUNT -> fill color, four discrete
// steps (0..3+). The ONLY input is the query row count computed below
// -- no geometry math here, just a lookup table.
const CHOROPLETH_SCALE = ["#eef3ef", "#a8cdb4", "#5a9c79", "#1b4332"];
function landmarkColor(count) {
  return CHOROPLETH_SCALE[Math.min(count, CHOROPLETH_SCALE.length - 1)];
}

// Same-origin base path for this cell's two fetch()es, independent of
// whether this notebook is running on the strict page (.../web/hub/21-.../)
// or its live-mode twin (.../web/hub-live/21-.../) -- both serve the
// SAME vendored files from .../web/hub/assets/geo/. `location` is a
// browser global (see reactive-cells.mjs's header on globals resolving
// through ordinary JS scope); the Node pinning test stubs `fetch`
// directly and never reads the computed URL, so the `typeof location
// === "undefined"` branch only matters there.
const geoAssetsBase =
  typeof location === "undefined"
    ? "../assets/geo/"
    : (/^(.*\/web\/)hub(?:-live)?\/[^/]+\/?$/.exec(location.pathname) || [, "../"])[1] + "hub/assets/geo/";

try {
  const [boroughsGeoJSON, thamesGeoJSON] = await Promise.all([
    fetch(geoAssetsBase + "london-boroughs.geojson").then((r) => r.json()),
    fetch(geoAssetsBase + "thames.geojson").then((r) => r.json()),
  ]);

  const boroughTriples = boroughsGeoJSON.features
    .map((f, i) => {
      const id = "ex:borough" + i;
      const wkt = geomToWkt(f.geometry).replace(/"/g, "");
      return `${id} a ex:Borough ; ex:name "${f.properties.name}" ; ex:hasGeom "${wkt}"^^geo:wktLiteral .`;
    })
    .join("\n  ");
  const landmarkTriples = LANDMARKS.map(([name, lon, lat], i) => {
    return `ex:landmark${i} a ex:Landmark ; ex:name "${name}" ; ex:hasGeom "POINT(${lon} ${lat})"^^geo:wktLiteral .`;
  }).join("\n  ");
  const thamesWkt = geomToWkt(thamesGeoJSON.features[0].geometry).replace(/"/g, "");

  const CHOROPLETH_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .
  ex:Thames a ex:River ; ex:hasGeom "${thamesWkt}"^^geo:wktLiteral .
  ${boroughTriples}
  ${landmarkTriples}
`;
  const dataset = await fn.parse(CHOROPLETH_TTL);

  // The ONE query this whole choropleth reads from: every
  // (boroughName, landmarkName) pair the engine decided sfWithin. A
  // borough with zero rows here just never appears as a key below --
  // groupBy defaults its count to 0, not a re-derivation of anything.
  const withinRows = await fn.query(dataset, `# Which landmark points are sfWithin which borough polygon, over the
# real 33-borough dataset -- the query that drives the choropleth fill.
    PREFIX ex:   <http://example.org/>
    PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
    SELECT ?boroughName ?landmarkName WHERE {
      ?borough  a ex:Borough  ; ex:name ?boroughName  ; ex:hasGeom ?bgeom .
      ?landmark a ex:Landmark ; ex:name ?landmarkName ; ex:hasGeom ?lgeom .
      # keep the pair only if the landmark point lies within the borough polygon
      FILTER(geof:sfWithin(?lgeom, ?bgeom))
    } ORDER BY ?boroughName ?landmarkName`);
  const landmarksByBorough = new Map();
  for (const row of withinRows) {
    const b = row.get("boroughName").value;
    const l = row.get("landmarkName").value;
    if (!landmarksByBorough.has(b)) landmarksByBorough.set(b, []);
    landmarksByBorough.get(b).push(l);
  }

  // A second, independent decided predicate over the SAME dataset --
  // linestring/multipolygon sfIntersects, decomposed component-wise
  // exactly like point/multipolygon sfWithin above. Folded into the
  // popup as a bonus fact, not into the fill color.
  const thamesRows = await fn.query(dataset, `# Which boroughs the Thames LineString sfIntersects -- feeds the
# per-borough popup's second, independent fact.
    PREFIX ex:   <http://example.org/>
    PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
    SELECT ?boroughName WHERE {
      ex:Thames ex:hasGeom ?rgeom .
      ?borough a ex:Borough ; ex:name ?boroughName ; ex:hasGeom ?bgeom .
      # keep the borough only if it shares a point with the Thames line
      FILTER(geof:sfIntersects(?rgeom, ?bgeom))
    }`);
  const thamesBoroughs = new Set(thamesRows.map((r) => r.get("boroughName").value));

  const container = document.createElement("div");
  container.className = "hub-leaflet-map";

  const map = L.map(container, { zoomControl: true, attributionControl: false });
  // Fixed center+zoom before any layer is added -- a detached
  // container has zero size, and fitBounds against it poisons the
  // view with NaN. Greater London's rough centroid/zoom, refined by
  // the real fitBounds once layers mount (post-attach frame below).
  map.setView([51.5, -0.12], 10);

  L.geoJSON(boroughsGeoJSON, {
    style: (feature) => {
      const count = (landmarksByBorough.get(feature.properties.name) || []).length;
      return { color: "#1a1e23", weight: 1, fillColor: landmarkColor(count), fillOpacity: 0.75 };
    },
    onEachFeature: (feature, layer) => {
      const name = feature.properties.name;
      const names = landmarksByBorough.get(name) || [];
      const crossed = thamesBoroughs.has(name);
      const list = names.length
        ? "<ul>" + names.map((n) => `<li>${n}</li>`).join("") + "</ul>"
        : "<p>(no landmark from this list)</p>";
      layer.bindPopup(
        `<strong>${name}</strong><br>` +
        `geof:sfWithin landmarks (${names.length}): ${list}` +
        `geof:sfIntersects the Thames: <strong>${crossed}</strong>`
      );
    },
  }).addTo(map);

  L.geoJSON(thamesGeoJSON, {
    style: { color: "#1a6fa8", weight: 3, opacity: 0.85 },
  }).addTo(map);

  for (const [name, lon, lat] of LANDMARKS) {
    L.circleMarker([lat, lon], {
      radius: 4,
      color: "#10130f",
      weight: 1,
      fillColor: "#f4b942",
      fillOpacity: 1,
    })
      .bindTooltip(name)
      .addTo(map);
  }

  // Fullscreen control (task #105): no plugin -- the native Fullscreen
  // API on the map's own container, with the still-common webkit
  // prefix as a fallback. invalidateSize() on the change event is
  // required: Leaflet computed its panes against the pre-fullscreen
  // box, and a size that changed outside Leaflet's own resize
  // observer (the browser doing it, not a CSS transition Leaflet
  // triggered) does not repaint on its own.
  const FullscreenControl = L.Control.extend({
    options: { position: "topright" },
    onAdd() {
      const el = L.DomUtil.create("div", "leaflet-bar leaflet-control leaflet-control-hub-fullscreen");
      const a = L.DomUtil.create("a", "", el);
      a.href = "#";
      a.title = "Toggle fullscreen";
      a.setAttribute("role", "button");
      a.setAttribute("aria-label", "Toggle fullscreen");
      a.textContent = "⤢";
      L.DomEvent.on(a, "click", (e) => {
        L.DomEvent.stopPropagation(e);
        L.DomEvent.preventDefault(e);
        const el2 = map.getContainer();
        const isFs = document.fullscreenElement || document.webkitFullscreenElement;
        if (!isFs) {
          (el2.requestFullscreen || el2.webkitRequestFullscreen)?.call(el2);
        } else {
          (document.exitFullscreen || document.webkitExitFullscreen)?.call(document);
        }
      });
      return el;
    },
  });
  map.addControl(new FullscreenControl());
  const onFullscreenChange = () => {
    map.invalidateSize();
    const isFs = document.fullscreenElement || document.webkitFullscreenElement;
    map.getContainer().classList.toggle("hub-leaflet-map-fs-active", !!isFs);
  };
  document.addEventListener("fullscreenchange", onFullscreenChange);
  document.addEventListener("webkitfullscreenchange", onFullscreenChange);

  // Live mode ONLY (task #105): data-hub-mode="live" is set on <body>
  // by docs/_includes/hub.njk exclusively for pages generated by
  // web/hub-live.11ty.js. Same cell source either way -- this branch
  // is the ONE place the notebook's behavior differs by capability,
  // not by content. The strict page this section's prose describes
  // never executes this branch, so it never attempts a network
  // request -- consistent with the page's own CSP (img-src 'self'
  // only in strict mode, which would block this fetch anyway).
  if (typeof document !== "undefined" && document.body?.getAttribute("data-hub-mode") === "live") {
    const osm = L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png", {
      maxZoom: 19,
      attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors',
    });
    L.control.layers({ "OpenStreetMap (live)": osm }, {}, { position: "bottomleft" }).addTo(map);
    // Test hook only (tests/web-demos/hub_post21_geo_check.sh) -- proves
    // the tile layer OBJECT was created without asserting any tile was
    // actually fetched (CI has no network guarantee, per that script's
    // own header).
    if (typeof window !== "undefined") window.__hubLiveTileLayer = osm;
  }

  // Leaflet needs its container sized AND attached to the document
  // before it can lay out panes or compute a bounds-fitting zoom; the
  // runtime attaches this cell's returned node only after this
  // function returns, so both the size refresh and the real
  // fitBounds run on a later frame, once the container has a size.
  const settle = () => {
    map.invalidateSize();
    map.fitBounds(L.geoJSON(boroughsGeoJSON).getBounds(), { padding: [16, 16] });
  };
  if (typeof requestAnimationFrame === "function") requestAnimationFrame(settle);
  else setTimeout(settle, 0);

  return container;
} catch (err) {
  return html`<div>map unavailable: ${String((err && err.message) || err)}</div>`;
}
```

Every fill color on this choropleth came out of the same
`FILTER(geof:sfWithin(?lgeom, ?bgeom))` query the prose above named:
Westminster and Greenwich are among the darkest boroughs shown (two
landmarks each from this post's fixed list), Richmond upon Thames is
darker still (three), and every borough with none of the sixteen
landmarks stays the palette's lightest shade — read that directly off
the map, not off a hardcoded claim here, since which exact boroughs
land where depends on the vendored, independently-simplified polygon
each landmark point happens to fall inside (see `assets/geo/
PROVENANCE.md`). Click any borough for its own popup, built the same
way: the `?landmarkName` rows this query returned for that one
borough, plus the separate `sfIntersects`-against-the-Thames fact.

`geof:sfDisjoint` is the complement of `sfIntersects`: two geometries
that share nothing. "Which cities lie *outside* the Greater London
box":

```observable-js
const dataset = await fn.parse(GEO_TTL);
const rows = await fn.query(dataset, `# Which cities lie outside the Greater London box: kept only where the
# city's point shares no point at all with the area polygon.
  PREFIX ex:   <http://example.org/>
  PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
  SELECT ?cityName WHERE {
    ex:GreaterLondonArea ex:hasGeom ?ageom .
    ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?cgeom .
    # keep the city only if it shares no point with the area polygon
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
const dataset = await fn.parse(GEO_TTL);
const rows = await fn.query(dataset, `# Cities ordered by distance from London, computed as an exact squared
# distance with one disclosed floored square root.
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
const ENVELOPE_TTL = `
  @prefix ex:  <http://example.org/> .
  @prefix geo: <http://www.opengis.net/ont/geosparql#> .
  ex:London a ex:City ; ex:name "London" ;
    ex:hasGeom "POINT(-0.1278 51.5074)"^^geo:wktLiteral .
  ex:GreaterLondonArea a ex:Area ; ex:name "Greater London (toy box)" ;
    ex:hasGeom "POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^geo:wktLiteral .
`;
const dataset = await fn.parse(ENVELOPE_TTL);
const rows = await fn.query(dataset, `# Axis-aligned bounding box of each named geometry, as a POLYGON.
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
  return fn.query(dataset, `# Does the named point stand in the given Simple Features relation to the box.
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
[series plan](../../../designissues/2026-07-05-docs-hub-plan/); the
[performance hub](../../perf/) covers the runtime-vs-runtime side of the
same engine.

Every live cell above is pinned in
[`tests/hub/post21_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post21_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn` adapter.
