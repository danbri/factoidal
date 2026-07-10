// Pins every live cell in
// docs/web/hub/21-geosparql-geometry-and-topology.md.
//
// The post's cells call the typed `fn` adapter only (fn.parse /
// fn.query) -- geof: functions are ordinary SPARQL expressions, so a
// GeoSPARQL query goes through the same query path every other post
// uses, no raw-Factoidal shim needed. The Node-side `fn` binding is the
// REAL npm/factoidal typed API; `pretty` is the shared node-side stub
// from _helpers.mjs (same shape dispatch as hub.njk's DOM pretty()).
//
// Cell 3 (index 2) is the Leaflet choropleth cell (task #105): it
// fetches the two vendored GeoJSON files (docs/web/hub/assets/geo/),
// converts every borough/landmark/river geometry to WKT, runs the
// live geof:sfWithin (landmark-in-borough) and geof:sfIntersects
// (Thames-through-borough) queries, and renders their results -- it
// does not recompute geometry itself. What's pinned here is (a) the
// pure GeoJSON->WKT serialization logic -- duplicated below from the
// cell's own inline copy, since cell bodies can't `import` (see
// docs/web/hub/README.md's "cell bindings" section) -- tested directly
// with plain assertions, no DOM involved, and (b) that the cell's
// actual shipped source runs to completion without throwing when given
// a minimal `document`/`L`/`fetch` stub standing in for the browser's
// real DOM, the real Leaflet library, and the real vendored GeoJSON
// fetch. Node has no layout engine, so a full visual render (borough
// fill colors, the fullscreen control, live-mode's OSM layer) is NOT
// asserted here -- that's tests/web-demos/hub_post21_geo_check.sh
// (headless Chromium, both the strict page and its live-mode twin).

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty, HUB_POST_DIR } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '21-geosparql-geometry-and-topology.md';

// The two vendored GeoJSON files the map cell fetches (task #105) --
// read once, from the same files docs/.eleventy.js passthrough-copies
// to the built site, so the Node stub below serves byte-identical
// content to what the browser would fetch.
const GEO_DIR = path.join(HUB_POST_DIR, 'assets', 'geo');
const BOROUGHS_GEOJSON = JSON.parse(fs.readFileSync(path.join(GEO_DIR, 'london-boroughs.geojson'), 'utf8'));
const THAMES_GEOJSON = JSON.parse(fs.readFileSync(path.join(GEO_DIR, 'thames.geojson'), 'utf8'));

const cells = extractObservableCells(POST_FILE);
const B = { fn: factoidal, pretty };

test('post21: post has 7 live cells', () => {
  assert.equal(cells.length, 7, `expected 7 live cells, found ${cells.length}`);
});

test('post21 cell 1 (parse the geo dataset): 15 triples', async () => {
  const result = await runObservableCell(cells[0], B);
  assert.equal(result, 15);
});

test('post21 cell 2 (geof:sfWithin): the two inside pairs, ordered', async () => {
  const result = await runObservableCell(cells[1], B);
  assert.deepEqual(result, {
    kind: 'table',
    columns: ['cityName', 'areaName'],
    rows: [
      ['"Edinburgh"', '"Scotland (toy box)"'],
      ['"London"', '"Greater London (toy box)"'],
    ],
  });
});

// --- Cell 3 (index 2): the Leaflet choropleth cell -------------------

// Mirrors the map cell's own inline `geomToWkt`/`ringToWkt`/
// `polygonCoordsToWkt` -- see the header comment above for why this is
// a duplicate rather than a shared import. Keep in sync by hand with
// the copy in docs/web/hub/21-geosparql-geometry-and-topology.md if
// either changes.
function ringToWkt(ring) {
  return '(' + ring.map(([lon, lat]) => lon + ' ' + lat).join(', ') + ')';
}
function polygonCoordsToWkt(coordinates) {
  return '(' + coordinates.map(ringToWkt).join(', ') + ')';
}
function geomToWkt(geom) {
  if (geom.type === 'Polygon') return 'POLYGON' + polygonCoordsToWkt(geom.coordinates);
  if (geom.type === 'MultiPolygon')
    return 'MULTIPOLYGON(' + geom.coordinates.map(polygonCoordsToWkt).join(', ') + ')';
  if (geom.type === 'LineString')
    return 'LINESTRING(' + geom.coordinates.map(([lon, lat]) => lon + ' ' + lat).join(', ') + ')';
  throw new Error('geomToWkt: unsupported geometry type ' + geom.type);
}

test('post21 map cell helper: geomToWkt serializes a simple Polygon', () => {
  const wkt = geomToWkt({
    type: 'Polygon',
    coordinates: [[[-0.5, 51.3], [0.3, 51.3], [0.3, 51.7], [-0.5, 51.3]]],
  });
  assert.equal(wkt, 'POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.3))');
});

test('post21 map cell helper: geomToWkt serializes a MultiPolygon with the OGC triple-paren nesting', () => {
  const wkt = geomToWkt({
    type: 'MultiPolygon',
    coordinates: [
      [[[0, 0], [1, 0], [1, 1], [0, 0]]],
      [[[2, 2], [3, 2], [3, 3], [2, 2]]],
    ],
  });
  assert.equal(wkt, 'MULTIPOLYGON(((0 0, 1 0, 1 1, 0 0)), ((2 2, 3 2, 3 3, 2 2)))');
  // Round-trips through the real engine (Parser.WKT.fst) -- proves the
  // nesting matches what SPARQL11.Algebra's geof: dispatch expects,
  // not just what looks right by eye.
  return factoidal
    .parse(`@prefix ex: <http://example.org/> .\n@prefix geo: <http://www.opengis.net/ont/geosparql#> .\nex:s ex:hasGeom "${wkt}"^^geo:wktLiteral .`)
    .then((ds) => assert.equal(ds.size, 1));
});

test('post21 map cell helper: geomToWkt serializes a LineString', () => {
  const wkt = geomToWkt({ type: 'LineString', coordinates: [[-0.5, 51.4], [-0.4, 51.45]] });
  assert.equal(wkt, 'LINESTRING(-0.5 51.4, -0.4 51.45)');
});

test('post21 choropleth query: landmark-in-borough sfWithin counts, run against the REAL engine', async () => {
  // The exact same query construction the map cell runs, over the
  // REAL vendored GeoJSON files and a small fixed landmark list --
  // pins what the F* engine actually decides for the real fixture
  // data (not a hand-simulated result), independent of any DOM/Leaflet
  // concern this test doesn't touch.
  const boroughTriples = BOROUGHS_GEOJSON.features
    .map((f, i) => `ex:borough${i} a ex:Borough ; ex:name "${f.properties.name}" ; ex:hasGeom "${geomToWkt(f.geometry)}"^^geo:wktLiteral .`)
    .join('\n');
  const LANDMARKS = [
    ['Big Ben', -0.1246, 51.5007],
    ['Buckingham Palace', -0.1419, 51.5014],
    ['Kew Gardens', -0.2955, 51.4787],
    ['Hampton Court Palace', -0.3367, 51.4035],
    ['Twickenham Stadium', -0.3419, 51.4560],
  ];
  const landmarkTriples = LANDMARKS
    .map(([name, lon, lat], i) => `ex:landmark${i} a ex:Landmark ; ex:name "${name}" ; ex:hasGeom "POINT(${lon} ${lat})"^^geo:wktLiteral .`)
    .join('\n');
  const dataset = await factoidal.parse(`
    @prefix ex:  <http://example.org/> .
    @prefix geo: <http://www.opengis.net/ont/geosparql#> .
    ${boroughTriples}
    ${landmarkTriples}
  `);
  const rows = await factoidal.query(dataset, `
    PREFIX ex:   <http://example.org/>
    PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
    SELECT ?boroughName ?landmarkName WHERE {
      ?borough  a ex:Borough  ; ex:name ?boroughName  ; ex:hasGeom ?bgeom .
      ?landmark a ex:Landmark ; ex:name ?landmarkName ; ex:hasGeom ?lgeom .
      FILTER(geof:sfWithin(?lgeom, ?bgeom))
    } ORDER BY ?boroughName ?landmarkName`);
  const byBorough = new Map();
  for (const row of rows) {
    const b = row.get('boroughName').value;
    if (!byBorough.has(b)) byBorough.set(b, []);
    byBorough.get(b).push(row.get('landmarkName').value);
  }
  assert.deepEqual(byBorough.get('Westminster'), ['Big Ben', 'Buckingham Palace']);
  assert.deepEqual(byBorough.get('Richmond upon Thames'), ['Hampton Court Palace', 'Kew Gardens', 'Twickenham Stadium']);
  // Every row's borough must be a real borough name from the vendored
  // file, and every row's landmark must be one of the five above --
  // catches a query that silently cross-joined onto the wrong subjects.
  const boroughNames = new Set(BOROUGHS_GEOJSON.features.map((f) => f.properties.name));
  const landmarkNames = new Set(LANDMARKS.map(([name]) => name));
  for (const row of rows) {
    assert.ok(boroughNames.has(row.get('boroughName').value));
    assert.ok(landmarkNames.has(row.get('landmarkName').value));
  }
});

test('post21 map cell (cell 3): runs to completion with a minimal document/L/fetch stub, no throw', async () => {
  // A chainable stub layer standing in for a real Leaflet Path/Layer:
  // .addTo()/.bindTooltip()/.bindPopup()/.setStyle() all return the
  // SAME object so the cell's `L.geoJSON(...).addTo(map)` and
  // `L.circleMarker(...).bindTooltip(name).addTo(map)` chains resolve
  // exactly the way real Leaflet's chaining API does.
  function stubLayer() {
    const layer = {};
    layer.addTo = () => layer;
    layer.bindTooltip = () => layer;
    layer.bindPopup = () => layer;
    layer.setStyle = () => layer;
    layer.getBounds = () => ({});
    return layer;
  }
  const stubL = {
    map: () => ({ setView() {}, addControl() {}, fitBounds() {}, invalidateSize() {}, getContainer: () => ({}) }),
    // Actually invokes style()/onEachFeature() per feature (real
    // borough/river data, from BOROUGHS_GEOJSON/THAMES_GEOJSON below)
    // so a typo in either callback -- e.g. a wrong `feature.properties`
    // key -- fails this test instead of silently never running.
    // Real Leaflet's `style` option accepts EITHER a per-feature
    // function (the borough choropleth layer) OR a plain style object
    // (the Thames layer) -- only call it when it's actually a
    // function, matching that same real Leaflet contract.
    geoJSON: (geojson, options) => {
      for (const f of (geojson && geojson.features) || []) {
        if (typeof options?.style === 'function') options.style(f);
        options?.onEachFeature?.(f, stubLayer());
      }
      return stubLayer();
    },
    circleMarker: () => stubLayer(),
    control: { layers: () => stubLayer() },
    tileLayer: () => stubLayer(),
    Control: { extend: (proto) => function StubControl() { Object.assign(this, proto); } },
    DomUtil: { create: () => ({ setAttribute() {} }) },
    DomEvent: { on() {}, off() {}, stopPropagation() {}, preventDefault() {} },
  };
  // The cell calls `document.createElement`/`addEventListener` and
  // reads `document.body` directly (ambient globals in the browser,
  // per reactive-cells.mjs's own header comment: "globals like Math/
  // JSON/console/document ... stay resolved through ordinary JS
  // scope"). Node has no `document`, so this test supplies the minimal
  // stub the cell's own DOM usage needs, then removes it -- this is a
  // test-only global, never touched by production code. `document.body`
  // is deliberately omitted (undefined): the cell's `document.body?.
  // getAttribute(...)` optional-chains past that, matching a page
  // where `hubMode` is unset (strict) -- this test never exercises the
  // live-mode OSM-tile branch, which is instead covered by
  // tests/web-demos/hub_post21_geo_check.sh's live-mode smoke.
  const previousDocument = globalThis.document;
  const previousFetch = globalThis.fetch;
  globalThis.document = {
    createElement: () => ({ className: '', style: {} }),
    addEventListener: () => {},
  };
  // Serve the real vendored GeoJSON files for the cell's page-relative
  // fetch() calls -- same pattern as tests/hub/post24_test.mjs's HDT
  // fixture stub. The URL argument is only suffix-matched (this cell's
  // own `geoAssetsBase` computation matters in a real browser, where
  // `location` exists; here `typeof location === "undefined"` so the
  // cell takes its Node-safe fallback path and this stub answers
  // whichever of the two files was asked for).
  globalThis.fetch = async (url) => {
    const body = String(url).includes('thames') ? THAMES_GEOJSON : BOROUGHS_GEOJSON;
    return { ok: true, async json() { return body; } };
  };
  try {
    const result = await runObservableCell(cells[2], { fn: factoidal, pretty, L: stubL });
    // Success path returns the container object the stub
    // `document.createElement` produced (not a `map unavailable`
    // fallback), proving fn.parse/fn.query/geomToWkt/landmarkColor/L/
    // fetch all ran without throwing.
    assert.ok(result && typeof result === 'object', 'map cell should return the map container object');
    assert.equal(result.className, 'hub-leaflet-map');
  } finally {
    if (previousDocument === undefined) delete globalThis.document; else globalThis.document = previousDocument;
    if (previousFetch === undefined) delete globalThis.fetch; else globalThis.fetch = previousFetch;
  }
});

// --- Cells 4-7 (index 3-6): unchanged from before the map cell was
// inserted, renumbered. ------------------------------------------------

test('post21 cell 4 (geof:sfDisjoint): the two cities outside the London box', async () => {
  const result = await runObservableCell(cells[3], B);
  assert.deepEqual(result, {
    kind: 'table',
    columns: ['cityName'],
    rows: [['"Edinburgh"'], ['"Manchester"']],
  });
});

test('post21 cell 5 (geof:distance ORDER BY): London 0 first, then Manchester, Edinburgh', async () => {
  const result = await runObservableCell(cells[4], B);
  assert.deepEqual(result, {
    kind: 'table',
    columns: ['cityName', 'd'],
    rows: [
      ['"London"', '"0.00000000000000000"^^http://www.w3.org/2001/XMLSchema#double'],
      ['"Manchester"', '"2.89252253232364639"^^http://www.w3.org/2001/XMLSchema#double'],
      ['"Edinburgh"', '"5.39747043160034365"^^http://www.w3.org/2001/XMLSchema#double'],
    ],
  });
});

test('post21 cell 6 (geof:envelope): polygon envelopes to itself, point to a degenerate box', async () => {
  const result = await runObservableCell(cells[5], B);
  assert.deepEqual(result, {
    kind: 'table',
    columns: ['name', 'env'],
    rows: [
      [
        '"Greater London (toy box)"',
        '"POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))"^^http://www.opengis.net/ont/geosparql#wktLiteral',
      ],
      [
        '"London"',
        '"POLYGON((-0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074))"^^http://www.opengis.net/ont/geosparql#wktLiteral',
      ],
    ],
  });
});

test('post21 cell 7 (exact boundary): on-edge point is intersects+touches but NOT within', async () => {
  const result = await runObservableCell(cells[6], B);
  assert.deepEqual(result, {
    kind: 'table',
    columns: ['point', 'sfWithin', 'sfIntersects', 'sfTouches'],
    rows: [
      ['exactly on the edge (y = 51.3)', false, true, true],
      ['strictly inside', true, true, false],
      ['clearly outside', false, false, false],
    ],
  });
});
