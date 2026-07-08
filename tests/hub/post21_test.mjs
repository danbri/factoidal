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
// Cell 3 (index 2) is the Leaflet map cell: it renders geof:sfWithin's
// result rather than computing anything new, so what's pinned here is
// (a) the pure WKT-parsing and color-selection logic -- duplicated
// below from the cell's own inline copy, since cell bodies can't
// `import` (see docs/web/hub/README.md's "cell bindings" section) --
// tested directly with plain assertions, no DOM involved, and (b) that
// the cell's actual shipped source runs to completion without throwing
// when given a minimal `document`/`L` stub standing in for the
// browser's real DOM and the real Leaflet library. Node has no layout
// engine, so a full visual render is NOT asserted here -- that's
// pending the headless-Chrome harness (issue #84).

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '21-geosparql-geometry-and-topology.md';

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

// --- Cell 3 (index 2): the Leaflet map cell -------------------------

// Mirrors the map cell's own inline `wktParse` -- see the header
// comment above for why this is a duplicate rather than a shared
// import. Keep in sync by hand with the copy in
// docs/web/hub/21-geosparql-geometry-and-topology.md if either changes.
function wktParse(wkt) {
  const s = wkt.trim();
  let m = /^POINT\s*\(\s*([+-]?[\d.]+)\s+([+-]?[\d.]+)\s*\)$/i.exec(s);
  if (m) return { type: 'Point', lon: Number(m[1]), lat: Number(m[2]) };
  m = /^POLYGON\s*\(\s*\(([^)]*)\)\s*\)$/i.exec(s);
  if (m) {
    const ring = m[1].split(',').map((pair) => {
      const parts = pair.trim().split(/\s+/).map(Number);
      return [parts[0], parts[1]]; // [lon, lat]
    });
    return { type: 'Polygon', ring };
  }
  throw new Error('wktParse: unrecognized WKT: ' + wkt);
}

// Mirrors the map cell's own inline `colorForWithin`.
function colorForWithin(isWithin) {
  return isWithin ? '#2d6a4f' : '#8a8f98';
}

test('post21 map cell helper: wktParse reads POINT lon/lat in WKT order', () => {
  assert.deepEqual(wktParse('POINT(-0.1278 51.5074)'), {
    type: 'Point', lon: -0.1278, lat: 51.5074,
  });
});

test('post21 map cell helper: wktParse reads a POLYGON ring as [lon, lat] pairs', () => {
  const result = wktParse(
    'POLYGON((-0.5 51.3, 0.3 51.3, 0.3 51.7, -0.5 51.7, -0.5 51.3))'
  );
  assert.deepEqual(result, {
    type: 'Polygon',
    ring: [[-0.5, 51.3], [0.3, 51.3], [0.3, 51.7], [-0.5, 51.7], [-0.5, 51.3]],
  });
});

test('post21 map cell helper: colorForWithin maps the engine boolean to green/grey', () => {
  assert.equal(colorForWithin(true), '#2d6a4f');
  assert.equal(colorForWithin(false), '#8a8f98');
});

test('post21 map cell color logic: London green/inside, Manchester + Edinburgh grey, for Greater London', async () => {
  // The exact sfWithin(?cgeom, GreaterLondonArea) relation the map cell
  // reads to decide the Greater-London-box color -- run against the
  // REAL npm/factoidal engine, not a hand-simulated result, so this
  // pins what the F* engine actually decides.
  const dataset = await factoidal.parse(`
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
  `);
  const rows = await factoidal.query(dataset, `
    PREFIX ex:   <http://example.org/>
    PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
    SELECT ?cityName WHERE {
      ?city a ex:City ; ex:name ?cityName ; ex:hasGeom ?cgeom .
      ex:GreaterLondonArea ex:hasGeom ?ageom .
      FILTER(geof:sfWithin(?cgeom, ?ageom))
    } ORDER BY ?cityName`);
  const withinGreaterLondon = new Set(rows.map((r) => r.get('cityName').value));
  const colorFor = (name) => colorForWithin(withinGreaterLondon.has(name));

  assert.equal(colorFor('London'), '#2d6a4f', 'London is sfWithin Greater London -- green');
  assert.equal(colorFor('Manchester'), '#8a8f98', 'Manchester is not sfWithin Greater London -- grey');
  assert.equal(colorFor('Edinburgh'), '#8a8f98', 'Edinburgh is not sfWithin Greater London (it is within Scotland instead) -- grey');
});

test('post21 map cell (cell 3): runs to completion with a minimal document/L stub, no throw', async () => {
  // A chainable stub layer standing in for a real Leaflet Path/Layer:
  // .addTo()/.bindTooltip()/.setStyle() all return the SAME object so
  // the cell's `L.geoJSON(...).bindTooltip(name).addTo(map)` and
  // `L.circleMarker(...).addTo(map)` chains resolve exactly the way
  // real Leaflet's chaining API does.
  function stubLayer() {
    const layer = {};
    layer.addTo = () => layer;
    layer.bindTooltip = () => layer;
    layer.setStyle = () => layer;
    return layer;
  }
  const stubL = {
    map: () => ({ fitBounds() {}, invalidateSize() {} }),
    geoJSON: () => stubLayer(),
    circleMarker: () => stubLayer(),
  };
  // The cell calls `document.createElement("div")` directly (an
  // ambient global in the browser, per reactive-cells.mjs's own header
  // comment: "globals like Math/JSON/console/document ... stay
  // resolved through ordinary JS scope"). Node has no `document`, so
  // this test supplies the minimal stub the cell's own DOM usage
  // needs, then removes it -- this is a test-only global, never
  // touched by production code.
  const previousDocument = globalThis.document;
  globalThis.document = {
    createElement: () => ({ className: '', style: {} }),
  };
  try {
    const result = await runObservableCell(cells[2], { fn: factoidal, pretty, L: stubL });
    // Success path returns the container object the stub
    // `document.createElement` produced (not a `map unavailable`
    // fallback), proving fn.parse/fn.query/wktParse/colorForWithin/L
    // all ran without throwing.
    assert.ok(result && typeof result === 'object', 'map cell should return the map container object');
    assert.equal(result.className, 'hub-leaflet-map');
  } finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
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
