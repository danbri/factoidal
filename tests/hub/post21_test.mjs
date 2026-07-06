// Pins every live cell in
// docs/web/hub/21-geosparql-geometry-and-topology.md.
//
// The post's cells call the typed `fn` adapter only (fn.parse /
// fn.query) -- geof: functions are ordinary SPARQL expressions, so a
// GeoSPARQL query goes through the same query path every other post
// uses, no raw-Factoidal shim needed. The Node-side `fn` binding is the
// REAL npm/factoidal typed API; `pretty` is the shared node-side stub
// from _helpers.mjs (same shape dispatch as hub.njk's DOM pretty()).

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '21-geosparql-geometry-and-topology.md';

const cells = extractObservableCells(POST_FILE);
const B = { fn: factoidal, pretty };

test('post21: post has 6 live cells', () => {
  assert.equal(cells.length, 6, `expected 6 live cells, found ${cells.length}`);
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

test('post21 cell 3 (geof:sfDisjoint): the two cities outside the London box', async () => {
  const result = await runObservableCell(cells[2], B);
  assert.deepEqual(result, {
    kind: 'table',
    columns: ['cityName'],
    rows: [['"Edinburgh"'], ['"Manchester"']],
  });
});

test('post21 cell 4 (geof:distance ORDER BY): London 0 first, then Manchester, Edinburgh', async () => {
  const result = await runObservableCell(cells[3], B);
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

test('post21 cell 5 (geof:envelope): polygon envelopes to itself, point to a degenerate box', async () => {
  const result = await runObservableCell(cells[4], B);
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

test('post21 cell 6 (exact boundary): on-edge point is intersects+touches but NOT within', async () => {
  const result = await runObservableCell(cells[5], B);
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
