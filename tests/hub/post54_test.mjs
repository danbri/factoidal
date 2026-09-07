// Pins docs/web/hub/54-skosdex-over-r2.md.
//
// The page has one interactive cell, so its cell source is not executed
// here (there is no DOM). What IS executed is the nine SPARQL shapes the
// cell ships: they are extracted from the cell's own `const shapes = […]`
// literal and run through the real store-over-HTTP host against a mock
// bucket, so a query that rots on the page fails here rather than
// silently answering nothing in a reader's browser.
//
// The recorded table in the post's prose is checked against those same
// measurements, so the objects and bytes a reader is told to expect are
// the ones the engine's plan actually asks for.
//
// Nothing here touches a network, Cloudflare or credentials.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

import { extractObservableCells } from './_helpers.mjs';
import { startMockBucket } from '../store-http/mock-bucket.mjs';
import { openStoreOverHttp } from '../../npm/factoidal/store-http/index.mjs';

const POST_FILE = '54-skosdex-over-r2.md';
const POST_PATH = new URL(`../../docs/web/hub/${POST_FILE}`, import.meta.url);
const SAMPLE = new URL('../../npm/factoidal/sample-store', import.meta.url).pathname;
const HUB_NJK = new URL('../../docs/_includes/hub.njk', import.meta.url);
const ELEVENTY = new URL('../../docs/.eleventy.js', import.meta.url);

const source = readFileSync(POST_PATH, 'utf8');
const cells = extractObservableCells(POST_FILE);

/** The nine shapes exactly as the shipped cell declares them. */
function shapesOfCell (cellSource) {
  const start = cellSource.indexOf('const shapes = [');
  assert.ok(start >= 0, 'the cell must declare `const shapes = [`');
  const open = cellSource.indexOf('[', start);
  let depth = 0;
  let end = -1;
  let quote = null;
  for (let index = open; index < cellSource.length; index += 1) {
    const character = cellSource[index];
    if (quote !== null) {
      if (character === '\\') index += 1;
      else if (character === quote) quote = null;
      continue;
    }
    if (character === '"' || character === "'" || character === '`') quote = character;
    else if (character === '[') depth += 1;
    else if (character === ']') {
      depth -= 1;
      if (depth === 0) { end = index; break; }
    }
  }
  assert.ok(end > open, 'the shapes literal must close');
  // eslint-disable-next-line no-new-func
  return new Function(`return ${cellSource.slice(open, end + 1)};`)();
}

const shapes = shapesOfCell(cells[0] ?? '');

test('post54: one interactive cell, nine named shapes', () => {
  assert.equal(cells.length, 1);
  assert.equal(shapes.length, 9);
  assert.equal(new Set(shapes.map((s) => s.id)).size, 9);
  for (const shape of shapes) {
    assert.ok(shape.title.length > 0, `${shape.id} has a title`);
    assert.ok(shape.why.length > 0, `${shape.id} says why`);
    assert.match(shape.q, /SELECT/);
  }
});

test('post54: says what the mechanism is, and what it is not', () => {
  assert.match(source, /hubHideCellSource:\s*true/);
  assert.match(source, /storeQueryPlan/);
  assert.match(source, /storeManifestInspect/);
  assert.match(source, /storeQuery/);
  assert.match(source, /SHA-256 the\s+manifest commits/);
  assert.match(source, /refused by name/);
  assert.match(source, /host-purity-lint/);
  assert.match(source, /full-manifest/);
  assert.match(source, /zoneExcluded/);
  // The R2 finding must stay in the prose while it is true.
  assert.match(source, /538 s/);
  assert.match(source, /25,533,404 bytes/);
  assert.match(source, /219,530,671/);
  assert.match(source, /36,106/);
  assert.match(source, /rate-limits the\s+`r2\.dev`/);
  assert.match(source, /connect-src 'self'/);
});

test('post54: the cell and the prose name the same bucket', () => {
  const inCell = /const r2Base = "([^"]+)"/.exec(cells[0]);
  assert.ok(inCell, 'the cell declares r2Base');
  assert.ok(source.includes(inCell[1].replace(/\/$/, '')),
    'the prose must name the same bucket the cell offers');
  assert.match(cells[0], /new URL\("\.\.\/assets\/store\/sample\/", location\.href\)/);
});

test('post54: the page can reach the engine and the store the cell asks for', () => {
  const njk = readFileSync(HUB_NJK, 'utf8');
  assert.match(njk, /async l4CallBlobIO\(op, args, blobIn\)/);
  assert.match(njk, /async openStoreOverHttp\(baseUrl, options\)/);
  assert.match(njk, /\/npm\/factoidal\/store-http\/index\.mjs/);
  const eleventy = readFileSync(ELEVENTY, 'utf8');
  assert.match(eleventy, /"\.\.\/npm\/factoidal\/store-http": "npm\/factoidal\/store-http"/);
  assert.match(eleventy, /"\.\.\/npm\/factoidal\/sample-store": "web\/hub\/assets\/store\/sample"/);
});

test('post54: the nine shapes answer over HTTP, and the table is what they cost',
  async () => {
    const bucket = await startMockBucket({ root: SAMPLE });
    try {
      const store = await openStoreOverHttp(bucket.url, { concurrency: 4 });
      assert.equal(store.generation, 'gen-1');
      assert.equal(store.facts.entries, 13);
      assert.equal(store.facts.bytes, 455818);
      assert.equal(store.facts.manifestBytes, 6044);

      // The prose table, read back out of the post.
      const recorded = new Map();
      for (const line of source.split('\n')) {
        const cell = /^\| ([^|]+?) \| `([^`]+)` \| (\d+) \| ([\d,]+) \| (\d+) \|$/.exec(line.trim());
        if (cell !== null) {
          recorded.set(cell[1].trim(), {
            mode: cell[2],
            objects: Number(cell[3]),
            bytes: Number(cell[4].replace(/,/g, '')),
            rows: Number(cell[5])
          });
        }
      }
      assert.equal(recorded.size, 9, 'the post records all nine questions');

      for (const shape of shapes) {
        const answer = await store.query(shape.q);
        const rows = answer.result.srj?.results?.bindings ?? [];
        assert.equal(answer.result.kind, 'select', shape.id);
        assert.ok(rows.length > 0, `${shape.id} answered no rows`);
        assert.ok(answer.requests.every((request) => request.verified),
          `${shape.id} sent an artifact the host had not checked`);
        assert.deepEqual(
          answer.artifacts.map((artifact) => artifact.key),
          answer.plan.keys.concat(answer.plan.blobKeys ?? []),
          `${shape.id} fetched something other than what the plan named`);

        const said = recorded.get(shape.title);
        assert.ok(said, `the post records no line for "${shape.title}"`);
        assert.equal(answer.plan.mode, said.mode, `${shape.id} plan mode`);
        assert.equal(answer.requests.length, said.objects, `${shape.id} objects`);
        assert.equal(answer.timings.networkBytes, said.bytes, `${shape.id} bytes`);
        assert.equal(rows.length, said.rows, `${shape.id} rows`);
      }

      // Eight of the nine read less than the whole generation; the ninth is
      // the unbound-predicate shape, and the post says which one that is.
      assert.equal(
        [...recorded.values()].filter((row) => row.objects < 13).length, 8);
      assert.equal(recorded.get('Predicate census').objects, 13);
    } finally {
      await bucket.close();
    }
  });
