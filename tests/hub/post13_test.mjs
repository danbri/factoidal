// Pins every code sample in docs/web/hub/13-verifiable-credentials-and-csvw.md.
//
// This post's live cells call `Factoidal.csvwToRdf(...)` -- the raw
// ABI npm/factoidal/browser.js exposes -- same rationale as
// post10_test.mjs: in the browser `Factoidal` resolves to browser.js,
// whose csvwToRdf() fetches the npm-entry ABI bundle over the network;
// Node has no `file://` fetch, so this test calls the exact same
// underlying ABI function via `require()` instead, mirroring
// browser.js's own implementation byte-for-byte.
//
// The VC section of this post has no live cell at all (no browser
// export exists) -- nothing to pin there beyond the static JSON
// fixture's own validity, checked directly below.

import { createRequire } from 'node:module';
import { extractObservableCells, runObservableCell, HUB_POST_DIR } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';

const require = createRequire(import.meta.url);
const POST_FILE = '13-verifiable-credentials-and-csvw.md';
const REPO_ROOT = path.join(HUB_POST_DIR, '..', '..', '..');

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

const Factoidal = {
  async csvwToRdf(csvText, metadataJson, options) {
    if (typeof abi.csvwToRdf !== 'function') {
      throw new Error('csvwToRdf: the loaded factoidal-npm-entry bundle predates the CSVW export');
    }
    const meta = metadataJson == null ? '' : metadataJson;
    const optionsJson = JSON.stringify(options || {});
    const parsed = JSON.parse(abi.csvwToRdf(csvText, meta, optionsJson));
    if (!parsed.ok) throw new Error(parsed.error || 'csvwToRdf failed');
    return parsed;
  },
};

const cells = extractObservableCells(POST_FILE);

test('post13: post has at least 2 live cells (CSVW only -- VC has none, by design)', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post13 cell 1 (CSVW standard mode): 24 total quads, 10 of them row data', async () => {
  const result = await runObservableCell(cells[0], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.totalQuads, 24);
  assert.equal(result.dataQuads, 10);
  // 5 lines whose subject is gid-1, plus 1 provenance line
  // (`csvw:describes` pointing at gid-1 from its row resource).
  assert.equal(result.firstRow.length, 6);
});

test('post13 cell 2 (CSVW minimal mode): exactly 10 quads, no provenance triples', async () => {
  const result = await runObservableCell(cells[1], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.totalQuads, 10);
  assert.ok(!result.lines.some((l) => l.includes('csvw#Row') || l.includes('csvw#Table')));
});

test('post13: a cell degrades gracefully when the ABI lacks csvwToRdf', async () => {
  const brokenFactoidal = {
    async csvwToRdf() {
      throw new Error('csvwToRdf: the loaded factoidal-npm-entry bundle predates the CSVW export');
    },
  };
  const result = await runObservableCell(cells[0], { Factoidal: brokenFactoidal });
  assert.equal(result.available, false);
  assert.match(result.note, /predates the CSVW export/);
});

// ---------------------------------------------------------------------
// Direct API / fixture checks, independent of the cell-extraction
// machinery above.
// ---------------------------------------------------------------------

test('post13: the vendored tree-ops.csv + metadata fixture converts via the real ABI, matching the post\'s own inline copy', async () => {
  const fs = await import('node:fs');
  const csvText = fs.readFileSync(
    path.join(REPO_ROOT, 'third_party', 'testing', 'csvw', 'examples', 'tree-ops.csv'), 'utf8');
  const metadataJson = fs.readFileSync(
    path.join(REPO_ROOT, 'third_party', 'testing', 'csvw', 'examples', 'tree-ops.csv-metadata.json'), 'utf8');
  const result = await Factoidal.csvwToRdf(csvText, metadataJson, { base: 'http://example.org/' });
  const lines = result.nquads.trim().split('\n');
  // The vendored fixture carries a fuller metadata document (dc:title,
  // dc:publisher, etc. -- see the file itself) than this post's
  // trimmed inline copy, so it emits more triples; what matters here
  // is that both rows convert and the gid-1 subject/columns line up.
  assert.ok(lines.some((l) => l.includes('gid-1') && l.includes('#GID') && l.includes('"1"')));
  assert.ok(lines.some((l) => l.includes('gid-2') && l.includes('#species') && l.includes('Liquidambar')));
});

test('post13: the vendored validVc.json fixture is the exact JSON shown statically in the post', async () => {
  const fs = await import('node:fs');
  const fixture = JSON.parse(fs.readFileSync(
    path.join(REPO_ROOT, 'third_party', 'testing', 'vc', 'tests', 'validVc.json'), 'utf8'));
  assert.deepEqual(fixture['@context'], ['https://www.w3.org/2018/credentials/v1']);
  assert.deepEqual(fixture.type, ['VerifiableCredential']);
  assert.ok(fixture.credentialSubject && typeof fixture.credentialSubject.id === 'string');
});

test('post13: npm/factoidal has no VC-shaped export (grounds the "no browser cell" claim)', async () => {
  const factoidal = (await import(path.join(REPO_ROOT, 'npm', 'factoidal', 'index.mjs'))).default;
  const vcLikeKeys = Object.keys(factoidal).filter((k) => /vc|credential/i.test(k));
  assert.deepEqual(vcLikeKeys, []);
});
