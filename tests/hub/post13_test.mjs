// Pins every live code cell in docs/web/hub/13-verifiable-credentials-and-csvw.md.
//
// The post has four live cells, in document order:
//   [0] VC Data Integrity step 1 -- RDFC-1.0 canonicalize the credential
//       dataset (`fn.canonicalize`, the same typed wrapper post 08
//       introduced).
//   [1] VC Data Integrity step 2 -- SHA-256 of the canonical form, via
//       Web Crypto's `crypto.subtle.digest` (a browser/Node built-in,
//       not one of our exports).
//   [2] CSVW standard mode  (`Factoidal.csvwToRdf`).
//   [3] CSVW minimal mode   (`Factoidal.csvwToRdf`).
//
// The Ed25519 sign/verify roundtrip is NATIVE-ONLY (vendored HACL* C
// does not link under wasm_of_ocaml -- tracked in #286), so it is shown
// as a `vc_runner --crypto` CLI transcript, not a live cell; the
// cell-runner cannot pin a native binary, so that transcript is pinned
// by the vc_runner --crypto self-test itself (8 pass, 0 fail).
//
// `Factoidal.csvwToRdf(...)` here calls the raw ABI npm/factoidal/
// browser.js exposes -- same rationale as post10_test.mjs: in the
// browser `Factoidal` resolves to browser.js, whose csvwToRdf() fetches
// the npm-entry ABI bundle over the network; Node has no `file://`
// fetch, so this test calls the same underlying ABI function via
// `require()` instead. `fn.canonicalize` is the real npm/factoidal
// typed API's `canonicalize`, mirroring `docs/_includes/hub.njk`'s
// `fn.canonicalize` adapter (which itself wraps browser.js's
// `canonicalize` binding).
//
// The VC *structural* validator still has no browser export (no
// `vcValidate`, nothing VC-shaped); the "no VC-shaped export" check at
// the bottom grounds that claim.

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
// The npm-index default export is the real typed API `fn.canonicalize`
// resolves to in the browser (via docs/_includes/hub.njk's `fn`
// adapter, which wraps browser.js's `canonicalize` binding).
const npmFactoidal = (await import('../../npm/factoidal/index.mjs')).default;
const fn = { canonicalize: npmFactoidal.canonicalize };

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

test('post13: post has 4 live cells (2 VC pipeline + 2 CSVW)', () => {
  assert.equal(cells.length, 4, `expected exactly 4 live cells, found ${cells.length}`);
});

test('post13 cell 1 (VC step 1: RDFC-1.0 canonicalize): 3 lines, bnode canonicalized to _:c14n0', async () => {
  const result = await runObservableCell(cells[0], { fn });
  assert.equal(result.lines, 3);
  assert.match(result.canonical, /_:c14n0/);
  // The credential's own IRIs survive; the arbitrary _:b0 label does not.
  assert.match(result.canonical, /urn:credential:1/);
  assert.ok(!result.canonical.includes('_:b0'));
});

test('post13 cell 2 (VC step 2: SHA-256 of canonical form): 64 hex chars, stable digest', async () => {
  const result = await runObservableCell(cells[1], { fn });
  assert.equal(result.hashLength, 64);
  assert.match(result.sha256, /^[0-9a-f]{64}$/);
  // Deterministic: this is the SHA-256 of the canonical credential
  // dataset the native vc_runner also signs.
  assert.equal(result.sha256, '1ae5f4ab2b655716e6fa6ce7e340fbeb13512adb6d09815e5e7b3f29c8a25e43');
});

test('post13 cell 3 (CSVW standard mode): 22 quads = 8 typed row data + 14 provenance', async () => {
  const result = await runObservableCell(cells[2], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.totalQuads, 22);
  assert.equal(result.dataQuads, 8);
  assert.equal(result.provenanceQuads, 14);
  // The first row's four emitted columns (code is suppressOutput), all
  // sharing the subject the {#code} fragment template built.
  assert.equal(result.sampleTypedTriples.length, 4);
  assert.ok(result.sampleTypedTriples.every((l) => l.startsWith('<http://example.org/sites#BRS>')));
  // datatype coercion is visible in the literal type: number -> xsd:double,
  // integer -> xsd:integer.
  assert.ok(result.sampleTypedTriples.some(
    (l) => l.includes('http://schema.org/latitude') && l.includes('XMLSchema#double')));
  assert.ok(result.sampleTypedTriples.some(
    (l) => l.includes('http://schema.org/population') && l.includes('XMLSchema#integer')));
});

test('post13 cell 4 (CSVW minimal mode): 8 typed quads, no provenance, template subjects', async () => {
  const result = await runObservableCell(cells[3], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.totalQuads, 8);
  assert.equal(result.hasDoubleTyping, true);
  assert.equal(result.hasIntegerTyping, true);
  // Both subjects come from the RFC 6570 fragment template aboutUrl.
  assert.deepEqual(
    [...result.templatedSubjects].sort(),
    ['<http://example.org/sites#BRS>', '<http://example.org/sites#BTH>']);
  assert.ok(!result.lines.some((l) => l.includes('csvw#Row') || l.includes('csvw#Table')));
});

test('post13: a CSVW cell degrades gracefully when the ABI lacks csvwToRdf', async () => {
  const brokenFactoidal = {
    async csvwToRdf() {
      throw new Error('csvwToRdf: the loaded factoidal-npm-entry bundle predates the CSVW export');
    },
  };
  const result = await runObservableCell(cells[2], { Factoidal: brokenFactoidal });
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

test('post13: npm/factoidal has no VC-shaped export (grounds the "structural validation has no browser export" claim)', async () => {
  const factoidal = (await import(path.join(REPO_ROOT, 'npm', 'factoidal', 'index.mjs'))).default;
  const vcLikeKeys = Object.keys(factoidal).filter((k) => /vc|credential/i.test(k));
  assert.deepEqual(vcLikeKeys, []);
});
