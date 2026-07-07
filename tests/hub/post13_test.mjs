// Pins every live code cell in docs/web/hub/13-verifiable-credentials-and-csvw.md.
//
// The post has four live cells, in document order:
//   [0] VC Data Integrity step 1 -- RDFC-1.0 canonicalize the credential
//       dataset (`Factoidal.canonicalize`, the raw ABI export post 08
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
// `require()` instead. `Factoidal.canonicalize` is the npm-index
// wrapper over the raw `canonicalizeToNQuads` ABI export, mirroring
// browser.js's `canonicalize` binding.
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
// The npm-index default export is what browser.js's `canonicalize`
// binding resolves to; use its wrapper so the cell's
// `Factoidal.canonicalize(text, { format })` contract is exercised
// exactly as it runs in-browser.
const npmFactoidal = (await import('../../npm/factoidal/index.mjs')).default;

const Factoidal = {
  canonicalize: npmFactoidal.canonicalize,
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
  const result = await runObservableCell(cells[0], { Factoidal });
  assert.equal(result.lines, 3);
  assert.match(result.canonical, /_:c14n0/);
  // The credential's own IRIs survive; the arbitrary _:b0 label does not.
  assert.match(result.canonical, /urn:credential:1/);
  assert.ok(!result.canonical.includes('_:b0'));
});

test('post13 cell 2 (VC step 2: SHA-256 of canonical form): 64 hex chars, stable digest', async () => {
  const result = await runObservableCell(cells[1], { Factoidal });
  assert.equal(result.hashLength, 64);
  assert.match(result.sha256, /^[0-9a-f]{64}$/);
  // Deterministic: this is the SHA-256 of the canonical credential
  // dataset the native vc_runner also signs.
  assert.equal(result.sha256, '1ae5f4ab2b655716e6fa6ce7e340fbeb13512adb6d09815e5e7b3f29c8a25e43');
});

test('post13 cell 3 (CSVW standard mode): 24 total quads, 10 of them row data', async () => {
  const result = await runObservableCell(cells[2], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.totalQuads, 24);
  assert.equal(result.dataQuads, 10);
  // 5 lines whose subject is gid-1, plus 1 provenance line
  // (`csvw:describes` pointing at gid-1 from its row resource).
  assert.equal(result.firstRow.length, 6);
});

test('post13 cell 4 (CSVW minimal mode): exactly 10 quads, no provenance triples', async () => {
  const result = await runObservableCell(cells[3], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.totalQuads, 10);
  assert.ok(!result.lines.some((l) => l.includes('csvw#Row') || l.includes('csvw#Table')));
});

test('post13: a CSVW cell degrades gracefully when the ABI lacks csvwToRdf', async () => {
  const brokenFactoidal = {
    canonicalize: npmFactoidal.canonicalize,
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
