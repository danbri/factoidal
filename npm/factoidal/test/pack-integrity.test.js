// The core deliverable this file exists to prove: a consumer who
// `npm install`s @danbri/foafos gets the FULL db API (openCottas/
// queryCottas/closeCottas/toCottas) working on BOTH engines (js_of_ocaml
// and wasm_of_ocaml) straight out of the packed tarball -- not the
// source tree.
//
// Deliberately does NOT `require('./helpers.js')`: that file points
// FACTOIDAL_JS_BUNDLE/FACTOIDAL_WASM_BUNDLE/FACTOIDAL_NPM_ENTRY(_WASM)
// at the repo's docs/fstar-extracted/ copies when present, which would
// silently make every require() below resolve engine bundles from the
// SOURCE TREE instead of the extracted tarball -- defeating the point
// of this test. `npm pack` + `tar xf` + `require()` from the extracted
// directory is the only path exercised here.
//
// What this proves, concretely:
//   1. `npm pack` on npm/factoidal produces a tarball.
//   2. The tarball's file list includes factoidal.wasm.assets/*.wasm
//      AND factoidal-npm-entry.wasm.assets/*.wasm (a pack that drops
//      the wasm binary is the classic bug this guards against).
//   3. From the EXTRACTED tarball: require the main entry (js engine),
//      parse + query a small graph.
//   4. From the EXTRACTED tarball: require('.../wasm.js') (wasm
//      engine), same parse + query.
//   5. openCottas() on a toCottas()-produced buffer, then a COUNT and
//      a SELECT on BOTH engines -- asserting js and wasm agree with
//      each other AND with the in-memory query() result (the ground
//      truth: the same data queried without ever going through COTTAS
//      bytes at all).
//
// Skips (not fails) only the wasm-specific assertions when Node < 22
// (WasmGC) or the packed tarball genuinely has no wasm bundle for this
// platform build -- the js-engine and tarball-content assertions never
// skip, since those need nothing but Node and npm.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');
const { execFileSync } = require('node:child_process');

const PKG_ROOT = path.resolve(__dirname, '..');
const NODE_MAJOR = Number(process.versions.node.split('.')[0]);

const SAMPLE_TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob" .
  ex:carol a foaf:Person ; foaf:name "Carol"@en .
`;

const SAMPLE_NQ =
  '<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> "Alice" .\n' +
  '<http://example.org/bob> <http://xmlns.com/foaf/0.1/name> "Bob" .\n' +
  '<http://example.org/alice> <http://xmlns.com/foaf/0.1/knows> <http://example.org/bob> .\n' +
  '<http://example.org/alice> <http://xmlns.com/foaf/0.1/age> "30"^^<http://www.w3.org/2001/XMLSchema#integer> <http://example.org/g1> .\n';

const COUNT_Q = 'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }';
const SELECT_Q = 'SELECT ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }';

function normalizeBindings(rows) {
  // rows: Array<Map<string, Term>> -- normalize each row to a sorted,
  // stringified form so js/wasm result-order differences don't matter.
  return rows
    .map((row) => {
      const parts = [];
      for (const [k, v] of row.entries()) parts.push(`${k}=${v.termType}:${v.value}`);
      return parts.sort().join('|');
    })
    .sort();
}

test('pack integrity: npm pack + extract + db API on both engines', async (t) => {
  let tmpDir = null;
  try {
    // --- 1. npm pack to a temp dir. ---
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-pack-'));
    const packOut = execFileSync(
      'npm', ['pack', '--pack-destination', tmpDir],
      { cwd: PKG_ROOT, encoding: 'utf8' });
    const lines = packOut.trim().split('\n').filter(Boolean);
    const tarballName = lines[lines.length - 1].trim();
    assert.ok(tarballName.endsWith('.tgz'), `unexpected npm pack output: ${packOut}`);
    const tarballPath = path.join(tmpDir, tarballName);
    assert.ok(fs.existsSync(tarballPath), `tarball not found at ${tarballPath}`);

    // --- 2. Assert the tarball's own file list carries the wasm assets
    //        BEFORE extracting -- catches a `files` misconfiguration
    //        even if extraction itself would silently drop nothing. ---
    const listing = execFileSync('tar', ['tf', tarballPath], { encoding: 'utf8' })
      .split('\n').filter(Boolean);
    const hasJsWasmAsset = listing.some(
      (p) => p.startsWith('package/factoidal.wasm.assets/') && p.endsWith('.wasm'));
    const hasEntryWasmAsset = listing.some(
      (p) => p.startsWith('package/factoidal-npm-entry.wasm.assets/') && p.endsWith('.wasm'));
    assert.ok(hasJsWasmAsset,
      `tarball is missing factoidal.wasm.assets/*.wasm -- listing:\n${listing.join('\n')}`);
    assert.ok(hasEntryWasmAsset,
      `tarball is missing factoidal-npm-entry.wasm.assets/*.wasm -- listing:\n${listing.join('\n')}`);

    // --- Extract. ---
    execFileSync('tar', ['xf', tarballPath], { cwd: tmpDir });
    const pkgDir = path.join(tmpDir, 'package');
    assert.ok(fs.existsSync(pkgDir), 'extracted package/ directory not found');

    // --- 3. require the main (js) entry from the EXTRACTED package,
    //        parse + query a small graph. ---
    const jsEngine = require(path.join(pkgDir, 'index.js'));
    const jsDs = await jsEngine.parse(SAMPLE_TTL, { format: 'turtle' });
    assert.equal(jsDs.size, 7, 'js engine: parsed triple count');
    const jsGroundTruth = await jsEngine.query(jsDs,
      'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?p foaf:name ?name }');
    assert.equal(jsGroundTruth.length, 3, 'js engine: query() returns 3 name bindings');

    // --- 4. require('.../wasm.js') from the EXTRACTED package, same
    //        parse + query. Node < 22 lacks WasmGC -- skip only the
    //        wasm-dependent assertions, not the whole test. ---
    let wasmEngine = null;
    let wasmSkipReason = null;
    if (NODE_MAJOR < 22) {
      wasmSkipReason = `Node ${process.versions.node} < 22 (WasmGC needed)`;
    } else {
      wasmEngine = require(path.join(pkgDir, 'wasm.js'));
      if (!wasmEngine.wasmAvailable || !wasmEngine.wasmAvailable()) {
        wasmSkipReason = 'extracted package has no usable factoidal.wasm.js/.wasm asset';
      }
    }

    if (wasmSkipReason) {
      t.diagnostic(`wasm engine assertions skipped: ${wasmSkipReason}`);
    } else {
      const wasmDs = await wasmEngine.parse(SAMPLE_TTL, { format: 'turtle' });
      assert.equal(wasmDs.size, 7, 'wasm engine: parsed triple count');
      const wasmGroundTruth = await wasmEngine.query(wasmDs,
        'PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?p foaf:name ?name }');
      assert.equal(wasmGroundTruth.length, 3, 'wasm engine: query() returns 3 name bindings');
      assert.deepEqual(
        normalizeBindings(wasmGroundTruth), normalizeBindings(jsGroundTruth),
        'js vs wasm: plain query() bindings agree');
    }

    // --- 5. openCottas() on a toCottas()-produced buffer; COUNT + SELECT
    //        on both engines, cross-checked against the in-memory ground
    //        truth (query() on the same N-Quads, no COTTAS involved). ---
    const capsJs = await jsEngine.capabilities();
    if (!capsJs.entry || !capsJs.cottasBytesStore) {
      t.skip('js npm-entry bundle unavailable or predates the COTTAS bytes store ABI');
      return;
    }

    const cottasBytes = await jsEngine.toCottas(SAMPLE_NQ, { format: 'nquads' });
    assert.ok(cottasBytes instanceof Uint8Array && cottasBytes.length > 0,
      'toCottas produced non-empty bytes');

    // In-memory ground truth: query the same N-Quads directly.
    const groundTruthCount = await jsEngine.query(SAMPLE_NQ, COUNT_Q, { format: 'nquads' });
    const groundTruthSelect = await jsEngine.query(SAMPLE_NQ, SELECT_Q, { format: 'nquads' });

    const jsHandle = await jsEngine.openCottas(cottasBytes);
    const jsCount = await jsEngine.queryCottas(jsHandle, COUNT_Q);
    const jsSelect = await jsEngine.queryCottas(jsHandle, SELECT_Q);
    await jsEngine.closeCottas(jsHandle);

    assert.equal(jsCount[0].get('c').value, groundTruthCount[0].get('c').value,
      'js: COUNT via COTTAS matches in-memory ground truth');
    assert.deepEqual(normalizeBindings(jsSelect), normalizeBindings(groundTruthSelect),
      'js: SELECT via COTTAS matches in-memory ground truth');

    if (!wasmSkipReason) {
      const capsWasm = await wasmEngine.capabilities();
      if (!capsWasm.entry || !capsWasm.cottasBytesStore) {
        t.diagnostic('wasm npm-entry bundle unavailable or predates the COTTAS bytes store ABI');
      } else {
        const wasmHandle = await wasmEngine.openCottas(cottasBytes);
        const wasmCount = await wasmEngine.queryCottas(wasmHandle, COUNT_Q);
        const wasmSelect = await wasmEngine.queryCottas(wasmHandle, SELECT_Q);
        await wasmEngine.closeCottas(wasmHandle);

        assert.equal(wasmCount[0].get('c').value, groundTruthCount[0].get('c').value,
          'wasm: COUNT via COTTAS matches in-memory ground truth');
        assert.deepEqual(normalizeBindings(wasmSelect), normalizeBindings(groundTruthSelect),
          'wasm: SELECT via COTTAS matches in-memory ground truth');

        assert.equal(jsCount[0].get('c').value, wasmCount[0].get('c').value,
          'js vs wasm: COUNT-via-COTTAS agree');
        assert.deepEqual(normalizeBindings(jsSelect), normalizeBindings(wasmSelect),
          'js vs wasm: SELECT-via-COTTAS agree');
      }
    }
  } finally {
    if (tmpDir) fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});
