// Proves browser-wasm.js's npm-entry ABI loader (loadNpmEntryWasm) and
// the openCottas/queryCottas/closeCottas/toCottas wrappers built on it
// (added alongside this test -- previously browser-wasm.js only drove
// the CLI bundle and had no way to reach the in-memory COTTAS bytes
// store; see that file's loadNpmEntryWasm() doc comment for the full
// rationale and cottas-bytes-store-wasm.test.js's header for the
// Stdint/Zstd history this API sits on top of).
//
// We can't spin up a real browser here; instead we drive
// browser-wasm.js the same way test/smoke-wasm.mjs already does for
// query() -- inject the npm-entry wasm bundle's source via
// _setFactoidalNpmEntryWasmSource() and an fs.readFileSync-based
// reader for its .wasm asset via _setNpmEntryWasmAssetFallback().
// Both hooks are test-only; a real browser uses fetch() for both and
// doesn't need them.
//
// Skips cleanly (does not fail) when Node < 22 (WasmGC) or the
// npm-entry wasm bundle/asset isn't present.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const NODE_MAJOR = Number(process.versions.node.split('.')[0]);

function resolveNpmEntryWasmBundle() {
  const envPath = process.env.FACTOIDAL_NPM_ENTRY_WASM;
  const jsPath = (envPath && fs.existsSync(envPath))
    ? envPath
    : path.resolve(__dirname, '..', 'factoidal-npm-entry.wasm.js');
  const assetsDir = path.join(path.dirname(jsPath), 'factoidal-npm-entry.wasm.assets');
  return { jsPath, assetsDir };
}

function skipReason() {
  if (NODE_MAJOR < 22) return `Node ${process.versions.node} < 22 (WasmGC needed)`;
  const { jsPath, assetsDir } = resolveNpmEntryWasmBundle();
  if (!fs.existsSync(jsPath)) return `factoidal-npm-entry.wasm.js not present at ${jsPath}`;
  if (!fs.existsSync(assetsDir) ||
      !fs.readdirSync(assetsDir).some((f) => f.endsWith('.wasm'))) {
    return `factoidal-npm-entry.wasm.assets/*.wasm not present at ${assetsDir}`;
  }
  return null;
}

async function loadBrowserWasmModule() {
  const mod = await import(
    require('node:url').pathToFileURL(path.resolve(__dirname, '..', 'browser-wasm.js')).href);
  const { jsPath, assetsDir } = resolveNpmEntryWasmBundle();
  const src = fs.readFileSync(jsPath, 'utf8');
  mod._setFactoidalNpmEntryWasmSource(src);
  mod._setNpmEntryWasmAssetFallback((assetSubPath) => {
    const basename = assetSubPath.split('/').pop();
    const abs = path.join(assetsDir, basename);
    if (!fs.existsSync(abs)) throw new Error(`npm-entry wasm asset not found: ${abs}`);
    return fs.readFileSync(abs);
  });
  return mod;
}

const SAMPLE_NQ = '<https://example.org/s> <https://example.org/p> "o" .\n' +
  '<https://example.org/s2> <https://example.org/p2> <https://example.org/o2> <https://example.org/g> .\n';

test('browser-wasm: loadNpmEntryWasm resolves an ABI with queryDataset', async (t) => {
  const reason = skipReason();
  if (reason) { t.skip(reason); return; }
  const mod = await loadBrowserWasmModule();
  const abi = await mod.loadNpmEntryWasm();
  assert.equal(typeof abi.queryDataset, 'function');
  assert.equal(typeof abi.openCottas, 'function');
});

test('browser-wasm: toCottas + openCottas + queryCottas + closeCottas round-trip', async (t) => {
  const reason = skipReason();
  if (reason) { t.skip(reason); return; }
  const mod = await loadBrowserWasmModule();

  const bytes = await mod.toCottas(SAMPLE_NQ);
  assert.ok(bytes instanceof Uint8Array && bytes.length > 0);

  const handle = await mod.openCottas(bytes);
  assert.equal(typeof handle, 'string');

  const count = await mod.queryCottas(handle,
    'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }');
  assert.equal(count.kind, 'select');
  assert.equal(count.srj.results.bindings[0].c.value, '1');

  const ask = await mod.queryCottas(handle,
    'ASK { <https://example.org/s> <https://example.org/p> "o" }');
  assert.equal(ask.kind, 'ask');
  assert.equal(ask.boolean, true);

  await mod.closeCottas(handle);
});

test('browser-wasm: openCottas accepts a hex string too', async (t) => {
  const reason = skipReason();
  if (reason) { t.skip(reason); return; }
  const mod = await loadBrowserWasmModule();

  const bytes = await mod.toCottas(SAMPLE_NQ);
  const hex = Buffer.from(bytes).toString('hex');
  const handle = await mod.openCottas(hex);
  const count = await mod.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }');
  assert.equal(count.srj.results.bindings[0].c.value, '1');
  await mod.closeCottas(handle);
});
