// Wasm-entry counterpart to cottas-bytes-store.test.js: proves the
// in-memory COTTAS bytes store ABI (openCottas/queryCottas/closeCottas/
// toCottas, bin/npm-entry/entry_jsoo.ml) also works when the npm-entry
// bundle is compiled through wasm_of_ocaml (factoidal-npm-entry.wasm.js)
// rather than js_of_ocaml (factoidal-npm-entry.js). Same fixture data,
// same assertions as the js version; run against the wasm ABI via
// wasm.js's `_loadEntryForTest` test hook (mirrors delta-log-wasm.test.js
// / wasm-parity.test.js's js-vs-wasm parity pattern). Skips cleanly when
// the wasm bundle or a WasmGC-capable Node is unavailable.
//
// HISTORY -- the Stdint/wasm gap this file used to pin, and why the
// fixture strategy changed:
//
// Until 2026-07-06, EVERY wasm COTTAS open failed with
// `Invalid_argument("Uint32.of_string")`: `FStar_UInt32`'s OCaml
// realization (F*'s ulib/ml/FStar_UInt32.ml) is `Stdint.Uint32`, and
// wasm_of_ocaml had no Wasm-level binding for the `uint32_*` primitives
// Stdint's C stubs realize natively and js_of_ocaml realizes via
// ../fstar_int_stubs.js's plain-JS `//Provides:` functions -- confirmed
// by disassembling a built factoidal.wasm.js with `wasm-dis` and
// finding every `uint32_*` import wired to wasm_stub_shims.py's blanket
// identity stub (`(...a)=>a[0]!==undefined?a[0]:0`) rather than real
// arithmetic, even though fstar_int_stubs.js was already being passed
// to `wasm_of_ocaml compile`. That's now fixed by
// ocaml-output/wasm_runtime/stdint_uint32_runtime.wat, a hand-written
// (not vendored) Wasm module giving wasm_of_ocaml real `uint32_*`
// bindings the same way ocaml-output/wasm_runtime/zarith_runtime.wat
// already does for Zarith's `ml_z_*` -- see that .wat file's header for
// the full rationale, and this directory's ../wasm_runtime/README.md.
//
// Fixing that gap exposed a SEPARATE, narrower one: the on-disk
// `tests/unit/fixtures/store_capabilities_sample.cottas` fixture (built
// long ago from tests/local/data/cottas_sample.nq, and normally read
// via `fs.readFileSync` + `openCottas`) has Zstd-compressed pages
// (confirmed: its bytes contain the Zstd frame magic `28 B5 2F FD`
// three times). Zstd decompression is realized by a *different*
// primitive, `caml_parquet_zstd_decompress_hex`
// (formal/fstar/experimental_ocaml_glue/parquet_zstd_stubs.c /
// ocaml-output/parquet_zstd_stubs.js), which is ALSO still
// identity/dummy-shimmed under wasm_of_ocaml (it shows up in
// `build-ocaml.sh wasm-factoidal`'s own "Missing Wasm primitives" log,
// same family as the pre-existing documented SHA/digestif gap in that
// script's header comment) -- opening the static compressed fixture
// under wasm now gets past the Stdint failure and instead throws a
// Wasm-level `RuntimeError: illegal cast` while decoding a page that
// decompressed to garbage. That is a distinct, still-open gap, out of
// scope for the Stdint fix; it does not affect js_of_ocaml (whose
// fzstd.umd.js-backed decompressor works today) or native.
//
// Because the *content* of that fixture is exactly
// tests/local/data/cottas_sample.nq (see cottas-bytes-store.test.js's
// header), every test below builds its own COTTAS bytes via
// `toCottas(nq)` (uncompressed -- small in-memory writes don't reach
// for Zstd) instead of reading the static compressed file, so these
// tests exercise the now-fixed Stdint/u32 path end-to-end (open, query,
// including default-graph matching, GRAPH ?g, ASK, and toCottas' own
// writer) without tripping over the separate Zstd gap. The static
// compressed fixture is still exercised fine on native and js_of_ocaml
// (cottas-bytes-store.test.js), so nothing regresses there.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const wasmEngine = require('../wasm.js');

const NODE_MAJOR = Number(process.versions.node.split('.')[0]);

const FIXTURE_NQ = path.resolve(
  __dirname, '..', '..', '..', 'tests', 'local', 'data', 'cottas_sample.nq');
const haveFixtures = fs.existsSync(FIXTURE_NQ);

function wasmSkipReason() {
  if (NODE_MAJOR < 22) {
    return `Node ${process.versions.node} < 22 (WasmGC needed)`;
  }
  if (!wasmEngine.wasmAvailable()) {
    return 'factoidal.wasm.js / .wasm asset not present ' +
      "(run 'build-ocaml.sh wasm-factoidal', then 'build-ocaml.sh npm')";
  }
  if (!haveFixtures) return 'fixture .nq not found';
  return null;
}

async function loadAbi() {
  const abi = await wasmEngine._loadEntryForTest();
  if (abi && typeof abi.openCottas === 'function') return abi;
  return null;
}

// Builds a fresh, uncompressed COTTAS byte buffer (hex) from the
// shared fixture .nq via the wasm ABI's own toCottas writer -- see the
// file header for why this replaces reading the static compressed
// fixture directly.
function buildCottasHex(abi) {
  const nq = fs.readFileSync(FIXTURE_NQ, 'utf8');
  const written = JSON.parse(abi.toCottas(nq));
  assert.equal(written.ok, true, JSON.stringify(written));
  assert.equal(written.quadCount, 5);
  return written.cottasHex;
}

test('wasm ABI: openCottas + queryCottas match the fixture\'s known content', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }
  const abi = await loadAbi();
  if (!abi) { t.skip('wasm npm-entry bundle predates openCottas'); return; }

  const cottasHex = buildCottasHex(abi);
  const opened = JSON.parse(abi.openCottas(cottasHex));
  assert.equal(opened.ok, true, JSON.stringify(opened));
  const handle = opened.handle;

  const countDefault = JSON.parse(
    abi.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'));
  assert.equal(countDefault.srj.results.bindings[0].c.value, '1');

  const countNamed = JSON.parse(
    abi.queryCottas(handle, 'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }'));
  assert.equal(countNamed.srj.results.bindings[0].c.value, '4');

  const ask = JSON.parse(abi.queryCottas(handle,
    'ASK { <https://example.org/default-subject> <https://example.org/status> "default" }'));
  assert.equal(ask.boolean, true);

  const closed = JSON.parse(abi.closeCottas(handle));
  assert.equal(closed.ok, true);
});

test('wasm ABI: toCottas + openCottas round-trip', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }
  const abi = await loadAbi();
  if (!abi) { t.skip('wasm npm-entry bundle predates toCottas'); return; }

  const cottasHex = buildCottasHex(abi);
  const opened = JSON.parse(abi.openCottas(cottasHex));
  assert.equal(opened.ok, true, JSON.stringify(opened));
  const count = JSON.parse(abi.queryCottas(opened.handle,
    'SELECT (COUNT(*) AS ?c) WHERE { GRAPH ?g { ?s ?p ?o } }'));
  assert.equal(count.srj.results.bindings[0].c.value, '4');
  abi.closeCottas(opened.handle);
});

test('wasm/js parity: openCottas + queryCottas give byte-identical SELECT bindings', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }
  const wasmAbi = await loadAbi();
  if (!wasmAbi) { t.skip('wasm npm-entry bundle predates openCottas'); return; }

  const jsEngine = require('..');
  const cottasHex = buildCottasHex(wasmAbi);
  const bytes = Buffer.from(cottasHex, 'hex');

  const jsHandle = await jsEngine.openCottas(bytes);
  const jsRows = await jsEngine.queryCottas(jsHandle,
    'SELECT ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }');
  await jsEngine.closeCottas(jsHandle);

  const wasmHandle = JSON.parse(wasmAbi.openCottas(cottasHex)).handle;
  const wasmSrj = JSON.parse(wasmAbi.queryCottas(wasmHandle,
    'SELECT ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }'));
  wasmAbi.closeCottas(wasmHandle);

  const norm = (rows) => rows.map((r) =>
    [...r.entries()].map(([k, v]) => `${k}=${v.value}`).sort().join('|')).sort();
  const wasmRowsNorm = wasmSrj.srj.results.bindings.map((b) =>
    Object.entries(b).map(([k, v]) => `${k}=${v.value}`).sort().join('|')).sort();
  assert.deepEqual(wasmRowsNorm, norm(jsRows));
});
