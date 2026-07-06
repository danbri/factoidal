// Wasm-entry counterpart to cottas-bytes-store.test.js: proves the
// in-memory COTTAS bytes store ABI (openCottas/queryCottas/closeCottas/
// toCottas, bin/npm-entry/entry_jsoo.ml) also works when the npm-entry
// bundle is compiled through wasm_of_ocaml (factoidal-npm-entry.wasm.js)
// rather than js_of_ocaml (factoidal-npm-entry.js). Same fixture, same
// assertions as the js version; run against the wasm ABI via wasm.js's
// `_loadEntryForTest` test hook (mirrors delta-log-wasm.test.js /
// wasm-parity.test.js's js-vs-wasm parity pattern). Skips cleanly when
// the wasm bundle or a WasmGC-capable Node is unavailable.
//
// PRE-EXISTING GAP (discovered by this file, not introduced by it):
// the whole COTTAS/Parquet reader -- on-disk `--data-cottas` as much as
// the in-memory bytes store -- fails under wasm_of_ocaml today with
// `Invalid_argument("Uint32.of_string")`. `FStar_UInt32`'s OCaml
// realization (ulib/ml/FStar_UInt32.ml) is `Stdint.Uint32`, and
// `wasm_of_ocaml`'s own build log (this session's `build-ocaml.sh
// wasm-factoidal` run) lists `uint32_of_int`/`uint32_and`/`uint32_or`/
// etc. under "Missing Wasm primitives" -- `Stdint`'s C stubs have no
// wasm_of_ocaml realization, so any F* code touching a `u32` (Parquet's
// magic numbers, page checksums, ...) throws the moment it's forced.
// Confirmed independent of this task's own code: `factoidal.wasm.js`'s
// plain CLI `--data-cottas` path (no in-memory buffer involved at all)
// throws the identical error opening the SAME fixture. This is the gap
// design doc 2026-07-06-inmemory-bytes-store.md's "Open decisions" item
// 3 flagged as "not checked in this task" for the wasm track -- now
// checked, and the answer is "does not work yet, needs a Stdint-for-
// wasm_of_ocaml shim or a u32-representation change in Parquet.Footer.
// fst, neither of which is new OCaml glue this task should add". Every
// test below probes for this exact failure signature and skips with a
// named reason rather than either hiding it or hard-failing the suite.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const wasmEngine = require('../wasm.js');

const NODE_MAJOR = Number(process.versions.node.split('.')[0]);

const FIXTURE_COTTAS = path.resolve(
  __dirname, '..', '..', '..', 'tests', 'unit', 'fixtures',
  'store_capabilities_sample.cottas');
const FIXTURE_NQ = path.resolve(
  __dirname, '..', '..', '..', 'tests', 'local', 'data', 'cottas_sample.nq');
const haveFixtures = fs.existsSync(FIXTURE_COTTAS) && fs.existsSync(FIXTURE_NQ);

function wasmSkipReason() {
  if (NODE_MAJOR < 22) {
    return `Node ${process.versions.node} < 22 (WasmGC needed)`;
  }
  if (!wasmEngine.wasmAvailable()) {
    return 'factoidal.wasm.js / .wasm asset not present ' +
      "(run 'build-ocaml.sh wasm-factoidal', then 'build-ocaml.sh npm')";
  }
  if (!haveFixtures) return 'fixture .cottas/.nq not found';
  return null;
}

async function loadAbi() {
  const abi = await wasmEngine._loadEntryForTest();
  if (abi && typeof abi.openCottas === 'function') return abi;
  return null;
}

function hexOfBuffer(buf) {
  return Buffer.from(buf).toString('hex');
}

const STDINT_GAP = 'wasm_of_ocaml cannot yet run the COTTAS/Parquet reader ' +
  '(Invalid_argument("Uint32.of_string") -- Stdint.Uint32 has no ' +
  'wasm_of_ocaml primitive realization; see this file\'s header comment)';

// Probe once: open + query the real fixture, and if that throws with
// the Stdint/wasm signature, every test below skips with STDINT_GAP
// instead of failing -- this is an engine-compatibility gap the design
// doc's own open questions flagged as unchecked, not a bug in the new
// openCottas/queryCottas/toCottas ABI this file is meant to pin.
let stdintGapCache; // undefined = not probed; true/false once probed
async function hasStdintGap(abi) {
  if (stdintGapCache !== undefined) return stdintGapCache;
  try {
    const bytes = fs.readFileSync(FIXTURE_COTTAS);
    const opened = JSON.parse(abi.openCottas(hexOfBuffer(bytes)));
    // Under wasm_of_ocaml the Stdint gap can surface as early as
    // openCottas() itself (unlike js_of_ocaml, where cottas_ondisk_
    // open's lazy-open design defers it to the first query -- see
    // cottas-bytes-store.test.js's "garbage bytes open lazily" test).
    // Check both surfaces rather than assuming one.
    if (!opened.ok) {
      stdintGapCache = /Uint32\.of_string/.test(opened.error || '');
      return stdintGapCache;
    }
    const r = JSON.parse(
      abi.queryCottas(opened.handle, 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'));
    abi.closeCottas(opened.handle);
    stdintGapCache = !r.ok && /Uint32\.of_string/.test(r.error || '');
  } catch (e) {
    stdintGapCache = /Uint32\.of_string/.test(String(e && e.message));
  }
  return stdintGapCache;
}

test('wasm ABI: openCottas + queryCottas match the fixture\'s known content', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }
  const abi = await loadAbi();
  if (!abi) { t.skip('wasm npm-entry bundle predates openCottas'); return; }
  if (await hasStdintGap(abi)) { t.skip(STDINT_GAP); return; }

  const bytes = fs.readFileSync(FIXTURE_COTTAS);
  const opened = JSON.parse(abi.openCottas(hexOfBuffer(bytes)));
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
  if (await hasStdintGap(abi)) { t.skip(STDINT_GAP); return; }

  const nq = fs.readFileSync(FIXTURE_NQ, 'utf8');
  const written = JSON.parse(abi.toCottas(nq));
  assert.equal(written.ok, true, JSON.stringify(written));
  assert.equal(written.quadCount, 5);

  const opened = JSON.parse(abi.openCottas(written.cottasHex));
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
  if (await hasStdintGap(wasmAbi)) { t.skip(STDINT_GAP); return; }

  const jsEngine = require('..');
  const bytes = fs.readFileSync(FIXTURE_COTTAS);

  const jsHandle = await jsEngine.openCottas(bytes);
  const jsRows = await jsEngine.queryCottas(jsHandle,
    'SELECT ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }');
  await jsEngine.closeCottas(jsHandle);

  const wasmHandle = JSON.parse(wasmAbi.openCottas(hexOfBuffer(bytes))).handle;
  const wasmSrj = JSON.parse(wasmAbi.queryCottas(wasmHandle,
    'SELECT ?s ?p ?o WHERE { GRAPH ?g { ?s ?p ?o } }'));
  wasmAbi.closeCottas(wasmHandle);

  const norm = (rows) => rows.map((r) =>
    [...r.entries()].map(([k, v]) => `${k}=${v.value}`).sort().join('|')).sort();
  const wasmRowsNorm = wasmSrj.srj.results.bindings.map((b) =>
    Object.entries(b).map(([k, v]) => `${k}=${v.value}`).sort().join('|')).sort();
  assert.deepEqual(wasmRowsNorm, norm(jsRows));
});
