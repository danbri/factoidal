#!/usr/bin/env node
// tools/deltalog-bench/bench-js-wasm.mjs
//
// Delta-log micro-bench driver for the js_of_ocaml and wasm_of_ocaml
// full-engine bundles, calling the SAME `deltaBatchToHex` export
// tools/deltalog-bench/deltalog_bench.ml's `sparql` mode exercises
// natively (bin/npm-entry/entry_jsoo.ml): parse one
// `INSERT DATA { <N triples> }` SPARQL Update statement ->
// RDF_Store_Columnar_DeltaMerge.update_ops_to_delta_entries ->
// RDF_Store_Columnar_DeltaLog.serialize_delta_batch -> hex.
//
// This is the FULL PIPELINE number (SPARQL-Update parsing included),
// not a pure serialize/parse-of-a-hand-built-batch number -- there is
// no shipped JS/wasm export of the raw serialize_delta_batch /
// parse_delta_batch functions, only this SPARQL-driven wrapper (see
// docs/web/perf/index.md "what's NOT measured"). Comparable to
// deltalog_bench.ml's `sparql` mode, NOT to the C-native/C-wasm/
// OCaml-native `pure` mode numbers.
//
// Usage: node bench-js-wasm.mjs (js|wasm) N
// Prints one JSON line to stdout.

import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const require = createRequire(import.meta.url);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.resolve(__dirname, '..', '..');

function buildInsertDataText(n) {
  const parts = ['INSERT DATA { '];
  for (let i = 0; i < n; i++) {
    parts.push(
      `<http://example.org/s${i}> <http://xmlns.com/foaf/0.1/knows> <http://example.org/o${i}> . `);
  }
  parts.push('}');
  return parts.join('');
}

async function loadJsAbi() {
  const p = path.join(REPO_ROOT, 'docs/fstar-extracted/factoidal-npm-entry.js');
  const mod = require(p);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  if (!abi || typeof abi.deltaBatchToHex !== 'function') {
    throw new Error('js bundle missing deltaBatchToHex export');
  }
  return abi;
}

async function loadWasmAbi() {
  const wasmEngine = require(path.join(REPO_ROOT, 'npm/factoidal/wasm.js'));
  if (!wasmEngine.wasmAvailable()) {
    throw new Error('wasm bundle / .wasm asset not present, or Node < 22');
  }
  const abi = await wasmEngine._loadEntryForTest();
  if (!abi || typeof abi.deltaBatchToHex !== 'function') {
    throw new Error('wasm bundle missing deltaBatchToHex export');
  }
  return abi;
}

async function main() {
  const [engineName, nStr] = process.argv.slice(2);
  const n = parseInt(nStr, 10);
  if (!['js', 'wasm'].includes(engineName) || !Number.isFinite(n)) {
    console.error('usage: bench-js-wasm.mjs (js|wasm) N');
    process.exit(2);
  }

  const abi = engineName === 'js' ? await loadJsAbi() : await loadWasmAbi();
  const text = buildInsertDataText(n);

  const t0 = process.hrtime.bigint();
  const raw = abi.deltaBatchToHex(text, '1', '0');
  const t1 = process.hrtime.bigint();

  const parsed = JSON.parse(raw);
  if (!parsed.ok) {
    console.error('deltaBatchToHex failed:', parsed.error || raw);
    process.exit(1);
  }

  const totalS = Number(t1 - t0) / 1e9;
  console.log(JSON.stringify({
    mode: 'sparql',
    engine: engineName,
    n,
    opCount: parsed.opCount,
    hexLen: parsed.hex.length,
    total_s: totalS,
  }));
}

main().catch((err) => {
  console.error(err.stack || String(err));
  process.exit(1);
});
