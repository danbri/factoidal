// Wasm-entry counterpart to delta-log.test.js (issue #282,
// docs/designissues/2026-07-06-browser-persistence.md): proves
// bin/npm-entry/entry_jsoo.ml's `deltaBatchToHex` /
// `deltaMergeApplyBrowser` exports also work when the npm-entry
// bundle is compiled through wasm_of_ocaml
// (factoidal-npm-entry.wasm.js) rather than js_of_ocaml
// (factoidal-npm-entry.js). Same byte-format/merge assertions as the
// js version, run against the wasm ABI via wasm.js's
// `_loadEntryForTest` test hook (mirrors wasm-parity.test.js's
// js-vs-wasm parity pattern). Skips cleanly when the wasm bundle or
// a WasmGC-capable Node is unavailable.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const wasmEngine = require('../wasm.js');

const NODE_MAJOR = Number(process.versions.node.split('.')[0]);

function wasmSkipReason() {
  if (NODE_MAJOR < 22) {
    return `Node ${process.versions.node} < 22 (WasmGC needed)`;
  }
  if (!wasmEngine.wasmAvailable()) {
    return 'factoidal.wasm.js / .wasm asset not present ' +
      "(run 'build-ocaml.sh wasm-factoidal', then 'build-ocaml.sh npm')";
  }
  return null;
}

async function loadAbi() {
  const abi = await wasmEngine._loadEntryForTest();
  if (abi && typeof abi.deltaBatchToHex === 'function') return abi;
  return null;
}

function appendBatch(abi, update, seq, epoch) {
  const parsed = JSON.parse(abi.deltaBatchToHex(update, String(seq), String(epoch || 0)));
  if (!parsed.ok) throw new Error(parsed.error || 'deltaBatchToHex failed');
  return parsed;
}

function merge(abi, baseNQuads, hexBlobs) {
  const parsed = JSON.parse(abi.deltaMergeApplyBrowser(baseNQuads, hexBlobs.join('\n')));
  if (!parsed.ok) throw new Error(parsed.error || 'deltaMergeApplyBrowser failed');
  return parsed.nquads;
}

test('wasm entry: deltaBatchToHex + deltaMergeApplyBrowser single INSERT DATA round-trips', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }
  const abi = await loadAbi();
  if (!abi) {
    t.skip('factoidal-npm-entry.wasm.js missing deltaBatchToHex ' +
      '(pending npm-entry wasm build)');
    return;
  }

  const b0 = appendBatch(abi, 'INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . }', 0, 0);
  assert.equal(b0.opCount, 1);
  assert.match(b0.hex, /^[0-9a-f]+$/);
  const nq = merge(abi, '', [b0.hex]);
  assert.match(nq, /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/);
});

test('wasm entry: deltaMergeApplyBrowser composes multiple batches order-independently', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }
  const abi = await loadAbi();
  if (!abi) {
    t.skip('factoidal-npm-entry.wasm.js missing deltaBatchToHex ' +
      '(pending npm-entry wasm build)');
    return;
  }

  const b0 = appendBatch(abi,
    'INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . <urn:x:b> <urn:x:p> <urn:x:v2> . }', 0, 0);
  const b1 = appendBatch(abi,
    'DELETE DATA { <urn:x:b> <urn:x:p> <urn:x:v2> . } ; INSERT DATA { <urn:x:c> <urn:x:p> <urn:x:v3> . }', 1, 0);

  // deltaMergeApplyBrowser sorts by db_seq internally -- feed the hex
  // blobs in REVERSE order to prove the caller doesn't have to sort.
  const nq = merge(abi, '', [b1.hex, b0.hex]);
  assert.match(nq, /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/);
  assert.match(nq, /<urn:x:c>\s+<urn:x:p>\s+<urn:x:v3>/);
  assert.doesNotMatch(nq, /<urn:x:b>/, 'urn:x:b was tombstoned by DELETE DATA');
});

test('wasm entry: deltaBatchToHex rejects an unsupported op (DELETE/INSERT WHERE)', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }
  const abi = await loadAbi();
  if (!abi) {
    t.skip('factoidal-npm-entry.wasm.js missing deltaBatchToHex ' +
      '(pending npm-entry wasm build)');
    return;
  }

  const parsed = JSON.parse(
    abi.deltaBatchToHex('DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }', '0', '0'));
  assert.equal(parsed.ok, false);
  assert.match(parsed.error, /unsupported|DELETE.?INSERT WHERE/i);
});
