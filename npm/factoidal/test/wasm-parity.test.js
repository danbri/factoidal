// Parity test: the wasm_of_ocaml engine must produce byte-identical
// results to the js_of_ocaml engine for the same inputs. Skips cleanly
// when the wasm bundle or a WasmGC-capable Node is unavailable.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const jsEngine = require('..');
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

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice foaf:name "Alice" ; foaf:age 30 ; foaf:knows ex:bob .
  ex:bob   foaf:name "Bob" .
`;

test('wasm parity: parse produces the same N-Quads', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }

  const [jsDs, wasmDs] = [
    await jsEngine.parse(TTL),
    await wasmEngine.parse(TTL),
  ];
  assert.equal(wasmDs.size, jsDs.size);
  // Compare through the engines' own serializers for byte parity.
  const jsNq = await jsEngine.serialize(jsDs);
  const wasmNq = await wasmEngine.serialize(wasmDs);
  assert.equal(wasmNq, jsNq);
});

test('wasm parity: SELECT bindings match', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }

  const q = `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name ?age WHERE { ?p foaf:name ?name OPTIONAL { ?p foaf:age ?age } }
  `;
  const norm = (rows) =>
    rows
      .map((r) => [...r.entries()]
        .map(([k, v]) => `${k}=${v.termType}:${v.value}`)
        .sort()
        .join('|'))
      .sort();
  const jsRows = await jsEngine.query(TTL, q);
  const wasmRows = await wasmEngine.query(TTL, q);
  assert.deepEqual(norm(wasmRows), norm(jsRows));
});

test('wasm parity: ASK matches', async (t) => {
  const reason = wasmSkipReason();
  if (reason) { t.skip(reason); return; }

  const q = `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    PREFIX ex:   <http://example.org/>
    ASK { ex:alice foaf:knows ex:bob }
  `;
  assert.equal(await wasmEngine.query(TTL, q), await jsEngine.query(TTL, q));
});
