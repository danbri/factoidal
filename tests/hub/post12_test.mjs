// Pins every code sample in docs/web/hub/12-the-api-tour.md.

import { createRequire } from 'node:module';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '12-the-api-tour.md';

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

// Cell 2 calls `Factoidal.loadNpmEntry()` -- the raw browser.js export
// that fetches (browser) / requires (here) the npm-entry ABI bundle
// and returns the ABI object itself. Same shape as browser.js's own
// loadNpmEntry(), just backed by require() instead of fetch().
const Factoidal = {
  async loadNpmEntry() {
    return abi;
  },
};

const cells = extractObservableCells(POST_FILE);

test('post12: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post12 cell 1 (parse + query, the one door): SELECT returns Alice then Bob', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.deepEqual(result, ['Alice', 'Bob']);
});

test('post12 cell 2 (capability probe): every RIF/SHACL/ShEx/OWL/RML/CSVW/JSON-LD capability is true against the real bundle', async () => {
  const result = await runObservableCell(cells[1], { Factoidal });
  assert.equal(result.available, true);
  for (const key of ['rif', 'shacl', 'shex', 'owlClosure', 'rml', 'csvw', 'jsonld']) {
    assert.equal(result.caps[key], true, `expected caps.${key} to be true against the committed bundle`);
  }
});

test('post12 cell 2 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async loadNpmEntry() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
  };
  const result = await runObservableCell(cells[1], { Factoidal: brokenFactoidal });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post12: capabilities() function list matches the table this post documents', async () => {
  const caps = await factoidal.capabilities();
  for (const key of [
    'entry', 'construct', 'update', 'canonicalize', 'graphs', 'canonicalHash',
    'shacl', 'shex', 'owlClosure', 'rml', 'csvw', 'jsonld', 'rif',
  ]) {
    assert.ok(key in caps, `capabilities() should report a '${key}' field`);
  }
  assert.equal(caps.entry, true);
  assert.equal(caps.rif, true);
  assert.equal(caps.csvw, true);
});

test('post12: the wasm entry\'s capabilities() now matches the js entry (grounds the "wasm caught up" prose update)', async () => {
  let wasmFactoidal;
  try {
    wasmFactoidal = require('../../npm/factoidal/wasm.js');
  } catch (err) {
    // Environment has no WasmGC-capable Node -- skip rather than false-fail.
    return;
  }
  const wasmCaps = await wasmFactoidal.capabilities();
  const jsCaps = await factoidal.capabilities();
  assert.equal(jsCaps.rif, true, 'js entry should support rif');
  // The wasm entry's npm-entry ABI bundle was rebuilt and a
  // require.main path bug in wasm.js's entry loader (which had
  // silently reported every one of these as false, independent of
  // whether the bundle actually had the function) is fixed. This
  // assertion is the measured fact the post's "wasm caught up"
  // section reports, not an assumption -- if this now fails, either
  // the bundle regressed or the loader fix was reverted.
  for (const key of ['shacl', 'shex', 'owlClosure', 'rml', 'csvw', 'jsonld', 'rif']) {
    assert.equal(wasmCaps[key], true, `expected wasm caps.${key} to be true`);
  }
});
