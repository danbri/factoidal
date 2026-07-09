// Typed-shape test for the browser-only durable delta log
// (browser.js's deltaLogOpen/Append/ReadAllHex/Merge/Destroy), which
// browser.d.ts now declares. browser.js itself can't be imported in
// Node (it uses `import.meta.url`, `fetch`, and `indexedDB`), so this
// follows tests/hub/post18_test.mjs's "swap IndexedDB for a Map, route
// every byte through the REAL abi" pattern: a stub that mirrors the
// browser.js deltaLog* CONTRACT exactly (same handle shape, same return
// shapes), then asserts those shapes match what browser.d.ts promises.
//
// This is a shape/contract gate, not a real-IndexedDB durability proof
// (only a browser navigation proves "survives a reload" — see
// tests/web-demos/browser_persistence_smoke.sh). It exists so the typed
// deltaLog surface can't drift from the ABI it wraps.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

function loadAbi() {
  const candidates = [
    process.env.FACTOIDAL_NPM_ENTRY,
    path.join(__dirname, '..', 'factoidal-npm-entry.js'),
    path.join(__dirname, '..', '..', '..', 'docs', 'fstar-extracted', 'factoidal-npm-entry.js'),
  ];
  for (const p of candidates) {
    if (!p || !fs.existsSync(p)) continue;
    const mod = require(p);
    const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
    if (abi && typeof abi.deltaBatchToHex === 'function') return abi;
  }
  return null;
}

const abi = loadAbi();
const skip = !abi ? 'npm-entry bundle with delta-log exports not present' : false;

// A Map-backed stand-in for browser.js's IndexedDB storage layer,
// mirroring the browser.js deltaLog* contract byte-for-byte through the
// real abi.deltaBatchToHex / abi.deltaMergeApplyBrowser.
function makeDeltaLog() {
  const stores = new Map(); // dbName -> [{seq, epoch, hex}]
  const storeFor = (n) => {
    if (!stores.has(n)) stores.set(n, []);
    return stores.get(n);
  };
  return {
    async deltaLogOpen(dbName) {
      const name = dbName || 'factoidal-delta-log';
      storeFor(name);
      return { dbName: name };
    },
    async deltaLogAppend(handle, sparqlUpdate, options) {
      if (!handle || typeof handle.dbName !== 'string') {
        throw new TypeError('deltaLogAppend: handle must be the object deltaLogOpen() returned');
      }
      const epoch = (options && options.epoch) || 0;
      const records = storeFor(handle.dbName);
      const seq = records.length;
      const parsed = JSON.parse(abi.deltaBatchToHex(sparqlUpdate, String(seq), String(epoch)));
      if (!parsed.ok) throw new Error(parsed.error || 'deltaBatchToHex failed');
      records.push({ seq, epoch, hex: parsed.hex });
      return { seq, opCount: parsed.opCount };
    },
    async deltaLogReadAllHex(handle) {
      return storeFor(handle.dbName).slice().sort((a, b) => a.seq - b.seq)
        .map((r) => r.hex).join('\n');
    },
    async deltaLogMerge(handle, baseNQuads) {
      const hex = await this.deltaLogReadAllHex(handle);
      const parsed = JSON.parse(abi.deltaMergeApplyBrowser(baseNQuads, hex));
      if (!parsed.ok) throw new Error(parsed.error || 'deltaMergeApplyBrowser failed');
      return parsed.nquads;
    },
    async deltaLogDestroy(handle) { stores.delete(handle.dbName); },
  };
}

test('deltaLogOpen returns a {dbName} handle (browser.d.ts DeltaLogHandle)', { skip }, async () => {
  const dl = makeDeltaLog();
  const handle = await dl.deltaLogOpen('t-open');
  assert.equal(typeof handle, 'object');
  assert.equal(typeof handle.dbName, 'string');
  assert.equal(handle.dbName, 't-open');
});

test('deltaLogAppend returns {seq:number, opCount:number}; seq climbs', { skip }, async () => {
  const dl = makeDeltaLog();
  const handle = await dl.deltaLogOpen('t-append');
  const r0 = await dl.deltaLogAppend(handle, 'INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . }');
  assert.equal(typeof r0.seq, 'number');
  assert.equal(typeof r0.opCount, 'number');
  assert.equal(r0.seq, 0);
  assert.equal(r0.opCount, 1);
  const r1 = await dl.deltaLogAppend(handle, 'INSERT DATA { <urn:x:b> <urn:x:p> <urn:x:v2> . }');
  assert.equal(r1.seq, 1);
});

test('deltaLogReadAllHex returns a string; deltaLogMerge returns merged N-Quads', { skip }, async () => {
  const dl = makeDeltaLog();
  const handle = await dl.deltaLogOpen('t-merge');
  await dl.deltaLogAppend(handle, 'INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . }');
  const hex = await dl.deltaLogReadAllHex(handle);
  assert.equal(typeof hex, 'string');
  assert.match(hex, /^[0-9a-f]+$/);
  const merged = await dl.deltaLogMerge(handle, '');
  assert.equal(typeof merged, 'string');
  assert.match(merged, /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/);
});

test('deltaLogAppend rejects a bad handle (contract shape check)', { skip }, async () => {
  const dl = makeDeltaLog();
  await assert.rejects(() => dl.deltaLogAppend({}, 'INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . }'), TypeError);
});

// browser.d.ts must actually declare the surface this file's contract
// mirrors — the whole point of typing a browser-only module.
test('browser.d.ts declares the deltaLog* surface + DeltaLogHandle', () => {
  const dts = fs.readFileSync(path.join(__dirname, '..', 'browser.d.ts'), 'utf8');
  assert.match(dts, /interface DeltaLogHandle\b/);
  for (const fn of [
    'deltaLogOpen', 'deltaLogAppend', 'deltaLogReadAllHex',
    'deltaLogMerge', 'deltaLogDestroy',
  ]) {
    assert.match(dts, new RegExp(`export function ${fn}\\(`), `browser.d.ts declares ${fn}`);
  }
  // The underscore-private test helper is deliberately left untyped.
  assert.doesNotMatch(dts, /_deltaLogCorruptLastForTest/,
    '_deltaLogCorruptLastForTest is intentionally undeclared (underscore-private)');
});

test('browser.d.ts declares the VC crypto surface (browser init story)', () => {
  const dts = fs.readFileSync(path.join(__dirname, '..', 'browser.d.ts'), 'utf8');
  for (const fn of [
    'vcSha256Hex', 'vcEd25519SecretToPublic', 'vcEd25519Sign',
    'vcEd25519Verify', 'vcEddsaCreateFromCanonical', 'vcEddsaVerifyFromCanonical',
  ]) {
    assert.match(dts, new RegExp(`export function ${fn}\\(`), `browser.d.ts declares ${fn}`);
  }
});
