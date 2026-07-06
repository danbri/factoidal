// Unit tests for the browser-persistence npm-entry ABI additions
// (issue #282, docs/designissues/2026-07-06-browser-persistence.md):
// bin/npm-entry/entry_jsoo.ml's `deltaBatchToHex` / `deltaMergeApplyBrowser`
// exports. These two functions do no I/O of their own (no IndexedDB, no
// filesystem) -- they are pure request/response wrappers around the
// F*-verified RDF_Store_Columnar_DeltaLog / RDF_Store_Columnar_DeltaMerge
// functions the native on-disk delta log also uses -- so they are
// exercised here directly in Node, fast and deterministic, as a
// complement to tests/web-demos/browser_persistence_smoke.sh's slower
// real-IndexedDB/real-browser-reload proof (which this file does not
// replace: only a real browser navigation proves the "survives a
// reload" claim; this file proves the byte-format/merge logic those
// browser calls are built on).

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const PENDING = 'pending npm-entry build (deltaBatchToHex/deltaMergeApplyBrowser)';

function entryCandidates() {
  const c = [];
  if (process.env.FACTOIDAL_NPM_ENTRY) c.push(process.env.FACTOIDAL_NPM_ENTRY);
  c.push(path.join(__dirname, '..', 'factoidal-npm-entry.js'));
  c.push(path.resolve(__dirname, '..', '..', '..', 'docs', 'fstar-extracted', 'factoidal-npm-entry.js'));
  return c;
}

function loadAbi() {
  for (const p of entryCandidates()) {
    if (!p || !fs.existsSync(p)) continue;
    const mod = require(p);
    const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
    if (abi && typeof abi.deltaBatchToHex === 'function') return abi;
  }
  return null;
}

const abi = loadAbi();
const skip = !abi ? PENDING : false;

function appendBatch(update, seq, epoch) {
  const parsed = JSON.parse(abi.deltaBatchToHex(update, String(seq), String(epoch || 0)));
  if (!parsed.ok) throw new Error(parsed.error || 'deltaBatchToHex failed');
  return parsed;
}

function merge(baseNQuads, hexBlobs) {
  const parsed = JSON.parse(abi.deltaMergeApplyBrowser(baseNQuads, hexBlobs.join('\n')));
  if (!parsed.ok) throw new Error(parsed.error || 'deltaMergeApplyBrowser failed');
  return parsed.nquads;
}

test('deltaBatchToHex + deltaMergeApplyBrowser: single INSERT DATA round-trips', { skip }, () => {
  const b0 = appendBatch('INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . }', 0, 0);
  assert.equal(b0.opCount, 1);
  assert.match(b0.hex, /^[0-9a-f]+$/);
  const nq = merge('', [b0.hex]);
  assert.match(nq, /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/);
});

test('deltaMergeApplyBrowser: multiple batches compose (add, then remove+add), order-independent input', { skip }, () => {
  const b0 = appendBatch('INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . <urn:x:b> <urn:x:p> <urn:x:v2> . }', 0, 0);
  const b1 = appendBatch('DELETE DATA { <urn:x:b> <urn:x:p> <urn:x:v2> . } ; INSERT DATA { <urn:x:c> <urn:x:p> <urn:x:v3> . }', 1, 0);

  // deltaMergeApplyBrowser sorts by db_seq internally -- feed the hex
  // blobs in REVERSE order to prove the caller doesn't have to sort.
  const nq = merge('', [b1.hex, b0.hex]);
  assert.match(nq, /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/);
  assert.match(nq, /<urn:x:c>\s+<urn:x:p>\s+<urn:x:v3>/);
  assert.doesNotMatch(nq, /<urn:x:b>/, 'urn:x:b was tombstoned by DELETE DATA');
});

test('deltaMergeApplyBrowser: CREATE + INSERT DATA into a brand-new named graph', { skip }, () => {
  const b0 = appendBatch(
    'CREATE GRAPH <urn:x:g1> ; INSERT DATA { GRAPH <urn:x:g1> { <urn:x:d> <urn:x:p> <urn:x:v4> } }', 0, 0);
  assert.equal(b0.opCount, 2);
  const nq = merge('', [b0.hex]);
  assert.match(nq, /<urn:x:d>\s+<urn:x:p>\s+<urn:x:v4>\s+<urn:x:g1>/);
});

test('deltaBatchToHex: unsupported op (DELETE/INSERT WHERE) rejects with an error, not silently', { skip }, () => {
  const parsed = JSON.parse(
    abi.deltaBatchToHex('DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }', '0', '0'));
  assert.equal(parsed.ok, false);
  assert.match(parsed.error, /unsupported|DELETE.?INSERT WHERE/i);
});

test('deltaMergeApplyBrowser: a corrupted (truncated) blob is skipped, never partially decoded', { skip }, () => {
  const b0 = appendBatch('INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . }', 0, 0);
  const b1 = appendBatch('INSERT DATA { <urn:x:e> <urn:x:p> <urn:x:v5> . }', 1, 0);

  const truncated = b1.hex.slice(0, Math.max(0, b1.hex.length - 8));
  const nq = merge('', [b0.hex, truncated]);

  assert.match(nq, /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/, 'clean batch 0 survives');
  assert.doesNotMatch(nq, /<urn:x:e>/, 'corrupted batch 1 never appears (skipped, not garbage-decoded)');
});

test('deltaMergeApplyBrowser: an existing named graph in the base is preserved and composed with', { skip }, () => {
  const baseNQuads = '<urn:x:existing> <urn:x:p> <urn:x:v0> <urn:x:g1> .\n';
  const b0 = appendBatch(
    'INSERT DATA { GRAPH <urn:x:g1> { <urn:x:d> <urn:x:p> <urn:x:v4> } }', 0, 0);
  const nq = merge(baseNQuads, [b0.hex]);
  assert.match(nq, /<urn:x:existing>\s+<urn:x:p>\s+<urn:x:v0>\s+<urn:x:g1>/);
  assert.match(nq, /<urn:x:d>\s+<urn:x:p>\s+<urn:x:v4>\s+<urn:x:g1>/);
});
