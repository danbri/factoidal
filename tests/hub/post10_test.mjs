// Pins every code sample in docs/web/hub/10-rules-rif-core.md.
//
// This post's cells call `Factoidal.rifEval(...)` -- the raw ABI
// npm/factoidal/browser.js exposes -- rather than the `fn` typed
// adapter (RIF has no `fn.*` wrapper in docs/_includes/hub.njk yet;
// see that file's CELL_BINDINGS / `const fn = {...}` object, which
// only covers parse/query/shaclValidate today). In the browser,
// `Factoidal` resolves to browser.js's module namespace, whose
// rifEval() fetches the npm-entry ABI bundle over the network
// (loadNpmEntry()'s `fetch()`). Node has no `file://` fetch, so this
// test instead builds a small shim that calls the exact same
// underlying ABI function (`abi.rifEval(rifXml, dataNQuads)`,
// JSON-parsed the same way) via `require()`, mirroring browser.js's
// own implementation byte-for-byte -- a faithful stand-in for the
// real network fetch, not a different code path.

import { createRequire } from 'node:module';
import { extractObservableCells, runObservableCell, HUB_POST_DIR } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const POST_FILE = '10-rules-rif-core.md';

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ../_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

// Same-shaped object as npm/factoidal/browser.js's default export, for
// exactly the two raw-ABI calls this post's cells use.
const Factoidal = {
  async rifEval(rifXml, dataNQuads) {
    if (typeof abi.rifEval !== 'function') {
      throw new Error('rifEval: the loaded factoidal-npm-entry bundle predates the RIF exports');
    }
    const parsed = JSON.parse(abi.rifEval(rifXml, dataNQuads));
    if (!parsed.ok) throw new Error(parsed.error || 'rifEval failed');
    return parsed;
  },
};

const cells = extractObservableCells(POST_FILE);

test('post10: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post10 cell 1 (gold + silver rules, two customers): each derives its own discount', async () => {
  const result = await runObservableCell(cells[0], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.inputCount, 4);
  assert.equal(result.derivedCount, 2);
  assert.equal(result.discounts.length, 2);
  const goldLine = result.discounts.find((l) => l.includes('customer017'));
  const silverLine = result.discounts.find((l) => l.includes('customer042'));
  assert.ok(goldLine && goldLine.includes('"10"'), 'customer017 (gold) should derive discount 10');
  assert.ok(silverLine && silverLine.includes('"5"'), 'customer042 (silver) should derive discount 5');
});

test('post10 cell 2 (unmatched status): no rule fires, nothing derived', async () => {
  const result = await runObservableCell(cells[1], { Factoidal });
  assert.equal(result.available, true);
  assert.equal(result.inputCount, 2);
  assert.equal(result.derivedCount, 0);
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post10: rifEval saturates the vendored Frames fixture as-is (DOCTYPE + entities, ground fact included)', async () => {
  const fs = await import('node:fs');
  const path = await import('node:path');
  const fixturePath = path.join(
    HUB_POST_DIR, '..', '..', '..', 'third_party', 'testing', 'rif', 'tc', 'Frames', 'Frames-premise.rif');
  const rifXml = fs.readFileSync(fixturePath, 'utf8');
  const result = await Factoidal.rifEval(rifXml, '');
  // The whole vendored document (gold rule, silver rule, and the
  // ground `customer017` fact) is passed as rifXml with no separate
  // data; with dataNQuads empty, inputCount is 0 and all 3 resulting
  // triples (the 2 ground facts plus the 1 derived discount) are
  // counted as "derived" by this runner's convention -- see the
  // rules-only cells above for the inputCount/derivedCount split this
  // post's live cells rely on instead.
  assert.equal(result.derivedCount, 3);
  assert.match(result.saturatedNquads, /#discount> "10"\^\^<http:\/\/www\.w3\.org\/2001\/XMLSchema#integer>/);
});

test('post10: a cell degrades gracefully (not a thrown rejection) when the ABI lacks rifEval', async () => {
  const brokenFactoidal = {
    async rifEval() {
      throw new Error('rifEval: the loaded factoidal-npm-entry bundle predates the RIF exports');
    },
  };
  const result = await runObservableCell(cells[0], { Factoidal: brokenFactoidal });
  assert.equal(result.available, false);
  assert.match(result.note, /predates the RIF exports/);
});
