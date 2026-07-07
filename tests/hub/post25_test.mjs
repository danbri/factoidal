// Pins every live cell in docs/web/hub/25-xml-wellformedness-and-xpath.md.
//
// The post's four cells call `Factoidal.xmlWellformed(xml)` and
// `Factoidal.xpathEval(xml, expr)` -- the raw browser.js exports backed
// by the F*-extracted Parser_XML.parse_xml_document and
// XPath_Eval.eval_xpath_from_root. As in post13/post23, `Factoidal` here
// is a small Node stub that mirrors those browser.js wrappers: it calls
// the SAME npm-entry ABI functions (abi.xmlWellformed / abi.xpathEval)
// the browser build loads, backed by require() instead of fetch().
// `pretty` is the shared node-side stub from _helpers.mjs.

import { createRequire } from 'node:module';
import { extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const POST_FILE = '25-xml-wellformedness-and-xpath.md';

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

// Mirrors npm/factoidal/browser.js's xmlWellformed()/xpathEval().
const Factoidal = {
  async xmlWellformed(xmlText) {
    assert.equal(typeof abi.xmlWellformed, 'function',
      'the loaded bundle predates the xmlWellformed export');
    const parsed = JSON.parse(abi.xmlWellformed(xmlText));
    if (!parsed.ok) throw new Error(parsed.error || 'xmlWellformed failed');
    return parsed;
  },
  async xpathEval(xmlText, xpathExpr) {
    assert.equal(typeof abi.xpathEval, 'function',
      'the loaded bundle predates the xpathEval export');
    const parsed = JSON.parse(abi.xpathEval(xmlText, xpathExpr));
    if (!parsed.ok) throw new Error(parsed.error || 'xpathEval failed');
    return parsed;
  },
};

const cells = extractObservableCells(POST_FILE);
const B = { Factoidal, pretty };

test('post25: post has 4 live cells', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

test('post25 cell 1 (well-formed document): wellformed true', async () => {
  const result = await runObservableCell(cells[0], B);
  assert.deepEqual(result, { ok: true, wellformed: true });
});

test('post25 cell 2 (mismatched close tag): wellformed false', async () => {
  const result = await runObservableCell(cells[1], B);
  assert.deepEqual(result, { ok: true, wellformed: false });
});

test('post25 cell 3 (//book/title node-set): two title elements', async () => {
  const result = await runObservableCell(cells[2], B);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['kind', 'name', 'value']);
  assert.deepEqual(result.rows, [
    ['element', 'title', 'SPARQL 1.1'],
    ['element', 'title', 'RDF Primer'],
  ]);
});

test('post25 cell 4 (four XPath result types): number/nodeset/string/boolean', async () => {
  const result = await runObservableCell(cells[3], B);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['expression', 'resultType', 'value']);
  assert.deepEqual(result.rows, [
    ['count(//book)', 'number', '2'],
    ['//book[1]/title/text()', 'nodeset', 'SPARQL 1.1'],
    ['string(//book[2]/@id)', 'string', 'b2'],
    ['count(//book) > 1', 'boolean', 'true'],
  ]);
});
