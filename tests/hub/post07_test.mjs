// Pins every code sample in docs/web/hub/07-json-ld-rdf-as-json.md.

import { createRequire } from 'node:module';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '07-json-ld-rdf-as-json.md';

function loadAbi() {
  const bundlePath = process.env.FACTOIDAL_NPM_ENTRY;
  assert.ok(bundlePath, 'FACTOIDAL_NPM_ENTRY must be set (see ./_helpers.mjs)');
  const mod = require(bundlePath);
  const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  assert.ok(abi, 'factoidalNpmEntry ABI object did not register');
  return abi;
}

const abi = loadAbi();

const cells = extractObservableCells(POST_FILE);

// The post's cells call the raw `Factoidal.jsonldToRdf(jsonldText)`
// contract (npm/factoidal/browser.js) directly, since there is no
// `fn.jsonldToRdf` adapter in docs/_includes/hub.njk today.
// browser.js's raw contract returns a PLAIN `{ok: true, nquads:
// string}` object (verified by reading browser.js's jsonldToRdf,
// which JSON.parses the npm-entry ABI's own response and returns it
// as-is) -- NOT a Dataset with `.size`/`.toNQuads()`. This shim
// reproduces that exact shape on top of the REAL npm/factoidal typed
// API's `jsonldToRdf(jsonldText, options) -> Promise<Dataset>`, so the
// cell source under test (which reads `result.nquads`, never
// `result.size`) is pinned against the same contract a real browser
// page's `Factoidal` binding actually exposes.
// jsonldFromRdf mirrors npm/factoidal/browser.js's raw contract: it
// calls the SAME npm-entry ABI function (abi.jsonldFromRdf) the browser
// build loads and returns its {ok, jsonld} envelope as-is.
const FactoidalNode = {
  async jsonldToRdf(jsonldText, options) {
    const ds = await factoidal.jsonldToRdf(jsonldText, options);
    return { ok: true, nquads: ds.toNQuads() };
  },
  async jsonldFromRdf(nquads, options) {
    assert.equal(typeof abi.jsonldFromRdf, 'function',
      'the loaded bundle predates the jsonldFromRdf export');
    const optionsJson = JSON.stringify(options || {});
    const parsed = JSON.parse(abi.jsonldFromRdf(nquads, optionsJson));
    if (!parsed.ok) throw new Error(parsed.error || 'jsonldFromRdf failed');
    return parsed;
  },
};

test('post07: post has at least 4 live cells', () => {
  assert.ok(cells.length >= 4, `expected >= 4 live cells, found ${cells.length}`);
});

test('post07 cell 1 (plain JSON, no @context): zero triples', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, { tripleCount: 0 });
});

test('post07 cell 2 (@context mapping): three triples, available', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal, Factoidal: FactoidalNode });
  assert.equal(result.available, true);
  const lines = result.nquads.trim().split('\n').sort();
  assert.deepEqual(lines, [
    '<http://example.org/alice> <http://schema.org/jobTitle> "Engineer" .',
    '<http://example.org/alice> <http://schema.org/name> "Alice" .',
    '<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://schema.org/Person> .',
  ]);
});

test('post07 cell 3 (round trip): JSON-LD -> N-Quads -> query returns Alice/Engineer', async () => {
  const result = await runObservableCell(cells[2], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, [{ name: 'Alice', title: 'Engineer' }]);
});

test('post07 cell 4 (fromRdf): N-Quads -> expanded JSON-LD node object', async () => {
  const result = await runObservableCell(cells[3], { fn: factoidal, Factoidal: FactoidalNode });
  assert.ok(Array.isArray(result), 'expanded form is an array of node objects');
  assert.equal(result.length, 1);
  const node = result[0];
  assert.equal(node['@id'], 'http://example.org/alice');
  assert.deepEqual(node['@type'], ['http://schema.org/Person']);
  assert.deepEqual(node['http://schema.org/name'], [{ '@value': 'Alice' }]);
  assert.deepEqual(node['http://schema.org/jobTitle'], [{ '@value': 'Engineer' }]);
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post07: capabilities() reports JSON-LD support (grounds the "check first" cell pattern)', async () => {
  const caps = await factoidal.capabilities();
  assert.equal(caps.jsonld, true);
});

test('post07: jsonldToRdf resolves relative @id against an explicit base option', async () => {
  const jsonld = JSON.stringify({
    '@context': { foaf: 'http://xmlns.com/foaf/0.1/', name: 'foaf:name' },
    '@id': 'alice',
    name: 'Alice',
  });
  const ds = await factoidal.jsonldToRdf(jsonld, { base: 'http://example.org/' });
  assert.equal(ds.size, 1);
  assert.equal([...ds][0].subject.value, 'http://example.org/alice');
});
