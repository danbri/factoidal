// Pins every code sample in docs/web/hub/07-json-ld-rdf-as-json.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '07-json-ld-rdf-as-json.md';

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
const FactoidalNode = {
  async jsonldToRdf(jsonldText, options) {
    const ds = await factoidal.jsonldToRdf(jsonldText, options);
    return { ok: true, nquads: ds.toNQuads() };
  },
};

test('post07: post has at least 3 live cells', () => {
  assert.ok(cells.length >= 3, `expected >= 3 live cells, found ${cells.length}`);
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
