// Pins every code sample in docs/web/hub/08-canonical-graphs-rdfc10.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '08-canonical-graphs-rdfc10.md';

const cells = extractObservableCells(POST_FILE);

// The post's cells call `fn.canonicalize(text, options)`.
// npm/factoidal's typed `canonicalize(data, options) -> Promise<string>`
// already matches that signature/return shape exactly (it additionally
// accepts a Dataset or array, which these cells never pass), so `fn`
// here is a pure pass-through -- no argument-shape translation needed.

test('post08: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post08 cell 1 (canonicalize twice, different bnode labels): identical bytes', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.equal(result.identical, true);
  assert.match(result.canonicalNQuads, /_:c14n0/);
  const lines = result.canonicalNQuads.trim().split('\n').sort();
  assert.deepEqual(lines, [
    '<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> .',
    '<http://example.org/alice> <http://xmlns.com/foaf/0.1/knows> _:c14n0 .',
    '<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> "Alice" .',
    '_:c14n0 <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://xmlns.com/foaf/0.1/Person> .',
    '_:c14n0 <http://xmlns.com/foaf/0.1/name> "Bob" .',
  ]);
});

test('post08 cell 2 (content-addressed hash): same facts hash equal, changed fact hashes differ', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal });
  assert.equal(result.sameFactsSameHash, true);
  assert.equal(result.differentFactsDifferentHash, true);
  assert.match(result.urn, /^urn:rdfc:sha256:[0-9a-f]{64}$/);
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post08: capabilities() reports canonicalize support (grounds the "check first" cell pattern)', async () => {
  const caps = await factoidal.capabilities();
  assert.equal(caps.canonicalize, true);
});

test('post08: canonicalize is a fixpoint on its own output', async () => {
  const once = await factoidal.canonicalize('_:a <http://x/p> "v" .\n', { format: 'nquads' });
  const again = await factoidal.canonicalize(once, { format: 'nquads' });
  assert.equal(again, once);
});
