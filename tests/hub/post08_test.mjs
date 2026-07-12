// Pins every code sample in docs/web/hub/08-canonical-graphs-rdfc10.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost } from './_helpers.mjs';

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

test('post08: post has 4 live cells (DOC_A/DOC_B hoisted into named cells)', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

test('post08: dependency inference wires DOC_A/DOC_B to both downstream cells', () => {
  const post = runReactivePost(cells, { fn: factoidal });
  assert.equal(post.names[0], 'DOC_A');
  assert.equal(post.names[1], 'DOC_B');
  for (const i of [2, 3]) {
    assert.ok(post.infos[i].refs.includes('DOC_A'), `cell ${i + 1} references DOC_A`);
    assert.ok(post.infos[i].refs.includes('DOC_B'), `cell ${i + 1} references DOC_B`);
  }
});

test('post08 cell 3 (canonicalize twice, different bnode labels): identical bytes', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[2]);
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

test('post08 cell 4 (content-addressed hash): same facts hash equal, changed fact hashes differ', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[3]);
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
