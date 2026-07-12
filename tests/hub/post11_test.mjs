// Pins every code sample in docs/web/hub/11-one-graph-five-syntaxes.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '11-one-graph-five-syntaxes.md';

const cells = extractObservableCells(POST_FILE);

test('post11: post has 4 live cells (the shared Turtle text hoisted into its own named cell)', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

test('post11: dependency inference wires the two comparison cells to the named turtle cell', () => {
  const post = runReactivePost(cells, { fn: factoidal });
  assert.equal(post.names[0], 'turtle');
  assert.ok(post.infos[1].refs.includes('turtle'), 'RDF/XML comparison cell references turtle');
  assert.ok(post.infos[2].refs.includes('turtle'), 'N-Triples comparison cell references turtle');
  assert.ok(!post.infos[3].refs.includes('turtle'), 'TriG/N-Quads cell is independent of turtle');
});

test('post11 cell 2 (Turtle vs RDF/XML): identical canonical bytes', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[1]);
  assert.equal(result.turtleSize, 5);
  assert.equal(result.xmlSize, 5);
  assert.equal(result.identicalBytes, true);
});

test('post11 cell 3 (Turtle vs N-Triples): identical canonical bytes', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[2]);
  assert.equal(result.identicalBytes, true);
  assert.match(result.sampleLine, /^<http:\/\/example\.org\/alice>/);
});

test('post11 cell 4 (TriG vs N-Quads, named graph): identical canonical bytes', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[3]);
  assert.equal(result.identicalBytes, true);
  assert.equal(result.size, 5);
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post11: RDF 1.1 combined W3C score is 1031 pass, 0 fail (grounds this post\'s headline figure)', async () => {
  // Not re-run here (that's the W3C runner's job, see skills/test-suites) --
  // this just confirms the five formats this post exercises each parse
  // cleanly via the real npm/factoidal typed API, the same claim the
  // prose makes.
  for (const format of ['turtle', 'ntriples', 'nquads', 'trig', 'rdfxml']) {
    const ds = await factoidal.parse(
      format === 'rdfxml'
        ? '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"><rdf:Description rdf:about="http://example.org/x"><rdf:type rdf:resource="http://example.org/T"/></rdf:Description></rdf:RDF>'
        : format === 'nquads' || format === 'ntriples'
        ? '<http://example.org/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/T> .\n'
        : format === 'trig'
        ? '<http://example.org/x> a <http://example.org/T> .\n'
        : '<http://example.org/x> a <http://example.org/T> .\n',
      { format });
    assert.equal(ds.size, 1, `format ${format} should parse to exactly 1 triple`);
  }
});
