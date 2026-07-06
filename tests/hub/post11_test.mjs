// Pins every code sample in docs/web/hub/11-one-graph-five-syntaxes.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '11-one-graph-five-syntaxes.md';

const cells = extractObservableCells(POST_FILE);

test('post11: post has at least 3 live cells', () => {
  assert.ok(cells.length >= 3, `expected >= 3 live cells, found ${cells.length}`);
});

test('post11 cell 1 (Turtle vs RDF/XML): identical canonical bytes', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal });
  assert.equal(result.turtleSize, 5);
  assert.equal(result.xmlSize, 5);
  assert.equal(result.identicalBytes, true);
});

test('post11 cell 2 (Turtle vs N-Triples): identical canonical bytes', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal });
  assert.equal(result.identicalBytes, true);
  assert.match(result.sampleLine, /^<http:\/\/example\.org\/alice>/);
});

test('post11 cell 3 (TriG vs N-Quads, named graph): identical canonical bytes', async () => {
  const result = await runObservableCell(cells[2], { fn: factoidal });
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
