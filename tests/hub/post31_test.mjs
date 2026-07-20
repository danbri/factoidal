// Pins every code sample in
// docs/web/hub/31-rdf-1-2-triple-terms.md.
//
// The live page binds `fn` to the in-browser adapter (browser.js +
// hub.njk); here `fn === factoidal` (the node npm API). Both reach the
// same F*-extracted Mode_12 parsers/evaluator — the parse opt-in is
// {format:'turtle12'} and the query opt-in is {version:'1.2'}.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '31-rdf-1-2-triple-terms.md';

const TTL = `
  PREFIX : <http://example.org/>
  PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
  VERSION "1.2"

  :einstein  :claimed <<( :light :travelsAt :c )>> .
  :aristotle :claimed <<( :earth :hasShape :flat )>> .

  :sunrise :happensIn :east ~:obs {| :confidence "0.99"^^xsd:decimal |} .

  :relativity :title "نظرية النسبية"@ar--rtl .
  :relativity :title "Theory of Relativity"@en--ltr .
`;

test('post31: Turtle 1.2 parses to 7 quads (2 claims + reifier expansion + base + 2 titles)', async () => {
  const dataset = await factoidal.parse(TTL, { format: 'turtle12' });
  assert.equal(dataset.size, 7);
});

test('post31: Mode_11 (default) silently skips the 1.2 constructs — opt-in is load-bearing', async () => {
  const m11 = await factoidal.parse(TTL, { format: 'turtle' });
  const m12 = await factoidal.parse(TTL, { format: 'turtle12' });
  assert.equal(m12.size, 7);
  // The lenient 1.1 parser drops the triple-term claims + reifier line,
  // keeping only the two title triples — no triple terms at all.
  assert.equal(m11.size, 2);
  assert.ok(![...m11].some((q) => q.object.termType === 'Quad'), 'Mode_11 has no triple terms');
  assert.ok([...m12].some((q) => q.object.termType === 'Quad'), 'Mode_12 has triple terms');
});

test('post31: a variable binds a whole triple term (Quad term)', async () => {
  const dataset = await factoidal.parse(TTL, { format: 'turtle12' });
  const rows = await factoidal.query(dataset, `
    PREFIX : <http://example.org/>
    SELECT ?who ?statement WHERE { ?who :claimed ?statement }
  `, { version: '1.2' });
  assert.equal(rows.length, 2);
  for (const r of rows) assert.equal(r.get('statement').termType, 'Quad');
});

test('post31: <<( ?s ?p ?o )>> pattern matches inside the triple term', async () => {
  const dataset = await factoidal.parse(TTL, { format: 'turtle12' });
  const rows = await factoidal.query(dataset, `
    PREFIX : <http://example.org/>
    SELECT ?who ?s ?p ?o WHERE { ?who :claimed <<( ?s ?p ?o )>> }
  `, { version: '1.2' });
  assert.equal(rows.length, 2);
  const byWho = Object.fromEntries(rows.map((r) => [r.get('who').value.split('/').pop(), r]));
  assert.equal(byWho.einstein.get('s').value, 'http://example.org/light');
  assert.equal(byWho.aristotle.get('o').value, 'http://example.org/flat');
});

test('post31: isTRIPLE(?t) is true for both claimed statements', async () => {
  const dataset = await factoidal.parse(TTL, { format: 'turtle12' });
  const rows = await factoidal.query(dataset, `
    PREFIX : <http://example.org/>
    SELECT ?who (isTRIPLE(?t) AS ?isQuoted) WHERE { ?who :claimed ?t }
  `, { version: '1.2' });
  assert.equal(rows.length, 2);
  for (const r of rows) assert.equal(r.get('isQuoted').value, 'true');
});

test('post31: the annotation confidence is readable as a plain triple', async () => {
  const dataset = await factoidal.parse(TTL, { format: 'turtle12' });
  const rows = await factoidal.query(dataset, `
    PREFIX : <http://example.org/>
    SELECT ?conf WHERE { ?obs :confidence ?conf }
  `, { version: '1.2' });
  assert.equal(rows.length, 1);
  assert.equal(rows[0].get('conf').value, '0.99');
});

// ---------------------------------------------------------------------
// Cell-pinning: extract the exact ```observable-js source shipped on the
// page and run it through the same reactive machinery the browser uses,
// with fn === factoidal (see post02_test.mjs for the pattern).
// ---------------------------------------------------------------------

const cells = extractObservableCells(POST_FILE);

test('post31: post has 6 live cells (ttl + dataset + 4 query cells)', () => {
  assert.equal(cells.length, 6, `expected 6 live cells, found ${cells.length}`);
});

test('post31: dependency inference wires ttl -> dataset -> every query cell', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  assert.deepEqual(post.names.slice(0, 2), ['ttl', 'dataset']);
  assert.ok(post.infos[1].refs.includes('ttl'), 'dataset cell references ttl');
  for (const i of [2, 3, 4, 5]) {
    assert.ok(post.infos[i].refs.includes('dataset'), `cell ${i + 1} references dataset`);
  }
});

test('post31 cell 3 (bind whole triple term): 2 rows, statement renders as <<( )>>', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[2]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['who', 'statement']);
  assert.equal(result.rows.length, 2);
  for (const row of result.rows) {
    assert.ok(row.some((c) => String(c).includes('<<(')), 'a cell renders a triple term');
  }
});

test('post31 cell 4 (match inside triple term): 2 rows, 4 columns', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[3]);
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['who', 's', 'p', 'o']);
  assert.equal(result.rows.length, 2);
});

test('post31 cell 5 (isTRIPLE): 2 rows, both true', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[4]);
  assert.equal(result.rows.length, 2);
  for (const row of result.rows) {
    assert.ok(row.some((c) => String(c).includes('true')), 'isQuoted is true');
  }
});

test('post31 cell 6 (annotation confidence): 0.99', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const result = await post.value(post.names[5]);
  assert.equal(result.rows.length, 1);
  assert.ok(String(result.rows[0][0]).includes('0.99'));
});
