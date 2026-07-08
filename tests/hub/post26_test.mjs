// Pins docs/web/hub/26-reactive-cells-declare-once-use-everywhere.md.
//
// Unlike the other post tests (which run each cell standalone via
// runObservableCell), this post's whole point is CROSS-CELL reference:
// `graph = fn.parse(ttl)` reads the `ttl` cell, `results = fn.query(
// graph, ...)` reads `graph`, and so on. So it exercises the reactive
// path -- runReactivePost() builds the same vendored-runtime module the
// browser builds, wires each cell's inputs with the SAME analyzeCell()
// compiler docs/_includes/hub.njk uses, and reads a named cell's value
// through the dependency chain. See tests/hub/_helpers.mjs.

import {
  NPM_FACTOIDAL_INDEX,
  extractObservableCells,
  runReactivePost,
  pretty,
} from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '26-reactive-cells-declare-once-use-everywhere.md';

const cells = extractObservableCells(POST_FILE);

test('post26: post ships the seven-cell reactive chain', () => {
  assert.equal(cells.length, 7, `expected 7 live cells, found ${cells.length}`);
});

// ---------------------------------------------------------------------
// Dependency inference: prove the compiler wires the cross-cell inputs,
// not just that each cell happens to run.
// ---------------------------------------------------------------------
test('post26: dependency inference names the right cells + inputs', () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });
  const byName = Object.fromEntries(post.infos.map((info, i) => [post.names[i], info]));

  // Named cells, in order.
  assert.deepEqual(
    post.names.slice(0, 6),
    ['ttl', 'graph', 'tripleCount', 'results', 'table', 'chartData'],
    'first six cells declare these names'
  );

  // ttl is a pure literal: no cross-cell inputs.
  assert.equal(byName.ttl.name, 'ttl');
  assert.deepEqual([...byName.ttl.refs], [], 'ttl references nothing');

  // graph depends on the fn builtin and the ttl cell.
  assert.ok(byName.graph.refs.includes('fn'), 'graph references fn');
  assert.ok(byName.graph.refs.includes('ttl'), 'graph references ttl');

  // tripleCount depends only on graph.
  assert.ok(byName.tripleCount.refs.includes('graph'), 'tripleCount references graph');

  // results depends on fn + graph.
  assert.ok(byName.results.refs.includes('fn'), 'results references fn');
  assert.ok(byName.results.refs.includes('graph'), 'results references graph');

  // chartData depends on results.
  assert.ok(byName.chartData.refs.includes('results'), 'chartData references results');

  // The final (anonymous) chart cell references Plot + chartData.
  const chartInfo = post.infos[6];
  assert.equal(chartInfo.name, null, 'chart cell is anonymous');
  assert.ok(chartInfo.refs.includes('Plot'), 'chart references Plot');
  assert.ok(chartInfo.refs.includes('chartData'), 'chart references chartData');
});

// ---------------------------------------------------------------------
// Values resolve through the chain: ttl -> graph -> {tripleCount,
// results} -> {table, chartData}. Reading a downstream name forces the
// runtime to compute (and await the promise-valued) upstream cells.
// ---------------------------------------------------------------------
test('post26: values propagate ttl -> graph -> results -> chartData', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });

  const ttl = await post.value('ttl');
  assert.equal(typeof ttl, 'string');
  assert.ok(ttl.includes('foaf:knows'), 'ttl carries the FOAF Turtle');

  const graph = await post.value('graph');
  assert.equal(graph.size, 14, 'parsed graph has 14 triples');

  const tripleCount = await post.value('tripleCount');
  assert.equal(tripleCount, 14, 'tripleCount cell read graph.size across cells');

  const results = await post.value('results');
  assert.equal(results.length, 4, 'one COUNT row per person');

  const table = await post.value('table');
  assert.equal(table.kind, 'table');
  assert.equal(table.rows.length, 4, 'pretty(results) is a 4-row table');

  const chartData = await post.value('chartData');
  assert.deepEqual(
    chartData,
    [
      { name: 'Alice', friends: 3 },
      { name: 'Carol', friends: 2 },
      { name: 'Bob', friends: 1 },
      { name: 'Dave', friends: 0 },
    ],
    'friend counts, DESC-ordered, reshaped for the chart'
  );
});

// ---------------------------------------------------------------------
// Reactivity: edit the upstream `ttl` cell (the Edit+Run path), and a
// downstream cell recomputes WITHOUT touching cells 2-4.
// ---------------------------------------------------------------------
test('post26: editing ttl re-runs graph + chartData downstream', async () => {
  const post = runReactivePost(cells, { fn: factoidal, pretty });

  assert.equal((await post.value('graph')).size, 14, 'baseline before edit');
  const before = await post.value('chartData');
  assert.equal(before.find((d) => d.name === 'Alice').friends, 3);

  // Add a fifth person, Erin, and make Bob know her too. Only the ttl
  // cell is redefined; graph/results/chartData are untouched.
  post.redefine('ttl', 'ttl = `\n' +
    '@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n' +
    '@prefix ex:   <http://example.org/> .\n\n' +
    'ex:alice a foaf:Person ; foaf:name "Alice" ;\n' +
    '  foaf:knows ex:bob , ex:carol , ex:dave , ex:erin .\n' +
    'ex:bob   a foaf:Person ; foaf:name "Bob" ;\n' +
    '  foaf:knows ex:carol , ex:erin .\n' +
    'ex:carol a foaf:Person ; foaf:name "Carol" ;\n' +
    '  foaf:knows ex:alice , ex:dave .\n' +
    'ex:dave  a foaf:Person ; foaf:name "Dave" .\n' +
    'ex:erin  a foaf:Person ; foaf:name "Erin" .\n' +
    '`');

  const graphAfter = await post.value('graph');
  assert.ok(graphAfter.size > 14, 'graph re-parsed after ttl edit');

  const after = await post.value('chartData');
  assert.equal(after.length, 5, 'Erin now appears — five people');
  assert.equal(after.find((d) => d.name === 'Alice').friends, 4, 'Alice now knows 4');
  assert.equal(after.find((d) => d.name === 'Erin').friends, 0, 'Erin knows nobody');
});
