// Regression pin, 2026-09-02: FILTER NOT EXISTS through the Lean WASM
// dataset-handle path answered zero rows, because the backend evaluation
// environment carried no dataset for the §18.6 EXISTS sub-evaluation
// (Wasm/Ops/Query.lean). Found by tools/w3c-persisted-census.sh, whose
// manifest-extraction query uses FILTER NOT EXISTS.
//
// Runs against the committed browser module, the same bytes the hub
// pages load (docs/web/hub/assets/l4/), through the handle ABI the
// pages use (datasetOpen -> datasetQuery).

import test from 'node:test';
import assert from 'node:assert/strict';

const L4_LOADER = new URL('../../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const { loadL4 } = await import(L4_LOADER.href);

const DATA = '<http://e/a> <http://e/p> <http://e/b> .\n';

function bindings(r) {
  assert.equal(r.ok, true, JSON.stringify(r));
  assert.equal(r.kind, 'select');
  return (r.srj.results && r.srj.results.bindings) || [];
}

test('FILTER NOT EXISTS keeps the row whose reversed pattern is absent', async () => {
  const engine = await loadL4();
  const open = engine.call('datasetOpen', [DATA, 'nquads', '']);
  assert.equal(open.ok, true, JSON.stringify(open));
  const rows = bindings(engine.call('datasetQuery', [open.handle,
    'SELECT ?s WHERE { ?s <http://e/p> ?o FILTER NOT EXISTS { ?o <http://e/p> ?s } }']));
  assert.equal(rows.length, 1);
  assert.equal(rows[0].s.value, 'http://e/a');
});

test('FILTER EXISTS drops that row', async () => {
  const engine = await loadL4();
  const open = engine.call('datasetOpen', [DATA, 'nquads', '']);
  const rows = bindings(engine.call('datasetQuery', [open.handle,
    'SELECT ?s WHERE { ?s <http://e/p> ?o FILTER EXISTS { ?o <http://e/p> ?s } }']));
  assert.equal(rows.length, 0);
});

test('the stateless queryDataset op agrees', async () => {
  const engine = await loadL4();
  const rows = bindings(engine.call('queryDataset', [DATA,
    'SELECT ?s WHERE { ?s <http://e/p> ?o FILTER NOT EXISTS { ?o <http://e/p> ?s } }']));
  assert.equal(rows.length, 1);
});
