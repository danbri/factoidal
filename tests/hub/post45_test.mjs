import test from 'node:test';
import assert from 'node:assert/strict';

import { extractObservableCells, runReactivePost } from './_helpers.mjs';

const cells = extractObservableCells('45-life-sciences-named-graphs.md');
const post = () => runReactivePost(cells, {});

test('post45: catalogue preserves the three committed legacy graphs and total', async () => {
  const catalogue = await post().value('lifeSciCatalog');
  assert.deepEqual(catalogue.map((entry) => entry.file), [
    'chromosome.ttl', 'sequence_variant.ttl', 'disease.ttl',
  ]);
  assert.equal(catalogue.reduce((sum, entry) => sum + entry.triples, 0), 43103);
});

test('post45: workload is the bounded chromosome/variant named-graph join', async () => {
  const query = await post().value('lifeSciQuery');
  assert.match(query, /GRAPH <urn:kgx:chromosome>/);
  assert.match(query, /GRAPH <urn:kgx:sequence_variant>/);
  assert.match(query, /LIMIT 20/);
});
