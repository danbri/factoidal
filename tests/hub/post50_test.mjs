import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';

import { extractObservableCells, runReactivePost } from './_helpers.mjs';

const cells = extractObservableCells('50-shardborough-life-sciences.md');

test('post50: preserves the declared Shardborough working set', async () => {
  const post = runReactivePost(cells, {});
  const borough = await post.value('lifeSciShardborough');
  assert.equal(borough.id, 'shardborough:lifesci-crossgraph:v0');
  assert.equal(borough.members.length, 3);
  assert.equal(borough.members.reduce((sum, member) => sum + member.triples, 0), 43103);
});

test('post50: documents the bounded, cross-graph workload', () => {
  const source = fs.readFileSync('docs/web/hub/50-shardborough-life-sciences.md', 'utf8');
  assert.match(source, /GRAPH <urn:kgx:chromosome>/);
  assert.match(source, /GRAPH <urn:kgx:sequence_variant>/);
  assert.match(source, /LIMIT 20/);
  assert.match(source, /factoidal-sparql-results/);
});

test('SPARQL result elements expose all four standard result views', () => {
  const source = fs.readFileSync('docs/web/hub/assets/sparql-result-elements.mjs', 'utf8');
  for (const tag of [
    'factoidal-sparql-results',
    'factoidal-sparql-graph',
    'factoidal-sparql-boolean',
    'factoidal-sparql-error',
  ]) assert.match(source, new RegExp(`customElements\\.define\\("${tag}"`));
  assert.match(source, /All languages/);
  assert.match(source, /All datatypes/);
  assert.match(source, /Swipeable row/);
});
