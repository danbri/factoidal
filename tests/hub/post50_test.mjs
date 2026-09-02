import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import fs from 'node:fs';

import { extractObservableCells, runReactivePost } from './_helpers.mjs';

const POST_FILE = '50-shardborough-life-sciences.md';
const ASSET_DIR = new URL('../../docs/web/hub/assets/blocks/lifesci-crossgraph/', import.meta.url);
const L4_LOADER = new URL('../../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const { loadL4 } = await import(L4_LOADER.href);

const cells = extractObservableCells(POST_FILE);
let enginePromise;
const engine = () => (enginePromise ??= loadL4());
const hex = bytes => Array.from(bytes, byte => byte.toString(16).padStart(2, '0')).join('');

const manifest = async () => {
  const post = runReactivePost(cells, {});
  return post.value('lifeSciShardborough');
};

test('post50: preserves the declared Shardborough working set', async () => {
  const borough = await manifest();
  assert.equal(borough.id, 'shardborough:lifesci-crossgraph:v0');
  assert.equal(borough.members.length, 3);
  assert.equal(borough.members.reduce((sum, member) => sum + member.triples, 0), 43103);
  assert.equal(borough.workerOperation, 'scanIBK3Predicate');
  const blocks = borough.members.flatMap(member => member.blocks);
  assert.equal(blocks.length, 12);
  assert.equal(blocks.reduce((sum, block) => sum + block.bytes, 0), 2621268);
  for (const member of borough.members) {
    assert.equal(member.blocks.reduce((sum, block) => sum + block.rows, 0), member.triples);
    assert.match(member.scope, /^source:[a-z_]+\.ttl:[0-9a-f]{64}$/);
  }
});

test('post50: bundled blocks have their declared exact identities', async () => {
  const borough = await manifest();
  for (const member of borough.members) {
    for (const block of member.blocks) {
      const bytes = fs.readFileSync(new URL(block.file, ASSET_DIR));
      assert.equal(bytes.length, block.bytes, block.file);
      assert.equal(createHash('sha256').update(bytes).digest('hex'), block.sha256, block.file);
    }
  }
});

test('post50: the Lean worker decodes every block to its declared row count', async () => {
  const borough = await manifest();
  const fn = await engine();
  for (const member of borough.members) {
    for (const block of member.blocks) {
      const bytes = fs.readFileSync(new URL(block.file, ASSET_DIR));
      const scan = fn.call('scanIBK3Predicate', [hex(bytes), `http://www.wikidata.org/prop/direct/${block.property}`, member.scope]);
      assert.equal(scan.ok, true, block.file);
      assert.equal(scan.rows, block.rows, block.file);
    }
  }
});

test('post50: the cross-graph query runs from two blocks with graph names from the manifest', async () => {
  const borough = await manifest();
  const fn = await engine();
  const pick = (graph, property) => {
    const member = borough.members.find(m => m.graph === graph);
    const block = member.blocks.find(b => b.property === property);
    const bytes = fs.readFileSync(new URL(block.file, ASSET_DIR));
    const scan = fn.call('scanIBK3Predicate', [hex(bytes), `http://www.wikidata.org/prop/direct/${property}`, member.scope]);
    return scan.ntriples.split('\n').filter(Boolean).map(line => line.replace(/ \.$/, ` <${graph}> .`)).join('\n');
  };
  const nquads = [pick('urn:kgx:chromosome', 'P31'), pick('urn:kgx:sequence_variant', 'P1057')].join('\n');
  const opened = fn.call('datasetOpen', [nquads, 'nquads', '']);
  assert.equal(opened.ok, true);
  assert.equal(opened.count, 9227 + 1357);
  const answer = fn.call('datasetQuery', [opened.handle, `PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX wd: <http://www.wikidata.org/entity/>
SELECT ?variant ?chrom WHERE {
  GRAPH <urn:kgx:chromosome> { ?chrom wdt:P31 wd:Q37748 }
  GRAPH <urn:kgx:sequence_variant> { ?variant wdt:P1057 ?chrom }
} LIMIT 20`]);
  assert.equal(answer.ok, true);
  assert.equal(answer.kind, 'select');
  assert.equal(answer.srj.results.bindings.length, 20);
  const wrongGraph = fn.call('datasetQuery', [opened.handle, `PREFIX wdt: <http://www.wikidata.org/prop/direct/>
ASK { GRAPH <urn:kgx:disease> { ?s wdt:P1057 ?o } }`]);
  assert.equal(wrongGraph.ok, true);
  assert.equal(wrongGraph.boolean, false);
});

test('post50: the labels block decodes and resolves a known entity', async () => {
  const borough = await manifest();
  const fn = await engine();
  const block = borough.labels;
  const bytes = fs.readFileSync(new URL(block.file, ASSET_DIR));
  assert.equal(bytes.length, block.bytes);
  assert.equal(createHash('sha256').update(bytes).digest('hex'), block.sha256);
  const scan = fn.call('scanIBK3Predicate', [hex(bytes), block.predicate, block.scope]);
  assert.equal(scan.ok, true);
  assert.equal(scan.rows, block.rows);
  const opened = fn.call('datasetOpen', [scan.ntriples, 'nquads', '']);
  assert.equal(opened.ok, true);
  const answer = fn.call('datasetQuery', [opened.handle,
    'SELECT ?label WHERE { <http://www.wikidata.org/entity/Q668633> <http://www.w3.org/2000/01/rdf-schema#label> ?label } LIMIT 1']);
  assert.equal(answer.ok, true);
  assert.equal(answer.srj.results.bindings[0].label.value, 'human chromosome 3');
});

test('post50: the four-hop chromosome-3 question answers through the indexed query path', async () => {
  const borough = await manifest();
  const fn = await engine();
  const pick = (graph, property) => {
    const member = borough.members.find(m => m.graph === graph);
    const block = member.blocks.find(b => b.property === property);
    const bytes = fs.readFileSync(new URL(block.file, ASSET_DIR));
    const scan = fn.call('scanIBK3Predicate', [hex(bytes), `http://www.wikidata.org/prop/direct/${property}`, member.scope]);
    return scan.ntriples.split('\n').filter(Boolean).map(line => line.replace(/ \.$/, ` <${graph}> .`)).join('\n');
  };
  const nquads = [pick('urn:kgx:sequence_variant', 'P1057'), pick('urn:kgx:sequence_variant', 'P3433'),
    pick('urn:kgx:disease', 'P2293'), pick('urn:kgx:disease', 'P2176')].join('\n');
  const opened = fn.call('datasetOpen', [nquads, 'nquads', '']);
  assert.equal(opened.ok, true);
  assert.equal(opened.count, 1357 + 1702 + 5586 + 2752);
  const started = performance.now();
  const answer = fn.call('datasetQuery', [opened.handle, `PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX wd: <http://www.wikidata.org/entity/>
SELECT ?variant ?gene ?disease ?drug WHERE {
  GRAPH <urn:kgx:sequence_variant> { ?variant wdt:P1057 wd:Q668633 . ?variant wdt:P3433 ?gene }
  GRAPH <urn:kgx:disease> { ?disease wdt:P2293 ?gene . ?disease wdt:P2176 ?drug }
} LIMIT 20`]);
  const elapsed = performance.now() - started;
  assert.equal(answer.ok, true);
  assert.equal(answer.srj.results.bindings.length, 20);
  assert.ok(elapsed < 60000, `four-hop query took ${Math.round(elapsed)} ms`);
});

test('post50: documents the bounded, cross-graph workload', () => {
  const source = fs.readFileSync('docs/web/hub/50-shardborough-life-sciences.md', 'utf8');
  assert.match(source, /GRAPH <urn:kgx:chromosome>/);
  assert.match(source, /GRAPH <urn:kgx:sequence_variant>/);
  assert.match(source, /LIMIT 20/);
  assert.match(source, /factoidal-sparql-results/);
  assert.match(source, /scanIBK3Predicate/);
  assert.match(source, /fetches only the blocks it names/);
  assert.match(source, /complete fallback/);
  assert.match(source, /LIMIT 20\s+limits the displayed answers, not the input work/);
  assert.match(source, /navigator\.storage\.getDirectory/);
  assert.match(source, /Clear local cache/);
  assert.match(source, /re-verified against the manifest/);
  assert.match(source, /decoded dataset is not persisted/);
  assert.match(source, /default-graph boundary explicitly/);
  assert.match(source, /do not carry graph identity yet/);
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
  assert.match(source, /Language tag/);
  assert.match(source, /language-tags/);
  assert.match(source, /datatypes/);
  assert.match(source, /Swipeable row/);
});
