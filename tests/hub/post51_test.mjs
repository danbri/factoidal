import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';

import { extractObservableCells } from './_helpers.mjs';

const POST_FILE = '51-query-shardborough-blocks-in-browser.md';
const POST_PATH = new URL(`../../docs/web/hub/${POST_FILE}`, import.meta.url);
const ASSET_DIR = new URL('../../docs/web/hub/assets/blocks/shardborough-three-way/', import.meta.url);
const L4_LOADER = new URL('../../docs/web/hub/assets/l4/l4factoidal.js', import.meta.url);
const { loadL4 } = await import(L4_LOADER.href);

const blocks = [
  { file: 'type.ibk3', predicate: 'http://example.org/type', rows: 4, bytes: 310, sha256: '7797b38983808f0dded40813672b79f4b8d9f07956ff203d9becab9df8e40a68' },
  { file: 'name.ibk3', predicate: 'http://example.org/name', rows: 5, bytes: 536, sha256: '6a26193245b2ede29b80a5dcc8530da9f3415f7f96188948d27438142bbd7ede' },
  { file: 'member.ibk3', predicate: 'http://example.org/member', rows: 4, bytes: 342, sha256: '78540ea53aab57c78d4b0f025d6fbbe307e40d16fbd822331ec1cc0d6c2e542d' },
];

const query = `SELECT ?person ?type ?name ?team WHERE {
  ?person <http://example.org/type> ?type .
  ?person <http://example.org/name> ?name .
  ?person <http://example.org/member> ?team .
}
ORDER BY ?person ?name ?team`;
const allTriplesQuery = 'SELECT * WHERE { ?person ?p ?v . }';

const cells = extractObservableCells(POST_FILE);
const blankNodeScope = 'source:three-way-subject:8d07b81bf71e0b4c548b5faae50c4231b41bd99ecedc00a5e46817413e815346';
// Two one-row IBK3 golden vectors published from one Turtle document:
//   _:shared ex:type ex:Thing ; ex:name "shared node" .
// They pin the source-scope rule without requiring a native publisher in the
// Node/browser test environment.
const bnodeTypeIbk3 = '49424b33030100000061000000000000000000000001000000020000005054443101030000000001000001000000000000004400000001060000007368617265640017000000687474703a2f2f6578616d706c652e6f72672f747970650018000000687474703a2f2f6578616d706c652e6f72672f5468696e67b48b81babcbfa203';
const bnodeNameIbk3 = '49424b33030100000080000000000000000000000001000000020000005054443101030000000001000001000000000000006300000001060000007368617265640017000000687474703a2f2f6578616d706c652e6f72672f6e616d65020b000000736861726564206e6f646527000000687474703a2f2f7777772e77332e6f72672f323030312f584d4c536368656d6123737472696e67004ac6f8d14cbcfb56';
let enginePromise;
const engine = () => (enginePromise ??= loadL4());

test('post51: keeps the notebook readable as one interactive cell', () => {
  assert.equal(cells.length, 1);
  const source = readFileSync(POST_PATH, 'utf8');
  assert.match(source, /hubHideCellSource:\s*true/);
  assert.match(source, /scanIBK3Predicate/);
  assert.match(source, /factoidal-sparql-results/);
  assert.match(source, /factoidal-sparql-boolean/);
  assert.match(source, /factoidal-sparql-error/);
  assert.match(source, /resource limits and the bounded PushIR request format/);
  assert.match(source, /Show all 13 triples/);
  assert.match(source, /one IBK3 artifact/);
  assert.match(source, /position.*subject ID.*predicate ID.*object ID/);
  assert.match(source, /datasetOpen/);
  assert.match(source, /datasetQuery/);
  assert.match(source, /Origin Private File System, IndexedDB or the File System API/);
  assert.match(source, /SELECT`,\s+`ASK` and `CONSTRUCT/);
  assert.match(source, /DESCRIBE` and remote `SERVICE`/);
});

test('post51: bundled blocks have their declared exact identities', () => {
  for (const block of blocks) {
    const bytes = readFileSync(new URL(block.file, ASSET_DIR));
    assert.equal(bytes.length, block.bytes, `${block.file} byte length`);
    assert.equal(createHash('sha256').update(bytes).digest('hex'), block.sha256, `${block.file} SHA-256`);
  }
});

test('post51: committed Lean WASM reflects the IBK3 block worker', async () => {
  const l4 = await engine();
  const reflected = l4.call('ops', []);
  assert.ok(reflected.ops.includes('scanIBK3Predicate'));
  assert.ok(reflected.ops.includes('queryIBK3BlockSetPreview'));
});

test('post51: real IBK3 bytes pass through the WASM worker into SPARQL', async () => {
  const l4 = await engine();
  const scans = blocks.map(block => {
    const hex = readFileSync(new URL(block.file, ASSET_DIR)).toString('hex');
    const result = l4.call('scanIBK3Predicate', [hex, block.predicate, blankNodeScope]);
    assert.equal(result.format, 'IBK3');
    assert.equal(result.blankNodeScope, blankNodeScope);
    assert.equal(result.rows, block.rows, `${block.file} decoded row count`);
    return result.ntriples;
  });
  const result = l4.call('queryDataset', [scans.join('\n'), query]);
  assert.equal(result.kind, 'select');
  assert.equal(result.srj.results.bindings.length, 6);
  const dana = result.srj.results.bindings.filter(row => row.person.value === 'http://example.org/dana');
  assert.equal(dana.length, 4, 'two names × two teams must preserve SPARQL multiplicity');
  const allTriples = l4.call('queryDataset', [scans.join('\n'), allTriplesQuery]);
  assert.equal(allTriples.kind, 'select');
  assert.equal(allTriples.srj.results.bindings.length, 13,
    'the exploratory SELECT * query must expose every decoded block row');

  const opened = l4.call('datasetOpen', [scans.join('\n'), 'nquads', '']);
  assert.equal(opened.count, 13);
  const throughHandle = l4.call('datasetQuery', [opened.handle, query]);
  assert.equal(throughHandle.srj.results.bindings.length, 6,
    'the notebook reusable-handle path must preserve the stateless query result');

  const construct = l4.call('datasetQuery', [opened.handle,
    'CONSTRUCT { ?person <http://example.org/label> ?name } WHERE { ?person <http://example.org/name> ?name }']);
  assert.equal(construct.kind, 'construct');
  assert.equal(construct.nquads.split('\n').filter(Boolean).length, 5);

  const blockSetJson = JSON.stringify(blocks.map(block => [
    block.predicate,
    readFileSync(new URL(block.file, ASSET_DIR)).toString('hex'),
  ]));
  const bounded = l4.call('queryIBK3BlockSetPreview', [blockSetJson, blankNodeScope, `${query}\nLIMIT 20`]);
  assert.equal(bounded.kind, 'select');
  assert.equal(bounded.srj.results.bindings.length, 6,
    'the bounded block-set operation must avoid changing the joined result');
  assert.throws(
    () => l4.call('queryIBK3BlockSetPreview', [blockSetJson, blankNodeScope, query]),
    /SELECT and CONSTRUCT require LIMIT/,
  );
});

test('post51: corrupt bytes fail closed at the worker boundary', async () => {
  const l4 = await engine();
  assert.throws(
    () => l4.call('scanIBK3Predicate', ['00', 'http://example.org/type', blankNodeScope]),
    /invalid or corrupt canonical IBK3 artifact/,
  );
});

test('post51: the browser query entry installs the Lean GeoSPARQL functions', async () => {
  const l4 = await engine();
  const geoAsk = `PREFIX geo: <http://www.opengis.net/ont/geosparql#>
PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
ASK {
  FILTER(geof:sfWithin(
    "POINT(2 2)"^^geo:wktLiteral,
    "POLYGON((0 0,4 0,4 4,0 4,0 0))"^^geo:wktLiteral))
}`;
  const answer = l4.call('queryDataset', [
    '<http://example.org/a> <http://example.org/p> <http://example.org/b> .',
    geoAsk,
  ]);
  assert.equal(answer.kind, 'ask');
  assert.equal(answer.boolean, true);
});

test('post51: the worker refuses an absent blank-node composition scope', async () => {
  const l4 = await engine();
  assert.throws(
    () => l4.call('scanIBK3Predicate', ['00', 'http://example.org/type', '']),
    /blankNodeScope must be non-empty/,
  );
});

test('post51: one import scope preserves cross-block blank-node identity and separates another source', async () => {
  const l4 = await engine();
  const sourceA = 'source:blank-node-golden-a';
  const typeA = l4.call('scanIBK3Predicate', [bnodeTypeIbk3, 'http://example.org/type', sourceA]);
  const nameA = l4.call('scanIBK3Predicate', [bnodeNameIbk3, 'http://example.org/name', sourceA]);
  const nameB = l4.call('scanIBK3Predicate', [bnodeNameIbk3, 'http://example.org/name', 'source:blank-node-golden-b']);
  const ask = `ASK {
    ?node <http://example.org/type> <http://example.org/Thing> .
    ?node <http://example.org/name> "shared node" .
  }`;
  assert.equal(l4.call('queryDataset', [`${typeA.ntriples}\n${nameA.ntriples}`, ask]).boolean, true,
    'two predicate blocks from one import unit lost their shared blank node');
  assert.equal(l4.call('queryDataset', [`${typeA.ntriples}\n${nameB.ntriples}`, ask]).boolean, false,
    'same-spelled blank labels from two import scopes were coalesced');
});
