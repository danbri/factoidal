// Unit tests for factoidal/fn — the strictly functional dataset API.
//
// Style mirrors test/api.test.js: tests needing the npm-entry ABI
// bundle (canonicalize/hash/entail/query-CONSTRUCT) probe
// capabilities() and skip with the "pending npm-entry build" reason
// when only the CLI bundle is available, exactly like the mutable API
// suite already does.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const fn = require('../fn.js');
const {
  FnDataset, EMPTY, fromDataset, toDataset, builder, fromChunks,
  parse, union, difference,
  filter, mapQuads, query, entail, canonicalize, hash, equals, graphs,
  cell, derive, capabilities,
} = fn;

const { Dataset, dataFactory: df } = require('../rdfjs.js');

const PENDING = 'pending npm-entry build';

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob" .
`;

// ---------------------------------------------------------------------
// Purity: no op mutates its inputs.
// ---------------------------------------------------------------------

test('purity: filter/mapQuads/union/difference do not alter their inputs', async () => {
  const ds = await parse(TTL);
  const before = ds.toNQuads();
  const beforeSize = ds.size;

  filter(ds, (q) => q.predicate.value.endsWith('name'));
  mapQuads(ds, (q) => q);
  union(ds, EMPTY);
  difference(ds, EMPTY);

  assert.equal(ds.toNQuads(), before, 'ds unchanged after ops ran over it');
  assert.equal(ds.size, beforeSize);
});

test('purity: FnDataset is frozen and its quad array cannot be mutated', async () => {
  const ds = await parse(TTL);
  assert.ok(Object.isFrozen(ds), 'FnDataset instance is frozen');
  const arr = ds.toArray();
  arr.push(df.quad(df.namedNode('http://x/s'), df.namedNode('http://x/p'),
    df.namedNode('http://x/o')));
  assert.equal(ds.size, arr.length - 1, 'toArray() returns a copy, not a live view');
  for (const q of ds) {
    assert.ok(Object.isFrozen(q), 'iterated quads are frozen');
  }
});

test('purity: filter output is independent of the input array', async () => {
  const ds = await parse(TTL);
  const names = filter(ds, (q) => q.predicate.value.endsWith('name'));
  assert.equal(names.size, 2);
  assert.equal(ds.size, 5, 'original untouched');
});

// ---------------------------------------------------------------------
// Union / difference algebra sanity.
// ---------------------------------------------------------------------

test('algebra: union with EMPTY is identity', async () => {
  const ds = await parse(TTL);
  assert.ok(await equals(union(ds, EMPTY), ds));
  assert.ok(await equals(union(EMPTY, ds), ds));
});

test('algebra: union is idempotent and deduplicates', async () => {
  const ds = await parse(TTL);
  const doubled = union(ds, ds);
  assert.equal(doubled.size, ds.size, 'union(ds, ds) has no duplicate quads');
  assert.ok(await equals(doubled, ds));
});

test('algebra: difference with EMPTY is identity, self-difference is EMPTY', async () => {
  const ds = await parse(TTL);
  assert.ok(await equals(difference(ds, EMPTY), ds));
  assert.equal(difference(ds, ds).size, 0);
  assert.ok(await equals(difference(ds, ds), EMPTY));
});

test('algebra: union/difference round-trip (a = (a-b) u (a intersect b))', async () => {
  const a = await parse(TTL);
  const b = filter(a, (q) => q.predicate.value.endsWith('name'));
  const rest = difference(a, b);
  assert.equal(rest.size + b.size, a.size);
  assert.ok(await equals(union(rest, b), a));
});

test('EMPTY is a genuinely empty, reusable constant', () => {
  assert.ok(EMPTY instanceof FnDataset);
  assert.equal(EMPTY.size, 0);
  assert.equal([...EMPTY].length, 0);
});

// ---------------------------------------------------------------------
// Hash stability under blank-node relabeling (canonicalization
// property test pattern, mirroring test/api.test.js's canonicalize()
// and canonicalHash() tests).
// ---------------------------------------------------------------------

test('hash: stable under blank-node relabeling; changes when content changes',
  async (t) => {
    const caps = await capabilities();
    if (!caps.canonicalize) {
      t.skip(`${PENDING} (or CLI bundle rebuild with --canonicalize)`);
      return;
    }
    const dsA = await parse(
      '_:x <http://x/p> _:y .\n_:y <http://x/p> "leaf" .\n', { format: 'nquads' });
    const dsB = await parse(
      '_:n1 <http://x/p> _:n2 .\n_:n2 <http://x/p> "leaf" .\n', { format: 'nquads' });
    const hA = await hash(dsA);
    const hB = await hash(dsB);
    assert.equal(hA, hB, 'isomorphic graphs under relabeling hash identically');
    assert.match(hA, /^[0-9a-f]{64}$/, 'hash() is a sha256 hex digest');

    const dsC = await parse(
      '_:x <http://x/p> _:y .\n_:y <http://x/p> "different" .\n', { format: 'nquads' });
    assert.notEqual(await hash(dsC), hA, 'different content hashes differently');
  });

test('hash: memoized (repeated calls on the same FnDataset return the same value fast)',
  async (t) => {
    const caps = await capabilities();
    if (!caps.canonicalize) {
      t.skip(PENDING);
      return;
    }
    const ds = await parse(TTL);
    const h1 = await hash(ds);
    const h2 = await hash(ds);
    assert.equal(h1, h2);
    // Concurrent callers before the first result lands share one
    // in-flight computation rather than double-canonicalizing.
    const ds2 = await parse(TTL);
    const [ha, hb] = await Promise.all([hash(ds2), hash(ds2)]);
    assert.equal(ha, hb);
  });

test('equals: ground (blank-node-free) data uses cheap exact quad-set comparison',
  async () => {
    const a = await parse('<http://x/a> <http://x/p> "v" .', { format: 'ntriples' });
    const b = await parse('<http://x/a> <http://x/p> "v" .', { format: 'ntriples' });
    const c = await parse('<http://x/a> <http://x/p> "w" .', { format: 'ntriples' });
    assert.ok(await equals(a, b));
    assert.ok(!(await equals(a, c)));
  });

test('equals: blank-node datasets fall back to canonical-hash equality',
  async (t) => {
    const caps = await capabilities();
    if (!caps.canonicalize) {
      t.skip(PENDING);
      return;
    }
    const a = await parse('_:x <http://x/p> "v" .', { format: 'ntriples' });
    const b = await parse('_:y <http://x/p> "v" .', { format: 'ntriples' });
    // Different source labels -> exact quad-token match fails, but the
    // graphs are isomorphic, so equals() must still say true.
    assert.ok(await equals(a, b));
  });

// ---------------------------------------------------------------------
// derive() memoization hit/miss behavior.
// ---------------------------------------------------------------------

test('derive: skips recompute when input hash is unchanged, recomputes when it changes',
  async (t) => {
    const caps = await capabilities();
    if (!caps.canonicalize) {
      t.skip(PENDING);
      return;
    }
    let calls = 0;
    const input = cell(await parse('<http://x/a> <http://x/p> "v" .', { format: 'ntriples' }));
    const derived = derive(async (ds) => { calls++; return ds.size; }, input);

    assert.equal(await derived.get(), 1);
    assert.equal(calls, 1, 'first get() always computes');

    assert.equal(await derived.get(), 1);
    assert.equal(calls, 1, 'unchanged cell -> memoized hit, no recompute');

    // Set a *different object* with the *same content* -> same hash ->
    // still a memoized hit, proving the key is content, not identity.
    input.set(await parse('<http://x/a> <http://x/p> "v" .', { format: 'ntriples' }));
    assert.equal(await derived.get(), 1);
    assert.equal(calls, 1, 'same content, different object -> still a hit');

    // Actually change the content -> must recompute.
    input.set(await parse(
      '<http://x/a> <http://x/p> "v" .\n<http://x/a> <http://x/p> "w" .',
      { format: 'ntriples' }));
    assert.equal(await derived.get(), 2);
    assert.equal(calls, 2, 'changed content -> recompute');
  });

test('derive: non-dataset inputs key by value identity', async () => {
  let calls = 0;
  const n = cell(2);
  const derived = derive(async (x) => { calls++; return x * 10; }, n);
  assert.equal(await derived.get(), 20);
  assert.equal(calls, 1);
  n.set(2);
  assert.equal(await derived.get(), 20);
  assert.equal(calls, 1, 'same primitive value -> memoized hit');
  n.set(3);
  assert.equal(await derived.get(), 30);
  assert.equal(calls, 2);
});

// ---------------------------------------------------------------------
// Streaming builder seam (builder()/fromChunks()) — the trivial
// in-memory implementation of the streaming-parser integration point.
// ---------------------------------------------------------------------

test('builder: accumulates chunks and finish() returns a deduplicated, frozen FnDataset', () => {
  const q1 = df.quad(df.namedNode('http://x/a'), df.namedNode('http://x/p'), df.literal('1'));
  const q2 = df.quad(df.namedNode('http://x/b'), df.namedNode('http://x/p'), df.literal('2'));
  const b = builder();
  b.addChunk(q1);            // a single quad
  b.addChunk([q2, q1]);      // a batch, with a duplicate of q1
  const ds = b.finish();
  assert.ok(ds instanceof FnDataset);
  assert.equal(ds.size, 2, 'duplicate across chunks is deduplicated at finish()');
  assert.ok(Object.isFrozen(ds));
});

test('builder: addChunk()/finish() reject use after finish()', () => {
  const b = builder();
  b.addChunk(df.quad(df.namedNode('http://x/a'), df.namedNode('http://x/p'), df.literal('1')));
  b.finish();
  assert.throws(() => b.addChunk(
    df.quad(df.namedNode('http://x/b'), df.namedNode('http://x/p'), df.literal('2'))));
  assert.throws(() => b.finish());
});

test('fromChunks: consumes an async iterable of quad batches into one FnDataset', async () => {
  async function* batches() {
    yield [df.quad(df.namedNode('http://x/a'), df.namedNode('http://x/p'), df.literal('1'))];
    yield [df.quad(df.namedNode('http://x/b'), df.namedNode('http://x/p'), df.literal('2'))];
  }
  const ds = await fromChunks(batches());
  assert.ok(ds instanceof FnDataset);
  assert.equal(ds.size, 2);
});

// ---------------------------------------------------------------------
// Interop round-trip with the mutable Dataset.
// ---------------------------------------------------------------------

test('interop: fromDataset/toDataset round-trips quad content', () => {
  const mutable = new Dataset([
    df.quad(df.namedNode('http://x/a'), df.namedNode('http://x/p'),
      df.literal('v')),
  ]);
  const frozen = fromDataset(mutable);
  assert.equal(frozen.size, 1);
  assert.ok(Object.isFrozen(frozen));

  const back = toDataset(frozen);
  assert.ok(back instanceof Dataset);
  assert.equal(back.size, 1);
  assert.equal(back.toNQuads(), mutable.toNQuads());

  // The round-tripped Dataset is independently mutable and does not
  // reach back into the frozen FnDataset.
  back.add(df.quad(df.namedNode('http://x/b'), df.namedNode('http://x/p'),
    df.literal('w')));
  assert.equal(back.size, 2);
  assert.equal(frozen.size, 1, 'mutating the round-tripped copy leaves frozen alone');
});

test('interop: query() accepts an FnDataset and returns Bindings[]', async () => {
  const ds = await parse(TTL);
  const rows = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name }
  `);
  assert.ok(Array.isArray(rows));
  assert.equal(rows.length, 2);
});

test('interop: query() CONSTRUCT returns an FnDataset', async (t) => {
  const caps = await capabilities();
  if (!caps.construct) {
    t.skip(PENDING);
    return;
  }
  const ds = await parse(TTL);
  const out = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    CONSTRUCT { ?p <http://x/hasName> ?n } WHERE { ?p foaf:name ?n }
  `);
  assert.ok(out instanceof FnDataset);
  assert.equal(out.size, 2);
});

test('interop: entail() materializes an RDFS closure as an FnDataset', async () => {
  // Reuses the SELECT+entail path (lib/api.js), not CONSTRUCT, so this
  // does not need the npm-entry bundle — see fn.js's entail() comment.
  const data = `
    @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
    @prefix ex:   <http://example.org/> .
    ex:Hotel rdfs:subClassOf ex:Place .
    ex:motel6 a ex:Hotel .
  `;
  const ds = await parse(data);
  const closure = await entail(ds, 'RDFS');
  assert.ok(closure instanceof FnDataset);
  assert.ok(closure.size > ds.size, 'closure adds at least the inferred triple');
});

test('interop: graphs() enumerates named graphs as FnDatasets', async () => {
  const ds = await parse(
    '@prefix ex: <http://x/> . ' +
    'ex:g1 { ex:a ex:p "one" . } ' +
    'ex:c ex:p "default" .',
    { format: 'trig' });
  const gs = graphs(ds);
  assert.equal(gs.length, 1);
  const [iri, g1] = gs[0];
  assert.equal(iri, 'http://x/g1');
  assert.ok(g1 instanceof FnDataset);
  assert.equal(g1.size, 1);
});

test('canonicalize: two blank-node relabelings of the same graph canonicalize identically',
  async (t) => {
    const caps = await capabilities();
    if (!caps.canonicalize) {
      t.skip(`${PENDING} (or CLI bundle rebuild with --canonicalize)`);
      return;
    }
    const a = await parse('_:x <http://x/p> _:y .\n_:y <http://x/p> "leaf" .\n',
      { format: 'nquads' });
    const b = await parse('_:n1 <http://x/p> _:n2 .\n_:n2 <http://x/p> "leaf" .\n',
      { format: 'nquads' });
    const canonA = await canonicalize(a);
    const canonB = await canonicalize(b);
    assert.equal(canonA, canonB);
  });
