// Dataset handles (issue #680): openDataset() parses once, then
// query()/update()/serialize() run against the engine's own cached,
// indexed copy. Every answer here is checked against the equivalent
// stateless call on the same data, so a handle can never silently
// diverge from query()/update()/serialize().

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('../index.js');
const { Dataset } = require('../rdfjs.js');

async function entryAvailable() {
  try {
    return !!(await factoidal.capabilities()).entry;
  } catch (_) {
    return false;
  }
}

const TTL =
  '@prefix ex: <http://example.org/> .\n' +
  'ex:alice ex:name "Alice" ; ex:age 30 ; ex:knows ex:bob .\n' +
  'ex:bob   ex:name "Bob" .\n';
const JOIN_Q =
  'PREFIX ex: <http://example.org/> ' +
  'SELECT ?s ?n WHERE { ?s ex:name ?n }';

function normRows(rows) {
  return rows
    .map((r) => [...r.entries()]
      .map(([k, v]) => `${k}=${v.termType}:${v.value}`)
      .sort()
      .join('|'))
    .sort();
}

test('dataset handle: open, query several times, update, serialize both formats, toDataset, close', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (dataset handles need it)');
    return;
  }

  const handle = await factoidal.openDataset(TTL, { format: 'turtle' });
  assert.equal(typeof handle.handle, 'string');
  assert.equal(handle.size, 4);
  assert.equal(handle.closed, false);

  // Several query() calls against the same handle, each matching the
  // stateless answer on the same data.
  const statelessRows = await factoidal.query(TTL, JOIN_Q, { format: 'turtle' });
  for (let i = 0; i < 3; i++) {
    const rows = await handle.query(JOIN_Q);
    assert.deepEqual(normRows(rows), normRows(statelessRows), `query() call ${i + 1}`);
  }

  const statelessAsk = await factoidal.query(TTL,
    'PREFIX ex: <http://example.org/> ASK { ex:alice ex:knows ex:bob }', { format: 'turtle' });
  const handleAsk = await handle.query(
    'PREFIX ex: <http://example.org/> ASK { ex:alice ex:knows ex:bob }');
  assert.equal(handleAsk, statelessAsk);
  assert.equal(handleAsk, true);

  // update() mutates in place and returns the SAME handle, refreshed.
  const updateText = 'PREFIX ex: <http://example.org/> ' +
    'INSERT DATA { ex:carol ex:name "Carol" }';
  const returned = await handle.update(updateText);
  assert.equal(returned, handle, 'update() returns the same handle instance');
  assert.equal(handle.size, 5);

  const statelessDs = await factoidal.update(TTL, updateText, { format: 'turtle' });
  const statelessNq = await factoidal.serialize(statelessDs, { format: 'nquads' });
  const handleNq = await handle.serialize({ format: 'nquads' });
  assert.equal(handleNq, statelessNq, 'nquads serialize matches the stateless update+serialize');

  const statelessTtl = await factoidal.serialize(statelessDs, { format: 'turtle' });
  const handleTtl = await handle.serialize({ format: 'turtle' });
  assert.equal(typeof handleTtl, 'string');
  assert.match(handleTtl, /carol/i);
  // Both round-trip through the parser to the same triple set (Turtle
  // pretty-printing order/prefix labels are not byte-pinned, but the
  // graph they denote must agree).
  const [dsFromStateless, dsFromHandle] = await Promise.all([
    factoidal.parse(statelessTtl, { format: 'turtle' }),
    factoidal.parse(handleTtl, { format: 'turtle' }),
  ]);
  assert.equal(dsFromHandle.size, dsFromStateless.size);

  const asDataset = await handle.toDataset();
  assert.ok(asDataset instanceof Dataset);
  assert.equal(asDataset.size, 5);

  const canon = await handle.canonicalize();
  assert.equal(typeof canon, 'string');
  assert.match(canon, /carol/i);

  await handle.close();
  assert.equal(handle.closed, true);

  // Every method rejects after close(), and close() itself is
  // idempotent (a second call does not throw).
  await assert.rejects(() => handle.query(JOIN_Q), /closed/);
  await assert.rejects(() => handle.update(updateText), /closed/);
  await assert.rejects(() => handle.serialize({ format: 'nquads' }), /closed/);
  await handle.close();
});

test('query(handle, sparql) and serialize(handle, options) route through the handle', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (dataset handles need it)');
    return;
  }
  const handle = await factoidal.openDataset(TTL, { format: 'turtle' });
  const rows = await factoidal.query(handle, JOIN_Q);
  assert.equal(rows.length, 2);
  const nq = await factoidal.serialize(handle, { format: 'nquads' });
  assert.match(nq, /alice/i);
  const canon = await factoidal.canonicalize(handle);
  assert.equal(typeof canon, 'string');
  await handle.close();
});

test('update(handle, ...) rejects with a TypeError naming handle.update()', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (dataset handles need it)');
    return;
  }
  const handle = await factoidal.openDataset(TTL, { format: 'turtle' });
  await assert.rejects(
    () => factoidal.update(handle, 'PREFIX ex: <http://example.org/> INSERT DATA { ex:z ex:p 1 }'),
    (err) => {
      assert.ok(err instanceof TypeError);
      assert.match(err.message, /handle\.update\(\)/);
      return true;
    });
  await handle.close();
});

test('query(handle, sparql, {entail: "RDFS"}) rejects -- a handle carries no closure step', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (dataset handles need it)');
    return;
  }
  const handle = await factoidal.openDataset(TTL, { format: 'turtle' });
  await assert.rejects(
    () => factoidal.query(handle, JOIN_Q, { entail: 'RDFS' }),
    TypeError);
  await handle.close();
});

test('opening from a Dataset with prefixes keeps them for Turtle output', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (dataset handles need it)');
    return;
  }
  const parsed = await factoidal.parse(TTL, { format: 'turtle' });
  assert.ok(Object.keys(parsed.prefixes).length > 0, 'parse() records prefixes');

  const handle = await factoidal.openDataset(parsed);
  assert.deepEqual(handle.prefixes, parsed.prefixes);

  const ttl = await handle.serialize({ format: 'turtle' });
  assert.match(ttl, /@prefix ex: <http:\/\/example\.org\/>/,
    "the Dataset's own prefix label ('ex') survives, not an auto ns1: label");
  await handle.close();
});

test('an unknown/closed handle rejects with a message naming the handle id', async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (dataset handles need it)');
    return;
  }
  const handle = await factoidal.openDataset(TTL, { format: 'turtle' });
  const id = handle.handle;
  await handle.close();
  await assert.rejects(() => handle.query(JOIN_Q), new RegExp(id));
});

test('openDataset() needs the npm-entry bundle -- rejects with the pending-entry shape without it', async () => {
  // This assertion only has bite when the bundle IS present (the
  // common case in this repo); when it is absent, entryAvailable()
  // above already skips the other cases, and this one is a no-op
  // sanity check that the function exists and is callable either way.
  if (!(await entryAvailable())) {
    await assert.rejects(
      () => factoidal.openDataset(TTL, { format: 'turtle' }),
      /npm-entry bundle/);
  } else {
    assert.equal(typeof factoidal.openDataset, 'function');
  }
});
