// A bare string where a function takes an options object names the
// format (0.8.0): serialize(ds, 'turtle') is serialize(ds, {format:'turtle'}).
// Before, the string was read as an empty options object and
// serialize(ds, 'turtle') returned N-Quads with no error. Any other
// non-object value is a TypeError naming the function.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('../index.js');

async function entryAvailable() {
  try {
    return !!(await factoidal.capabilities()).entry;
  } catch (_) {
    return false;
  }
}

const NT = '<http://ex/s> <http://ex/p> "1.5"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n';

test("parse(text, 'ntriples') is parse(text, {format:'ntriples'})", async () => {
  const ds = await factoidal.parse(NT, 'ntriples');
  assert.equal(ds.size, 1);
  const same = await factoidal.parse(NT, { format: 'ntriples' });
  assert.equal(
    await factoidal.serialize(ds, 'nquads'),
    await factoidal.serialize(same, { format: 'nquads' }));
});

test("serialize(ds, 'turtle') is Turtle, not silent N-Quads", async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (Turtle serialization needs it)');
    return;
  }
  const ds = await factoidal.parse(NT, 'ntriples');
  const ttl = await factoidal.serialize(ds, 'turtle');
  assert.equal(ttl, await factoidal.serialize(ds, { format: 'turtle' }));
  assert.match(ttl, /@prefix/, 'Turtle output carries a @prefix directive');
  assert.match(ttl, /\b1\.5\b/, 'xsd:decimal prints as the bare shorthand');
  assert.doesNotMatch(ttl, /XMLSchema#decimal>/, 'no quoted-typed decimal');
});

test("openDataset(text, 'ntriples') and handle.serialize('turtle')", async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (dataset handles need it)');
    return;
  }
  const h = await factoidal.openDataset(NT, 'ntriples');
  try {
    assert.equal(h.size, 1);
    assert.match(await h.serialize('turtle'), /@prefix/);
    assert.equal(await h.serialize('nquads'), await h.serialize({ format: 'nquads' }));
  } finally {
    await h.close();
  }
});

test("update, canonicalize and query accept the bare format string", async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (UPDATE, canonicalize and query need it)');
    return;
  }
  const out = await factoidal.update(
    NT, 'INSERT DATA { <http://ex/s> <http://ex/q> <http://ex/o> }', 'ntriples');
  assert.equal(out.size, 2);
  assert.equal(
    await factoidal.canonicalize(NT, 'ntriples'),
    await factoidal.canonicalize(NT, { format: 'ntriples' }));
  const rows = await factoidal.query(NT, 'SELECT ?o WHERE { ?s ?p ?o }', 'ntriples');
  assert.equal(rows.length, 1);
});

test('a non-object, non-string options argument is a TypeError naming the function', async () => {
  const ds = await factoidal.parse(NT, 'ntriples');
  await assert.rejects(
    () => factoidal.serialize(ds, 42),
    /serialize: options must be an object or a format string/);
  await assert.rejects(() => factoidal.parse(NT, true), /parse: options must be/);
  await assert.rejects(() => factoidal.canonicalize(NT, 7), /canonicalize: options must be/);
});
