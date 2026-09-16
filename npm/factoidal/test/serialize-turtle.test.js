// serialize(data, {format:'turtle'}) — the newly-exposed Turtle output
// path (entry_jsoo.ml's serializeTurtle export was shipped in the ABI
// but the typed serialize() previously rejected 'turtle' as "pending").
// This pins the wired path. Needs the npm-entry bundle; no-op-skips
// otherwise.

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

test("serialize(..., {format:'turtle'}) emits prefix-compacted Turtle", async (t) => {
  if (!(await entryAvailable())) {
    t.skip('npm-entry bundle not present (Turtle serialization needs it)');
    return;
  }
  const nt = '<http://ex/s> <http://ex/p> <http://ex/o> .\n';
  const ttl = await factoidal.serialize(nt, { format: 'turtle', inputFormat: 'ntriples' });
  assert.equal(typeof ttl, 'string');
  assert.match(ttl, /@prefix/, 'Turtle output carries a @prefix directive');
  assert.match(ttl, /:s\b/, 'subject is prefix-compacted');
  // 'ttl' is an accepted alias for 'turtle'.
  const ttl2 = await factoidal.serialize(nt, { format: 'ttl', inputFormat: 'ntriples' });
  assert.match(ttl2, /@prefix/);
});

test('serialize rejects an unknown output format', async () => {
  await assert.rejects(
    () => factoidal.serialize('<a> <b> <c> .', { format: 'rdfxml', inputFormat: 'ntriples' }),
    /format must be/);
});

// ---------------------------------------------------------------------
// serialize(..., {format:'turtle', prefixes, literalShorthand}) --
// issue #681.
// ---------------------------------------------------------------------

const NT_TWO_S = '<http://ex/a> <http://ex/p> <http://ex/o> .\n' +
  '<http://ex/b> <http://ex/p> <http://ex/o> .\n';

test('serialize turtle: caller prefixes appear as given', async (t) => {
  if (!(await entryAvailable())) { t.skip('npm-entry bundle not present'); return; }
  const ttl = await factoidal.serialize(NT_TWO_S, {
    format: 'turtle', inputFormat: 'ntriples',
    prefixes: { ex: 'http://ex/' },
  });
  assert.match(ttl, /@prefix ex: <http:\/\/ex\/>/);
  assert.match(ttl, /\bex:a\b/);
  assert.match(ttl, /\bex:b\b/);
  assert.ok(!/ns1:/.test(ttl), 'no auto-generated label when a caller prefix already covers the namespace');
});

test('serialize turtle: unused caller prefixes are not emitted', async (t) => {
  if (!(await entryAvailable())) { t.skip('npm-entry bundle not present'); return; }
  const ttl = await factoidal.serialize(NT_TWO_S, {
    format: 'turtle', inputFormat: 'ntriples',
    prefixes: { ex: 'http://ex/', unused: 'http://unused.example/' },
  });
  assert.ok(!ttl.includes('unused:'), 'an unused caller namespace is dropped, not emitted');
  assert.ok(!ttl.includes('unused.example'));
});

test('serialize turtle: auto ns1: labels skip caller labels already in use', async (t) => {
  if (!(await entryAvailable())) { t.skip('npm-entry bundle not present'); return; }
  // A second, unprefixed namespace still needs an auto label; the
  // engine must not reuse 'ex' (the caller's own label) for it.
  const nt = '<http://ex/a> <http://other/p> <http://other/o> .\n';
  const ttl = await factoidal.serialize(nt, {
    format: 'turtle', inputFormat: 'ntriples',
    prefixes: { ex: 'http://ex/' },
  });
  assert.match(ttl, /@prefix ex: <http:\/\/ex\/>/);
  assert.match(ttl, /@prefix ns1: <http:\/\/other\/>/,
    'the auto label for the second namespace must not collide with the caller label');
});

test('serialize turtle: literal shorthand is on by default (220.0, true print bare)', async (t) => {
  if (!(await entryAvailable())) { t.skip('npm-entry bundle not present'); return; }
  const nt = '<http://ex/s> <http://ex/p> "220.0"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n' +
    '<http://ex/s> <http://ex/p> "true"^^<http://www.w3.org/2001/XMLSchema#boolean> .\n';
  const ttl = await factoidal.serialize(nt, { format: 'turtle', inputFormat: 'ntriples' });
  assert.match(ttl, /\bp>?\s*220\.0\b|\s220\.0[\s,.]/, 'the decimal literal prints bare');
  assert.match(ttl, /\btrue\b(?!"?\^\^)/, 'the boolean literal prints bare');
  assert.ok(!ttl.includes('^^'), 'neither literal carries an explicit datatype IRI');
});

test('serialize turtle: literalShorthand:false turns off the bare-literal printing', async (t) => {
  if (!(await entryAvailable())) { t.skip('npm-entry bundle not present'); return; }
  const nt = '<http://ex/s> <http://ex/p> "220.0"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n' +
    '<http://ex/s> <http://ex/p> "true"^^<http://www.w3.org/2001/XMLSchema#boolean> .\n';
  const ttl = await factoidal.serialize(nt, {
    format: 'turtle', inputFormat: 'ntriples', literalShorthand: false,
  });
  assert.match(ttl, /"220\.0"\^\^xsd:decimal/);
  assert.match(ttl, /"true"\^\^xsd:boolean/);
});

test('serialize turtle: parse-then-serialize keeps the source prefixes', async (t) => {
  if (!(await entryAvailable())) { t.skip('npm-entry bundle not present'); return; }
  const ds = await factoidal.parse(
    '@prefix ex: <http://ex/> .\n@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n' +
    'ex:s foaf:knows ex:o .\n', { format: 'turtle' });
  assert.deepEqual(ds.prefixes, { ex: 'http://ex/', foaf: 'http://xmlns.com/foaf/0.1/' });
  const ttl = await factoidal.serialize(ds, { format: 'turtle' });
  assert.match(ttl, /@prefix ex: <http:\/\/ex\/>/);
  assert.match(ttl, /@prefix foaf: <http:\/\/xmlns\.com\/foaf\/0\.1\/>/);
  assert.match(ttl, /\bex:s\b/);
  assert.match(ttl, /\bfoaf:knows\b/);
});
