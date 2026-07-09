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
