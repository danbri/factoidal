// Pins the two observable facts about parse() output order documented
// in README.md's "Blank nodes, labels and statement order" section
// (https://github.com/danbri/factoidal/issues/683):
//
//   1. An anonymous blank node's `_anonN` label suffix reflects the
//      DOCUMENT (parse-time) order its `[]` was encountered in --
//      Parser.Turtle.fst's `fresh_bnode`, N counting from 0.
//   2. The returned Dataset's quad order does NOT reflect document
//      order at all: parseToDatasetJson answers
//      RDF_Canonical.canonical_nquads, which SORTS lines
//      (RDF.Canonical.fst's `canonical_nquads`), before
//      Dataset.fromNQuads ever sees the text -- there is no
//      "insertion order" left to preserve by the time a caller gets
//      the Dataset back.
//
// A change to either fact (the label numbering scheme, or dropping
// the sort) is a deliberate, reviewed decision, not an accidental
// drift -- this test turns such a change red so it gets one. See the
// issue above before touching Parser.Turtle.fst's fresh_bnode,
// RDF.Canonical.fst's canonical_nquads, or lib/api.js's
// freshBnodePrefix.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { parse, dataFactory: df } = require('..');

// Textual/document order is charlie, alice, bravo -- deliberately NOT
// alphabetical, so "labels follow document order" and "labels follow
// sorted order" would predict DIFFERENT _anonN <-> subject pairings.
// If a future change accidentally sorted before labelling, this test
// would catch it (a "labels follow source order" assertion built on
// already-alphabetical names could pass by coincidence either way).
const TTL = `
  @prefix ex: <http://example.org/> .
  ex:charlie ex:p [ ex:q "c" ] .
  ex:alice   ex:p [ ex:q "a" ] .
  ex:bravo   ex:p [ ex:q "b" ] .
`;

function bnodeObjectOf(ds, localName) {
  const subj = df.namedNode('http://example.org/' + localName);
  const pred = df.namedNode('http://example.org/p');
  const quads = [...ds.match(subj, pred)];
  assert.equal(quads.length, 1, `exactly one ex:p triple for ex:${localName}`);
  assert.equal(quads[0].object.termType, 'BlankNode',
    `ex:${localName}'s ex:p object is the blank node from its [ ex:q ... ]`);
  return quads[0].object.value;
}

test('anonymous blank-node label suffixes follow document order, not sorted/subject order', async () => {
  const ds = await parse(TTL);

  const charlieBnode = bnodeObjectOf(ds, 'charlie'); // 1st [] in the document
  const aliceBnode = bnodeObjectOf(ds, 'alice');      // 2nd
  const bravoBnode = bnodeObjectOf(ds, 'bravo');      // 3rd

  assert.ok(charlieBnode.endsWith('_anon0'),
    `ex:charlie's [] is first in the document, expected a label ending _anon0, got ${charlieBnode}`);
  assert.ok(aliceBnode.endsWith('_anon1'),
    `ex:alice's [] is second in the document, expected a label ending _anon1, got ${aliceBnode}`);
  assert.ok(bravoBnode.endsWith('_anon2'),
    `ex:bravo's [] is third in the document, expected a label ending _anon2, got ${bravoBnode}`);

  // All three came from ONE parse() call (one document): same
  // p<k>_d<n>_ scope prefix on every label, per README.md's
  // "Blank nodes, labels and statement order" section.
  const prefix = charlieBnode.slice(0, charlieBnode.indexOf('_anon'));
  assert.equal(aliceBnode.slice(0, aliceBnode.indexOf('_anon')), prefix,
    'all three blank nodes share one per-document scope prefix');
  assert.equal(bravoBnode.slice(0, bravoBnode.indexOf('_anon')), prefix,
    'all three blank nodes share one per-document scope prefix');
});

test('toNQuads() lines are in sorted (canonical) order, not document order', async () => {
  const ds = await parse(TTL);

  const lines = ds.toNQuads().trim().split('\n').filter((l) => l.length > 0);
  assert.equal(lines.length, 6, 'three ex:p triples + three ex:q triples');

  const sorted = [...lines].sort();
  assert.deepEqual(lines, sorted, 'toNQuads() output is already lexicographically sorted');

  // Not a vacuous check: 'ex:alice' (whose [] was SECOND in the
  // document, _anon1) sorts before 'ex:charlie' (FIRST in the
  // document, _anon0) -- proving the output order is sorted-by-content,
  // not document/insertion order, which would have put charlie's line
  // first.
  const aliceLineIndex = lines.findIndex((l) => l.includes('http://example.org/alice'));
  const charlieLineIndex = lines.findIndex((l) => l.includes('http://example.org/charlie'));
  assert.ok(aliceLineIndex >= 0 && charlieLineIndex >= 0);
  assert.ok(aliceLineIndex < charlieLineIndex,
    "alice's triple (document position 2) sorts before charlie's (document position 1): " +
    'output order is sorted, not preserved document order');
});
