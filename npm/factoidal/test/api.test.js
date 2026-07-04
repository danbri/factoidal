// Unit tests for the typed public API (js_of_ocaml engine).
//
// Tests that only need the existing CLI bundle run unconditionally.
// Tests that need the npm-entry ABI bundle (CONSTRUCT, UPDATE) or a
// CLI bundle built after `factoidal canonicalize` landed
// (canonicalization) probe capabilities() and skip with reason
// "pending npm-entry build" until the main build cycle produces the
// new artifacts.

'use strict';

require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('..');
const { parse, query, update, serialize, canonicalize, capabilities,
  Dataset, dataFactory: df } = factoidal;

const PENDING = 'pending npm-entry build';

const TTL = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:age 30 ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob" .
  ex:carol foaf:name "Carol"@en .
`;

test('parse: turtle smoke', async () => {
  const ds = await parse(TTL);
  assert.ok(ds instanceof Dataset);
  assert.equal(ds.size, 7);
  const names = ds.match(null, df.namedNode('http://xmlns.com/foaf/0.1/name'));
  assert.equal(names.size, 3);
});

test('parse: ntriples smoke', async () => {
  const ds = await parse(
    '<http://x/a> <http://x/p> "v" .\n<http://x/a> <http://x/p> _:b .\n',
    { format: 'ntriples' });
  assert.equal(ds.size, 2);
});

test('parse: nquads smoke (named graph preserved)', async () => {
  const ds = await parse(
    '<http://x/a> <http://x/p> "v" <http://x/g> .\n' +
    '<http://x/a> <http://x/p> "w" .\n',
    { format: 'nquads' });
  assert.equal(ds.size, 2);
  assert.equal(ds.match(null, null, null, df.namedNode('http://x/g')).size, 1);
  assert.equal(ds.match(null, null, null, df.defaultGraph()).size, 1);
});

test('parse: trig smoke (named graph preserved)', async () => {
  const ds = await parse(
    '@prefix ex: <http://x/> . ex:g { ex:a ex:p "v" . }',
    { format: 'trig' });
  assert.equal(ds.size, 1);
  assert.equal(ds.match(null, null, null, df.namedNode('http://x/g')).size, 1);
});

test('parse: rdfxml smoke', async () => {
  const ds = await parse(
    '<?xml version="1.0"?>\n' +
    '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" ' +
    'xmlns:ex="http://x/">' +
    '<rdf:Description rdf:about="http://x/a"><ex:p>val</ex:p>' +
    '</rdf:Description></rdf:RDF>',
    { format: 'rdfxml' });
  assert.equal(ds.size, 1);
  assert.equal([...ds][0].object.value, 'val');
});

test('parse: baseIRI resolves relative IRIs', async () => {
  const ds = await parse('<a> <http://x/p> <b> .', {
    format: 'turtle',
    baseIRI: 'http://base.example/dir/',
  });
  assert.equal(ds.size, 1);
  assert.equal([...ds][0].subject.value, 'http://base.example/dir/a');
  assert.equal([...ds][0].object.value, 'http://base.example/dir/b');
});

test('parse: blank-node labels from separate parses stay distinct', async () => {
  const doc = '_:b1 <http://x/p> "v" .\n';
  const d1 = await parse(doc, { format: 'ntriples' });
  const d2 = await parse(doc, { format: 'ntriples' });
  const b1 = [...d1][0].subject;
  const b2 = [...d2][0].subject;
  assert.equal(b1.termType, 'BlankNode');
  assert.ok(!b1.equals(b2),
    'same source label in two documents must not join');
});

test('query: SELECT returns Bindings[] of RDF/JS terms', async () => {
  const rows = await query(TTL, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?person ?name WHERE { ?person foaf:name ?name }
  `);
  assert.ok(Array.isArray(rows));
  assert.equal(rows.length, 3);
  for (const row of rows) {
    assert.ok(row instanceof Map, 'each solution is a Map');
  }
  const byName = new Map(rows.map((r) => [r.get('name').value, r]));
  assert.deepEqual([...byName.keys()].sort(), ['Alice', 'Bob', 'Carol']);

  const alice = byName.get('Alice');
  assert.equal(alice.get('person').termType, 'NamedNode');
  assert.equal(alice.get('person').value, 'http://example.org/alice');
  const carolName = byName.get('Carol').get('name');
  assert.equal(carolName.termType, 'Literal');
  assert.equal(carolName.language, 'en');
});

test('query: typed literal binding carries its datatype', async () => {
  const rows = await query(TTL, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?age WHERE { ?p foaf:age ?age }
  `);
  assert.equal(rows.length, 1);
  const age = rows[0].get('age');
  assert.equal(age.termType, 'Literal');
  assert.equal(age.value, '30');
  assert.equal(age.datatype.value, 'http://www.w3.org/2001/XMLSchema#integer');
});

test('query: accepts a Dataset input', async () => {
  const ds = await parse(TTL);
  const rows = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?n WHERE { ?p foaf:name ?n }
  `);
  assert.equal(rows.length, 3);
});

test('query: ASK returns a boolean', async () => {
  const yes = await query(TTL, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    PREFIX ex:   <http://example.org/>
    ASK { ex:alice foaf:knows ex:bob }
  `);
  assert.equal(typeof yes, 'boolean');
  assert.equal(yes, true);
  const no = await query(TTL, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    PREFIX ex:   <http://example.org/>
    ASK { ex:bob foaf:knows ex:alice }
  `);
  assert.equal(no, false);
});

test('query: multiple documents load as separate graphs', async () => {
  const rows = await query(
    [
      { text: '<http://x/a> <http://x/p> "one" .', format: 'ntriples' },
      { text: '<http://x/b> <http://x/p> "two" .', format: 'ntriples' },
    ],
    'SELECT ?s WHERE { ?s <http://x/p> ?o }');
  assert.equal(rows.length, 2);
});

test('query: entail RDFS infers subclass instances', async () => {
  const data = `
    @prefix schema: <http://schema.org/> .
    @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
    @prefix ex:     <http://example.org/> .
    schema:Place a rdfs:Class .
    schema:Hotel rdfs:subClassOf schema:Place .
    ex:motel6 a schema:Hotel .
  `;
  const q = 'PREFIX schema: <http://schema.org/> ' +
    'SELECT ?s WHERE { ?s a schema:Place }';
  const none = await query(data, q);
  const rdfs = await query(data, q, { entail: 'RDFS' });
  assert.equal(none.length, 0);
  assert.ok(rdfs.length >= 1);
});

test('query: malformed query rejects with diagnostics', async () => {
  await assert.rejects(
    () => query(TTL, 'SELECT WITHOUT WHERE BUT MALFORMED'),
    (e) => e instanceof Error && /parse error|failed/i.test(e.message));
});

test('serialize: engine round-trip is stable (nquads)', async () => {
  const ds = await parse(TTL);
  const once = await serialize(ds);
  assert.equal(typeof once, 'string');
  assert.ok(once.includes('<http://example.org/alice>'));
  const again = await serialize(Dataset.fromNQuads(once));
  assert.equal(again, once, 'serialize is a fixpoint on its own output');
  assert.equal(Dataset.fromNQuads(once).size, ds.size);
});

test('serialize: ntriples output', async () => {
  const nt = await serialize('<http://x/a> <http://x/p> "v" .', {
    inputFormat: 'ntriples',
    format: 'ntriples',
  });
  assert.equal(nt.trim(), '<http://x/a> <http://x/p> "v" .');
});

test('canonicalize: isomorphic datasets get identical canonical N-Quads',
  async (t) => {
    const caps = await capabilities();
    if (!caps.canonicalize) {
      t.skip(`${PENDING} (or CLI bundle rebuild with --canonicalize)`);
      return;
    }
    // Same graph, different blank-node labels (bnode-rename stability).
    const docA = '_:x <http://x/p> _:y .\n_:y <http://x/p> "leaf" .\n';
    const docB = '_:n1 <http://x/p> _:n2 .\n_:n2 <http://x/p> "leaf" .\n';
    const canonA = await canonicalize(docA, { format: 'nquads' });
    const canonB = await canonicalize(docB, { format: 'nquads' });
    assert.equal(canonA, canonB);
    assert.ok(/_:c14n/.test(canonA), 'labels are canonical c14n labels');

    // Parsing relabels bnodes per document; canonicalization must
    // erase that difference too.
    const d1 = await parse(docA, { format: 'nquads' });
    const d2 = await parse(docA, { format: 'nquads' });
    assert.equal(await canonicalize(d1), await canonicalize(d2));
  });

test('query: CONSTRUCT returns a Dataset', async (t) => {
  const caps = await capabilities();
  if (!caps.construct) {
    t.skip(PENDING);
    return;
  }
  const out = await query(TTL, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    CONSTRUCT { ?p <http://x/hasName> ?n } WHERE { ?p foaf:name ?n }
  `);
  assert.ok(out instanceof Dataset);
  assert.equal(out.size, 3);
  for (const q of out) {
    assert.equal(q.predicate.value, 'http://x/hasName');
  }
});

test('update: INSERT DATA adds quads', async (t) => {
  const caps = await capabilities();
  if (!caps.update) {
    t.skip(PENDING);
    return;
  }
  const ds = await parse('<http://x/a> <http://x/p> "v" .', {
    format: 'ntriples' });
  const out = await update(ds,
    'INSERT DATA { <http://x/b> <http://x/p> "w" }');
  assert.ok(out instanceof Dataset);
  assert.equal(out.size, 2);
});

test('update: without npm-entry bundle rejects with pending message',
  async (t) => {
    const caps = await capabilities();
    if (caps.update) {
      t.skip('npm-entry bundle present — pending-message path not reachable');
      return;
    }
    await assert.rejects(
      () => update('<http://x/a> <http://x/p> "v" .',
        'INSERT DATA { <http://x/b> <http://x/p> "w" }',
        { format: 'ntriples' }),
      (e) => e.message.includes(PENDING));
  });

test('version matches package.json', () => {
  assert.equal(factoidal.version, require('../package.json').version);
});
