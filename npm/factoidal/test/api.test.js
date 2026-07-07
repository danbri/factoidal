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
const { parse, query, update, serialize, canonicalize, graphs,
  canonicalHash, shaclValidate, shexValidate, owlClosure, rmlMap,
  csvwToRdf, jsonldToRdf, jsonldFromRdf, didKeyResolve, xmlWellformed,
  xpathEval, rifEval, capabilities, Dataset,
  dataFactory: df } = factoidal;

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

test('graphs: enumerates named graphs from a parsed TriG document', async () => {
  const ds = await parse(
    '@prefix ex: <http://x/> . ' +
    'ex:g1 { ex:a ex:p "one" . } ' +
    'ex:g2 { ex:b ex:p "two" . } ' +
    'ex:c ex:p "default" .',
    { format: 'trig' });
  const gs = graphs(ds);
  assert.equal(gs.length, 2, 'default graph is excluded');
  const names = gs.map(([iri]) => iri).sort();
  assert.deepEqual(names, ['http://x/g1', 'http://x/g2']);
  const g1 = gs.find(([iri]) => iri === 'http://x/g1')[1];
  assert.ok(g1 instanceof Dataset);
  assert.equal(g1.size, 1);
  assert.equal([...g1][0].object.value, 'one');
});

test('canonicalHash: isomorphic graphs get identical hash under bnode relabeling',
  async (t) => {
    const caps = await capabilities();
    if (!caps.canonicalHash) {
      t.skip(`${PENDING} (or CLI bundle rebuild with --canonicalize)`);
      return;
    }
    const dsA = await parse(
      '@prefix ex: <http://x/> . ' +
      'ex:g { _:x ex:p _:y . _:y ex:p "leaf" . }',
      { format: 'trig' });
    const dsB = await parse(
      '@prefix ex: <http://x/> . ' +
      'ex:g { _:n1 ex:p _:n2 . _:n2 ex:p "leaf" . }',
      { format: 'trig' });
    const [, gA] = graphs(dsA)[0];
    const [, gB] = graphs(dsB)[0];
    const hashA = await canonicalHash(gA);
    const hashB = await canonicalHash(gB);
    assert.equal(hashA, hashB);
    assert.ok(/_:c14n/.test(hashA), 'hash is canonical c14n-labeled N-Quads');
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

test('parse: jsonld (expanded/inline-context form) via the npm-entry ABI',
  async (t) => {
    const caps = await capabilities();
    if (!caps.entry) {
      t.skip(`${PENDING} (parseToDatasetJson's JSON-LD dispatch needs the entry bundle)`);
      return;
    }
    const jsonld = JSON.stringify({
      '@context': { foaf: 'http://xmlns.com/foaf/0.1/', name: 'foaf:name' },
      '@id': 'http://example.org/alice',
      name: 'Alice',
    });
    const ds = await parse(jsonld, { format: 'jsonld' });
    assert.equal(ds.size, 1);
    const [q] = [...ds];
    assert.equal(q.subject.value, 'http://example.org/alice');
    assert.equal(q.predicate.value, 'http://xmlns.com/foaf/0.1/name');
    assert.equal(q.object.value, 'Alice');
  });

test('jsonldToRdf: parses JSON-LD with an explicit base option', async (t) => {
  const caps = await capabilities();
  if (!caps.jsonld) { t.skip(PENDING); return; }

  const jsonld = JSON.stringify({
    '@context': { foaf: 'http://xmlns.com/foaf/0.1/', name: 'foaf:name' },
    '@id': 'alice',
    name: 'Alice',
  });
  const ds = await jsonldToRdf(jsonld, { base: 'http://example.org/' });
  assert.equal(ds.size, 1);
  assert.equal([...ds][0].subject.value, 'http://example.org/alice');
});

test('shaclValidate: SHACL Core validation returns conforms + a report Dataset',
  async (t) => {
    const caps = await capabilities();
    if (!caps.shacl) { t.skip(PENDING); return; }

    const shapes = `
      @prefix sh:   <http://www.w3.org/ns/shacl#> .
      @prefix foaf: <http://xmlns.com/foaf/0.1/> .
      @prefix ex:   <http://example.org/> .
      ex:PersonShape a sh:NodeShape ;
        sh:targetClass foaf:Person ;
        sh:property [ sh:path foaf:name ; sh:minCount 1 ] .
    `;
    const ok = await shaclValidate(TTL, shapes);
    assert.equal(ok.conforms, true);
    assert.ok(ok.report instanceof Dataset);

    const noName = `
      @prefix foaf: <http://xmlns.com/foaf/0.1/> .
      @prefix ex:   <http://example.org/> .
      ex:dave a foaf:Person .
    `;
    const bad = await shaclValidate(noName, shapes);
    assert.equal(bad.conforms, false);
  });

test('shexValidate: ShEx validation of one focus node against one shape',
  async (t) => {
    const caps = await capabilities();
    if (!caps.shex) { t.skip(PENDING); return; }

    const schema = JSON.stringify({
      type: 'Schema',
      shapes: [{
        type: 'ShapeDecl', id: 'http://example.org/PersonShape',
        shapeExpr: {
          type: 'Shape',
          expression: {
            type: 'TripleConstraint',
            predicate: 'http://xmlns.com/foaf/0.1/name',
            valueExpr: { type: 'NodeConstraint', nodeKind: 'literal' },
          },
        },
      }],
    });
    const verdict = await shexValidate(
      TTL, schema, 'http://example.org/alice', 'http://example.org/PersonShape');
    assert.equal(verdict, true);

    // Also accepts RDF/JS terms for focus/shape.
    const viaTerm = await shexValidate(
      TTL, schema, df.namedNode('http://example.org/alice'),
      df.namedNode('http://example.org/PersonShape'));
    assert.equal(viaTerm, true);
  });

test('owlClosure: RDFS closure materializes rdfs:subClassOf inference',
  async (t) => {
    const caps = await capabilities();
    if (!caps.owlClosure) { t.skip(PENDING); return; }

    const data = `
      @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
      @prefix ex:   <http://example.org/> .
      ex:Hotel rdfs:subClassOf ex:Place .
      ex:motel6 a ex:Hotel .
    `;
    const before = await parse(data);
    const closure = await owlClosure(data, 'RDFS');
    assert.ok(closure instanceof Dataset);
    assert.ok(closure.size > before.size);
    const rows = [...closure].filter((q) =>
      q.subject.value === 'http://example.org/motel6' &&
      q.predicate.value === 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type' &&
      q.object.value === 'http://example.org/Place');
    assert.equal(rows.length, 1, 'motel6 a ex:Place is inferred via subClassOf');
  });

test('rmlMap: evaluates an RML mapping graph against JSON source data',
  async (t) => {
    const caps = await capabilities();
    if (!caps.rml) { t.skip(PENDING); return; }

    const mapping = `
      @prefix rml: <http://w3id.org/rml/> .
      @prefix foaf: <http://xmlns.com/foaf/0.1/> .
      @prefix ex:   <http://example.org/> .
      ex:TM a rml:TriplesMap ;
        rml:logicalSource [ a rml:LogicalSource ;
          rml:iterator "$.people[*]" ;
          rml:referenceFormulation rml:JSONPath ;
          rml:source [ a rml:RelativePathSource ; rml:root rml:MappingDirectory ; rml:path "x" ] ] ;
        rml:subjectMap [ rml:template "http://example.org/person/{$.id}" ] ;
        rml:predicateObjectMap [ rml:predicate foaf:name ; rml:objectMap [ rml:reference "$.name" ] ] .
    `;
    const source = JSON.stringify({
      people: [{ id: '1', name: 'Alice' }, { id: '2', name: 'Bob' }],
    });
    const ds = await rmlMap(mapping, source, 'json');
    assert.ok(ds instanceof Dataset);
    assert.equal(ds.size, 2);
    assert.equal(
      ds.match(df.namedNode('http://example.org/person/1'),
        df.namedNode('http://xmlns.com/foaf/0.1/name')).size,
      1);
  });

test('csvwToRdf: converts a vendored W3C CSVW fixture (minimal mode)',
  async (t) => {
    const caps = await capabilities();
    if (!caps.csvw) { t.skip(PENDING); return; }

    // Real vendored fixtures from the W3C CSVW test suite (test027's
    // metadata + the shared tree-ops.csv table it describes) — not a
    // synthetic imitation (iron rule #6).
    const fs = require('node:fs');
    const path = require('node:path');
    const dir = path.join(__dirname, '..', '..', '..',
      'third_party', 'testing', 'csvw', 'tests');
    const csv = fs.readFileSync(path.join(dir, 'tree-ops.csv'), 'utf8');
    const meta = fs.readFileSync(
      path.join(dir, 'test027-user-metadata.json'), 'utf8');

    const ds = await csvwToRdf(csv, meta,
      { mode: 'minimal', base: 'http://example.org/' });
    assert.ok(ds instanceof Dataset);
    // 2 data rows x 5 columns, bare cell triples only in minimal mode.
    assert.equal(ds.size, 10);
    // The schema-level aboutUrl "#gid-{GID}" resolves against the
    // metadata's own url ("tree-ops.csv"), itself resolved against base.
    const subj = df.namedNode('http://example.org/tree-ops.csv#gid-1');
    assert.equal(ds.match(subj).size, 5);
    const street = ds.match(subj,
      df.namedNode('http://example.org/tree-ops.csv#on_street'));
    assert.equal(street.size, 1);
    assert.equal([...street][0].object.value, 'ADDISON AV');
  });

test('csvwToRdf: standard mode emits the csvw:TableGroup wrapper; no metadata infers from header',
  async (t) => {
    const caps = await capabilities();
    if (!caps.csvw) { t.skip(PENDING); return; }

    const fs = require('node:fs');
    const path = require('node:path');
    const dir = path.join(__dirname, '..', '..', '..',
      'third_party', 'testing', 'csvw', 'tests');
    const csv = fs.readFileSync(path.join(dir, 'tree-ops.csv'), 'utf8');

    // '' metadata: schema inferred from the CSV's own header row
    // (csv2rdf's embedded-metadata case, the suite's test028 shape).
    const ds = await csvwToRdf(csv, '',
      { base: 'http://example.org/', url: 'tree-ops.csv' });
    assert.ok(ds instanceof Dataset);
    const groupType = [...ds].filter((q) =>
      q.predicate.value === 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type' &&
      q.object.value === 'http://www.w3.org/ns/csvw#TableGroup');
    assert.equal(groupType.length, 1, 'standard mode wraps in a csvw:TableGroup');
    const rownums = [...ds].filter((q) =>
      q.predicate.value === 'http://www.w3.org/ns/csvw#rownum');
    assert.equal(rownums.length, 2, 'one csvw:rownum per data row');
  });

test('rifEval: RIF Core saturation materializes derived triples',
  async (t) => {
    const caps = await capabilities();
    if (!caps.rif) { t.skip(PENDING); return; }

    const data = '@prefix foaf: <http://xmlns.com/foaf/0.1/> . ' +
      '@prefix ex: <http://example.org/> . ex:alice foaf:knows ex:bob .';
    // "?x foaf:knows ?y -> ?y foaf:knows ?x", RIF-Frame shape (see
    // fn.test.js's rif() test for provenance of this pattern).
    const rules = `<?xml version="1.0" encoding="UTF-8"?>
<Document xmlns="http://www.w3.org/2007/rif#">
  <payload>
    <Group>
      <sentence>
        <Forall>
          <declare><Var>x</Var></declare>
          <declare><Var>y</Var></declare>
          <formula>
            <Implies>
              <if>
                <Frame>
                  <object><Var>x</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const>
                    <Var>y</Var>
                  </slot>
                </Frame>
              </if>
              <then>
                <Frame>
                  <object><Var>y</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const>
                    <Var>x</Var>
                  </slot>
                </Frame>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
    </Group>
  </payload>
</Document>`;
    const saturated = await rifEval(data, rules);
    assert.ok(saturated instanceof Dataset);
    assert.equal(
      saturated.match(df.namedNode('http://example.org/bob'),
        df.namedNode('http://xmlns.com/foaf/0.1/knows'),
        df.namedNode('http://example.org/alice')).size,
      1, 'the symmetric rule derives bob foaf:knows alice');
  });

test('capabilities: shacl/shex/owlClosure/rml/jsonld/rif fields are present', async () => {
  const caps = await capabilities();
  for (const key of ['shacl', 'shex', 'owlClosure', 'rml', 'jsonld', 'rif',
                     'jsonldFromRdf', 'didKey', 'xml', 'xpath']) {
    assert.equal(typeof caps[key], 'boolean', `capabilities().${key} is a boolean`);
  }
});

test('xmlWellformed: accepts well-formed, rejects malformed', async () => {
  assert.equal(await xmlWellformed('<a><b/></a>'), true);
  assert.equal(await xmlWellformed('<a><b></a>'), false);
});

test('xpathEval: XPath 1.0 over an XML document', async () => {
  const r = await xpathEval('<r><a>1</a><a>2</a></r>', 'count(/r/a)');
  assert.equal(r.resultType, 'number');
  assert.equal(Number(r.value), 2);
});

test('didKeyResolve: Ed25519 did:key resolves to a DID Document', async () => {
  const doc = await didKeyResolve(
    'did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK');
  assert.ok(doc instanceof Dataset);
  assert.ok(doc.size >= 1, 'DID Document has at least one triple');
});

test('jsonldFromRdf: N-Quads serialize to expanded JSON-LD (reverse of jsonldToRdf)', async () => {
  const jld = await jsonldFromRdf('<http://ex/s> <http://ex/p> "o" .');
  assert.ok(Array.isArray(jld), 'expanded JSON-LD is an array of node objects');
  assert.equal(jld.length, 1);
});

test('version matches package.json', () => {
  assert.equal(factoidal.version, require('../package.json').version);
});
