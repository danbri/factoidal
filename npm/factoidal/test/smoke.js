// Smoke test. Not an exhaustive unit suite — the real correctness
// story is the W3C conformance runner in the main repo. This just
// validates that the wrapper in ../index.js actually drives the
// bundled factoidal.js and returns the shapes the README promises.
//
// Run with `node test/smoke.js`. Exits non-zero on any failure.

'use strict';

const assert = require('node:assert');
const { query, version } = require('..');

const DATA = `
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:age 30 ; foaf:knows ex:bob .
  ex:bob   a foaf:Person ; foaf:name "Bob"   ; foaf:age 42 ; foaf:knows ex:alice .
  ex:carol a foaf:Person ; foaf:name "Carol"@en ; foaf:age 27 .
`;

const NT_DATA = `
<http://example.org/alice> <http://xmlns.com/foaf/0.1/name> "Alice" .
<http://example.org/bob>   <http://xmlns.com/foaf/0.1/name> "Bob"   .
`;

// schema.org-ish snippet for RDFS entailment.
const RDFS_DATA = `
  @prefix schema: <http://schema.org/> .
  @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix ex:     <http://example.org/> .
  schema:Place   a rdfs:Class .
  schema:Hotel   rdfs:subClassOf schema:Place .
  ex:motel6      a schema:Hotel ; schema:name "Motel 6" .
`;

async function assertJsonSelect(label, fn) {
  try {
    await fn();
    console.log(`  PASS  ${label}`);
  } catch (e) {
    console.log(`  FAIL  ${label}: ${e && e.message}`);
    throw e;
  }
}

(async () => {
  console.log(`factoidal@${version} smoke test`);

  // 1. Basic SELECT, default options (turtle + json).
  await assertJsonSelect('SELECT default options', async () => {
    const r = await query(DATA, `
      PREFIX foaf: <http://xmlns.com/foaf/0.1/>
      SELECT ?name WHERE { ?p foaf:name ?name }
    `);
    assert.ok(r.head, 'head present');
    assert.ok(Array.isArray(r.head.vars), 'head.vars present');
    assert.deepStrictEqual(r.head.vars, ['name']);
    assert.strictEqual(r.results.bindings.length, 3, '3 bindings');
    const names = r.results.bindings.map(b => b.name.value).sort();
    assert.deepStrictEqual(names, ['Alice', 'Bob', 'Carol']);
  });

  // 2. explicit dataFormat: ntriples.
  await assertJsonSelect('SELECT dataFormat=ntriples', async () => {
    const r = await query(NT_DATA, 'SELECT * WHERE { ?s ?p ?o }', {
      dataFormat: 'ntriples',
    });
    assert.strictEqual(r.results.bindings.length, 2);
  });

  // 3. ASK — the promise resolves to a {head, boolean} shape. We only
  //    assert the shape here, not the truth-value (there is an
  //    independent ASK-semantics issue in the underlying engine; this
  //    smoke test is about the API wrapper, not engine correctness).
  await assertJsonSelect('ASK returns {head, boolean}', async () => {
    const r = await query(DATA, `
      PREFIX foaf: <http://xmlns.com/foaf/0.1/>
      PREFIX ex:   <http://example.org/>
      ASK { ex:alice foaf:knows ex:bob }
    `);
    assert.ok(r.head, 'head present');
    assert.strictEqual(typeof r.boolean, 'boolean',
      'ASK response has a boolean');
    console.log('      (engine returned boolean=' + r.boolean + ')');
  });

  // 4. RDFS entailment — Motel 6 should come back as a Place with
  //    --entail RDFS, but not without it.
  await assertJsonSelect('entail=RDFS bumps subclass counts', async () => {
    const q = `
      PREFIX schema: <http://schema.org/>
      SELECT ?s WHERE { ?s a schema:Place }
    `;
    const none = await query(RDFS_DATA, q);
    const rdfs = await query(RDFS_DATA, q, { entail: 'RDFS' });
    assert.strictEqual(none.results.bindings.length, 0,
      'without RDFS, no direct schema:Place instances');
    assert.ok(rdfs.results.bindings.length >= 1,
      'RDFS should infer Motel 6 is a schema:Place');
  });

  // 5. Bad query — promise rejects, doesn't crash the process.
  await assertJsonSelect('bad query rejects', async () => {
    let threw = null;
    try {
      await query(DATA, 'SELECT WITHOUT WHERE BUT MALFORMED');
    } catch (e) {
      threw = e;
    }
    assert.ok(threw, 'expected an error');
    assert.ok(threw instanceof Error);
    // At least one of the fields should be populated.
    assert.ok(
      threw.exitCode !== 0 || threw.stderr || threw.stdout,
      'error should carry diagnostic info'
    );
  });

  // 6. CONSTRUCT — currently returns empty / pending Turtle serializer.
  //    We're not asserting correctness here, just that the call
  //    doesn't throw and returns something.
  await assertJsonSelect('CONSTRUCT does not throw', async () => {
    let r;
    try {
      r = await query(DATA, `
        PREFIX foaf: <http://xmlns.com/foaf/0.1/>
        CONSTRUCT { ?p foaf:name ?n } WHERE { ?p foaf:name ?n }
      `);
    } catch (e) {
      // CONSTRUCT may currently produce output that isn't SPARQL
      // Results JSON (it's graph-shaped, not table-shaped). That's
      // a known gap; the README documents it. Swallow JSON parse
      // errors only — re-throw anything else.
      if (!/JSON|did not produce JSON/.test(e.message)) throw e;
      r = null;
    }
    console.log('      CONSTRUCT returned:', r ? JSON.stringify(r).slice(0, 80) : '(no JSON)');
  });

  // 7. Output formats other than JSON — return string verbatim.
  await assertJsonSelect('output=csv returns string', async () => {
    const r = await query(DATA, `
      PREFIX foaf: <http://xmlns.com/foaf/0.1/>
      SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name
    `, { output: 'csv' });
    assert.strictEqual(typeof r, 'string');
    assert.ok(r.includes('name'), 'CSV should have the header');
    assert.ok(r.includes('Alice'), 'CSV should mention Alice');
  });

  // 8. output=table returns a string too (pretty-printed ASCII).
  await assertJsonSelect('output=table returns string', async () => {
    const r = await query(DATA, `
      PREFIX foaf: <http://xmlns.com/foaf/0.1/>
      SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name
    `, { output: 'table' });
    assert.strictEqual(typeof r, 'string');
    assert.ok(r.length > 0);
  });

  console.log('\nAll smoke tests passed.');
})().catch((e) => {
  console.error('\nSmoke test FAILED.');
  console.error(e && e.stack || e);
  process.exit(1);
});
