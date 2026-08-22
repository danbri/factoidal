// SPARQL 1.1 §17.6 extension functions — issue #463.
// https://github.com/danbri/factoidal/issues/463
//
// Pins the Comunica-style registry surface end-to-end through the
// npm-entry bundle: custom functions (sync AND async) in FILTER, BIND,
// and SELECT expressions; the unknown-IRI error; primitive and
// term-object return values; argument marshaling (SRJ term shape);
// and unregister/clear. The async cases exercise lib/api.js's
// re-evaluation trampoline over the synchronous extracted engine.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  query,
  registerExtensionFunction,
  unregisterExtensionFunction,
  clearExtensionFunctions,
} = require('..');

const EX = 'http://example.org/fn#';

const DATA = `
@prefix : <http://example.org/> .
:alice :name "Alice" ; :age 30 .
:bob   :name "Bob"   ; :age 7 .
`;

test.afterEach(async () => { await clearExtensionFunctions(); });

test('unknown extension IRI: FILTER drops every row (§17.6 error)', async () => {
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s WHERE { ?s <http://example.org/name> ?n .
                      FILTER(fn:noSuchFunction(?n)) }`);
  assert.deepEqual(rows, []);
});

test('unknown extension IRI: BIND leaves the variable unbound', async () => {
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s ?x WHERE { ?s <http://example.org/name> ?n .
                         BIND(fn:noSuchFunction(?n) AS ?x) }`);
  assert.equal(rows.length, 2);
  for (const row of rows) assert.equal(row.get('x'), undefined);
});

test('sync function in FILTER: boolean return', async () => {
  await registerExtensionFunction(`${EX}isAdult`, (args) => {
    assert.equal(args.length, 1);
    assert.equal(args[0].type, 'literal');
    return Number(args[0].value) >= 18;
  });
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s WHERE { ?s <http://example.org/age> ?a .
                      FILTER(fn:isAdult(?a)) }`);
  assert.equal(rows.length, 1);
  assert.equal(rows[0].get('s').value, 'http://example.org/alice');
});

test('sync function in BIND: string return becomes an xsd:string literal', async () => {
  await registerExtensionFunction(`${EX}shout`, (args) =>
    String(args[0].value).toUpperCase());
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?loud WHERE { ?s <http://example.org/name> ?n .
                         BIND(fn:shout(?n) AS ?loud) }
    ORDER BY ?loud`);
  assert.deepEqual(rows.map((r) => r.get('loud').value), ['ALICE', 'BOB']);
});

test('sync function in a SELECT expression', async () => {
  await registerExtensionFunction(`${EX}double`, (args) =>
    2 * Number(args[0].value));
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s (fn:double(?a) AS ?d)
    WHERE { ?s <http://example.org/age> ?a } ORDER BY ?d`);
  assert.deepEqual(rows.map((r) => r.get('d').value), ['14', '60']);
});

test('ASYNC function in FILTER resolves through the trampoline', async () => {
  await registerExtensionFunction(`${EX}isAdultAsync`, async (args) => {
    await new Promise((resolve) => setTimeout(resolve, 5));
    return Number(args[0].value) >= 18;
  });
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s WHERE { ?s <http://example.org/age> ?a .
                      FILTER(fn:isAdultAsync(?a)) }`);
  assert.equal(rows.length, 1);
  assert.equal(rows[0].get('s').value, 'http://example.org/alice');
});

test('ASYNC function in BIND: term-object return with datatype', async () => {
  await registerExtensionFunction(`${EX}category`, async (args) => ({
    type: 'literal',
    value: Number(args[0].value) >= 18 ? 'adult' : 'child',
    datatype: 'http://www.w3.org/2001/XMLSchema#string',
  }));
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s ?c WHERE { ?s <http://example.org/age> ?a .
                         BIND(fn:category(?a) AS ?c) }
    ORDER BY ?s`);
  assert.deepEqual(rows.map((r) => r.get('c').value), ['adult', 'child']);
});

test('two async functions chain across rounds (nested calls converge)', async () => {
  await registerExtensionFunction(`${EX}plusOne`, async (args) =>
    Number(args[0].value) + 1);
  await registerExtensionFunction(`${EX}timesTen`, async (args) =>
    Number(args[0].value) * 10);
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s (fn:timesTen(fn:plusOne(?a)) AS ?v)
    WHERE { ?s <http://example.org/age> ?a } ORDER BY ?v`);
  assert.deepEqual(rows.map((r) => r.get('v').value), ['80', '310']);
});

test('uri return: function producing an IRI term', async () => {
  await registerExtensionFunction(`${EX}toIri`, (args) => ({
    type: 'uri',
    value: 'http://example.org/minted/' + args[0].value,
  }));
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT (fn:toIri(?n) AS ?i)
    WHERE { <http://example.org/alice> <http://example.org/name> ?n }`);
  assert.equal(rows[0].get('i').termType, 'NamedNode');
  assert.equal(rows[0].get('i').value, 'http://example.org/minted/Alice');
});

test('throwing / rejecting functions are the §17.6 error, not a crash', async () => {
  await registerExtensionFunction(`${EX}boom`, () => {
    throw new Error('sync boom');
  });
  await registerExtensionFunction(`${EX}boomAsync`, async () => {
    throw new Error('async boom');
  });
  const rows = await query(DATA, `
    PREFIX fn: <${EX}>
    SELECT ?s ?x ?y WHERE { ?s <http://example.org/name> ?n .
                            BIND(fn:boom(?n) AS ?x)
                            BIND(fn:boomAsync(?n) AS ?y) }`);
  assert.equal(rows.length, 2);
  for (const row of rows) {
    assert.equal(row.get('x'), undefined);
    assert.equal(row.get('y'), undefined);
  }
});

test('unregister restores the unknown-IRI error', async () => {
  const iri = `${EX}transient`;
  await registerExtensionFunction(iri, () => true);
  const before = await query(DATA, `
    SELECT ?s WHERE { ?s <http://example.org/name> ?n .
                      FILTER(<${iri}>(?n)) }`);
  assert.equal(before.length, 2);
  await unregisterExtensionFunction(iri);
  const after = await query(DATA, `
    SELECT ?s WHERE { ?s <http://example.org/name> ?n .
                      FILTER(<${iri}>(?n)) }`);
  assert.deepEqual(after, []);
});

test('built-ins keep precedence: an xsd cast IRI is never offered to the registry', async () => {
  let called = false;
  await registerExtensionFunction(
    'http://www.w3.org/2001/XMLSchema#integer', () => { called = true; return 999; });
  const rows = await query(DATA, `
    PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
    SELECT (xsd:integer("41") AS ?v) WHERE {}`);
  assert.equal(rows[0].get('v').value, '41');
  assert.equal(called, false);
});
