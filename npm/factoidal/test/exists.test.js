// Regression pin for issue #343 on the npm surface: FILTER EXISTS /
// NOT EXISTS returned ZERO rows through the engine bundle while the
// W3C runner (a different evaluation path) stayed green. Reported by
// the package owner from a webapp; both forms empty at once, which no
// correct engine can produce — every row satisfies exactly one of
// EXISTS / NOT EXISTS for the same inner pattern.
//
// Companion native pin: tests/local/cli_exists_regressions.sh.
require('./helpers.js');

const test = require('node:test');
const assert = require('node:assert/strict');

const { parse, query } = require('..');

const TTL = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  _:a foaf:name "Alice" ; foaf:knows _:b .
  _:b foaf:name "Bob" .
`;

const names = (rows) => {
  const out = [];
  for (const b of rows) out.push(b.get('name').value);
  return out.sort();
};

test('FILTER EXISTS keeps exactly the rows whose inner pattern matches', async () => {
  const ds = await parse(TTL, { format: 'turtle' });
  const rows = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name FILTER EXISTS { ?p foaf:knows ?q } }
  `);
  assert.deepEqual(names(rows), ['Alice']);
});

test('FILTER NOT EXISTS keeps exactly the complementary rows', async () => {
  const ds = await parse(TTL, { format: 'turtle' });
  const rows = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name FILTER NOT EXISTS { ?p foaf:knows ?q } }
  `);
  assert.deepEqual(names(rows), ['Bob']);
});

test('EXISTS and NOT EXISTS partition the rows (the impossible-both-empty check)', async () => {
  const ds = await parse(TTL, { format: 'turtle' });
  const exists = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name FILTER EXISTS { ?p foaf:knows ?q } }
  `);
  const notExists = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name FILTER NOT EXISTS { ?p foaf:knows ?q } }
  `);
  const all = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name }
  `);
  const partition = names(exists).concat(names(notExists)).sort();
  assert.deepEqual(partition, names(all));
});

test('EXISTS nested under ! (exercises the recursive substitution)', async () => {
  const ds = await parse(TTL, { format: 'turtle' });
  const rows = await query(ds, `
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?p foaf:name ?name FILTER ( ! EXISTS { ?p foaf:knows ?q } ) }
  `);
  assert.deepEqual(names(rows), ['Bob']);
});
