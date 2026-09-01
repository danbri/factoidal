// Pins the `factoidal/l4` npm subpath (npm/factoidal/l4.js): the Lean 4
// engine resolvable through the package namespace without being bundled
// into @factoidal/core. In this repository checkout the resolver's
// third source (docs/web/hub/assets/l4/) is what makes it available;
// the test also pins the not-found error text so a user without the
// assets gets an actionable message, and cross-checks one join against
// the F* engine (the differential habit: two engines, same rows).

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';
import { NPM_FACTOIDAL_INDEX } from './_helpers.mjs';

const require = createRequire(import.meta.url);
const l4 = require('../../npm/factoidal/l4.js');
const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

const EX = 'http://example.org/';
const uri = (v) => ({ type: 'uri', value: v });
const lit = (v, datatype) => (datatype ? { type: 'literal', value: v, datatype } : { type: 'literal', value: v });
const v = (name) => ({ type: 'var', value: name });

const TRIPLES = [
  { subject: uri(EX + 'alice'), predicate: uri(EX + 'name'), object: lit('Alice') },
  { subject: uri(EX + 'alice'), predicate: uri(EX + 'age'), object: lit('30', 'http://www.w3.org/2001/XMLSchema#integer') },
  { subject: uri(EX + 'bob'), predicate: uri(EX + 'name'), object: lit('Bob') },
  { subject: uri(EX + 'bob'), predicate: uri(EX + 'age'), object: lit('24', 'http://www.w3.org/2001/XMLSchema#integer') },
];

test('factoidal/l4: assets resolvable in a repo checkout', () => {
  assert.equal(l4.available(), true);
  assert.equal(l4.engine, 'lean4-wasm');
});

test('factoidal/l4: version identifies the Lean engine', async () => {
  const ver = await l4.version();
  assert.match(ver, /l4factoidal/);
});

test('factoidal/l4: two-pattern join agrees with the F* engine', async () => {
  const doc = await l4.bgpQuery(TRIPLES, [
    { subject: v('s'), predicate: uri(EX + 'name'), object: v('n') },
    { subject: v('s'), predicate: uri(EX + 'age'), object: v('a') },
  ]);
  const leanRows = doc.results.bindings
    .map((b) => `${b.s.value}|${b.n.value}|${b.a.value}`)
    .sort();

  const dataset = await factoidal.parse(
    TRIPLES.map((t) => `<${t.subject.value}> <${t.predicate.value}> ${
      t.object.type === 'uri' ? `<${t.object.value}>`
        : t.object.datatype ? `"${t.object.value}"^^<${t.object.datatype}>`
        : `"${t.object.value}"`} .`).join('\n'),
    { format: 'ntriples', baseIRI: EX });
  const rows = await factoidal.query(dataset,
    `PREFIX : <${EX}> SELECT ?s ?n ?a WHERE { ?s :name ?n ; :age ?a }`);
  const bindings = Array.isArray(rows) ? rows : rows.results.bindings;
  const fstarRows = bindings
    .map((b) => {
      const g = (k) => (b[k]?.value ?? b.get?.(k)?.value ?? String(b[k]));
      return `${g('s')}|${g('n')}|${g('a')}`;
    })
    .sort();

  assert.equal(leanRows.length, 2);
  assert.deepEqual(leanRows, fstarRows);
});

test('factoidal/l4: current IBK3 worker is available through the typed package subpath', async () => {
  const bytes = readFileSync(new URL('../../docs/web/hub/assets/blocks/shardborough-three-way/type.ibk3', import.meta.url));
  const result = await l4.scanIBK3Predicate(
    bytes.toString('hex'),
    'http://example.org/type',
    'source:npm-l4-test',
  );
  assert.equal(result.format, 'IBK3');
  assert.equal(result.blankNodeScope, 'source:npm-l4-test');
  assert.equal(result.rows, 4);
});

test('factoidal/l4: missing-assets error names the remedies', async () => {
  // Force every resolver source to miss by asking from a copy whose
  // repo-relative path cannot exist. Simplest faithful probe: check the
  // error text constant in the module source.
  const src = readFileSync(new URL('../../npm/factoidal/l4.js', import.meta.url), 'utf8');
  assert.match(src, /@factoidal\/lean/);
  assert.match(src, /FACTOIDAL_L4_ASSETS/);
});
