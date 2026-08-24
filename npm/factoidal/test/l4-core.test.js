// factoidal/l4-core — the typed core API served by the Lean 4 engine
// (L4Factoidal compiled to wasm, dispatch ABI). Every case here runs
// through require('../l4-core.js'); the differential case cross-checks
// one join against the F* engine (require('../index.js')).
//
// Skips wholesale when the Lean wasm assets are not resolvable
// (l4.js's three-source ladder found nothing).
//
// Known engine differences accommodated (and ONLY these):
//   - N-Quads line order from the Lean engine may differ from the F*
//     engine's sorted order — content comparisons sort lines first.
//   - Blank-node labels are NOT salted per document by the Lean engine
//     yet: the one multi-document merge case is t.todo (see below).

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const AVAILABLE = require('../l4.js').available();
const l4core = require('../l4-core.js');

function skipUnlessAvailable(t) {
  if (AVAILABLE) return false;
  t.skip('Lean wasm assets not resolvable (l4.js available() is false)');
  return true;
}

// Sort N-Quads text into a canonical line list (order-insensitive
// content comparison — the Lean engine's line order is not pinned to
// the F* engine's sorted order).
function sortedLines(nq) {
  return nq.split('\n').filter((l) => l.trim() !== '').sort();
}

// One binding row (Map<string, Term>) -> a stable string; a row LIST
// -> a sorted multiset key. Sorting each row's entries first makes the
// comparison independent of SRJ row-key order.
function rowKey(row) {
  return JSON.stringify(
    [...row.entries()]
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
      .map(([name, term]) => [
        name, term.termType, term.value,
        term.termType === 'Literal' ? term.datatype.value : '',
        term.termType === 'Literal' ? term.language : '',
      ]));
}
function rowMultiset(rows) {
  return rows.map(rowKey).sort();
}

const X = 'http://x/';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const RDFS_SUBCLASS = 'http://www.w3.org/2000/01/rdf-schema#subClassOf';
const XSD_INT = 'http://www.w3.org/2001/XMLSchema#integer';

const JOIN_NT =
  `<${X}alice> <${X}name> "Alice" .\n` +
  `<${X}alice> <${X}age> "30"^^<${XSD_INT}> .\n` +
  `<${X}bob> <${X}name> "Bob" .\n` +
  `<${X}bob> <${X}age> "24"^^<${XSD_INT}> .\n`;
const JOIN_Q =
  `SELECT ?s ?n ?a WHERE { ?s <${X}name> ?n . ?s <${X}age> ?a }`;

// ---------------------------------------------------------------------
// parse + serialize round-trips
// ---------------------------------------------------------------------

test('l4-core parse: ntriples/turtle/nquads/trig round-trip to N-Quads', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const cases = [
    { format: 'ntriples', text: `<${X}s> <${X}p> "c" .`,
      quad: `<${X}s> <${X}p> "c" .` },
    { format: 'turtle',
      text: `@prefix x: <${X}> . x:s x:p "c" .`,
      quad: `<${X}s> <${X}p> "c" .` },
    { format: 'nquads', text: `<${X}s> <${X}p> <${X}o> <${X}g> .`,
      quad: `<${X}s> <${X}p> <${X}o> <${X}g> .` },
    { format: 'trig',
      text: `<${X}g> { <${X}s> <${X}p> <${X}o> . }`,
      quad: `<${X}s> <${X}p> <${X}o> <${X}g> .` },
  ];
  for (const c of cases) {
    const ds = await l4core.parse(c.text, { format: c.format });
    assert.equal(ds.size, 1, `${c.format}: one quad parsed`);
    const nq = await l4core.serialize(ds, { format: 'nquads' });
    assert.deepEqual(sortedLines(nq), [c.quad],
      `${c.format}: round-trips through serialize({format:'nquads'})`);
  }
});

test('l4-core parse: turtle relative IRI resolves against baseIRI', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.parse(`<me> <${X}p> "c" .`,
    { format: 'turtle', baseIRI: 'http://base.example/dir/doc' });
  const nq = await l4core.serialize(ds, { format: 'nquads' });
  assert.deepEqual(sortedLines(nq),
    [`<http://base.example/dir/me> <${X}p> "c" .`]);
});

// ---------------------------------------------------------------------
// query
// ---------------------------------------------------------------------

test('l4-core query: SELECT returns a typed literal binding', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const rows = await l4core.query(
    `<${X}s> <${X}age> "30"^^<${XSD_INT}> .`,
    `SELECT ?a WHERE { ?s <${X}age> ?a }`, { format: 'ntriples' });
  assert.equal(rows.length, 1);
  const a = rows[0].get('a');
  assert.equal(a.termType, 'Literal');
  assert.equal(a.value, '30');
  assert.equal(a.datatype.value, XSD_INT);
});

test('l4-core query: SELECT with a two-pattern join', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const rows = await l4core.query(JOIN_NT, JOIN_Q, { format: 'ntriples' });
  assert.equal(rows.length, 2);
  const names = rows.map((r) => r.get('n').value).sort();
  assert.deepEqual(names, ['Alice', 'Bob']);
});

test('l4-core query: ASK true and false', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const data = `<${X}s> <${X}p> "c" .`;
  assert.equal(
    await l4core.query(data, 'ASK { ?s ?p ?o }', { format: 'ntriples' }),
    true);
  assert.equal(
    await l4core.query(data, `ASK { <${X}none> <${X}q> "zz" }`,
      { format: 'ntriples' }),
    false);
});

test('l4-core query: CONSTRUCT returns a Dataset', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const out = await l4core.query(
    `<${X}s> <${X}p> "c" .`,
    `CONSTRUCT { ?s <${X}q> ?o } WHERE { ?s <${X}p> ?o }`,
    { format: 'ntriples' });
  assert.equal(out.constructor.name, 'Dataset');
  assert.equal(out.size, 1);
  const nq = await l4core.serialize(out, { format: 'nquads' });
  assert.deepEqual(sortedLines(nq), [`<${X}s> <${X}q> "c" .`]);
});

test('l4-core query: accepts a Dataset instance as input', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.parse(JOIN_NT, { format: 'ntriples' });
  const rows = await l4core.query(ds, JOIN_Q);
  assert.equal(rows.length, 2);
});

// ---------------------------------------------------------------------
// update
// ---------------------------------------------------------------------

test('l4-core update: INSERT DATA then query sees the triple', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.update(
    `<${X}s> <${X}p> "c" .`,
    `INSERT DATA { <${X}a> <${X}b> <${X}c> }`, { format: 'ntriples' });
  assert.equal(ds.size, 2);
  const hit = await l4core.query(ds, `ASK { <${X}a> <${X}b> <${X}c> }`);
  assert.equal(hit, true);
});

// ---------------------------------------------------------------------
// serialize
// ---------------------------------------------------------------------

// The committed Lean wasm's serializeTurtle op raises a raw
// WebAssembly.Exception (a Lean panic) on ANY non-empty graph — only
// the empty graph serializes. Engine-side bug (formal/lean4/Wasm/Ops/
// Parse.lean's serializeTurtle -> turtleOfGraphAuto), out of scope for
// the npm wiring; this case flips to passing when the wasm is rebuilt
// fixed.
test("l4-core serialize({format:'turtle'}) contains the expected term",
  { todo: 'committed Lean wasm panics (WebAssembly.Exception) in serializeTurtle on any non-empty graph' },
  async (t) => {
    if (skipUnlessAvailable(t)) return;
    const ttl = await l4core.serialize(
      `<${X}s> <${X}p> <${X}o> .`,
      { format: 'turtle', inputFormat: 'ntriples' });
    assert.match(ttl, /http:\/\/x\/s/);
  });

test("l4-core serialize rejects format:'ntriples' (CLI-only path)", async (t) => {
  if (skipUnlessAvailable(t)) return;
  await assert.rejects(
    () => l4core.serialize(`<${X}s> <${X}p> "c" .`,
      { format: 'ntriples', inputFormat: 'ntriples' }),
    /not implemented by the Lean 4 engine/);
});

// ---------------------------------------------------------------------
// canonicalize
// ---------------------------------------------------------------------

test('l4-core canonicalize: isomorphic graphs get identical canonical text', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const g1 = `_:a <${X}p> _:b .\n_:b <${X}q> _:a .`;
  const g2 = `_:z <${X}p> _:y .\n_:y <${X}q> _:z .`;
  const c1 = await l4core.canonicalize(g1, { format: 'ntriples' });
  const c2 = await l4core.canonicalize(g2, { format: 'ntriples' });
  assert.equal(c1, c2);
  assert.match(c1, /_:c14n\d/);
});

// ---------------------------------------------------------------------
// closures and checks
// ---------------------------------------------------------------------

const RDFS_DATA =
  `<${X}A> <${RDFS_SUBCLASS}> <${X}B> .\n` +
  `<${X}i> <${RDF_TYPE}> <${X}A> .\n`;

test('l4-core coreRdfsClosure infers a type via subClassOf', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const r = await l4core.coreRdfsClosure(RDFS_DATA, { format: 'ntriples' });
  assert.equal(r.ok, true);
  assert.ok(r.ntriples.includes(`<${X}i> <${RDF_TYPE}> <${X}B> .`),
    'closure contains the rdfs9-derived type triple');
});

test('l4-core rhoDfClosure / rdfsPlusClosure return certified envelopes', async (t) => {
  if (skipUnlessAvailable(t)) return;
  // Same contract as index.js: {ok, ntriples} — the raw certified
  // result the theorem registry talks about, not a Dataset.
  const rho = await l4core.rhoDfClosure(RDFS_DATA, { format: 'ntriples' });
  assert.equal(rho.ok, true);
  assert.equal(typeof rho.ntriples, 'string');
  const plus = await l4core.rdfsPlusClosure(RDFS_DATA, { format: 'ntriples' });
  assert.equal(plus.ok, true);
  assert.equal(typeof plus.ntriples, 'string');
  assert.ok(plus.ntriples.includes(`<${X}i> <${RDF_TYPE}> <${X}B> .`));
});

test('l4-core coreRdfsCheck / rhoDfFragmentCheck report booleans', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const inFrag = await l4core.coreRdfsCheck(
    `<${X}A> <${RDFS_SUBCLASS}> <${X}B> .`, { format: 'ntriples' });
  assert.equal(inFrag.ok, true);
  assert.equal(typeof inFrag.fragment, 'boolean');
  assert.equal(inFrag.fragment, true);
  const alias = await l4core.rhoDfFragmentCheck(
    `<${X}A> <${RDFS_SUBCLASS}> <${X}B> .`, { format: 'ntriples' });
  assert.equal(alias.fragment, true);
});

test("l4-core owlClosure mode 'OWL-RL' returns a Dataset superset", async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.owlClosure(RDFS_DATA, 'OWL-RL', { format: 'ntriples' });
  assert.equal(ds.constructor.name, 'Dataset');
  assert.ok(ds.size >= 2, 'closure keeps the input triples');
  const nq = await l4core.serialize(ds, { format: 'nquads' });
  assert.ok(sortedLines(nq).includes(`<${X}i> <${RDF_TYPE}> <${X}B> .`));
});

// ---------------------------------------------------------------------
// capabilities honesty
// ---------------------------------------------------------------------

test('l4-core capabilities: entry true, shacl false, tableau false', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const caps = await l4core.capabilities();
  assert.equal(caps.entry, true);
  assert.equal(caps.shacl, false);
  assert.equal(caps.tableau, false);
  assert.equal(caps.owlClosure, true);
  assert.equal(caps.update, true);
  assert.equal(caps.canonicalize, true);
});

// ---------------------------------------------------------------------
// error pins — the exact texts api.js produces on this driver
// ---------------------------------------------------------------------

test('l4-core shaclValidate rejects with the missing-entry-fn error', async (t) => {
  if (skipUnlessAvailable(t)) return;
  // The entry object exists but has no shaclValidate fn, so api.js's
  // requireEntryFn throws pendingError('SHACL validation').
  await assert.rejects(
    () => l4core.shaclValidate(`<${X}s> <${X}p> "c" .`,
      `<${X}sh> <${X}q> "s" .`, { format: 'ntriples' }),
    /SHACL validation needs the factoidal-npm-entry bundle/);
});

test("l4-core query({entail:'RDFS'}) rejects with the NOT_SUPPORTED text", async (t) => {
  if (skipUnlessAvailable(t)) return;
  // entail !== 'none' routes to the CLI path, which this driver stubs
  // with the l4-core NOT_SUPPORTED message.
  await assert.rejects(
    () => l4core.query(`<${X}s> <${X}p> "c" .`, 'SELECT * { ?s ?p ?o }',
      { format: 'ntriples', entail: 'RDFS' }),
    /not implemented by the Lean 4 engine/);
});

// ---------------------------------------------------------------------
// differential parity vs the F* engine
// ---------------------------------------------------------------------

test('l4-core vs F* engine: same join, same row multiset', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const fstar = require('../index.js');
  const leanRows = await l4core.query(JOIN_NT, JOIN_Q, { format: 'ntriples' });
  const fstarRows = await fstar.query(JOIN_NT, JOIN_Q, { format: 'ntriples' });
  assert.equal(leanRows.length, 2);
  assert.deepEqual(rowMultiset(leanRows), rowMultiset(fstarRows));
});

// ---------------------------------------------------------------------
// multi-document blank-node scoping — known Lean engine gap
// ---------------------------------------------------------------------

// The Lean engine does not yet salt blank-node labels per document:
// two documents each using _:b0 are conflated into ONE node at merge,
// where the F* engine's per-document renaming
// (RDF.Dataset.Merge.rename_dataset_bnodes) keeps them distinct.
// Verified against the F* engine in this same fixture (2 distinct
// subjects there, 1 from Lean). Flips to passing when the Lean side
// grows the per-document bnode salt.
test('l4-core multi-document merge keeps blank-node labels document-scoped',
  { todo: 'Lean engine is missing the per-document blank-node salt (F*: RDF.Dataset.Merge.rename_dataset_bnodes)' },
  async (t) => {
    if (skipUnlessAvailable(t)) return;
    const d1 = `_:b0 <${X}p> "one" .`;
    const d2 = `_:b0 <${X}p> "two" .`;
    const rows = await l4core.query([d1, d2],
      `SELECT DISTINCT ?s WHERE { ?s <${X}p> ?o }`, { format: 'turtle' });
    assert.equal(rows.length, 2,
      'two documents each with _:b0 must contribute two distinct nodes');
  });
