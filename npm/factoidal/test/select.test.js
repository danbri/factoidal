// factoidal/select — the backend selector (issue #618). Exercises all
// five backend values, the throw-vs-fall-through split, the lean1st
// override list, and slowcompareboth's agree/disagree reporting.
//
// The Lean-unsupported test cases (shaclValidate) need the Lean wasm
// assets resolvable; skip wholesale otherwise, same pattern as
// l4-core.test.js.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const select = require('../select.js');
const { Dataset } = require('../rdfjs.js');

const LEAN_AVAILABLE = require('../l4.js').available();

function skipUnlessLean(t) {
  if (LEAN_AVAILABLE) return false;
  t.skip('Lean wasm assets not resolvable (l4.js available() is false)');
  return true;
}

// The op names the RESOLVED wasm actually serves (same defensive
// pattern as l4-core.test.js's leanOps()/skipUnlessOp() -- the
// committed wasm can predate an op added in the same landing as its
// tests).
let leanOpsPromise = null;
function leanOps() {
  if (!leanOpsPromise) {
    leanOpsPromise = require('../l4.js')
      .loadL4()
      .then((eng) =>
        typeof eng.call === 'function' ? eng.call('ops', []).ops : [])
      .catch(() => []);
  }
  return leanOpsPromise;
}

async function skipUnlessOp(t, op) {
  if (skipUnlessLean(t)) return true;
  const ops = await leanOps();
  if (!ops.includes(op)) {
    t.skip(`resolved Lean wasm predates the '${op}' op (ops reflection)`);
    return true;
  }
  return false;
}

const TTL = '@prefix ex: <http://example.org/> . ex:a ex:b ex:c .';
const SHAPES =
  '@prefix sh: <http://www.w3.org/ns/shacl#> . ' +
  '@prefix ex: <http://example.org/> . ' +
  '[] a sh:NodeShape ; sh:targetNode ex:a ; sh:property [ sh:path ex:b ; sh:minCount 1 ] .';

// ---------------------------------------------------------------------
// BACKENDS / capabilityTable shape
// ---------------------------------------------------------------------

test('BACKENDS lists exactly the five owner-ruled values', () => {
  assert.deepEqual(
    [...select.BACKENDS].sort(),
    ['fstar', 'fstar1st', 'lean', 'lean1st', 'slowcompareboth'].sort());
});

test('createSelector rejects an unknown backend', () => {
  assert.throws(() => select.createSelector({ backend: 'nope' }), TypeError);
});

test('capabilityTable is derived from live capabilities(), not hand-written', async () => {
  const table = await select.capabilityTable();
  // Every ALWAYS_IF_ENTRY-style function both engines' typed APIs wire
  // to a fixed op name -- both true whenever an entry bundle loads.
  for (const fn of ['parse', 'query', 'update', 'serialize', 'canonicalize',
    'coreRdfsClosure', 'rhoDfClosure', 'rdfsPlusClosure', 'owlClosure',
    'owlIsConsistent', 'owlEntails']) {
    assert.equal(table[fn].fstar, true, `fstar should support ${fn}`);
  }
  // shaclValidate/shexValidate/tableauMaterialise/rmlMap/csvwToRdf/
  // jsonldToRdf/rifEval/xsltTransform are not in the Lean engine's
  // 13-op typed-API surface (bin/linux-x86_64/l4factoidal ops lists 21
  // raw ops; only 13 are wired to lib/api.js's typed wrappers) --
  // Lean must report false for every one of them.
  for (const fn of ['shaclValidate', 'shexValidate', 'tableauMaterialise',
    'rmlMap', 'csvwToRdf', 'jsonldToRdf', 'rifEval', 'xsltTransform']) {
    assert.equal(table[fn].lean, false, `lean should NOT support ${fn}`);
    assert.equal(table[fn].fstar, true, `fstar should support ${fn}`);
  }
});

test('capabilityTable: clParse is Lean-only -- lean true, fstar false', async (t) => {
  if (skipUnlessLean(t)) return;
  const table = await select.capabilityTable();
  assert.equal(table.clParse.lean, true);
  assert.equal(table.clParse.fstar, false);
});

// ---------------------------------------------------------------------
// The five backend values, each observable in the result envelope
// (sub-question 1: the answering engine must be visible).
// ---------------------------------------------------------------------

test("backend 'lean': answers from Lean and is observable as engine:'lean'", async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'lean' });
  const r = await sel.parse(TTL);
  assert.equal(r.engine, 'lean');
  assert.equal(r.backend, 'lean');
  assert.ok(r.value instanceof Dataset);
  assert.equal(r.value.size, 1);
});

test("backend 'fstar': answers from F* and is observable as engine:'fstar'", async () => {
  const sel = select.createSelector({ backend: 'fstar' });
  const r = await sel.parse(TTL);
  assert.equal(r.engine, 'fstar');
  assert.equal(r.backend, 'fstar');
  assert.ok(r.value instanceof Dataset);
  assert.equal(r.value.size, 1);
});

test("backend 'lean1st': answers from Lean when Lean implements the fn", async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'lean1st' });
  const r = await sel.parse(TTL);
  assert.equal(r.engine, 'lean');
});

test("backend 'lean1st': falls through to F* when Lean does not implement the fn", async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'lean1st' });
  const r = await sel.shaclValidate(TTL, SHAPES);
  assert.equal(r.engine, 'fstar');
  assert.equal(typeof r.value.conforms, 'boolean');
});

test("backend 'fstar1st': answers from F* when F* implements the fn (it always does here)", async () => {
  const sel = select.createSelector({ backend: 'fstar1st' });
  const r = await sel.parse(TTL);
  assert.equal(r.engine, 'fstar');
});

test("backend 'fstar1st': falls through to Lean via the mirror path", async (t) => {
  if (skipUnlessLean(t)) return;
  // No ROUTABLE function is F*-unsupported in this build (F* is the
  // superset engine), so exercise the mirror mechanism directly: force
  // it with overrideFns, which fstar1st also honours (routes to the
  // OTHER engine -- lean -- regardless of what F* implements).
  const sel = select.createSelector({ backend: 'fstar1st', overrideFns: ['parse'] });
  const r = await sel.parse(TTL);
  assert.equal(r.engine, 'lean');
});

// ---------------------------------------------------------------------
// Throw-vs-fall-through: "a request naming exactly one engine never
// gets an answer from the other."
// ---------------------------------------------------------------------

test("backend 'lean' throws (never falls back to F*) for a function Lean does not implement", async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'lean' });
  await assert.rejects(() => sel.shaclValidate(TTL, SHAPES));
});

test("backend 'fstar' throws (never falls back to Lean) for a function it does not implement", async () => {
  // No ROUTABLE function is missing from F* in this build (verified by
  // the capabilityTable test above), so this exercises the same throw
  // MECHANISM (invoke()'s "not a function on this engine" guard) with a
  // function name that genuinely is not on either typed API -- the
  // observable behaviour ('fstar' never silently answers from 'lean')
  // is identical to the real-capability-gap case exercised on 'lean'.
  const sel = select.createSelector({ backend: 'fstar' });
  await assert.rejects(
    () => sel.call('thisFunctionDoesNotExistOnAnyEngine', []),
    TypeError);
});

// ---------------------------------------------------------------------
// lean1st's optional override list: route to F* regardless of whether
// Lean implements the function.
// ---------------------------------------------------------------------

test('lean1st overrideFns (instance-level) routes named functions to F* even though Lean supports them', async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'lean1st', overrideFns: ['parse'] });
  const overridden = await sel.parse(TTL);
  assert.equal(overridden.engine, 'fstar', 'parse is in overrideFns -> F*');
  const notOverridden = await sel.query(TTL, 'ASK { ?s ?p ?o }');
  assert.equal(notOverridden.engine, 'lean', 'query is not in overrideFns -> Lean');
});

test('lean1st overrideFns (per-call) beats the instance default for that one call only', async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'lean1st' });
  const overridden = await sel.parse(TTL, {}, { overrideFns: ['parse'] });
  assert.equal(overridden.engine, 'fstar');
  const nextCall = await sel.parse(TTL); // no override this time
  assert.equal(nextCall.engine, 'lean', 'override does not leak to the next call');
});

test('per-call backend override beats the instance default (the "fn flavour" requirement)', async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'lean' });
  const r = await sel.parse(TTL, {}, { backend: 'fstar' });
  assert.equal(r.engine, 'fstar');
  // the instance default is untouched
  const r2 = await sel.parse(TTL);
  assert.equal(r2.engine, 'lean');
});

// ---------------------------------------------------------------------
// slowcompareboth: needs both engines to support the fn; reports
// agree/disagree rather than throwing on a genuine disagreement.
// ---------------------------------------------------------------------

test('slowcompareboth throws when only one engine supports the function', async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'slowcompareboth' });
  await assert.rejects(() => sel.shaclValidate(TTL, SHAPES), /needs BOTH engines/);
});

test('slowcompareboth: agreeing parse -- RDFC-1.0 isomorphism, agree:true', async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'slowcompareboth' });
  const r = await sel.parse(TTL);
  assert.equal(r.engine, 'both');
  assert.equal(r.agree, true);
  assert.equal(r.comparison.method, 'rdfc1.0-isomorphism');
  assert.ok(r.lean instanceof Dataset);
  assert.ok(r.fstar instanceof Dataset);
});

test('slowcompareboth: agreeing SELECT query -- bag-of-bindings, agree:true', async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'slowcompareboth' });
  const r = await sel.query(TTL, 'SELECT * WHERE { ?s ?p ?o }');
  assert.equal(r.agree, true);
  assert.equal(r.comparison.method, 'bag-of-bindings');
});

test('slowcompareboth: agreeing ASK query -- strict-equality, agree:true', async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'slowcompareboth' });
  const r = await sel.query(TTL, 'ASK { ?s ?p ?o }');
  assert.equal(r.agree, true);
  assert.equal(r.comparison.method, 'strict-equality');
  assert.equal(r.lean, true);
  assert.equal(r.fstar, true);
});

test('slowcompareboth: a CONTRIVED disagreement is reported (agree:false), not thrown', async () => {
  // Two data-shaped-identically-but-different result sets, run through
  // the exact comparator slowcompareboth uses (compareValues is
  // exported for this reason) -- a real two-engine disagreement is not
  // producible on demand (both engines are independently-verified
  // implementations of the same spec), so this contrives the SAME
  // input shape a real disagreement would have.
  const rowsA = [new Map([
    ['s', { termType: 'NamedNode', value: 'http://example.org/a' }],
  ])];
  const rowsB = [new Map([
    ['s', { termType: 'NamedNode', value: 'http://example.org/DIFFERENT' }],
  ])];
  const cmp = await select.compareValues('query', rowsA, rowsB);
  assert.equal(cmp.equal, false);
  assert.equal(cmp.method, 'bag-of-bindings');

  const dsA = Dataset.fromNQuads('<http://x/1> <http://x/p> "v" .\n');
  const dsB = Dataset.fromNQuads('<http://x/2> <http://x/p> "v" .\n');
  const cmpDs = await select.compareValues('parse', dsA, dsB);
  assert.equal(cmpDs.equal, false);
  assert.equal(cmpDs.method, 'rdfc1.0-isomorphism');
});

test('slowcompareboth: blank-node relabeling does not itself cause a false disagreement', async () => {
  // Same graph, different (per-engine-arbitrary) blank node labels --
  // this is the case decision 3 exists for: RDFC-1.0 isomorphism must
  // treat these as equal.
  const dsA = Dataset.fromNQuads('_:x1 <http://x/p> "v" .\n');
  const dsB = Dataset.fromNQuads('_:zzz <http://x/p> "v" .\n');
  const cmp = await select.compareValues('parse', dsA, dsB);
  assert.equal(cmp.equal, true);
  assert.equal(cmp.method, 'rdfc1.0-isomorphism');
});

// ---------------------------------------------------------------------
// clParse: the first Lean-only op on the typed capability table.
// formal/fstar has no CL/IKL parser, so backend:'fstar' must throw
// (never silently answer from Lean) and slowcompareboth must fail on
// the capability precondition (nothing to compare), not on an
// execution error from calling a function that does not exist.
// ---------------------------------------------------------------------

const PURE_CL_TEXT = "(uttered Bram 'I saw Jon watching Foxworth by the nut tree')";
const IKL_TEXT =
  "(witnessed Clud (that (saw Jon (that (cached Foxworth 'the beech hollow')))))";

test("backend 'lean': clParse answers with the parse envelope", async (t) => {
  if (skipUnlessLean(t)) return;
  if (await skipUnlessOp(t, 'clParse')) return;
  const sel = select.createSelector({ backend: 'lean' });
  const r = await sel.clParse(IKL_TEXT);
  assert.equal(r.engine, 'lean');
  assert.equal(r.backend, 'lean');
  assert.equal(r.value.ok, true);
  assert.equal(r.value.sentences, 1);
  assert.equal(r.value.pureCL, false);
  assert.equal(r.value.normalized, IKL_TEXT);
});

test("backend 'fstar': clParse throws (never falls back to Lean) -- formal/fstar has no CL/IKL parser", async () => {
  const sel = select.createSelector({ backend: 'fstar' });
  await assert.rejects(() => sel.clParse(PURE_CL_TEXT), TypeError);
});

test("backend 'fstar1st': clParse falls through to Lean, since F* never implements it", async (t) => {
  if (skipUnlessLean(t)) return;
  if (await skipUnlessOp(t, 'clParse')) return;
  const sel = select.createSelector({ backend: 'fstar1st' });
  const r = await sel.clParse(PURE_CL_TEXT);
  assert.equal(r.engine, 'lean');
  assert.equal(r.value.pureCL, true);
});

test("backend 'slowcompareboth': clParse fails the capability precondition, not a silent one-sided answer", async (t) => {
  if (skipUnlessLean(t)) return;
  const sel = select.createSelector({ backend: 'slowcompareboth' });
  await assert.rejects(() => sel.clParse(PURE_CL_TEXT), /needs BOTH engines/);
});

// ---------------------------------------------------------------------
// Owner decision, 2026-08-26 (issue #618, scope-change comment): the
// IKL-to-RDF projection ("direction B": clToDataset, queryWithIklService)
// stays off the npm surface -- "IKL doesn't have shapes or named
// profiles. Take it out of npm for now." These ops are NOT deleted from
// the compiled wasm (no rebuild happened for this decision); they are
// held back at the JS layer only. Pinned here so a later change can't
// quietly wire them back in without failing a test that names the
// decision.
//
// clParse used to sit in this same list, misattributed to the same
// owner decision. CORRECTION 2026-08-26 (see l4-core.js's OPS comment):
// clParse reads CLIF text and never produces RDF, so it was never part
// of direction B -- it was unwired only because nobody had decided to
// wrap it, and it is wired now (tests above). It must not be added
// back to this list.
// ---------------------------------------------------------------------

const WITHHELD_CL_IKL_OPS = ['clToDataset', 'queryWithIklService'];

test('capabilityTable/ROUTABLE never mention the withheld CL/IKL ops', async () => {
  const table = await select.capabilityTable();
  for (const op of WITHHELD_CL_IKL_OPS) {
    assert.equal(op in table, false, `${op} must not appear in capabilityTable()`);
    assert.equal(select.ROUTABLE.includes(op), false, `${op} must not appear in ROUTABLE`);
  }
});

test('l4-core.js exports none of the withheld CL/IKL ops as callable functions', () => {
  const l4core = require('../l4-core.js');
  for (const op of WITHHELD_CL_IKL_OPS) {
    assert.equal(typeof l4core[op], 'undefined', `l4-core.js must not export ${op}`);
  }
});

test('the withheld CL/IKL ops are still present in the compiled wasm (held back, not deleted)', async (t) => {
  if (skipUnlessLean(t)) return;
  const eng = await require('../l4.js').loadL4();
  if (typeof eng.call !== 'function') { t.skip('resolved wasm predates the dispatch ABI'); return; }
  const ops = eng.call('ops', []).ops;
  for (const op of WITHHELD_CL_IKL_OPS) {
    assert.ok(ops.includes(op),
      `${op} should still be a real op on the wasm's own reflection -- ` +
      'this is a JS-surface hold-back, not a wasm rebuild');
  }
});

// ---------------------------------------------------------------------
// Owner decision, 2026-08-26: x-ikl-* entailment regimes are not
// exposed through the npm API (IKL has no notion of shapes or named
// profiles). Rejected at the JS layer in BOTH lib/api.js's query()
// (the shared choke point for index.js/l4-core.js/select.js) and
// fn.js's entail() (which would otherwise pass an unrecognised regime
// string through unchanged).
// ---------------------------------------------------------------------

test('query() rejects x-ikl-* entail regimes (F* engine)', async () => {
  const factoidal = require('../index.js');
  const ds = await factoidal.parse(TTL);
  await assert.rejects(
    () => factoidal.query(ds, 'SELECT * WHERE { ?s ?p ?o }', { entail: 'x-ikl-core' }),
    /x-ikl-\* entailment regimes are not exposed/);
});

test('query() rejects x-ikl-* entail regimes case-insensitively (Lean engine)', async (t) => {
  if (skipUnlessLean(t)) return;
  const l4core = require('../l4-core.js');
  const ds = await l4core.parse(TTL);
  await assert.rejects(
    () => l4core.query(ds, 'SELECT * WHERE { ?s ?p ?o }', { entail: 'X-IKL-Whatever' }),
    /x-ikl-\* entailment regimes are not exposed/);
});

test('fn.js entail() rejects x-ikl-* before it ever reaches the engine', async () => {
  const fn = require('../fn.js');
  const ds = await fn.parse(TTL);
  await assert.rejects(
    () => fn.entail(ds, 'x-ikl-foo'),
    /x-ikl-\* entailment regimes are not exposed/);
});

test('select query() propagates the x-ikl-* rejection', async () => {
  const sel = select.createSelector({ backend: 'fstar' });
  await assert.rejects(
    () => sel.query(TTL, 'SELECT * WHERE { ?s ?p ?o }', { entail: 'x-ikl-core' }),
    /x-ikl-\* entailment regimes are not exposed/);
});

test('compareValues compares bindings as a BAG: duplicate rows are significant', async () => {
  const row = () => new Map([
    ['s', { termType: 'NamedNode', value: 'http://example.org/a' }],
  ]);
  const once = [row()];
  const twice = [row(), row()];
  const cmp = await select.compareValues('query', once, twice);
  assert.equal(cmp.equal, false, 'a bag with 1 copy != a bag with 2 copies');
});
