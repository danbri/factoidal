// factoidal/select — the backend selector (issue #618).
//
// One typed surface, two independently verified engines behind it: the
// F* extraction (./index.js) and the Lean 4 extraction (./l4-core.js).
// Owner ruling, 2026-08-26 (issue #618, comment
// https://github.com/danbri/factoidal/issues/618#issuecomment-5425162574,
// written up as a spec in
// https://github.com/danbri/factoidal/issues/618#issuecomment-5425193280):
//
//   Per-instance option; per-call override on at least the `fn` flavour
//   of the API. Five values: lean, fstar, lean1st, fstar1st,
//   slowcompareboth. `lean`/`fstar` THROW if the requested function is
//   not available in that engine -- a request naming exactly one
//   engine never gets an answer from the other. `lean1st` falls
//   through to F* for functions Lean does not implement (and takes an
//   optional override list of function names to route to F* even when
//   Lean implements them); `fstar1st` mirrors that. `slowcompareboth`
//   runs both and compares.
//
// This module is the createSelector() implementation; the sub-question
// answers the ruling asked the implementation to settle (not invent)
// are recorded next to the code that embodies each one:
//
//   1. observability  -> the {engine, backend, value} envelope, below.
//   2. slowcompareboth disagreement -> returns both + agree:false
//      (never throws for a genuine disagreement); throws only when a
//      capability precondition isn't met, or when a call itself
//      errors on at least one side (a different failure mode, kept
//      distinct -- see call()'s slowcompareboth branch).
//   3. "same answer" -> RDFC-1.0 isomorphism (via ./fn.js's equals(),
//      which already implements it) for anything Dataset-shaped;
//      SPARQL SELECT bindings are compared as a BAG (order-insensitive,
//      duplicates significant) with blank-node labels renamed to a
//      stable per-side canonical form first -- see compareValues().
//
// This module does not change index.js, l4-core.js or fn.js: it is a
// pure consumer of their existing typed surfaces plus fn.js's
// FnDataset equals()/fromDataset() for the RDFC-1.0 comparison. Every
// existing require('factoidal/l4'|'l4-core'|'.'|'./fn') call site is
// unaffected.

'use strict';

const fstarApi = require('./index.js');
const leanApi = require('./l4-core.js');
const fn = require('./fn.js');
const { Dataset } = require('./rdfjs.js');

const BACKENDS = Object.freeze(
  ['lean', 'fstar', 'lean1st', 'fstar1st', 'slowcompareboth']);

function assertBackend(name, who) {
  if (!BACKENDS.includes(name)) {
    throw new TypeError(
      `${who}: backend must be one of ${BACKENDS.join(', ')} (got ${JSON.stringify(name)})`);
  }
}

// ---------------------------------------------------------------------
// Capability derivation.
//
// index.js and l4-core.js are both built from lib/api.js's buildApi()
// driver, so capabilities() has ONE shape for both engines
// (lib/api.js:2010-2073) and every flag in it is computed from
// `typeof <that engine's real loaded entry object>[opName] ===
// 'function'` -- not a hand-maintained guess here. A handful of
// functions are wired to a fixed op name and gated only by
// requireEntryFn (no capabilities() flag): those are available
// whenever capabilities().entry is true, for whichever engine's entry
// actually defines that op. Cross-checked against the Lean side's own
// dispatch-ABI reflection (`bin/linux-x86_64/l4factoidal ops`, and
// l4.call('ops', []) at runtime) -- both list exactly these 16 of the
// engine's 21 ops as the ones lib/api.js's typed wrappers reach:
// parseToDatasetJson, queryDataset, updateDataset, serializeNQuads,
// serializeTurtle, canonicalizeToNQuads, owlClosure, owlIsConsistent,
// owlEntails, rhoDfClosure, rhoDfFragmentCheck, rdfsPlusClosure,
// clParse, clSerialize, clAlphaNorm, clNormalize. These four CL/IKL
// ops are the Lean-only entries in capabilityTable(): formal/fstar has
// no CL/IKL parser, so engineSupports(fstarApi, <any of the four>) is
// false on the very first `typeof` guard below -- index.js never
// exports any of the four names at all. The other 5 are real ops on
// the resolved wasm with no typed-API wrapper in l4-core.js, so they
// are correctly absent from ALWAYS_IF_ENTRY/CAP_FLAG below and from
// capabilityTable()'s output, for two different reasons (see
// l4-core.js's OPS comment for the full text):
//   - clToDataset, queryWithIklService: present in the compiled wasm
//     but DELETED from the engine source, 2026-08-26 (issue #626), and
//     already off the npm surface by owner decision (issue #618). The
//     artifact is ahead of its source until it is rebuilt (issue
//     #627). `clParse`/`clSerialize`/`clAlphaNorm`/`clNormalize` are
//     NOT part of that removal -- none of them reads or produces RDF,
//     so all four are wired above instead.
//   - clFiniteSat: DEFERRED, not excluded (owner decision, 2026-08-26)
//     -- it takes a caller-supplied finite-interpretation JSON
//     encoding that has no user yet, and a typed wrapper would freeze
//     that shape before we know whether it is right. Reachable only
//     through the raw dispatch ABI.
//   - ops, datasetOpen/Query/Update/Serialize/Close: not an owner
//     ruling, just not yet wired (no typed-wrapper shape for a
//     stateful handle exists in lib/api.js today).
// See docs/designissues/2026-08-22-npm-l4-module-packaging.md's #618
// section for the note.
const ALWAYS_IF_ENTRY = new Set([
  'parse', 'query', 'update', 'serialize', 'canonicalize', 'graphs',
  'canonicalHash', 'coreRdfsClosure', 'coreRdfsCheck', 'rhoDfClosure',
  'rhoDfFragmentCheck', 'rdfsPlusClosure', 'owlClosure', 'owlIsConsistent',
  'owlEntails', 'clParse', 'clSerialize', 'clAlphaNorm', 'clNormalize',
]);

// Every other routable function's support is reported by a
// capabilities() family flag.
const CAP_FLAG = {
  shaclValidate: 'shacl',
  shexValidate: 'shex',
  tableauMaterialise: 'tableau',
  tableauDlInconsistent: 'tableau',
  rmlMap: 'rml',
  csvwToRdf: 'csvw',
  jsonldToRdf: 'jsonld',
  jsonldFromRdf: 'jsonldFromRdf',
  didKeyResolve: 'didKey',
  xmlWellformed: 'xml',
  xpathEval: 'xpath',
  rifEval: 'rif',
  xsltTransform: 'xslt',
  mathmlEval: 'mathml',
  xformsRecalc: 'xforms',
  jsonSchemaValidate: 'jsonSchema',
  schematronValidate: 'schematron',
  toanSummation: 'toan', toanProduct: 'toan', toanSimplify: 'toan',
  toanDiff: 'toan', toanSubst: 'toan',
  matrixDeterminant: 'matrix', matrixScalarProduct: 'matrix',
  matrixVectorProduct: 'matrix', matrixOuterProduct: 'matrix',
  sigmoidPoints: 'sigmoid', sigmoidFormulaMathml: 'sigmoid',
  openCottas: 'cottasBytesStore', queryCottas: 'cottasBytesStore',
  closeCottas: 'cottasBytesStore', toCottas: 'cottasBytesStore',
  vcSha256Hex: 'vcCrypto', vcEd25519SecretToPublic: 'vcCrypto',
  vcEd25519Sign: 'vcCrypto', vcEd25519Verify: 'vcCrypto',
  vcEddsaCreateFromCanonical: 'vcCrypto', vcEddsaVerifyFromCanonical: 'vcCrypto',
};

const ROUTABLE = Object.freeze([...ALWAYS_IF_ENTRY, ...Object.keys(CAP_FLAG)]);

async function engineSupports(engineApi, fnName) {
  if (typeof engineApi[fnName] !== 'function') return false;
  let caps;
  try {
    caps = await engineApi.capabilities();
  } catch {
    return false;
  }
  if (ALWAYS_IF_ENTRY.has(fnName)) return !!caps.entry;
  const flag = CAP_FLAG[fnName];
  return flag ? !!caps[flag] : false;
}

/**
 * The capability table (issue #618): for every routable function name,
 * whether the Lean engine and the F* engine each support it right now
 * -- derived live from both engines' capabilities() probes (see
 * engineSupports() above), never hand-written from assumption. This is
 * exactly the table lean1st/fstar1st consult for fall-through, and
 * what makes lean/fstar's throw-on-unavailable correct rather than a
 * guess.
 * @returns {Promise<Record<string, {lean: boolean, fstar: boolean}>>}
 */
async function capabilityTable() {
  const table = {};
  for (const fnName of ROUTABLE) {
    table[fnName] = {
      lean: await engineSupports(leanApi, fnName),
      fstar: await engineSupports(fstarApi, fnName),
    };
  }
  return table;
}

function engineApiFor(name) {
  return name === 'lean' ? leanApi : fstarApi;
}

async function invoke(engineName, fnName, args) {
  const api = engineApiFor(engineName);
  if (typeof api[fnName] !== 'function') {
    throw new TypeError(
      `factoidal/select: '${fnName}' is not a function on the ${engineName} engine`);
  }
  // api[fnName] (lib/api.js's typed wrapper) already throws a clear
  // capability error when the loaded entry lacks the underlying op --
  // this is what makes backend:'lean'/'fstar' throw instead of
  // silently answering from nowhere (the ruling's "a request naming
  // exactly one engine never gets an answer from the other").
  return api[fnName](...args);
}

// ---------------------------------------------------------------------
// "Same answer" (sub-question 3): RDFC-1.0 isomorphism for anything
// Dataset-shaped (reusing fn.js's equals(), which already implements
// the cheapest-correct-path chain down to canonical-hash comparison);
// a documented BAG comparison for SPARQL SELECT bindings, since RDFC-1.0
// canonicalizes RDF graphs/datasets, not solution bindings, and SPARQL
// results are bags (duplicate rows are significant, order is not
// significant without ORDER BY).
// ---------------------------------------------------------------------

async function datasetsIsomorphic(a, b) {
  return fn.equals(fn.fromDataset(a), fn.fromDataset(b));
}

function termFingerprint(term) {
  if (!term) return '';
  if (term.termType === 'Literal') {
    return `L:${term.value}^^${term.datatype ? term.datatype.value : ''}` +
      (term.language ? `@${term.language}` : '');
  }
  return `${term.termType[0]}:${term.value}`;
}

// Blank-node labels are per-engine arbitrary; relabel them to a stable
// b0, b1, ... sequence assigned in first-appearance order (scanning
// rows in order, variables in sorted-name order within each row) so
// two independently-run engines' otherwise-identical result sets
// compare equal. This is NOT RDFC-1.0 (that operates on RDF graphs);
// it is the analogous idea applied to one result set's bindings.
function normalizeBindingsBag(rows) {
  const varNames = new Set();
  for (const row of rows) for (const k of row.keys()) varNames.add(k);
  const sortedVars = [...varNames].sort();
  const bnodeLabels = new Map();
  let counter = 0;
  return rows.map((row) => sortedVars.map((v) => {
    const term = row.get(v);
    if (!term) return `${v}=∅`;
    if (term.termType === 'BlankNode') {
      let label = bnodeLabels.get(term.value);
      if (label === undefined) {
        label = `_:b${counter++}`;
        bnodeLabels.set(term.value, label);
      }
      return `${v}=B:${label}`;
    }
    return `${v}=${termFingerprint(term)}`;
  }).join('|')).sort();
}

function bagsEqual(a, b) {
  if (a.length !== b.length) return false;
  const remaining = a.slice().sort();
  const other = b.slice().sort();
  for (let i = 0; i < remaining.length; i++) {
    if (remaining[i] !== other[i]) return false;
  }
  return true;
}

function omit(obj, key) {
  const rest = {};
  for (const k of Object.keys(obj)) if (k !== key) rest[k] = obj[k];
  return rest;
}

function shallowScalarEqual(a, b) {
  const ak = Object.keys(a).sort();
  const bk = Object.keys(b).sort();
  if (ak.length !== bk.length) return false;
  for (let i = 0; i < ak.length; i++) if (ak[i] !== bk[i]) return false;
  return ak.every((k) => JSON.stringify(a[k]) === JSON.stringify(b[k]));
}

// Some typed-API results wrap the Dataset-valued payload in a scalar
// field rather than returning it bare.
const DATASET_FIELD_HINT = {
  tableauMaterialise: 'dataset',
  shaclValidate: 'report',
};
// ... and some wrap RDF as raw N-Triples/N-Quads TEXT rather than a
// Dataset -- comparing that text with strict string equality would be
// wrong (two engines' raw, non-canonical serializations can differ in
// blank-node labels and line order for the same graph), so these parse
// the field back into a Dataset first.
const RDF_TEXT_FIELD_HINT = {
  coreRdfsClosure: 'ntriples',
  rhoDfClosure: 'ntriples',
  rdfsPlusClosure: 'ntriples',
};

/**
 * Decide whether two engines' results for the same call are "the same
 * answer" (sub-question 3). Returns { equal, method } so a caller can
 * see which comparison was used, not just the verdict.
 */
async function compareValues(fnName, leanValue, fstarValue) {
  if (leanValue instanceof Dataset && fstarValue instanceof Dataset) {
    return {
      equal: await datasetsIsomorphic(leanValue, fstarValue),
      method: 'rdfc1.0-isomorphism',
    };
  }
  if (Array.isArray(leanValue) && Array.isArray(fstarValue)) {
    return {
      equal: bagsEqual(
        normalizeBindingsBag(leanValue), normalizeBindingsBag(fstarValue)),
      method: 'bag-of-bindings',
    };
  }
  if (fnName === 'serialize' &&
      typeof leanValue === 'string' && typeof fstarValue === 'string') {
    try {
      const a = Dataset.fromNQuads(leanValue);
      const b = Dataset.fromNQuads(fstarValue);
      return {
        equal: await datasetsIsomorphic(a, b),
        method: 'rdfc1.0-isomorphism(serialize-as-nquads)',
      };
    } catch {
      // Not N-Quads/N-Triples-shaped text (e.g. Turtle/RDF-XML) -- no
      // isomorphism-aware parse available here; fall through to a
      // labelled strict-string comparison rather than guessing.
      return { equal: leanValue === fstarValue, method: 'strict-equality(non-nquads-text)' };
    }
  }
  const rdfField = RDF_TEXT_FIELD_HINT[fnName];
  if (rdfField && leanValue && fstarValue &&
      typeof leanValue[rdfField] === 'string' && typeof fstarValue[rdfField] === 'string') {
    const a = Dataset.fromNQuads(leanValue[rdfField]);
    const b = Dataset.fromNQuads(fstarValue[rdfField]);
    const dsEqual = await datasetsIsomorphic(a, b);
    const restEqual = shallowScalarEqual(omit(leanValue, rdfField), omit(fstarValue, rdfField));
    return { equal: dsEqual && restEqual, method: `rdfc1.0-isomorphism+scalar-fields(${rdfField})` };
  }
  const dsField = DATASET_FIELD_HINT[fnName];
  if (dsField && leanValue && fstarValue &&
      leanValue[dsField] instanceof Dataset && fstarValue[dsField] instanceof Dataset) {
    const dsEqual = await datasetsIsomorphic(leanValue[dsField], fstarValue[dsField]);
    const restEqual = shallowScalarEqual(omit(leanValue, dsField), omit(fstarValue, dsField));
    return { equal: dsEqual && restEqual, method: `rdfc1.0-isomorphism+scalar-fields(${dsField})` };
  }
  if (leanValue !== null && fstarValue !== null &&
      typeof leanValue === 'object' && typeof fstarValue === 'object') {
    return { equal: shallowScalarEqual(leanValue, fstarValue), method: 'structural-equality' };
  }
  return { equal: leanValue === fstarValue, method: 'strict-equality' };
}

// ---------------------------------------------------------------------
// The selector.
// ---------------------------------------------------------------------

/**
 * Create a backend selector instance (per-instance option; every
 * method also takes a trailing callOptions with a per-call {backend,
 * overrideFns} override -- the "at least the fn flavour" requirement).
 *
 * @param {object} [options]
 * @param {'lean'|'fstar'|'lean1st'|'fstar1st'|'slowcompareboth'} [options.backend='fstar1st']
 * @param {string[]} [options.overrideFns] lean1st only: function names
 *   to route to F* regardless of whether Lean implements them.
 */
function createSelector(options) {
  const opts = options || {};
  const defaultBackend = opts.backend || 'fstar1st';
  assertBackend(defaultBackend, 'createSelector');
  const defaultOverrideFns = new Set(opts.overrideFns || []);

  /**
   * Dispatch one call by function name. Returns:
   *   - {engine: 'lean'|'fstar', backend, value} for lean/fstar/lean1st/fstar1st
   *   - {engine: 'both', backend, agree, comparison, lean, fstar} for
   *     slowcompareboth (never thrown for a genuine disagreement --
   *     agree:false IS the reportable finding).
   * Throws (never falls back) when:
   *   - backend is 'lean'/'fstar' and that engine doesn't implement fnName;
   *   - backend is 'slowcompareboth' and EITHER engine doesn't implement
   *     fnName (nothing to compare -- use lean1st/fstar1st instead);
   *   - the underlying call itself throws on at least one side under
   *     slowcompareboth (a different failure mode from "disagreement":
   *     the thrown Error carries .lean/.fstar outcome records so both
   *     sides are still inspectable).
   */
  async function call(fnName, args, callOptions) {
    const co = callOptions || {};
    const backend = co.backend || defaultBackend;
    assertBackend(backend, `select.call('${fnName}')`);
    const overrideFns = co.overrideFns ? new Set(co.overrideFns) : defaultOverrideFns;

    if (backend === 'lean') {
      return { engine: 'lean', backend, value: await invoke('lean', fnName, args) };
    }
    if (backend === 'fstar') {
      return { engine: 'fstar', backend, value: await invoke('fstar', fnName, args) };
    }
    if (backend === 'lean1st') {
      if (!overrideFns.has(fnName) && await engineSupports(leanApi, fnName)) {
        return { engine: 'lean', backend, value: await invoke('lean', fnName, args) };
      }
      return { engine: 'fstar', backend, value: await invoke('fstar', fnName, args) };
    }
    if (backend === 'fstar1st') {
      if (!overrideFns.has(fnName) && await engineSupports(fstarApi, fnName)) {
        return { engine: 'fstar', backend, value: await invoke('fstar', fnName, args) };
      }
      return { engine: 'lean', backend, value: await invoke('lean', fnName, args) };
    }

    // slowcompareboth
    const [leanOk, fstarOk] = await Promise.all([
      engineSupports(leanApi, fnName), engineSupports(fstarApi, fnName),
    ]);
    if (!leanOk || !fstarOk) {
      throw new Error(
        `factoidal/select: slowcompareboth('${fnName}') needs BOTH engines to ` +
        `support the function (lean=${leanOk}, fstar=${fstarOk}); ` +
        "use backend 'lean1st' or 'fstar1st' to fall through instead.");
    }
    const [leanOutcome, fstarOutcome] = await Promise.allSettled([
      invoke('lean', fnName, args), invoke('fstar', fnName, args),
    ]);
    if (leanOutcome.status === 'rejected' || fstarOutcome.status === 'rejected') {
      const err = new Error(
        `factoidal/select: slowcompareboth('${fnName}') -- at least one engine's ` +
        'call threw (capability check passed, so this is an execution error, ' +
        'not a missing op); see .lean/.fstar for both outcomes.');
      err.engine = 'both';
      err.backend = 'slowcompareboth';
      err.agree = false;
      err.lean = leanOutcome.status === 'fulfilled'
        ? { ok: true, value: leanOutcome.value }
        : { ok: false, error: String((leanOutcome.reason && leanOutcome.reason.message) || leanOutcome.reason) };
      err.fstar = fstarOutcome.status === 'fulfilled'
        ? { ok: true, value: fstarOutcome.value }
        : { ok: false, error: String((fstarOutcome.reason && fstarOutcome.reason.message) || fstarOutcome.reason) };
      throw err;
    }
    const comparison = await compareValues(fnName, leanOutcome.value, fstarOutcome.value);
    return {
      engine: 'both',
      backend,
      agree: comparison.equal,
      comparison: { method: comparison.method },
      lean: leanOutcome.value,
      fstar: fstarOutcome.value,
    };
  }

  return {
    backend: defaultBackend,
    overrideFns: [...defaultOverrideFns],
    call,
    capabilityTable,
    // Named sugar over call() for the common typed-API functions --
    // the "fn flavour" per-call override: every one takes a trailing
    // {backend, overrideFns} that overrides this instance's default
    // for that one call only.
    parse: (text, parseOptions, callOptions) => call('parse', [text, parseOptions], callOptions),
    query: (data, sparql, queryOptions, callOptions) => call('query', [data, sparql, queryOptions], callOptions),
    update: (data, updateText, callOptions) => call('update', [data, updateText], callOptions),
    serialize: (data, serializeOptions, callOptions) => call('serialize', [data, serializeOptions], callOptions),
    canonicalize: (data, callOptions) => call('canonicalize', [data], callOptions),
    canonicalHash: (data, callOptions) => call('canonicalHash', [data], callOptions),
    graphs: (data, callOptions) => call('graphs', [data], callOptions),
    owlClosure: (data, mode, callOptions) => call('owlClosure', [data, mode], callOptions),
    owlIsConsistent: (data, owlOptions, callOptions) => call('owlIsConsistent', [data, owlOptions], callOptions),
    owlEntails: (premise, conclusion, owlOptions, callOptions) => call('owlEntails', [premise, conclusion, owlOptions], callOptions),
    coreRdfsClosure: (data, closureOptions, callOptions) => call('coreRdfsClosure', [data, closureOptions], callOptions),
    coreRdfsCheck: (data, closureOptions, callOptions) => call('coreRdfsCheck', [data, closureOptions], callOptions),
    rhoDfClosure: (data, closureOptions, callOptions) => call('rhoDfClosure', [data, closureOptions], callOptions),
    rhoDfFragmentCheck: (data, closureOptions, callOptions) => call('rhoDfFragmentCheck', [data, closureOptions], callOptions),
    rdfsPlusClosure: (data, closureOptions, callOptions) => call('rdfsPlusClosure', [data, closureOptions], callOptions),
    shaclValidate: (data, shapes, shaclOptions, callOptions) => call('shaclValidate', [data, shapes, shaclOptions], callOptions),
    shexValidate: (data, schema, focus, shape, callOptions) => call('shexValidate', [data, schema, focus, shape], callOptions),
    // Lean-only (see ALWAYS_IF_ENTRY's comment above): backend:'fstar'
    // throws, since index.js never exports clParse at all.
    clParse: (clifText, callOptions) => call('clParse', [clifText], callOptions),
    // Lean-only, same reason as clParse.
    clSerialize: (clifText, callOptions) => call('clSerialize', [clifText], callOptions),
    clAlphaNorm: (clifText, callOptions) => call('clAlphaNorm', [clifText], callOptions),
    clNormalize: (clifText, callOptions) => call('clNormalize', [clifText], callOptions),
    // clFiniteSat is intentionally NOT given named sugar here (owner
    // decision, 2026-08-26): deferred, reachable via call('clFiniteSat',
    // [interpJson, clifText], callOptions) instead. See ALWAYS_IF_ENTRY's
    // comment above.
  };
}

module.exports = {
  BACKENDS,
  ROUTABLE,
  createSelector,
  capabilityTable,
  engineSupports,
  compareValues,
};
