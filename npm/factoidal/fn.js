// factoidal/fn — a strictly functional dataset API.
//
// Every extracted engine operation is a value-to-value function (F*
// has no mutation to expose); RDF/JS DatasetCore's add/delete is
// wrapper-side skeuomorphism on top of that. This module makes the JS
// contract match the verified one: FnDataset is a frozen snapshot, all
// operations are free functions that return new values, and content
// identity (RDFC-1.0 canonical hash) is exposed as a first-class,
// memoized value so callers can build dataflow graphs that skip
// recompute when nothing actually changed.
//
// Design rationale, cost model, and the dataflow (cell/derive) pattern
// are documented in
// docs/designissues/2026-07-05-functional-dataset-api.md. Read that
// first if any decision below looks arbitrary — none of them are.
//
// This module is additive: it does not change rdfjs.js or lib/api.js.
// It wraps the already-built JS-engine api (./index.js) — no engine
// plumbing is forked here, only a frozen data shape and pure
// composition on top of it.

'use strict';

const crypto = require('node:crypto');

const engineApi = require('./index.js');
const {
  Dataset,
  dataFactory,
  quadToNQuads,
  quadsToNQuads,
} = require('./rdfjs.js');

// ---------------------------------------------------------------------
// FnDataset — a frozen snapshot of a quad set.
//
// Internal representation is exactly rdfjs.js's model (an array of
// already-frozen RDF/JS Quad terms) — the same representation
// lib/api.js's toDocs() already treats as the engine's interchange
// handle via toNQuads(). FnDataset adds nothing to that representation
// except: (a) freezing the wrapper itself so no method can mutate it,
// (b) de-duplication on construction so every FnDataset is a proper
// *set* of quads (no duplicate tokens), and (c) lazy, memoized
// derived values (raw N-Quads text, canonical hash) held in
// module-level WeakMaps rather than object fields — Object.freeze(ds)
// stays true for the whole lifetime of ds; the memo tables are a side
// channel, not a hole in the immutability contract.
// ---------------------------------------------------------------------

// ds (FnDataset) -> string, the cheap non-canonical N-Quads
// serialization. Computed once per instance, cached by identity.
const NQUADS_CACHE = new WeakMap();
// ds -> string (once settled) | Promise<string> (in flight), the
// RDFC-1.0 canonical N-Quads text. Shared with HASH_CACHE's input so
// two callers awaiting hash(ds) concurrently trigger one canonicalize
// call, not two.
const CANON_CACHE = new WeakMap();
// ds -> string (once settled) | Promise<string> (in flight), the
// sha256 hex digest of the canonical N-Quads text.
const HASH_CACHE = new WeakMap();

function assertFnDataset(v, who) {
  if (!(v instanceof FnDataset)) {
    throw new TypeError(`${who}: expected an FnDataset`);
  }
  return v;
}

// ---------------------------------------------------------------------
// Backend interface — capabilities-style, mirroring lib/api.js's
// `driver` shape (buildApi(driver) there; FnDataset(backend) here).
// FnDataset does NOT assume its representation is an in-memory quad
// array or an N-Quads string; it holds an opaque `_backend` satisfying
// this interface:
//
//   size               : number
//   quads()            : Iterable<Quad>   -- read access; may materialize
//   precomputedHash    : string | null    -- skip canonicalize() if set
//
// Exactly one backend exists today, arrayBackend, below. It exists so
// that a future on-disk (COTTAS) backend or a sidecar-hash backend can
// implement this same three-member interface without any free
// function in this module changing shape — see the design doc's
// "future backends" section for what those would look like and why
// filter()/mapQuads() below (which fully materialize via toArray())
// are the concrete piece of debt such a backend would need to repay
// with pushdown, not something this slice claims to have solved.
// ---------------------------------------------------------------------

function arrayBackend(quads) {
  return {
    kind: 'array',
    size: quads.length,
    quads: () => quads,
    precomputedHash: null,
  };
}

// Build a de-duplicated FnDataset from any iterable of RDF/JS quads.
// Every public constructor path (fromDataset, union, difference,
// filter, mapQuads, query's CONSTRUCT wrapping, builder().finish())
// funnels through this, so "FnDataset quads never repeat" is an
// invariant, not a hope. Always produces an arrayBackend today — a
// COTTAS-backed constructor would be a sibling entry point, not a
// change to this one.
function makeFnDataset(quadsIterable) {
  const seen = new Set();
  const out = [];
  for (const q of quadsIterable) {
    const frozen = dataFactory.fromQuad(q); // normalizes + (re)freezes
    const key = quadToNQuads(frozen);
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(frozen);
  }
  return new FnDataset(arrayBackend(Object.freeze(out)));
}

class FnDataset {
  /** @private use fromDataset/parse/union/... instead of `new`. */
  constructor(backend) {
    this._backend = backend;
    Object.freeze(this);
  }

  get size() {
    return this._backend.size;
  }

  [Symbol.iterator]() {
    return this._backend.quads()[Symbol.iterator]();
  }

  /** A fresh array of this dataset's (frozen) quads. Materializes. */
  toArray() {
    return [...this._backend.quads()];
  }

  /**
   * Raw N-Quads text, arrival order, not canonicalized. Cheap (pure
   * JS serialization, no engine round-trip) for the array backend;
   * memoized. This is *identity-adjacent*, not identity — two
   * isomorphic datasets with different blank-node labels serialize to
   * different text here. Use hash()/canonicalize() for
   * label-independent identity.
   */
  toNQuads() {
    let cached = NQUADS_CACHE.get(this);
    if (cached === undefined) {
      cached = quadsToNQuads(this.toArray());
      NQUADS_CACHE.set(this, cached);
    }
    return cached;
  }

  /** Read-only quad-pattern match (RDF/JS DatasetCore shape), no engine call. */
  match(subject, predicate, object, graph) {
    return makeFnDataset(this.toArray().filter((q) =>
      (!subject || subject.equals(q.subject)) &&
      (!predicate || predicate.equals(q.predicate)) &&
      (!object || object.equals(q.object)) &&
      (!graph || graph.equals(q.graph))));
  }
}

/** The empty dataset — the identity element for union() and difference(). */
const EMPTY = new FnDataset(arrayBackend(Object.freeze([])));

// ---------------------------------------------------------------------
// Interop with the mutable RDF/JS layer.
// ---------------------------------------------------------------------

/** Snapshot a (possibly mutable) RDF/JS Dataset into an FnDataset. */
function fromDataset(dataset) {
  if (!(dataset instanceof Dataset)) {
    throw new TypeError('fromDataset: expected an RDF/JS Dataset');
  }
  return makeFnDataset(dataset);
}

/** Materialize an FnDataset into a fresh, independently-mutable Dataset. */
function toDataset(ds) {
  assertFnDataset(ds, 'toDataset');
  return new Dataset(ds.toArray());
}

// ---------------------------------------------------------------------
// Streaming seam: builder() / fromChunks().
//
// This module's `parse()` needs the whole document as one string
// (mirroring index.js's parse()); a future streaming RDF parser would
// instead produce quads incrementally, batch by batch, without ever
// holding the whole document in memory at once. builder() is the
// intended integration point for that: a mutable accumulator that
// FINALIZES into a frozen FnDataset. Everything upstream of finish()
// (a hypothetical streaming Turtle/N-Quads reader feeding addChunk()
// per parsed batch) is not part of this slice; everything downstream —
// every op in this module — only ever sees the finished, immutable
// value finish() returns, never the accumulator itself. The
// implementation below is deliberately the trivial in-memory case
// (accumulate an array, dedup once at finish()); it exists so the
// call shape is settled before a real streaming parser exists.
// ---------------------------------------------------------------------

/**
 * A mutable accumulator for incrementally-arriving quads. addChunk()
 * accepts one quad or an iterable of quads (so a parser can hand over
 * whatever batch size is convenient); finish() de-duplicates once and
 * returns a frozen FnDataset. Calling either method after finish() throws.
 */
function builder() {
  let pending = [];
  let finished = false;
  return {
    addChunk(chunk) {
      if (finished) throw new Error('builder: addChunk() called after finish()');
      if (chunk && typeof chunk.termType === 'string') {
        pending.push(chunk); // a single Quad
      } else {
        for (const q of chunk) pending.push(q); // an iterable of Quads
      }
    },
    finish() {
      if (finished) throw new Error('builder: finish() already called');
      finished = true;
      const result = makeFnDataset(pending);
      pending = null; // release; no further mutation is possible anyway
      return result;
    },
  };
}

/**
 * Sugar over builder(): consume a (sync or async) iterable of chunks
 * into one finished FnDataset. A streaming parser exposing an async
 * iterator of quad batches plugs in here directly.
 */
async function fromChunks(chunks) {
  const b = builder();
  for await (const chunk of chunks) b.addChunk(chunk);
  return b.finish();
}

// ---------------------------------------------------------------------
// Parsing, algebra, query — all free functions.
// ---------------------------------------------------------------------

/** Parse one RDF document into an FnDataset. Mirrors index.js's parse(). */
async function parse(text, options) {
  return fromDataset(await engineApi.parse(text, options));
}

/** Set union, first-seen order (a's quads, then b's not already present). */
function union(a, b) {
  assertFnDataset(a, 'union'); assertFnDataset(b, 'union');
  return makeFnDataset([...a, ...b]);
}

/** Quads in a that are not in b. */
function difference(a, b) {
  assertFnDataset(a, 'difference'); assertFnDataset(b, 'difference');
  const bKeys = new Set(b.toArray().map(quadToNQuads));
  return makeFnDataset(a.toArray().filter((q) => !bKeys.has(quadToNQuads(q))));
}

/** Keep quads matching quadPred(quad) => boolean. */
function filter(ds, quadPred) {
  assertFnDataset(ds, 'filter');
  if (typeof quadPred !== 'function') {
    throw new TypeError('filter: quadPred must be a function');
  }
  // A subset of an already-deduplicated set has no new duplicates to
  // remove; still normalize each quad for the frozen-terms guarantee.
  return new FnDataset(arrayBackend(Object.freeze(
    ds.toArray().filter(quadPred).map((q) => dataFactory.fromQuad(q)))));
}

/**
 * Transform every quad with f(quad) => quad. Output is re-deduplicated
 * (mapQuads can collapse distinct inputs onto the same output quad —
 * e.g. a rename that merges two subjects — and FnDataset is always a
 * set, never a multiset).
 */
function mapQuads(ds, f) {
  assertFnDataset(ds, 'mapQuads');
  if (typeof f !== 'function') {
    throw new TypeError('mapQuads: f must be a function');
  }
  return makeFnDataset(ds.toArray().map(f));
}

/**
 * Run a SPARQL 1.1 query. SELECT -> Bindings[]; ASK -> boolean;
 * CONSTRUCT -> FnDataset. Delegates entirely to index.js's query() —
 * same capability gating (CONSTRUCT needs the npm-entry bundle; its
 * absence throws the existing "pending npm-entry build" Error).
 */
async function query(ds, sparql, options) {
  assertFnDataset(ds, 'query');
  const result = await engineApi.query(toDataset(ds), sparql, options);
  return result instanceof Dataset ? fromDataset(result) : result;
}

/**
 * Materialize an entailment closure as a new FnDataset.
 *
 * Reuses query()'s existing entailment support rather than adding new
 * engine plumbing — but *not* via CONSTRUCT: the npm-entry ABI's
 * queryDataset has no entailment parameter (entailment closure stays
 * on the CLI path, per lib/api.js), and the CLI path does not support
 * CONSTRUCT at all, so "CONSTRUCT ... WHERE ... { entail }" is not
 * reachable through the existing API today. Instead this runs
 * `SELECT ?s ?p ?o WHERE { ?s ?p ?o }` with the entailment option
 * (exactly the combination test/api.test.js's "query: entail RDFS
 * infers subclass instances" already exercises) and repackages each
 * solution row as a quad — pure JS reshaping of already-materialized
 * bindings, not new RDF/SPARQL semantics, so it works with the CLI
 * bundle alone (no npm-entry bundle required).
 *
 * Scope limitation (documented, not silent): like a bare
 * `WHERE { ?s ?p ?o }` in SPARQL generally, this closes over the
 * *default graph* only — named-graph triples are not restated. A
 * named-graph-aware entail() would need `GRAPH ?g { ?s ?p ?o }` and
 * per-graph closure semantics that the underlying query() does not
 * define today.
 */
// Case-insensitive regime aliases ('rdfs', 'owl-rl', 'owlrl', 'owl_rl')
// normalized to the engine's exact-case ENTAIL_VALUES spelling ('RDFS',
// 'OWL-RL'); anything else (including already-correct casing, or a
// genuinely invalid value) passes through unchanged so engineApi.query's
// own validation reports the honest error rather than this function
// guessing at what the caller meant.
const ENTAIL_REGIME_ALIASES = {
  none: 'none', rdfs: 'RDFS', 'owl-rl': 'OWL-RL', owlrl: 'OWL-RL', owl_rl: 'OWL-RL',
};

function normalizeEntailRegime(regime) {
  const key = String(regime == null ? 'none' : regime).toLowerCase();
  return ENTAIL_REGIME_ALIASES[key] || regime;
}

// x-ikl-* is withheld from the npm API by OWNER DECISION, 2026-08-26
// (https://github.com/danbri/factoidal/issues/618): IKL has no notion
// of shapes or named profiles, so an x-ikl-<suffix> entailment-regime
// family invents a taxonomy the specification does not have.
// engineApi.query() (lib/api.js) already rejects this, but
// normalizeEntailRegime() above passes any unrecognised string through
// UNCHANGED before it gets there — check explicitly here too, so this
// function's own contract states the rule rather than depending on a
// downstream check someone could relax without noticing this call
// site. Case-insensitive, any suffix; see test/select.test.js.
function rejectIklRegime(regime, who) {
  if (regime != null && /^x-ikl/i.test(String(regime))) {
    throw new TypeError(
      `${who}: entail '${regime}' is not exposed through the npm API -- ` +
      'the x-ikl-* entailment regimes are not exposed through the ' +
      'npm API (owner decision 2026-08-26, danbri/factoidal#618); ' +
      'the Lean engine no longer defines the family either ' +
      '(danbri/factoidal#626).');
  }
}

async function entail(ds, regime) {
  assertFnDataset(ds, 'entail');
  rejectIklRegime(regime, 'entail');
  const rows = await engineApi.query(
    toDataset(ds), 'SELECT ?s ?p ?o WHERE { ?s ?p ?o }',
    { entail: normalizeEntailRegime(regime) });
  return makeFnDataset(
    rows.map((row) => dataFactory.quad(row.get('s'), row.get('p'), row.get('o'))));
}

/**
 * SHACL Core validation. Needs the npm-entry engine bundle. Neither
 * argument is mutated or consumed -- both stay valid FnDatasets after
 * the call, same as every other op in this module.
 *
 * @param {FnDataset} ds the data graph
 * @param {FnDataset} shapes the shapes graph
 * @returns {Promise<{conforms: boolean, report: FnDataset}>} report is
 *   SHACL_Validation.validation_report_to_graph's graph (sh:conforms +
 *   one sh:ValidationResult per violation).
 */
async function validate(ds, shapes) {
  assertFnDataset(ds, 'validate');
  assertFnDataset(shapes, 'validate');
  const r = await engineApi.shaclValidate(toDataset(ds), toDataset(shapes));
  return { conforms: r.conforms, report: fromDataset(r.report) };
}

/**
 * ShEx (Shape Expressions) validation of one focus node against one
 * shape. Needs the npm-entry engine bundle.
 *
 * @param {FnDataset} ds the data graph
 * @param {string} schema ShExJ (JSON Schema form), as text
 * @param {string|{termType,value}} focus an IRI, "_:label", or an
 *   RDF/JS NamedNode/BlankNode term
 * @param {string|{termType,value}|null} [shape] a shape label; omit/
 *   null to validate against the schema's own `start`
 * @returns {Promise<boolean|null>} null means "deferred" -- outside
 *   this engine's decidable ShEx fragment, never a guessed answer.
 */
async function shex(ds, schema, focus, shape) {
  assertFnDataset(ds, 'shex');
  return engineApi.shexValidate(toDataset(ds), schema, focus, shape);
}

/**
 * Evaluate an RML mapping graph against one logical source's raw
 * data, materializing the generated triples as a new FnDataset. Needs
 * the npm-entry engine bundle. Scope cut (documented, not silent):
 * every triples map in `mapping` reads the SAME `source` -- joins
 * across two different logical sources are not reachable through this
 * one-source entry point (see engineApi.rmlMap's doc comment).
 *
 * @param {FnDataset} mapping the RML mapping graph
 * @param {string} source raw JSON or CSV text (not RDF)
 * @param {'json'|'csv'} kind
 * @returns {Promise<FnDataset>}
 */
async function fromMapping(mapping, source, kind) {
  assertFnDataset(mapping, 'fromMapping');
  return fromDataset(await engineApi.rmlMap(toDataset(mapping), source, kind));
}

/**
 * CSVW csv2rdf conversion (w3.org/TR/csv2rdf): convert raw tabular
 * data plus an optional CSVW metadata document into a new FnDataset.
 * Needs the npm-entry engine bundle. Unlike fromMapping there is no
 * FnDataset input -- both arguments are raw text (CSVW's metadata
 * format is JSON, not RDF). Scope cut (documented, not silent --
 * mirrors fromMapping's one-source cut): every table in a multi-table
 * `tables` group reads the SAME `csv` text. Datatype `format` facets,
 * list-valued (`separator`) cells, and full inherited-property
 * propagation are not yet implemented -- see engineApi.csvwToRdf's
 * doc comment and the CSVW program plan for measured coverage.
 *
 * @param {string} csv raw RFC 4180 tabular data (not RDF)
 * @param {string} [metadata] CSVW metadata document (JSON text);
 *   '' / omitted infers the schema from the CSV's own header row
 * @param {{mode?: 'standard'|'minimal', base?: string, url?: string}}
 *   [options] see engineApi.csvwToRdf
 * @returns {Promise<FnDataset>}
 */
async function fromCsvw(csv, metadata, options) {
  return fromDataset(await engineApi.csvwToRdf(csv, metadata, options));
}

/**
 * RIF Core forward-chaining saturation, materialized as a new
 * FnDataset (input triples + derived triples, default graph only --
 * RIF Core has no named-graph notion). Needs the npm-entry engine
 * bundle.
 *
 * @param {FnDataset} ds the premise graph
 * @param {string} rules a RIF Core XML rule document
 * @returns {Promise<FnDataset>}
 */
async function rif(ds, rules) {
  assertFnDataset(ds, 'rif');
  return fromDataset(await engineApi.rifEval(toDataset(ds), rules));
}

/**
 * The CERTIFIED core-RDFS closure
 * (formal/fstar/RDF.Entailment.RDFS.RhoDFClosure.fst's
 * `rho_df_closure`): rdfs2/3/5/7/9/11 only, with the machine-checked
 * decides-iff (docs/theorem-registry.md). "corerdfs" is this project's
 * API name for the fragment the literature calls ρdf —
 * subPropertyOf/subClassOf/type/domain/range (Muñoz, Pérez &
 * Gutierrez, "Simple and Efficient Minimal RDFS", J. Web Semantics
 * 7(3), 2009). Mirrors engineApi.coreRdfsClosure's `{ok, ntriples}`
 * result, with `ntriples` parsed into an FnDataset via
 * Dataset.fromNQuads — pure JS, no extra engine round-trip. Needs the
 * npm-entry engine bundle. `rhoDfClosure` is kept below as a
 * literature-name alias.
 * @param {FnDataset} ds
 * @param {{format?: string}} [options]
 * @returns {Promise<{ok: boolean, dataset: FnDataset}>}
 */
async function coreRdfsClosure(ds, options) {
  assertFnDataset(ds, 'coreRdfsClosure');
  const r = await engineApi.coreRdfsClosure(toDataset(ds), options);
  return { ok: r.ok, dataset: fromDataset(Dataset.fromNQuads(r.ntriples)) };
}
/** Literature-name alias for coreRdfsClosure (ρdf; see above). */
const rhoDfClosure = coreRdfsClosure;

/**
 * Decidable core-RDFS fragment check (`is_rho_df_frag`, tied by an F*
 * lemma to the prop the regime theorems quantify over): does the
 * certified coreRdfsClosure guarantee apply to `ds`? Needs the
 * npm-entry engine bundle. `rhoDfFragmentCheck` is kept below as a
 * literature-name alias.
 * @param {FnDataset} ds
 * @param {{format?: string}} [options]
 * @returns {Promise<{ok: boolean, fragment: boolean}>}
 */
async function coreRdfsCheck(ds, options) {
  assertFnDataset(ds, 'coreRdfsCheck');
  return engineApi.coreRdfsCheck(toDataset(ds), options);
}
/** Literature-name alias for coreRdfsCheck (ρdf; see above). */
const rhoDfFragmentCheck = coreRdfsCheck;

/**
 * RDFS-Plus closure (RDF.Entailment.RDFSPlus.fst's
 * `rdfs_plus_closure`): the full RDFS step plus the practical OWL
 * subset — owl:sameAs, owl:inverseOf, Symmetric/Transitive/Functional/
 * InverseFunctionalProperty, equivalentClass/Property ("RDFS-Plus",
 * Allemang & Hendler 2008; "RDFS++", AllegroGraph). Every OWL row
 * carries a proved licensing + truth lemma; no chain-level
 * completeness claim (theorem registry) — weaker than
 * coreRdfsClosure's decides-iff guarantee. Needs the npm-entry engine
 * bundle.
 * @param {FnDataset} ds
 * @param {{format?: string}} [options]
 * @returns {Promise<{ok: boolean, dataset: FnDataset, rounds: number}>}
 */
async function rdfsPlusClosure(ds, options) {
  assertFnDataset(ds, 'rdfsPlusClosure');
  const r = await engineApi.rdfsPlusClosure(toDataset(ds), options);
  return {
    ok: r.ok,
    dataset: fromDataset(Dataset.fromNQuads(r.ntriples)),
    rounds: r.rounds,
  };
}

/**
 * OWL tableau materialisation (formal/fstar/Tableau.fst's
 * `tableau_materialise`): add `i rdf:type <ClassExpression>` for every
 * individual the model-construction reasoner proves is a member of an
 * OWL class expression (someValuesFrom / hasValue / unionOf /
 * intersectionOf, and the named class an equivalentClass restriction
 * defines). Needs the npm-entry engine bundle. Default graph only.
 *
 * @param {FnDataset} ds the ontology + ABox graph
 * @returns {Promise<{dataset: FnDataset, addedCount: number}>} dataset
 *   is input + tableau-derived triples; addedCount is how many the
 *   tableau added.
 */
async function tableauMaterialise(ds) {
  assertFnDataset(ds, 'tableauMaterialise');
  const r = await engineApi.tableauMaterialise(toDataset(ds));
  return { dataset: fromDataset(r.dataset), addedCount: r.addedCount };
}

/**
 * OWL DL inconsistency verdict (bin/owl-runner's DL pipeline: OWL-RL
 * closure -> tableau materialise -> OWL-RL closure -> is_inconsistent).
 * `rlAlone` is the plain OWL-RL verdict on the same input, so a caller
 * can see the cases the tableau adds. Needs the npm-entry engine
 * bundle. Default graph only.
 *
 * @param {FnDataset} ds the ontology + ABox graph
 * @returns {Promise<{inconsistent: boolean, rlAlone: boolean}>}
 */
async function tableauDlInconsistent(ds) {
  assertFnDataset(ds, 'tableauDlInconsistent');
  return engineApi.tableauDlInconsistent(toDataset(ds));
}

/**
 * OWL DL consistency verdict via the verified clash-detecting tableau
 * (formal/fstar/Tableau.Refute.fst's `tableau_consistent` over the
 * OWL-RL closure -- the pure verified chain bin/owl-runner runs under
 * `--regime dl`, minus its native-only z3 oracle). Needs the npm-entry
 * bundle. Default graph only.
 *
 * `consistent` is three-valued: `false` (a clash on every tableau
 * branch), `true` (a model was constructed), or `null` -- the refuter
 * exhausted its fuel budget before deciding, with `reason` naming the
 * cap. `null` is never collapsed to `false`.
 *
 * @param {FnDataset|string} ontology the ontology + ABox graph -- an
 *   FnDataset, or raw RDF text (Turtle by default, per `options.format`)
 * @param {{format?: string, fuel?: number|string}} [options]
 * @returns {Promise<{consistent: boolean|null, reason?: string}>}
 */
async function owlIsConsistent(ontology, options) {
  const data = ontology instanceof FnDataset ? toDataset(ontology) : ontology;
  return engineApi.owlIsConsistent(data, options);
}

/**
 * OWL entailment check: does `premise` entail `conclusion`? Verified
 * two-path dispatch (`via: "closure"` for the OWL-RL closure path,
 * `via: "refutation"` for negate-and-refute), mirroring bin/owl-runner.
 * Needs the npm-entry bundle. Default graph only. `entailed` is
 * three-valued (`true` / `false` / `null` budget-out, `reason` names the
 * cap).
 *
 * @param {FnDataset|string} premise an FnDataset or raw RDF text
 * @param {FnDataset|string} conclusion an FnDataset or raw RDF text
 * @param {{format?: string, fuel?: number|string}} [options]
 * @returns {Promise<{entailed: boolean|null, via: 'closure'|'refutation', reason?: string}>}
 */
async function owlEntails(premise, conclusion, options) {
  const p = premise instanceof FnDataset ? toDataset(premise) : premise;
  const c = conclusion instanceof FnDataset ? toDataset(conclusion) : conclusion;
  return engineApi.owlEntails(p, c, options);
}

/**
 * RDFC-1.0 canonicalization: canonical N-Quads text. Needs the
 * npm-entry bundle (same gating as index.js's canonicalize()).
 */
async function canonicalize(ds) {
  assertFnDataset(ds, 'canonicalize');
  let cached = CANON_CACHE.get(ds);
  if (cached === undefined) {
    const p = engineApi.canonicalize(toDataset(ds)).then((text) => {
      CANON_CACHE.set(ds, text); // replace the in-flight promise
      return text;
    });
    CANON_CACHE.set(ds, p);
    cached = p;
  }
  return cached;
}

/**
 * sha256 hex digest of canonicalize(ds). O(n log n) once (the
 * canonicalization cost — see the design doc's cost model) and O(1)
 * on every call after, memoized by FnDataset identity in a
 * module-level WeakMap so the frozen object itself never changes.
 * Concurrent callers before the first result lands share one
 * in-flight computation.
 *
 * Backend hook: if `ds`'s backend already carries a
 * `precomputedHash` (e.g. a COTTAS backend reading a `.c14n.sha256`
 * sidecar — see the design doc's "future backends" section), that
 * value is returned directly and canonicalize() is never called. The
 * array backend never sets this, so today this is always a live
 * computation; the check exists so a future backend gets the
 * shortcut for free, without hash()'s callers changing.
 */
async function hash(ds) {
  assertFnDataset(ds, 'hash');
  if (ds._backend.precomputedHash) return ds._backend.precomputedHash;
  const cached = HASH_CACHE.get(ds);
  if (typeof cached === 'string') return cached;
  if (cached) return cached; // already in flight
  const p = canonicalize(ds).then((canon) => {
    const hex = crypto.createHash('sha256').update(canon, 'utf8')
      .digest('hex');
    HASH_CACHE.set(ds, hex); // replace the in-flight promise
    return hex;
  });
  HASH_CACHE.set(ds, p);
  return p;
}

/** Already-settled hash, if any (including a backend's precomputedHash) — never triggers computation. */
function peekHash(ds) {
  if (ds._backend.precomputedHash) return ds._backend.precomputedHash;
  const c = HASH_CACHE.get(ds);
  return typeof c === 'string' ? c : null;
}

function hasBlankNode(ds) {
  for (const q of ds) {
    if (q.subject.termType === 'BlankNode') return true;
    if (q.object.termType === 'BlankNode') return true;
    if (q.graph.termType === 'BlankNode') return true;
  }
  return false;
}

/**
 * Structural equality, cheapest-correct-path first (see the design
 * doc's cost model section for the full argument):
 *
 *  1. Different sizes -> not equal, O(1).
 *  2. Both sides already have a memoized hash -> compare those, O(1).
 *  3. Exact quad-set match (same terms, same labels) -> equal, O(n).
 *     This is sound regardless of blank nodes: identical tokens can
 *     never be a false positive.
 *  4. No blank nodes anywhere -> the step-3 negative is authoritative
 *     (ground quads have no relabeling to hide behind) -> not equal.
 *  5. Otherwise (blank nodes present, step 3 was inconclusive) ->
 *     the only sound test left is RDFC-1.0 canonical-hash equality,
 *     which is exactly the O(n log n) canonicalize() cost this module
 *     tries to avoid paying twice.
 */
async function equals(a, b) {
  assertFnDataset(a, 'equals'); assertFnDataset(b, 'equals');
  if (a === b) return true;
  if (a.size !== b.size) return false;
  const ha = peekHash(a);
  const hb = peekHash(b);
  if (ha !== null && hb !== null) return ha === hb;
  const aKeys = new Set(a.toArray().map(quadToNQuads));
  const bTokens = b.toArray().map(quadToNQuads);
  const exact = bTokens.length === aKeys.size &&
    bTokens.every((t) => aKeys.has(t));
  if (exact) return true;
  if (!hasBlankNode(a) && !hasBlankNode(b)) return false;
  const [h1, h2] = await Promise.all([hash(a), hash(b)]);
  return h1 === h2;
}

/**
 * Open a COTTAS/Parquet artifact's raw bytes as a queryable, read-only
 * store (docs/designissues/2026-07-06-inmemory-bytes-store.md, browser
 * call site). Needs the npm-entry engine bundle. Unlike every other
 * constructor in this module, the returned object is NOT an FnDataset:
 * the whole point of the design is that rows decode lazily as a query
 * touches them, never materializing the corpus into heap FnDataset
 * quads (measured 64-161 B/quad vs. an FnDataset/heap Dataset's
 * ~877 B/quad for the same data, in the design doc's native numbers).
 *
 * @param {string|Uint8Array|ArrayBuffer} bytes whole `.cottas` file contents
 * @returns {Promise<{handle: string,
 *   query: (sparql: string) => Promise<Array<Map<string,object>>|boolean|FnDataset>,
 *   close: () => Promise<void>}>}
 *   query() divergences from fn.query() (documented, not silent): no
 *   entail option, no write/--delta-log overlay (read-only), and a
 *   query shape the backend executor can't push down rejects instead
 *   of silently falling back to a full materialize (see
 *   engineApi.queryCottas's doc comment). CONSTRUCT still returns an
 *   FnDataset (materialized once for that query only).
 */
async function openCottas(bytes) {
  const handle = await engineApi.openCottas(bytes);
  let closed = false;
  return {
    handle,
    async query(sparql) {
      if (closed) throw new Error('openCottas store: query() called after close()');
      const result = await engineApi.queryCottas(handle, sparql);
      return result instanceof Dataset ? fromDataset(result) : result;
    },
    async close() {
      if (closed) return;
      closed = true;
      await engineApi.closeCottas(handle);
    },
  };
}

/**
 * Serialize an FnDataset to COTTAS/Parquet bytes via the native writer
 * (the same pure `Tot` F* function `factoidal compact --native-writer`
 * uses). Needs the npm-entry engine bundle. Round-trips through
 * openCottas(): feeding the result straight back into openCottas()
 * reproduces the same queryable store.
 *
 * @param {FnDataset} ds
 * @returns {Promise<Uint8Array>}
 */
async function toCottas(ds) {
  assertFnDataset(ds, 'toCottas');
  return engineApi.toCottas(toDataset(ds));
}

/**
 * Enumerate named graphs (default graph excluded), first-seen order.
 * Reuses index.js's graphs() enumeration; wraps each per-graph
 * Dataset back into an FnDataset.
 */
function graphs(ds) {
  assertFnDataset(ds, 'graphs');
  return engineApi.graphs(toDataset(ds))
    .map(([iri, graphDataset]) => [iri, fromDataset(graphDataset)]);
}

// ---------------------------------------------------------------------
// Dataflow seed: cell (mutable input slot) + derive (hash-keyed,
// memoized pure recompute). Deliberately tiny and dependency-free —
// see the design doc's §"dataflow pattern" for the worked example
// this is extracted from.
// ---------------------------------------------------------------------

/** A minimal mutable box holding one dataflow input value. */
function cell(initial) {
  let value = initial;
  return {
    get: () => value,
    set(v) { value = v; },
  };
}

// A dataflow value's recompute key: FnDataset content-hash for
// datasets (so two different FnDataset objects with the same content
// count as "unchanged"), the value itself otherwise (primitives
// compare by ===, which is exactly what a dataflow graph needs for
// non-dataset inputs like a SPARQL string or a numeric parameter).
async function keyOf(value) {
  return value instanceof FnDataset ? hash(value) : value;
}

/**
 * A derived dataflow node: recomputes fn(...inputCells.map(c=>c.get()))
 * only when at least one input's content-key has changed since the
 * last .get(). First call always computes (there is no prior key to
 * compare against).
 */
function derive(fn, ...inputCells) {
  let lastKeys = null;
  let lastResult;
  return {
    async get() {
      const values = inputCells.map((c) => c.get());
      const keys = await Promise.all(values.map(keyOf));
      if (lastKeys && keys.length === lastKeys.length &&
          keys.every((k, i) => k === lastKeys[i])) {
        return lastResult; // skip recompute — nothing actually changed
      }
      lastResult = await fn(...values);
      lastKeys = keys;
      return lastResult;
    },
  };
}

/**
 * Left-to-right function composition for Observable-style dataflow.
 * `pipe(f, g, h)(x)` is `h(g(f(x)))`, awaiting any step that returns a
 * Promise, so async engine functions (query, entail, xsltTransform, ...)
 * compose with sync ones without the caller threading awaits. With no
 * functions it is the identity. Every step must be a function.
 * @param {...Function} fns
 * @returns {(input: any) => Promise<any>}
 */
function pipe(...fns) {
  for (const f of fns) {
    if (typeof f !== 'function') {
      throw new TypeError('pipe: every argument must be a function');
    }
  }
  return async (input) => {
    let value = input;
    for (const f of fns) {
      value = await f(value);
    }
    return value;
  };
}

// -----------------------------------------------------------------
// Typed engine functions (#74). Re-exported unchanged from the JS
// engine api — each is already a pure, value-in / value-out function
// over one F*-extracted engine (XSLT, MathML, XForms, JSON Schema,
// Schematron, TOAN CAS, matrix algebra), so they belong in the
// functional surface as-is. See index.d.ts / fn.d.ts for signatures.
// -----------------------------------------------------------------
const {
  xsltTransform,
  mathmlEval,
  xformsRecalc,
  jsonSchemaValidate,
  schematronValidate,
  toanSummation,
  toanProduct,
  toanSimplify,
  toanDiff,
  toanSubst,
  matrixDeterminant,
  matrixScalarProduct,
  matrixVectorProduct,
  matrixOuterProduct,
  sigmoidPoints,
  sigmoidFormulaMathml,
  vcSha256Hex,
  vcEd25519SecretToPublic,
  vcEd25519Sign,
  vcEd25519Verify,
  vcEddsaCreateFromCanonical,
  vcEddsaVerifyFromCanonical,
  queryHdt,
} = engineApi;

module.exports = {
  FnDataset,
  EMPTY,
  fromDataset,
  toDataset,
  builder,
  fromChunks,
  parse,
  union,
  difference,
  filter,
  mapQuads,
  query,
  entail,
  validate,
  shex,
  fromMapping,
  fromCsvw,
  rif,
  coreRdfsClosure,
  coreRdfsCheck,
  rhoDfClosure,
  rhoDfFragmentCheck,
  rdfsPlusClosure,
  tableauMaterialise,
  tableauDlInconsistent,
  owlIsConsistent,
  owlEntails,
  canonicalize,
  hash,
  equals,
  openCottas,
  toCottas,
  graphs,
  cell,
  derive,
  pipe,
  // Typed engine functions (#74 FP surface).
  xsltTransform,
  mathmlEval,
  xformsRecalc,
  jsonSchemaValidate,
  schematronValidate,
  toanSummation,
  toanProduct,
  toanSimplify,
  toanDiff,
  toanSubst,
  matrixDeterminant,
  matrixScalarProduct,
  matrixVectorProduct,
  matrixOuterProduct,
  sigmoidPoints,
  sigmoidFormulaMathml,
  vcSha256Hex,
  vcEd25519SecretToPublic,
  vcEd25519Sign,
  vcEd25519Verify,
  vcEddsaCreateFromCanonical,
  vcEddsaVerifyFromCanonical,
  queryHdt,
  capabilities: engineApi.capabilities,
};
