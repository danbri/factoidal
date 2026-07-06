// factoidal — public API layer, shared by index.js (js_of_ocaml) and
// wasm.js (wasm_of_ocaml).
//
// Two ways to reach the engine, tried in order:
//
//   1. The npm-entry ABI bundle (factoidal-npm-entry.js /
//      factoidal-npm-entry.wasm.js — built from bin/npm-entry/
//      entry_jsoo.ml). A persistent, function-call ABI: strings in,
//      JSON out. Supports everything including CONSTRUCT, UPDATE and
//      RDFC-1.0 canonicalization.
//
//   2. The single-shot CLI bundle (factoidal.js / factoidal.wasm.js),
//      driven argv-style via lib/engine-js.js / lib/engine-wasm.js.
//      Covers parse / SELECT / ASK / serialize today; CONSTRUCT and
//      UPDATE are not reachable through the CLI surface, and
//      canonicalize requires a bundle built after the `factoidal
//      canonicalize` subcommand landed.
//
// Operations that need the npm-entry bundle throw an Error whose
// message contains "pending npm-entry build" when only the CLI bundle
// is available. All semantic work happens inside the F*-extracted
// engine either way; this layer only shapes arguments and results.

'use strict';

const {
  Dataset,
  dataFactory,
  termFromSrj,
} = require('../rdfjs.js');

const DATA_FORMAT_EXT = {
  turtle:    'ttl',
  ttl:       'ttl',
  ntriples:  'nt',
  nt:        'nt',
  nquads:    'nq',
  nq:        'nq',
  trig:      'trig',
  rdfxml:    'rdf',
  'rdf-xml': 'rdf',
  rdf:       'rdf',
  jsonld:    'jsonld',
  'json-ld': 'jsonld',
};

// Canonical format tag for the npm-entry ABI (RDF_Format.format_of_string
// accepts these names directly).
const DATA_FORMAT_TAG = {
  ttl: 'turtle', nt: 'ntriples', nq: 'nquads', trig: 'trig', rdf: 'rdfxml',
  jsonld: 'jsonld',
};

const ENTAIL_VALUES = new Set(['none', 'RDFS', 'OWL-RL']);

function extForFormat(fmt) {
  const key = String(fmt || 'turtle').toLowerCase();
  if (!(key in DATA_FORMAT_EXT)) {
    throw new TypeError(
      `Unknown format '${fmt}'. Expected one of: ` +
      Object.keys(DATA_FORMAT_EXT).join(', ')
    );
  }
  return DATA_FORMAT_EXT[key];
}

function engineError(prefix, res) {
  const msg = (res.stderr || res.stdout ||
    `factoidal exited with code ${res.exitCode}`).trim();
  const err = new Error(`${prefix}: ${msg}`);
  err.exitCode = res.exitCode;
  err.stderr = res.stderr;
  err.stdout = res.stdout;
  return err;
}

function pendingError(what) {
  return new Error(
    `${what} needs the factoidal-npm-entry bundle, which is not present ` +
    '— pending npm-entry build (formal/fstar/build-ocaml.sh js + npm ' +
    'with bin/npm-entry/entry_jsoo.ml wired in; see bin/npm-entry/README.md).'
  );
}

// Extract the JSON object from CLI stdout defensively (a stray line
// must not break the parse).
function jsonFromStdout(stdout, what) {
  const first = stdout.indexOf('{');
  const last = stdout.lastIndexOf('}');
  if (first < 0 || last < first) {
    const err = new Error(`${what}: engine did not produce JSON: ${stdout}`);
    err.stdout = stdout;
    throw err;
  }
  return JSON.parse(stdout.slice(first, last + 1));
}

// Detect the query form for result-shape dispatch. IRIs and comments
// are blanked first so '#' inside a PREFIX IRI cannot hide the verb.
// The engine's SPARQL parser remains the authority — this only picks
// the output shape.
function sniffQueryForm(sparql) {
  const cleaned = String(sparql)
    .replace(/<[^>]*>/g, ' ')
    .replace(/#[^\n]*/g, ' ');
  const m = cleaned.match(/\b(select|ask|construct|describe)\b/i);
  return m ? m[1].toLowerCase() : 'select';
}

// SRJ bindings -> Array<Map<string, Term>>
function bindingsFromSrj(srj) {
  const rows = (srj && srj.results && srj.results.bindings) || [];
  return rows.map((row) => {
    const map = new Map();
    for (const [name, term] of Object.entries(row)) {
      map.set(name, termFromSrj(term));
    }
    return map;
  });
}

/**
 * Build the public API around a driver.
 *
 * @param {object} driver
 * @param {(args: string[], files: Array<{name,content}>) =>
 *         ({stdout,stderr,exitCode}|Promise)} driver.runCli
 * @param {() => (object|null|Promise<object|null>)} driver.loadEntry
 *        Returns the npm-entry ABI object (factoidalNpmEntry) or null.
 * @param {string} driver.engineName  'js' | 'wasm' (error messages).
 */
function buildApi(driver) {
  let parseCounter = 0;
  let entryCache; // undefined = not tried; null = unavailable

  async function entry() {
    if (entryCache === undefined) {
      try {
        entryCache = (await driver.loadEntry()) || null;
      } catch (_) {
        entryCache = null;
      }
    }
    return entryCache;
  }

  async function run(args, files) {
    return driver.runCli(args, files);
  }

  function entryResult(jsonText, what) {
    const r = JSON.parse(jsonText);
    if (!r.ok) throw new Error(`${what}: ${r.error}`);
    return r;
  }

  function freshBnodePrefix() {
    return `p${parseCounter++}_`;
  }

  // Normalize the `data` argument of query/update/serialize/
  // canonicalize into engine inputs. Accepts a Dataset, a raw string
  // (with options.format, default turtle), or an array of those —
  // each element is loaded as its own document so blank-node labels
  // stay document-scoped (the per-document renaming is F*'s
  // RDF.Dataset.Merge.rename_dataset_bnodes, applied at engine load).
  function toDocs(data, options) {
    const opts = options || {};
    const items = Array.isArray(data) ? data : [data];
    return items.map((item, i) => {
      if (item instanceof Dataset) {
        return { ext: 'nq', content: item.toNQuads() };
      }
      if (typeof item === 'string') {
        return { ext: extForFormat(opts.format), content: item };
      }
      if (item && typeof item.text === 'string') {
        return { ext: extForFormat(item.format || opts.format), content: item.text };
      }
      throw new TypeError(
        `data[${i}]: expected a Dataset, a string, or {text, format}`);
    });
  }

  function docsToCliFiles(docs) {
    const files = [];
    const flags = [];
    docs.forEach((d, i) => {
      const name = `/static/data${i}.${d.ext}`;
      files.push({ name, content: d.content });
      flags.push('-d', name);
    });
    return { files, flags };
  }

  // Normalize toDocs() output into one concatenated N-Quads "dataset
  // handle" string via the entry ABI -- the same per-document
  // parseToDatasetJson-then-concatenate shape query()/update()/
  // canonicalize() each already inline. Needs the entry bundle (the
  // caller must have already checked `e` is non-null); factored out
  // here for the SHACL/ShEx/OWL-closure/RML wrappers below, which all
  // hand the engine a dataset-handle N-Quads string rather than raw
  // Turtle (consistent with every other entry ABI call).
  function docsToEntryNQuads(e, docs, what) {
    let nq = '';
    for (const d of docs) {
      if (d.ext === 'nq') { nq += d.content; continue; }
      const r = entryResult(
        e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
        `${what}(parse)`);
      nq += r.nquads;
    }
    return nq;
  }

  // A ShEx focus/shape-label argument is either a raw string (an IRI,
  // or "_:label" for a blank node -- the entry ABI's own convention)
  // or an RDF/JS term (NamedNode/BlankNode); accepting both lets a
  // caller pass a term straight out of a query() binding.
  function shexTermToString(t, who) {
    if (typeof t === 'string') return t;
    if (t && typeof t.termType === 'string') {
      if (t.termType === 'BlankNode') return `_:${t.value}`;
      if (t.termType === 'NamedNode') return t.value;
      throw new TypeError(`${who}: expected an IRI or blank node term`);
    }
    throw new TypeError(`${who}: expected a string or an RDF/JS term`);
  }

  // Everything below is async so both drivers (sync jsoo, async wasm)
  // and both paths (entry, CLI) share one shape.

  /**
   * Parse one RDF document into a Dataset.
   * @param {string} text
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function parse(text, options) {
    if (typeof text !== 'string') {
      throw new TypeError('parse: text must be a string');
    }
    const opts = options || {};
    const ext = extForFormat(opts.format);
    const baseIRI = opts.baseIRI || '';
    const bnodePrefix = freshBnodePrefix();

    const e = await entry();
    if (e) {
      const r = entryResult(
        e.parseToDatasetJson(text, DATA_FORMAT_TAG[ext], baseIRI), 'parse');
      return Dataset.fromNQuads(r.nquads, { blankNodePrefix: bnodePrefix });
    }

    const name = `/static/data.${ext}`;
    const args = ['--dump-nq', '-d', name];
    if (baseIRI) args.push('-b', baseIRI);
    const res = await run(args, [{ name, content: text }]);
    if (res.exitCode !== 0) throw engineError('parse failed', res);
    return Dataset.fromNQuads(res.stdout, { blankNodePrefix: bnodePrefix });
  }

  /**
   * Run a SPARQL 1.1 query.
   * @param {Dataset|string|Array} data
   * @param {string} sparql
   * @param {{format?: string, entail?: 'none'|'RDFS'|'OWL-RL'}} [options]
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   *   SELECT -> Bindings[] (Map of variable name -> RDF/JS Term),
   *   ASK -> boolean, CONSTRUCT -> Dataset.
   */
  async function query(data, sparql, options) {
    if (typeof sparql !== 'string') {
      throw new TypeError('query: sparql must be a string');
    }
    const opts = options || {};
    const entail = opts.entail || 'none';
    if (!ENTAIL_VALUES.has(entail)) {
      throw new TypeError(
        `query: entail must be one of ${[...ENTAIL_VALUES].join(', ')}`);
    }
    const form = sniffQueryForm(sparql);
    const docs = toDocs(data, opts);

    // The npm-entry ABI covers all query forms but has no entailment
    // parameter; entailment closure stays on the CLI path.
    const e = entail === 'none' ? await entry() : null;
    if (e) {
      // The ABI's dataset handle is N-Quads: normalize non-N-Quads
      // documents through parseToDatasetJson first (each document
      // separately, preserving per-document blank-node scoping in F*).
      let nq = '';
      for (const d of docs) {
        if (d.ext === 'nq') { nq += d.content; continue; }
        const r = entryResult(
          e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
          'query(parse)');
        nq += r.nquads;
      }
      const r = entryResult(e.queryDataset(nq, sparql), 'query');
      if (r.kind === 'ask') return r.boolean;
      if (r.kind === 'construct') {
        return Dataset.fromNQuads(r.nquads, {
          blankNodePrefix: freshBnodePrefix(),
        });
      }
      return bindingsFromSrj(r.srj);
    }

    if (form === 'construct' || form === 'describe') {
      throw pendingError(`${form.toUpperCase()} queries`);
    }

    const { files, flags } = docsToCliFiles(docs);
    const args = [...flags, '-e', sparql, '-o', 'json'];
    if (entail !== 'none') args.push('--entail', entail);
    const res = await run(args, files);
    if (res.exitCode !== 0) throw engineError('query failed', res);
    const srj = jsonFromStdout(res.stdout, 'query');
    if (form === 'ask' || typeof srj.boolean === 'boolean') {
      return !!srj.boolean;
    }
    return bindingsFromSrj(srj);
  }

  /**
   * Apply a SPARQL 1.1 Update to a dataset, returning the new Dataset.
   * Needs the npm-entry bundle.
   * @param {Dataset|string|Array} data
   * @param {string} updateText
   * @param {{format?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function update(data, updateText, options) {
    if (typeof updateText !== 'string') {
      throw new TypeError('update: updateText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('SPARQL UPDATE');
    const docs = toDocs(data, options);
    let nq = '';
    for (const d of docs) {
      if (d.ext === 'nq') { nq += d.content; continue; }
      const r = entryResult(
        e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
        'update(parse)');
      nq += r.nquads;
    }
    const r = entryResult(e.updateDataset(nq, updateText), 'update');
    return Dataset.fromNQuads(r.nquads, {
      blankNodePrefix: freshBnodePrefix(),
    });
  }

  /**
   * Serialize a dataset (engine-produced bytes, sorted N-Quads order).
   * @param {Dataset|string|Array} data
   * @param {{format?: 'nquads'|'ntriples', inputFormat?: string}} [options]
   * @returns {Promise<string>}
   */
  async function serialize(data, options) {
    const opts = options || {};
    const outFormat = String(opts.format || 'nquads').toLowerCase();
    if (outFormat !== 'nquads' && outFormat !== 'ntriples') {
      throw new TypeError(
        "serialize: format must be 'nquads' or 'ntriples' " +
        '(turtle output is pending npm-entry build)');
    }
    const docs = toDocs(data, { format: opts.inputFormat });

    if (outFormat === 'nquads') {
      const e = await entry();
      if (e && docs.every((d) => d.ext === 'nq')) {
        const nq = docs.map((d) => d.content).join('');
        return entryResult(e.serializeNQuads(nq), 'serialize').nquads;
      }
    }

    const { files, flags } = docsToCliFiles(docs);
    const mode = outFormat === 'nquads' ? '--dump-nq' : '--dump';
    const res = await run([mode, ...flags], files);
    if (res.exitCode !== 0) throw engineError('serialize failed', res);
    return res.stdout;
  }

  /**
   * RDFC-1.0 canonicalization: canonical blank-node labels + sorted
   * canonical N-Quads.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<string>}
   */
  async function canonicalize(data, options) {
    const docs = toDocs(data, options);

    const e = await entry();
    if (e) {
      let nq = '';
      for (const d of docs) {
        if (d.ext === 'nq') { nq += d.content; continue; }
        const r = entryResult(
          e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
          'canonicalize(parse)');
        nq += r.nquads;
      }
      return entryResult(e.canonicalizeToNQuads(nq), 'canonicalize').nquads;
    }

    const { files, flags } = docsToCliFiles(docs);
    const res = await run(['--canonicalize', ...flags], files);
    if (res.exitCode !== 0) {
      if (/unknown option/.test(res.stderr || '')) {
        throw new Error(
          'canonicalize: this engine bundle predates the --canonicalize ' +
          'flag — pending npm-entry build (rebuild via ' +
          'formal/fstar/build-ocaml.sh js + npm).');
      }
      throw engineError('canonicalize failed', res);
    }
    return res.stdout;
  }

  /**
   * Enumerate the named graphs of an already-parsed Dataset.
   *
   * Graphs-api design (docs/designissues/2026-07-05-graphs-api-design.md
   * section 1.3): DatasetCore.match(null,null,null,graphNode) already
   * gives per-graph read access, but match() alone cannot answer "what
   * graph names exist" -- this is exactly that enumeration, and only
   * that: it walks quads already produced by the F*-verified parser, so
   * it needs no engine round-trip (no new RDF/SPARQL semantics, rule
   * #11 stays satisfied trivially).
   *
   * @param {Dataset} dataset
   * @returns {Array<[iri: string, graph: Dataset]>}
   *   default graph excluded, first-seen order.
   */
  function graphs(dataset) {
    if (!(dataset instanceof Dataset)) {
      throw new TypeError('graphs: expected a Dataset');
    }
    const seen = new Map(); // iri -> graph term (first occurrence)
    for (const q of dataset) {
      const g = q.graph;
      if (!g || g.termType === 'DefaultGraph') continue;
      if (!seen.has(g.value)) seen.set(g.value, g);
    }
    const out = [];
    for (const [iri, gTerm] of seen) {
      out.push([iri, dataset.match(null, null, null, gTerm)]);
    }
    return out;
  }

  /**
   * RDFC-1.0 canonical hash of a single graph -- the graph-scoped
   * sibling of canonicalize(), gated via capabilities() the same way
   * (docs/designissues/2026-07-05-graphs-api-design.md section 1.3).
   * Accepts a whole dataset or (more usually) one entry of graphs()'s
   * output; either way, every quad's graph component is dropped before
   * canonicalizing, matching RDF.Canonical.fst's
   * canonicalize_named_graph, which projects the named graph into
   * `{ ds_default = g; ds_named = [] }` before reusing
   * canonicalize_to_nquads unmodified.
   *
   * @param {Dataset} datasetOrGraph
   * @returns {Promise<string>} canonical N-Quads text for that graph alone.
   */
  async function canonicalHash(datasetOrGraph) {
    if (!(datasetOrGraph instanceof Dataset)) {
      throw new TypeError(
        'canonicalHash: expected a Dataset (e.g. one entry of graphs())');
    }
    const asDefaultGraph = new Dataset(
      datasetOrGraph.toArray().map(
        (q) => dataFactory.quad(q.subject, q.predicate, q.object)));
    return canonicalize(asDefaultGraph.toNQuads(), { format: 'nquads' });
  }

  // Some loaded entry bundles predate one of these exports (e.g. an
  // older/stale wasm-target build) -- `e` itself is truthy (loadEntry
  // succeeded), but `e[fnName]` is undefined, which would otherwise
  // surface as a confusing "e.shaclValidate is not a function". Fail
  // with the same pendingError() shape callers already expect from a
  // missing bundle.
  function requireEntryFn(e, fnName, what) {
    if (typeof e[fnName] !== 'function') throw pendingError(what);
  }

  /**
   * SHACL Core validation. Needs the npm-entry bundle (SHACL_Validation
   * is only linked into the entry/CLI bundles, not exposed on the
   * argv-driven CLI surface today).
   * @param {Dataset|string|Array} data
   * @param {Dataset|string|Array} shapes
   * @param {{format?: string}} [options] applies to both data and shapes
   * @returns {Promise<{conforms: boolean, report: Dataset}>}
   *   report is SHACL_Validation.validation_report_to_graph's graph
   *   (sh:conforms + one sh:ValidationResult per violation).
   */
  async function shaclValidate(data, shapes, options) {
    const e = await entry();
    if (!e) throw pendingError('SHACL validation');
    requireEntryFn(e, 'shaclValidate', 'SHACL validation');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'shaclValidate(data)');
    const shapesNq = docsToEntryNQuads(e, toDocs(shapes, options), 'shaclValidate(shapes)');
    const r = entryResult(e.shaclValidate(dataNq, shapesNq), 'shaclValidate');
    return {
      conforms: r.conforms,
      report: Dataset.fromNQuads(r.reportNquads, {
        blankNodePrefix: freshBnodePrefix(),
      }),
    };
  }

  /**
   * ShEx (Shape Expressions) validation of one focus node against one
   * shape. Needs the npm-entry bundle.
   * @param {Dataset|string|Array} data
   * @param {string} schemaJson the schema, as text -- either ShExJ (a
   *   JSON Schema document) or ShExC (the compact human-readable
   *   syntax; formal/fstar/Parser.ShExC.fst). Dispatch rule: the schema
   *   text's first non-whitespace character decides the format -- '{'
   *   means ShExJ, anything else is parsed as ShExC. No separate flag
   *   or file-extension hint is needed; a schema whose ShExC text
   *   happens to start with whitespace then '{' would misdetect, but no
   *   valid ShExC document starts that way (ShExC always opens with a
   *   directive keyword, a shape label, or START).
   * @param {string|{termType,value}} focus an IRI, "_:label", or an
   *   RDF/JS NamedNode/BlankNode term
   * @param {string|{termType,value}|null} [shape] a shape label (same
   *   shapes as focus); omit/null to validate against the schema's own `start`
   * @param {{format?: string}} [options]
   * @returns {Promise<boolean|null>} null means "deferred" -- outside
   *   this engine's decidable ShEx fragment, never a guessed answer
   *   (see formal/fstar/ShEx.Validation.fst's file header).
   */
  async function shexValidate(data, schemaJson, focus, shape, options) {
    const e = await entry();
    if (!e) throw pendingError('ShEx validation');
    requireEntryFn(e, 'shexValidate', 'ShEx validation');
    if (typeof schemaJson !== 'string') {
      throw new TypeError('shexValidate: schemaJson must be a string');
    }
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'shexValidate(data)');
    const focusStr = shexTermToString(focus, 'shexValidate(focus)');
    const shapeStr = shape == null ? '' : shexTermToString(shape, 'shexValidate(shape)');
    const r = entryResult(
      e.shexValidate(dataNq, schemaJson, focusStr, shapeStr), 'shexValidate');
    return r.verdict;
  }

  const OWL_CLOSURE_MODES = { rdfs: 'RDFS', 'owl-rl': 'OWL-RL', owlrl: 'OWL-RL', owl_rl: 'OWL-RL' };

  function normalizeClosureMode(mode) {
    const canonical = OWL_CLOSURE_MODES[String(mode || '').toLowerCase()];
    if (!canonical) {
      throw new TypeError(
        `owlClosure: mode must be 'RDFS' or 'OWL-RL' (got '${mode}')`);
    }
    return canonical;
  }

  /**
   * RDFS or OWL-RL entailment closure, materialized as a new Dataset
   * (input triples + derived triples). Needs the npm-entry bundle.
   * Scope cut: only the default graph is closed over (same cut
   * fn.js's entail() documents for its own CLI-path implementation).
   * @param {Dataset|string|Array} data
   * @param {'RDFS'|'OWL-RL'} mode
   * @param {{format?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function owlClosure(data, mode, options) {
    const e = await entry();
    if (!e) throw pendingError('OWL/RDFS closure');
    requireEntryFn(e, 'owlClosure', 'OWL/RDFS closure');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'owlClosure(data)');
    const r = entryResult(
      e.owlClosure(dataNq, normalizeClosureMode(mode)), 'owlClosure');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * Evaluate an RML mapping graph against one logical source's raw
   * data, returning the generated triples as a Dataset. Needs the
   * npm-entry bundle. Scope cut (documented, not silent): every
   * triples map in `mapping` reads the SAME `sourceData` -- joins
   * across two DIFFERENT logical sources are not reachable through
   * this one-source entry point (see bin/rml-runner/rml_runner.ml for
   * the full multi-source join driver).
   * @param {Dataset|string|Array} mapping the RML mapping graph (Turtle by default)
   * @param {string} sourceData raw JSON or CSV text (not RDF)
   * @param {'json'|'csv'} sourceKind
   * @param {{format?: string}} [options] applies to `mapping`
   * @returns {Promise<Dataset>}
   */
  async function rmlMap(mapping, sourceData, sourceKind, options) {
    const e = await entry();
    if (!e) throw pendingError('RML mapping evaluation');
    requireEntryFn(e, 'rmlMap', 'RML mapping evaluation');
    if (typeof sourceData !== 'string') {
      throw new TypeError('rmlMap: sourceData must be a string');
    }
    const kind = String(sourceKind || '').toLowerCase();
    if (kind !== 'json' && kind !== 'csv') {
      throw new TypeError("rmlMap: sourceKind must be 'json' or 'csv'");
    }
    const mappingNq = docsToEntryNQuads(e, toDocs(mapping, options), 'rmlMap(mapping)');
    const r = entryResult(e.rmlMap(mappingNq, sourceData, kind), 'rmlMap');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * CSVW csv2rdf conversion (w3.org/TR/csv2rdf): convert tabular data
   * plus an optional CSVW metadata document into a Dataset. Needs the
   * npm-entry bundle. Scope cut (documented, not silent -- mirrors
   * rmlMap's one-source cut): every table in a multi-table `tables`
   * group reads the SAME `csvText`. Datatype `format` facets,
   * list-valued (`separator`) cells, and full inherited-property
   * propagation are not yet implemented -- see
   * docs/designissues/2026-07-05-csvw-program-plan.md for measured
   * coverage.
   * @param {string} csvText raw RFC 4180 tabular data (not RDF)
   * @param {string} [metadataJson] CSVW metadata document (JSON text);
   *   '' / omitted infers the schema from the CSV's own header row
   * @param {{mode?: 'standard'|'minimal', base?: string, url?: string}}
   *   [options] mode defaults to 'standard' (full csvw:TableGroup/
   *   Table/Row wrapper); base is the resolution base IRI (default
   *   'file:///'); url is the tabular file's own URL used when the
   *   metadata carries none (default 'table.csv') -- cell predicates
   *   default to `<tableUrl>#<colName>`, so url shapes every emitted
   *   predicate IRI.
   * @returns {Promise<Dataset>}
   */
  async function csvwToRdf(csvText, metadataJson, options) {
    if (typeof csvText !== 'string') {
      throw new TypeError('csvwToRdf: csvText must be a string');
    }
    const meta = metadataJson == null ? '' : metadataJson;
    if (typeof meta !== 'string') {
      throw new TypeError('csvwToRdf: metadataJson must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('CSVW csv2rdf conversion');
    requireEntryFn(e, 'csvwToRdf', 'CSVW csv2rdf conversion');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.mode ? { mode: String(opts.mode).toLowerCase() } : {}),
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.url ? { url: opts.url } : {}),
    });
    const r = entryResult(e.csvwToRdf(csvText, meta, optionsJson), 'csvwToRdf');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * Parse a JSON-LD document into a Dataset, with JSON-LD-specific
   * options `parse()` has no room for. Needs the npm-entry bundle
   * (plain `parse(text, {format:'jsonld'})` also works now -- see
   * bin/npm-entry/entry_jsoo.ml's parseToDatasetJson JSON-LD fix --
   * this exists for callers that need rdfDirection/expandContext/
   * processingMode).
   * @param {string} jsonldText
   * @param {{base?: string, rdfDirection?: string, expandContext?: string,
   *   processingMode?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function jsonldToRdf(jsonldText, options) {
    if (typeof jsonldText !== 'string') {
      throw new TypeError('jsonldToRdf: jsonldText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('jsonldToRdf');
    requireEntryFn(e, 'jsonldToRdf', 'jsonldToRdf');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.rdfDirection ? { rdfDirection: opts.rdfDirection } : {}),
      ...(opts.expandContext ? { expandContext: opts.expandContext } : {}),
      ...(opts.processingMode ? { processingMode: opts.processingMode } : {}),
    });
    const r = entryResult(e.jsonldToRdf(jsonldText, optionsJson), 'jsonldToRdf');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * RIF Core forward-chaining saturation, materialized as a new
   * Dataset (input triples + derived triples, default graph only --
   * RIF Core has no named-graph notion). Needs the npm-entry bundle.
   * @param {Dataset|string|Array} data the premise graph
   * @param {string} rifRulesXml a RIF Core XML rule document
   * @param {{format?: string}} [options] applies to `data`
   * @returns {Promise<Dataset>}
   */
  async function rifEval(data, rifRulesXml, options) {
    const e = await entry();
    if (!e) throw pendingError('RIF Core evaluation');
    requireEntryFn(e, 'rifEval', 'RIF Core evaluation');
    if (typeof rifRulesXml !== 'string') {
      throw new TypeError('rifEval: rifRulesXml must be a string');
    }
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'rifEval(data)');
    const r = entryResult(e.rifEval(rifRulesXml, dataNq), 'rifEval');
    return Dataset.fromNQuads(r.saturatedNquads, {
      blankNodePrefix: freshBnodePrefix(),
    });
  }

  // -----------------------------------------------------------------
  // In-memory COTTAS bytes store (docs/designissues/2026-07-06-
  // inmemory-bytes-store.md, stage 5). Needs the npm-entry bundle
  // (bin/npm-entry/entry_jsoo.ml's openCottas/queryCottas/closeCottas/
  // toCottas exports). Unlike every other operation in this file, the
  // "dataset" here is NOT an in-heap Dataset: openCottas() returns an
  // opaque handle string naming an entry the F*-verified COTTAS/Parquet
  // reader decodes lazily, row-group by row-group, as queryCottas()
  // touches it -- the whole point of the design (heap-store parity
  // would defeat the memory win the design doc measures). See
  // queryCottas's doc comment for the query-shape/entailment/write
  // divergences from query() this implies.
  // -----------------------------------------------------------------

  // Accept a hex string, a Uint8Array/Buffer, or a plain ArrayBuffer;
  // normalize to the lowercase hex string the entry ABI's string-only
  // wire contract requires (same "strings in, JSON out" ABI every
  // other entry export uses -- see entry_jsoo.ml's file header).
  function bytesToHex(bytesLike, who) {
    if (typeof bytesLike === 'string') {
      if (!/^[0-9a-fA-F]*$/.test(bytesLike) || bytesLike.length % 2 !== 0) {
        throw new TypeError(`${who}: string input must be an even-length hex string`);
      }
      return bytesLike.toLowerCase();
    }
    let u8;
    if (bytesLike instanceof Uint8Array) u8 = bytesLike;
    else if (bytesLike instanceof ArrayBuffer) u8 = new Uint8Array(bytesLike);
    else {
      throw new TypeError(
        `${who}: expected a hex string, Uint8Array, Buffer, or ArrayBuffer`);
    }
    // Buffer's native hex codec when available (Node); a per-byte
    // string-concat loop allocates millions of intermediate strings on
    // a corpus-scale artifact (it measurably dominated the bytes-store
    // path's RSS at 50,000 quads before this branch existed).
    if (typeof Buffer !== 'undefined' && typeof Buffer.from === 'function') {
      return Buffer.from(u8.buffer, u8.byteOffset, u8.byteLength).toString('hex');
    }
    const HEX = '0123456789abcdef';
    const parts = new Array(u8.length);
    for (let i = 0; i < u8.length; i++) {
      parts[i] = HEX[u8[i] >> 4] + HEX[u8[i] & 15];
    }
    return parts.join('');
  }

  function hexToBytes(hex) {
    const out = new Uint8Array(hex.length / 2);
    for (let i = 0; i < out.length; i++) {
      out[i] = parseInt(hex.substr(i * 2, 2), 16);
    }
    return out;
  }

  /**
   * Open a COTTAS/Parquet artifact's raw bytes as a queryable,
   * read-only store -- the in-memory-bytes-store design's browser call
   * site. Needs the npm-entry bundle. The store is NOT materialized
   * into a heap Dataset: rows are decoded lazily by queryCottas() as a
   * query actually touches them (measured 64-161 B/quad in the design
   * doc's native numbers, vs. ~877 B/quad for a fully-parsed heap
   * Dataset of the same data).
   *
   * @param {string|Uint8Array|ArrayBuffer} bytes whole `.cottas` file contents
   * @returns {Promise<string>} an opaque handle for queryCottas()/closeCottas()
   */
  async function openCottas(bytes) {
    const e = await entry();
    if (!e) throw pendingError('openCottas (in-memory COTTAS bytes store)');
    requireEntryFn(e, 'openCottas', 'openCottas');
    const hex = bytesToHex(bytes, 'openCottas');
    const r = entryResult(e.openCottas(hex), 'openCottas');
    return r.handle;
  }

  /**
   * Run a SPARQL 1.1 query against a store opened by openCottas().
   * Needs the npm-entry bundle.
   *
   * Divergences from query() (documented, not silent):
   *  - No `entail` option -- bare COTTAS bytes carry no closure step.
   *  - No write/--delta-log overlay -- read-only (design doc §2.4's
   *    write-overlay story composes at the native store_caps layer;
   *    it is not wired into this browser ABI).
   *  - A query SHAPE the backend executor can't push down (rare; the
   *    same honest-failure posture the native `--data-cottas` CLI path
   *    has for run_select_query_backend_dataset/run_ask_query_backend_
   *    dataset returning None) rejects with an Error rather than
   *    silently falling back to a full materialize -- that fallback
   *    would defeat the store's whole memory argument.
   *  - DESCRIBE is not supported (same cut queryDataset's ABI has).
   *
   * @param {string} handle from openCottas()
   * @param {string} sparql
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   *   SELECT -> Bindings[], ASK -> boolean, CONSTRUCT -> Dataset
   *   (materialized once, via SPARQL11_Store.materialize_dataset_backend
   *   -- see entry_jsoo.ml's queryCottas doc comment for why CONSTRUCT
   *   alone pays that cost).
   */
  async function queryCottas(handle, sparql) {
    if (typeof handle !== 'string') {
      throw new TypeError('queryCottas: handle must be the string openCottas() returned');
    }
    if (typeof sparql !== 'string') {
      throw new TypeError('queryCottas: sparql must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('queryCottas');
    requireEntryFn(e, 'queryCottas', 'queryCottas');
    const r = entryResult(e.queryCottas(handle, sparql), 'queryCottas');
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct') {
      return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
    }
    return bindingsFromSrj(r.srj);
  }

  /**
   * Release a store opened by openCottas(). Drops the handle from this
   * process's registry only -- it does NOT evict the underlying byte
   * cache the entry bundle keeps for the process's lifetime (design
   * doc "Open decisions" item 1: no eviction API exists yet). A page
   * that opens many short-lived stores still grows that cache for the
   * tab's lifetime; this is a documented limitation, not a silent leak.
   * @param {string} handle
   * @returns {Promise<void>}
   */
  async function closeCottas(handle) {
    if (typeof handle !== 'string') {
      throw new TypeError('closeCottas: handle must be the string openCottas() returned');
    }
    const e = await entry();
    if (!e) throw pendingError('closeCottas');
    requireEntryFn(e, 'closeCottas', 'closeCottas');
    entryResult(e.closeCottas(handle), 'closeCottas');
  }

  /**
   * Serialize a dataset to COTTAS/Parquet bytes via the native writer
   * (RDF.CottasStore.BaseWriter.serialize_cottas_v2 -- the SAME pure
   * `Tot` F* function `factoidal compact --native-writer` uses), for a
   * caller to persist (IndexedDB/OPFS) or offer as a download. Needs
   * the npm-entry bundle. Round-trips through openCottas(): the bytes
   * this returns are valid input to openCottas() and to the native
   * `--data-cottas`/`--data-cottas-mem` CLI flags, byte-for-byte.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<Uint8Array>}
   */
  async function toCottas(data, options) {
    const e = await entry();
    if (!e) throw pendingError('toCottas (native COTTAS serialization)');
    requireEntryFn(e, 'toCottas', 'toCottas');
    const nq = docsToEntryNQuads(e, toDocs(data, options), 'toCottas');
    const r = entryResult(e.toCottas(nq), 'toCottas');
    return hexToBytes(r.cottasHex);
  }

  /**
   * Feature probe, for tests and downstream capability checks.
   * @returns {Promise<{entry: boolean, construct: boolean,
   *   update: boolean, canonicalize: boolean, graphs: boolean,
   *   canonicalHash: boolean, shacl: boolean, shex: boolean,
   *   owlClosure: boolean, rml: boolean, csvw: boolean, jsonld: boolean,
   *   rif: boolean}>}
   */
  let capsCache = null;
  async function capabilities() {
    if (capsCache) return capsCache;
    capsCache = capabilitiesUncached();
    return capsCache;
  }

  async function capabilitiesUncached() {
    const e = await entry();
    if (e) {
      return {
        entry: true, construct: true, update: true, canonicalize: true,
        graphs: true, canonicalHash: true,
        // Per-function probes, not a blanket `true` -- an older/stale
        // loaded bundle (e.g. a wasm-target build that predates one of
        // these exports) reports its ACTUAL surface rather than
        // over-promising (see requireEntryFn's doc comment above).
        shacl: typeof e.shaclValidate === 'function',
        shex: typeof e.shexValidate === 'function',
        owlClosure: typeof e.owlClosure === 'function',
        rml: typeof e.rmlMap === 'function',
        csvw: typeof e.csvwToRdf === 'function',
        jsonld: typeof e.jsonldToRdf === 'function',
        rif: typeof e.rifEval === 'function',
        cottasBytesStore: typeof e.openCottas === 'function' &&
          typeof e.queryCottas === 'function' && typeof e.toCottas === 'function',
      };
    }
    // Probe --canonicalize support on the CLI bundle with a 1-quad doc.
    // canonicalHash rides the same engine support as canonicalize (it is
    // canonicalize() applied to one graph's triples); graphs() is pure
    // JS enumeration and needs no engine at all.
    let canon = false;
    try {
      const res = await run(
        ['--canonicalize', '-d', '/static/cap.nq'],
        [{ name: '/static/cap.nq',
           content: '<http://x/s> <http://x/p> "o" .\n' }]);
      canon = res.exitCode === 0;
    } catch (_) { canon = false; }
    return {
      entry: false, construct: false, update: false, canonicalize: canon,
      graphs: true, canonicalHash: canon,
      shacl: false, shex: false, owlClosure: false, rml: false,
      csvw: false, jsonld: false, rif: false, cottasBytesStore: false,
    };
  }

  return {
    parse,
    query,
    update,
    serialize,
    canonicalize,
    graphs,
    canonicalHash,
    shaclValidate,
    shexValidate,
    owlClosure,
    rmlMap,
    csvwToRdf,
    jsonldToRdf,
    rifEval,
    openCottas,
    queryCottas,
    closeCottas,
    toCottas,
    capabilities,
    Dataset,
    dataFactory,
  };
}

module.exports = { buildApi, sniffQueryForm, bindingsFromSrj };
