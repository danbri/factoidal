// factoidal — formally-verified SPARQL 1.1 + RDF 1.1 for Node.
//
// CommonJS entry point (js_of_ocaml engine). Public API:
//
//   parse(text, {format, baseIRI})      -> Promise<Dataset>
//   query(data, sparql, {entail})       -> Promise<Bindings[] | boolean | Dataset>
//   update(data, updateText)            -> Promise<Dataset>
//   serialize(data, {format})           -> Promise<string>
//   canonicalize(data, {format})        -> Promise<string>   (RDFC-1.0)
//   graphs(dataset)                     -> Array<[iri, Dataset]>  (named graphs)
//   canonicalHash(datasetOrGraph)       -> Promise<string>   (RDFC-1.0, one graph)
//   shaclValidate(data, shapes)         -> Promise<{conforms, report: Dataset}>
//   shexValidate(data, schema, focus, shape) -> Promise<boolean|null>
//   owlClosure(data, mode)              -> Promise<Dataset>  ('RDFS'|'OWL-RL')
//   rmlMap(mapping, sourceData, kind)   -> Promise<Dataset>  (kind: 'json'|'csv')
//   csvwToRdf(csvText, metadataJson, options) -> Promise<Dataset>  (CSVW csv2rdf)
//   jsonldToRdf(jsonldText, options)    -> Promise<Dataset>
//   rifEval(data, rifRulesXml)          -> Promise<Dataset>  (RIF Core saturation)
//   openCottas(bytes)                   -> Promise<string>   (handle; bytes is
//                                          hex|Uint8Array|ArrayBuffer of a
//                                          whole .cottas artifact)
//   queryCottas(handle, sparql)         -> Promise<Bindings[] | boolean | Dataset>
//                                          (in-memory COTTAS bytes store --
//                                          rows decode lazily, no heap Dataset)
//   closeCottas(handle)                 -> Promise<void>
//   toCottas(data)                      -> Promise<Uint8Array>  (native COTTAS
//                                          writer; round-trips into openCottas)
//   dataFactory                         -> RDF/JS DataFactory
//   Dataset                             -> RDF/JS DatasetCore class
//
// shaclValidate/shexValidate/owlClosure/rmlMap/csvwToRdf/jsonldToRdf/rifEval/
// openCottas/queryCottas/closeCottas/toCottas need the npm-entry ABI bundle
// (same gate as update()/canonicalize()); see capabilities() to probe for it.
// See docs/designissues/2026-07-06-inmemory-bytes-store.md for the
// openCottas/queryCottas/toCottas design and its documented divergences
// from parse()/query() (no entailment, no write overlay, read-only).
//
// Bindings are Maps of variable name -> RDF/JS Term. See index.d.ts
// for the full types and README.md for examples.
//
// The legacy single-shot API from 0.1.0-alpha scaffolding is kept as
// queryRaw(dataString, queryString, {dataFormat, entail, output}) —
// it returns parsed SPARQL Results JSON (or a raw string for
// non-JSON output formats).
//
// For the wasm engine with the same API, require('factoidal/wasm').

'use strict';

const fs = require('node:fs');
const path = require('node:path');

const engine = require('./lib/engine-js.js');
const { buildApi } = require('./lib/api.js');
const rdfjs = require('./rdfjs.js');

const pkg = require('./package.json');
const version = pkg.version;

// ---------------------------------------------------------------------
// npm-entry ABI loader. The entry bundle (built from
// bin/npm-entry/entry_jsoo.ml) registers `factoidalNpmEntry` on
// module.exports (Node) / globalThis (browser). Optional — everything
// the CLI bundle can do works without it.
// ---------------------------------------------------------------------

function entryCandidates() {
  const c = [];
  if (process.env.FACTOIDAL_NPM_ENTRY) c.push(process.env.FACTOIDAL_NPM_ENTRY);
  c.push(path.join(__dirname, 'factoidal-npm-entry.js'));
  c.push(path.resolve(
    __dirname, '..', '..', 'docs', 'fstar-extracted', 'factoidal-npm-entry.js'));
  return c;
}

function loadEntry() {
  for (const p of entryCandidates()) {
    if (!p || !fs.existsSync(p)) continue;
    const mod = require(p);
    const abi = (mod && mod.factoidalNpmEntry) ||
      (globalThis.factoidalNpmEntry);
    if (abi && typeof abi.queryDataset === 'function') return abi;
  }
  return null;
}

const api = buildApi({
  engineName: 'js',
  runCli: engine.runCli,
  loadEntry,
});

// ---------------------------------------------------------------------
// Legacy raw API (pre-RDF/JS scaffolding surface, kept for the smoke
// tests and for callers that want the CLI's other output formats).
// ---------------------------------------------------------------------

const OUTPUT_FORMATS = new Set(['json', 'csv', 'tsv', 'xml', 'table', 'ntriples']);
const ENTAIL_VALUES = new Set(['none', 'RDFS', 'OWL-RL']);
const DATA_FORMAT_EXT = {
  turtle: 'ttl', ttl: 'ttl', ntriples: 'nt', nt: 'nt', nquads: 'nq',
  nq: 'nq', trig: 'trig', rdfxml: 'rdf', 'rdf-xml': 'rdf', rdf: 'rdf',
};

function queryRaw(dataString, queryString, options) {
  return Promise.resolve().then(() => {
    if (typeof dataString !== 'string') {
      throw new TypeError('queryRaw: dataString must be a string');
    }
    if (typeof queryString !== 'string') {
      throw new TypeError('queryRaw: queryString must be a string');
    }
    const opts = options || {};
    const dataFormat = String(opts.dataFormat || 'turtle').toLowerCase();
    const entail = opts.entail || 'none';
    const output = opts.output || 'json';
    if (!(dataFormat in DATA_FORMAT_EXT)) {
      throw new TypeError(`queryRaw: unknown dataFormat '${opts.dataFormat}'`);
    }
    if (!ENTAIL_VALUES.has(entail)) {
      throw new TypeError(
        `queryRaw: entail must be one of ${[...ENTAIL_VALUES].join(', ')}`);
    }
    if (!OUTPUT_FORMATS.has(output)) {
      throw new TypeError(
        `queryRaw: output must be one of ${[...OUTPUT_FORMATS].join(', ')}`);
    }

    const name = `/static/data.${DATA_FORMAT_EXT[dataFormat]}`;
    const args = ['-d', name, '-e', queryString, '-o', output];
    if (entail !== 'none') args.push('--entail', entail);

    const res = engine.runCli(args, [{ name, content: dataString }]);
    if (res.exitCode !== 0) {
      const msg = (res.stderr || res.stdout ||
        `factoidal exited with code ${res.exitCode}`).trim();
      const err = new Error('SPARQL query failed: ' + msg);
      err.exitCode = res.exitCode;
      err.stderr = res.stderr;
      err.stdout = res.stdout;
      throw err;
    }
    if (output !== 'json') return res.stdout;

    const first = res.stdout.indexOf('{');
    const last = res.stdout.lastIndexOf('}');
    if (first < 0 || last < first) {
      const err = new Error(
        'factoidal did not produce JSON on stdout. Raw output: ' + res.stdout);
      err.stdout = res.stdout;
      err.stderr = res.stderr;
      throw err;
    }
    return JSON.parse(res.stdout.slice(first, last + 1));
  });
}

module.exports = {
  // Public typed API
  parse: api.parse,
  query: api.query,
  update: api.update,
  serialize: api.serialize,
  canonicalize: api.canonicalize,
  graphs: api.graphs,
  canonicalHash: api.canonicalHash,
  shaclValidate: api.shaclValidate,
  shexValidate: api.shexValidate,
  owlClosure: api.owlClosure,
  rmlMap: api.rmlMap,
  csvwToRdf: api.csvwToRdf,
  jsonldToRdf: api.jsonldToRdf,
  rifEval: api.rifEval,
  openCottas: api.openCottas,
  queryCottas: api.queryCottas,
  closeCottas: api.closeCottas,
  toCottas: api.toCottas,
  capabilities: api.capabilities,
  Dataset: rdfjs.Dataset,
  dataFactory: rdfjs.dataFactory,
  // Legacy raw surface
  queryRaw,
  // Metadata
  version,
};
