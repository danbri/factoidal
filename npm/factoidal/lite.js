// factoidal/lite — the 'lite' profile entry point (issue #684).
//
// Same construction as index.js (js_of_ocaml engine, npm-entry ABI
// driver), but:
//   - the npm-entry ABI loader resolves factoidal-npm-entry-lite.js
//     instead of factoidal-npm-entry.js;
//   - there is no CLI bundle here at all -- runCli() always rejects,
//     naming the lite profile (no entailment regimes, no queryHdt);
//   - the export list is the core surface only. The lite entry bundle
//     omits SHACL, ShEx, OWL closure, JSON-LD, RDF/XML, CSVW, RML,
//     RIF, XML, XPath, VC crypto and COTTAS (bin/npm-entry/README.md,
//     entry_lite_jsoo.ml's header comment), so those typed wrappers
//     are not exported here at all -- a caller wanting them imports
//     '@factoidal/core' (the full profile) instead of getting a
//     runtime rejection from a name that looks supported.
//
//   const factoidal = require('@factoidal/core/lite');
//   const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples' });
//   const rows = await factoidal.query(ds, 'SELECT * WHERE { ?s ?p ?o }');
//
// See README.md's "Choosing a bundle: full or lite" section for the
// measured size difference and the full capability matrix.

'use strict';

const fs = require('node:fs');
const path = require('node:path');

const { buildApi } = require('./lib/api.js');
const rdfjs = require('./rdfjs.js');

const pkg = require('./package.json');
const version = pkg.version;

const CLI_UNAVAILABLE_MESSAGE =
  "factoidal/lite: the 'lite' profile ships no CLI bundle (no " +
  'entailment regimes, no queryHdt) -- require("@factoidal/core") ' +
  '(the full profile) for those.';

// ---------------------------------------------------------------------
// npm-entry ABI loader (lite flavor). Same three-step resolution
// ladder as index.js's loadEntry(), pointed at the lite bundle: an
// explicit env override, then the package-local file, then the
// GitHub Pages mirror under docs/fstar-extracted/.
// ---------------------------------------------------------------------

function entryCandidates() {
  const c = [];
  if (process.env.FACTOIDAL_NPM_ENTRY_LITE) c.push(process.env.FACTOIDAL_NPM_ENTRY_LITE);
  c.push(path.join(__dirname, 'factoidal-npm-entry-lite.js'));
  c.push(path.resolve(
    __dirname, '..', '..', 'docs', 'fstar-extracted', 'factoidal-npm-entry-lite.js'));
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
  engineName: 'js-lite',
  runCli: async () => ({
    exitCode: 1,
    stdout: '',
    stderr: CLI_UNAVAILABLE_MESSAGE,
  }),
  loadEntry,
});

module.exports = {
  parse: api.parse,
  query: api.query,
  registerExtensionFunction: api.registerExtensionFunction,
  unregisterExtensionFunction: api.unregisterExtensionFunction,
  clearExtensionFunctions: api.clearExtensionFunctions,
  registerServiceEndpoint: api.registerServiceEndpoint,
  clearServiceEndpoints: api.clearServiceEndpoints,
  update: api.update,
  openDataset: api.openDataset,
  serialize: api.serialize,
  canonicalize: api.canonicalize,
  graphs: api.graphs,
  canonicalHash: api.canonicalHash,
  capabilities: api.capabilities,
  DatasetHandle: api.DatasetHandle,
  ParseError: api.ParseError,
  Dataset: rdfjs.Dataset,
  dataFactory: rdfjs.dataFactory,
  version,
  engine: 'js-lite',
};
