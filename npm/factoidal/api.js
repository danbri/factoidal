// factoidal — bundler-friendly, CSP-safe entry point (issue #682).
//
// index.js / wasm.js reach the engine by fetching or `require()`-ing a
// bundle file and, for the browser side (browser.js's loadNpmEntry),
// evaluating its source with `new Function(src)`. A page served under
// `Content-Security-Policy: script-src 'self'` (no `unsafe-eval`)
// refuses that call, and a bundler (esbuild, webpack, Rollup, ...)
// has no file to fetch at all — it needs a statically importable
// module.
//
// This module does neither. createApi() takes an ALREADY-LOADED
// npm-entry ABI object (the `factoidalNpmEntry` value
// `factoidal-npm-entry.js` / `factoidal-npm-entry.wasm.js` registers
// on `module.exports` under CommonJS, or on `globalThis` under a
// classic `<script src="factoidal-npm-entry.js">` tag) and wires
// lib/api.js's typed surface around it directly — no fetch, no eval:
//
//   const { createApi } = require('@factoidal/core/api');
//   const { factoidalNpmEntry } = require('@factoidal/core/factoidal-npm-entry.js');
//   const factoidal = createApi(factoidalNpmEntry);
//   const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples' });
//   const rows = await factoidal.query(ds, 'SELECT * WHERE { ?s ?p ?o }');
//
// entry also accepts a Promise of the ABI object, or a zero-argument
// function returning either (an object, or a Promise of one) — useful
// when the entry bundle is loaded asynchronously, e.g. a classic
// <script> tag's `load` event, or a dynamic `import()`:
//
//   const factoidal = createApi(() => import('@factoidal/core/factoidal-npm-entry.js')
//     .then((m) => m.factoidalNpmEntry ?? globalThis.factoidalNpmEntry));
//
// What this route does NOT cover: the CLI bundle (factoidal.js /
// factoidal.wasm.js) is never loaded here, so entailment-regime
// queries ({entail: 'RDFS' | 'OWL-RL'}) and queryHdt() reject — both
// need the CLI's argv-driven surface, which stays a separate,
// eval-based bundle (see index.js/wasm.js and README.md's "Bundlers
// and Content Security Policy" section for why, and for the two ways
// to load the entry bundle itself without `unsafe-eval`).

'use strict';

const { buildApi, ParseError } = require('./lib/api.js');
const rdfjs = require('./rdfjs.js');
const pkg = require('./package.json');

const version = pkg.version;

const CLI_UNAVAILABLE_MESSAGE =
  'this API was created from an engine entry object; the CLI bundle ' +
  '(factoidal.js) is not loaded, so entailment-regime queries and ' +
  'queryHdt are unavailable here';

function isThenable(x) {
  return !!x && (typeof x === 'object' || typeof x === 'function') &&
    typeof x.then === 'function';
}

// Confirm the resolved value looks like the factoidalNpmEntry ABI
// object (rather than, say, the whole module that WRAPS it, or a
// typo'd import) before wiring it into buildApi -- queryDataset is
// the one op every ABI variant (js/wasm, any bundle age) has always
// exported, so its presence is the cheapest reliable signal.
function requireAbi(abi) {
  if (!abi || typeof abi.queryDataset !== 'function') {
    const got = abi === null || abi === undefined ? String(abi) : typeof abi;
    throw new TypeError(
      'createApi: expected the factoidalNpmEntry ABI object (one with ' +
      'a queryDataset function -- the value factoidal-npm-entry.js / ' +
      'factoidal-npm-entry.wasm.js registers as module.exports.' +
      'factoidalNpmEntry or globalThis.factoidalNpmEntry), got ' + got +
      '. Did you pass the whole module instead of its .factoidalNpmEntry property?');
  }
  return abi;
}

/**
 * Build a typed API (parse/query/serialize/... — the same surface
 * index.js/wasm.js export) around an already-loaded npm-entry ABI
 * object, without fetching or `eval`-ing anything.
 *
 * @param {object|Promise<object>|(() => object|Promise<object>)} entry
 *   The `factoidalNpmEntry` ABI object, a Promise of one, or a
 *   zero-argument function returning either.
 * @param {{engineName?: string, initCrypto?: () => Promise<void>}} [options]
 * @returns {object} buildApi()'s typed surface, with `engine` set to
 *   `options.engineName` (default 'entry') and `version` the package
 *   version.
 */
function createApi(entry, options) {
  const opts = options || {};
  // When `entry` is already a plain object (the common case --
  // `createApi(mod.factoidalNpmEntry)`), there is nothing to await:
  // validate right now and fail loudly, instead of degrading into the
  // CLI_UNAVAILABLE_MESSAGE path the first time a caller runs a query.
  let resolved = (typeof entry !== 'function' && !isThenable(entry))
    ? requireAbi(entry)
    : undefined;

  async function loadEntry() {
    if (resolved !== undefined) return resolved;
    const produced = typeof entry === 'function' ? entry() : entry;
    resolved = requireAbi(await produced);
    return resolved;
  }

  return buildApi({
    engineName: opts.engineName || 'entry',
    loadEntry,
    runCli: async () => ({
      exitCode: 1,
      stdout: '',
      stderr: CLI_UNAVAILABLE_MESSAGE,
    }),
    initCrypto: opts.initCrypto,
  });
}

module.exports = {
  createApi,
  buildApi,
  ParseError,
  Dataset: rdfjs.Dataset,
  dataFactory: rdfjs.dataFactory,
  version,
};
