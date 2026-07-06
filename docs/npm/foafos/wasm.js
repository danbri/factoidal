// factoidal — Node entry point for the **wasm** engine.
//
// Same public API as index.js (parse / query / update / serialize /
// canonicalize / graphs / canonicalHash / dataFactory / Dataset),
// backed by the wasm_of_ocaml
// bundle (factoidal.wasm.js + factoidal.wasm.assets/). Requires a
// WasmGC-capable runtime: Node >= 22.
//
//   const factoidal = require('factoidal/wasm');
//   const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples',
//     baseIRI: 'http://example.org/' });
//
// All calls are async (wasm instantiation happens per invocation on
// the CLI path). For browsers, see browser-wasm.js.

'use strict';

const fs = require('node:fs');
const path = require('node:path');

const engine = require('./lib/engine-wasm.js');
const { buildApi } = require('./lib/api.js');
const rdfjs = require('./rdfjs.js');

const pkg = require('./package.json');
const version = pkg.version;

// ---------------------------------------------------------------------
// npm-entry ABI loader (wasm flavor). The wasm entry bundle
// (factoidal-npm-entry.wasm.js) is an async IIFE like the CLI wasm
// loader; we capture its Promise via the same one-marker rewrite,
// await initialization once, and cache the exported ABI object.
// ---------------------------------------------------------------------

// The bundle's entry is an immediately-invoked async factory:
//   ;(<param>=>async <arg>=>{...})(...)
// wasm_of_ocaml minifies <param> differently across versions ('$'
// before mid-2026, 'ag' in 6.4.1) - match the shape, not a fixed
// name, and splice the __fwPromise capture in after the leading ';'.
const IIFE_RE = /;\((\$|[A-Za-z_$][\w$]*)=>async /;
const IIFE_CAPTURE = ';globalThis.__fwPromise=';

function entryCandidates() {
  const c = [];
  if (process.env.FACTOIDAL_NPM_ENTRY_WASM) {
    c.push(process.env.FACTOIDAL_NPM_ENTRY_WASM);
  }
  c.push(path.join(__dirname, 'factoidal-npm-entry.wasm.js'));
  c.push(path.resolve(
    __dirname, '..', '..', 'docs', 'fstar-extracted',
    'factoidal-npm-entry.wasm.js'));
  return c;
}

let entryPromise = null;

async function loadEntry() {
  if (entryPromise) return entryPromise;
  entryPromise = (async () => {
    for (const p of entryCandidates()) {
      if (!p || !fs.existsSync(p)) continue;
      const raw = fs.readFileSync(p, 'utf8');
      const m = IIFE_RE.exec(raw);
      if (!m) continue;
      const src = raw.slice(0, m.index) + IIFE_CAPTURE + raw.slice(m.index + 1);
      const module_ = { exports: {} };
      const prevFw = globalThis.__fwPromise;
      delete globalThis.__fwPromise;
      try {
        // The entry bundle has no CLI main — it only registers exports
        // — so no argv/exit shimming is needed. Real fs is fine: the
        // loader reads its .wasm asset relative to module paths BUT
        // does so via `require.main.filename` (not the `__filename`
        // param above) to find `factoidal-npm-entry.wasm.assets/`.
        // When this file is loaded from a consumer whose own
        // require.main lives elsewhere (any test/ subdirectory, any
        // downstream package), the real require.main points at the
        // wrong directory and the asset read throws ENOENT deep
        // inside the wasm loader's init — silently caught below and
        // misreported as "entry bundle unavailable" (this is what
        // made capabilities() report entry:false for the wasm engine
        // even though the bundle was present and valid). Wrap `require`
        // so `.main.filename` points at the bundle itself, which sits
        // next to its own `.wasm.assets/` directory.
        const fakeRequire = Object.assign(
          (name) => require(name), { main: { filename: p } });
        (new Function('module', 'exports', 'require', '__filename',
          '__dirname', src))(
          module_, module_.exports, fakeRequire, p, path.dirname(p));
        const fw = globalThis.__fwPromise;
        if (fw && typeof fw.then === 'function') await fw;
        const abi = module_.exports.factoidalNpmEntry ||
          (globalThis.jsoo_exports && globalThis.jsoo_exports.factoidalNpmEntry) ||
          globalThis.factoidalNpmEntry;
        if (abi && typeof abi.queryDataset === 'function') return abi;
      } catch (_) {
        // Fall through to the next candidate / CLI fallback.
      } finally {
        if (prevFw === undefined) delete globalThis.__fwPromise;
        else globalThis.__fwPromise = prevFw;
      }
    }
    return null;
  })();
  return entryPromise;
}

const api = buildApi({
  engineName: 'wasm',
  runCli: engine.runCli,
  loadEntry,
});

module.exports = {
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
  wasmAvailable: engine.wasmAvailable,
  version,
  // Test-only hook: the raw npm-entry ABI object (deltaBatchToHex,
  // deltaMergeApplyBrowser, shaclValidate, ...) loaded straight off
  // the wasm bundle, bypassing buildApi()'s Dataset-shaped surface.
  // Mirrors browser-wasm.js's _setFactoidalWasmSource/
  // _setWasmAssetFallback test hooks. Not part of the public API.
  _loadEntryForTest: loadEntry,
};
