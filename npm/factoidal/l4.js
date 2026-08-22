// factoidal/l4 — the Lean 4 engine (L4Factoidal compiled to wasm32)
// behind the same package namespace as the F*-extracted engines.
//
//   const l4 = require('factoidal/l4');        // or import('factoidal/l4')
//   await l4.version();                        // "L4Factoidal ..."
//   await l4.bgpQuery(triples, bgp);           // SPARQL results JSON
//
// DELIBERATELY NOT BUNDLED: the wasm artifact (~1.4 MB) does not ship
// inside @factoidal/core, so installing the F* engines does not pay
// for the Lean one (packaging decision:
// docs/designissues/2026-08-22-npm-l4-module-packaging.md). This
// module is a thin resolver over three sources, first hit wins:
//
//   1. the companion package `@factoidal/lean` (npm-installed users);
//   2. $FACTOIDAL_L4_ASSETS — a directory holding
//      l4factoidal.{js,mjs,wasm} (custom deployments);
//   3. the repository checkout layout (docs/web/hub/assets/l4/) —
//      what the hub tests and in-repo development use.
//
// The three files must stay together and keep their names: the
// Emscripten glue resolves the .wasm sidecar from its own basename
// (see skills/lean4-wasm-export, "the naming trap").
//
// API surface mirrors docs/web/hub/assets/l4/l4factoidal.js (phase-1
// ABI: version + bgpQuery). New exports appear here when they are
// added to formal/lean4/Wasm/Exports.lean and the wasm is rebuilt.

'use strict';

const { existsSync } = require('node:fs');
const path = require('node:path');
const { pathToFileURL } = require('node:url');

function resolveLoader() {
  try {
    return require.resolve('@factoidal/lean/l4factoidal.js');
  } catch { /* not installed */ }
  const env = process.env.FACTOIDAL_L4_ASSETS;
  if (env && existsSync(path.join(env, 'l4factoidal.js'))) {
    return path.join(env, 'l4factoidal.js');
  }
  const repo = path.join(__dirname, '..', '..', 'docs', 'web', 'hub', 'assets', 'l4', 'l4factoidal.js');
  if (existsSync(repo)) return repo;
  return null;
}

let l4Promise = null;

async function loadL4() {
  if (l4Promise) return l4Promise;
  const loaderPath = resolveLoader();
  if (!loaderPath) {
    throw new Error(
      'factoidal/l4: Lean engine assets not found. Install the companion ' +
      'package (npm install @factoidal/lean), or set FACTOIDAL_L4_ASSETS to ' +
      'a directory containing l4factoidal.js, l4factoidal.mjs and ' +
      'l4factoidal.wasm. The Lean engine ships separately so ' +
      '@factoidal/core stays small.');
  }
  l4Promise = import(pathToFileURL(loaderPath).href).then((m) => m.loadL4());
  return l4Promise;
}

module.exports = {
  engine: 'lean4-wasm',
  /** True when the wasm assets are resolvable without loading them. */
  available: () => resolveLoader() !== null,
  /** Load (once) and return the low-level engine handle. */
  loadL4,
  /** Engine identification string from the Lean side. */
  version: async () => (await loadL4()).version(),
  /**
   * Evaluate a basic graph pattern over an in-memory triple list.
   * Arguments and result use SPARQL Query Results JSON term shapes;
   * see docs/web/hub/36-lean-in-the-browser.md for worked examples.
   */
  bgpQuery: async (triples, bgp) => (await loadL4()).bgpQuery(triples, bgp),
};
