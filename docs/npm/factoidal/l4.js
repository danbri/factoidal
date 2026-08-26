// factoidal/l4 — the Lean 4 engine (L4Factoidal compiled to wasm32)
// behind the same package namespace as the F*-extracted engines.
//
//   const l4 = require('factoidal/l4');        // or import('factoidal/l4')
//   await l4.version();                        // "L4Factoidal ..."
//   await l4.bgpQuery(triples, bgp);           // SPARQL results JSON
//
// BUNDLED since issue #618: `@factoidal/core` now ships the Lean wasm
// directly under `l4-assets/` (l4factoidal.{js,mjs,wasm} + version.json
// — l4-assets/version.json, not this package's own version.json, which
// stays the F* engine's), so one `npm install @factoidal/core` gets
// both engines. The +23%-tarball objection that shaped the earlier
// companion-package split
// (docs/designissues/2026-08-22-npm-l4-module-packaging.md) no longer
// applies once measured against the real 21-op dispatch surface — see
// that doc's "issue #618: option A after all" section for the full
// argument. This module is now a resolver over FOUR sources, first hit
// wins:
//
//   1. this package's own l4-assets/ (the normal case, since #618);
//   2. the companion package `@factoidal/lean` (never published — kept
//      only as a manual-override path for anyone pinning an older
//      Lean build against a newer core; see npm/factoidal-lean/README.md);
//   3. $FACTOIDAL_L4_ASSETS — a directory holding
//      l4factoidal.{js,mjs,wasm} (custom deployments);
//   4. the repository checkout layout (docs/web/hub/assets/l4/) —
//      what the hub tests and in-repo development use.
//
// Every source's three files must stay together and keep their names:
// the Emscripten glue resolves the .wasm sidecar from its own basename
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
  const inPkg = path.join(__dirname, 'l4-assets', 'l4factoidal.js');
  if (existsSync(inPkg)) return inPkg;
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
      'factoidal/l4: Lean engine assets not found. They normally ship in ' +
      "this package's own l4-assets/ directory — if it is missing, this " +
      'checkout/install is incomplete. Otherwise set FACTOIDAL_L4_ASSETS ' +
      'to a directory containing l4factoidal.js, l4factoidal.mjs and ' +
      'l4factoidal.wasm, or install the (unpublished, override-only) ' +
      'companion package @factoidal/lean.');
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
