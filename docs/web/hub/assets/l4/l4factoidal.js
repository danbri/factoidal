// l4factoidal.js — ES-module loader for the Lean 4 engine compiled to
// WebAssembly. ONE artifact serves the browser, Node and Deno.
//
//   import { loadL4 } from './l4factoidal.js';
//   const l4 = await loadL4();
//   l4.version();                 // "l4factoidal-wasm 0.1.0 (…)"
//   l4.bgpQuery(triples, bgp);    // SPARQL Query Results JSON
//
// HOW ONE FILE SERVES THREE RUNTIMES
// The only thing the three environments genuinely disagree about is how
// to get the .wasm bytes, and Emscripten's glue already handles that
// correctly for all three: `fetch` under a browser, `node:fs` under
// Node, and Deno takes the Node path through its `node:` compatibility
// layer (needs `--allow-read` for a `file:` URL). What it will NOT do is
// honour a `wasmBinary` we pass in — Emscripten 6 resolves the sidecar
// from the GLUE FILE'S OWN BASENAME and ignores the option, which is why
// the glue is named `l4factoidal.mjs` and the module `l4factoidal.wasm`.
// Rename one and every runtime fails with ENOENT on the other.
//
// MEMORY
// Every `char *` the wasm returns is malloc'd inside the module and is
// freed here in a `finally`, so a throwing JSON.parse cannot leak. See
// formal/lean4/Wasm/l4_shim.c for the ownership contract.
//
// Regenerate the wasm with formal/lean4/Wasm/build-wasm.sh.

import createModule from './l4factoidal.mjs';

let modulePromise = null;

/**
 * Instantiate the Lean engine (once per module instance; repeated calls
 * return the same promise). Resolves to the API object.
 */
export function loadL4() {
  if (modulePromise) return modulePromise;
  modulePromise = (async () => {
    const Module = await createModule();

    const cVersion = Module.cwrap('l4_version_c', 'number', []);
    const cBgpQuery = Module.cwrap('l4_bgp_query_c', 'number', ['string', 'string']);
    const cFree = Module.cwrap('l4_free_result', null, ['number']);
    const cInit = Module.cwrap('l4_init', 'number', []);

    // Run the Lean module initialisers now, so the first query is timed
    // as a query rather than as initialisation.
    if (!cInit()) throw new Error('l4factoidal: Lean module initialisation failed');

    /** Read a returned string out of the wasm heap and release it. */
    const take = (ptr) => {
      if (!ptr) throw new Error('l4factoidal: the engine returned no result');
      try { return Module.UTF8ToString(ptr); } finally { cFree(ptr); }
    };

    const asJson = (v) => (typeof v === 'string' ? v : JSON.stringify(v));

    return {
      /** The Lean-side ABI version string. */
      version() { return take(cVersion()); },

      /**
       * Evaluate a Basic Graph Pattern (SPARQL 1.1 §18.3) with Lean's
       * `L4Factoidal.SPARQL.evalBgp`.
       *
       * @param data  array of {subject,predicate,object} term objects
       *              (or the equivalent JSON string)
       * @param bgp   array of the same shape, where any position may be
       *              {"type":"var","value":"…"}
       * @returns     a SPARQL 1.1 Query Results JSON document
       * @throws      if the Lean side reports a decoding error
       */
      bgpQuery(data, bgp) {
        const parsed = JSON.parse(take(cBgpQuery(asJson(data), asJson(bgp))));
        if (parsed.error) throw new Error(`l4factoidal: ${parsed.error}`);
        return parsed;
      },

      /** Escape hatch for tests: the raw Emscripten module. */
      _module: Module,
    };
  })();
  return modulePromise;
}

export default loadL4;
