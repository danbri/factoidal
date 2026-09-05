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
//
// WASM VERSIONING (issue #584)
// docs/sw.js serves same-origin assets stale-while-revalidate, keyed
// by pathname. Without a content-derived query string on the wasm
// fetch, a fresh l4factoidal.js could pair with the PREVIOUS build's
// l4factoidal.wasm for one page load after a deploy (loader and wasm
// share one URL, so a stale cache entry for that URL is
// indistinguishable from a fresh one). WASM_VERSION below is the
// first 12 hex chars of the wasm's sha256 (matching version.json's
// wasmSha256) and is stamped into this file by build-wasm.sh step 9
// every time the wasm is rebuilt, so the URL changes exactly when the
// bytes change.

// Stamped by formal/lean4/Wasm/build-wasm.sh step 9 -- do not hand-edit.
const WASM_VERSION = "7df3acd699ec";

import createModule from './l4factoidal.mjs';

let modulePromise = null;

// Only a browser/worker page load goes through the ServiceWorker's
// cache; Node's (and Deno's node-compat) `fs.readFileSync` path
// resolves the locateFile() result as a literal filesystem path, so
// appending a query string there would 404 against a file that
// doesn't exist under that name. Version the URL only where the
// staleness this fixes can actually happen.
const isNodeLike = !!(globalThis.process && globalThis.process.versions && globalThis.process.versions.node);

/**
 * Instantiate the Lean engine (once per module instance; repeated calls
 * return the same promise). Resolves to the API object.
 */
export function loadL4() {
  if (modulePromise) return modulePromise;
  modulePromise = (async () => {
    const moduleArg = isNodeLike ? {} : {
      // Called by the Emscripten glue only to resolve the sibling
      // .wasm (see l4factoidal.mjs's findWasmBinary); appending the
      // content-hash query string here is the fix, not a rename --
      // the glue still opens the file by its real basename.
      locateFile(path, scriptDirectory) {
        return path.endsWith('.wasm')
          ? `${scriptDirectory}${path}?v=${WASM_VERSION}`
          : scriptDirectory + path;
      },
    };
    const Module = await createModule(moduleArg);

    const cVersion = Module.cwrap('l4_version_c', 'number', []);
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

    // Emscripten's cwrap `string` converter uses the WebAssembly stack.
    // Multi-megabyte RDF/block requests can therefore overflow STACK_SIZE
    // before Lean sees them. Allocate input UTF-8 on the wasm heap instead;
    // the C shim copies each input into a Lean String synchronously, so these
    // buffers can be released as soon as the exported call returns.
    const callWithHeapStrings = (fn, texts) => {
      const pointers = [];
      try {
        for (const text of texts) {
          const size = Module.lengthBytesUTF8(text) + 1;
          const ptr = Module._malloc(size);
          if (!ptr) throw new Error('l4factoidal: could not allocate a WASM input buffer');
          Module.stringToUTF8(text, ptr, size);
          pointers.push(ptr);
        }
        return fn(...pointers);
      } finally {
        for (let i = pointers.length - 1; i >= 0; i--) Module._free(pointers[i]);
      }
    };

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
        const resultPtr = callWithHeapStrings(Module._l4_bgp_query_c,
          [asJson(data), asJson(bgp)]);
        const parsed = JSON.parse(take(resultPtr));
        if (parsed.error) throw new Error(`l4factoidal: ${parsed.error}`);
        return parsed;
      },

      /**
       * The dispatch ABI (formal/lean4/Wasm/Dispatch.lean): one entry
       * for every npm-entry-shaped op the Lean engine serves. Method
       * names and envelopes match bin/npm-entry/entry_jsoo.ml.
       *
       * @param op    the method name, e.g. "parseToDatasetJson";
       *              "ops" lists the available names
       * @param args  array of positional STRING arguments
       * @returns     the parsed {"ok":true,...} envelope
       * @throws      if the Lean side reports {"ok":false,"error":...}
       */
      call(op, args) {
        const resultPtr = callWithHeapStrings(Module._l4_call_c,
          [op, JSON.stringify(args)]);
        const parsed = JSON.parse(take(resultPtr));
        if (parsed.ok === false) throw new Error(`l4factoidal: ${parsed.error}`);
        return parsed;
      },

      /**
       * The dispatch ABI, plus ONE contiguous byte region.
       *
       * For ops whose input is block bytes rather than text
       * (`storeQuery`; the `ops` reflection lists them under
       * `blobOps`). The bytes are written straight into the wasm heap
       * with no encoding — no hex, no base64 — and copied once into a
       * Lean ByteArray on the Lean side. Which bytes belong to which
       * artifact is said in `args`, as {"key","offset","len"} windows
       * into the region; Lean bounds-checks every one of them, so this
       * call cannot pass a stale or out-of-range pointer.
       *
       * @param op    the method name, e.g. "storeQuery"
       * @param args  array of positional STRING arguments
       * @param blob  Uint8Array (or ArrayBuffer) of the concatenated bytes
       * @returns     the parsed {"ok":true,...} envelope
       * @throws      if the Lean side reports {"ok":false,"error":...}
       */
      callBlob(op, args, blob) {
        const bytes = blob instanceof Uint8Array ? blob : new Uint8Array(blob ?? 0);
        const blobPtr = bytes.length > 0 ? Module._malloc(bytes.length) : 0;
        if (bytes.length > 0 && !blobPtr) {
          throw new Error('l4factoidal: could not allocate a WASM blob buffer');
        }
        try {
          if (bytes.length > 0) Module.HEAPU8.set(bytes, blobPtr);
          const resultPtr = callWithHeapStrings(
            (opPtr, argsPtr) => Module._l4_call_blob_c(opPtr, argsPtr, blobPtr, bytes.length),
            [op, JSON.stringify(args)]);
          const parsed = JSON.parse(take(resultPtr));
          if (parsed.ok === false) throw new Error(`l4factoidal: ${parsed.error}`);
          return parsed;
        } finally {
          if (blobPtr) Module._free(blobPtr);
        }
      },

      /**
       * The dispatch ABI, plus ONE byte region IN and ONE byte region
       * OUT.
       *
       * For the ops of `L4Wasm.blobIoOpNames` (the `ops` envelope lists
       * them under `blobIoOps`), whose RESULT is bytes rather than
       * text. The bytes leave the module raw — no hex, no base64 — and
       * are copied out of the wasm heap into a fresh Uint8Array before
       * the module's buffer is released. The copy is required: the heap
       * is detached and replaced when the module grows, so a subarray
       * view of it can go stale between calls.
       *
       * Every other op answers as `call` does, with an empty region.
       *
       * @param op     the method name, e.g. "blobEcho"
       * @param args   array of positional STRING arguments
       * @param blobIn Uint8Array (or ArrayBuffer) carried IN; may be omitted
       * @returns      { envelope, bytes } — the parsed {"ok":true,...}
       *               envelope and a Uint8Array of the out region
       * @throws       if the Lean side reports {"ok":false,"error":...}
       */
      callBlobIO(op, args, blobIn) {
        const bytes = blobIn instanceof Uint8Array
          ? blobIn
          : new Uint8Array(blobIn ?? 0);
        // Two 32-bit out parameters, uint8_t **out_ptr and size_t
        // *out_len, in one 8-byte cell.
        const outCell = Module._malloc(8);
        if (!outCell) throw new Error('l4factoidal: could not allocate the out-parameter cell');
        const blobPtr = bytes.length > 0 ? Module._malloc(bytes.length) : 0;
        if (bytes.length > 0 && !blobPtr) {
          Module._free(outCell);
          throw new Error('l4factoidal: could not allocate a WASM blob buffer');
        }
        let outPtr = 0;
        try {
          Module.setValue(outCell, 0, 'i32');
          Module.setValue(outCell + 4, 0, 'i32');
          if (bytes.length > 0) Module.HEAPU8.set(bytes, blobPtr);
          const resultPtr = callWithHeapStrings(
            (opPtr, argsPtr) => Module._l4_call_blob_io_c(
              opPtr, argsPtr, blobPtr, bytes.length, outCell, outCell + 4),
            [op, JSON.stringify(args)]);
          outPtr = Module.getValue(outCell, 'i32') >>> 0;
          const outLen = Module.getValue(outCell + 4, 'i32') >>> 0;
          const envelope = JSON.parse(take(resultPtr));
          if (envelope.ok === false) throw new Error(`l4factoidal: ${envelope.error}`);
          // slice() copies; HEAPU8 is replaced wholesale when the
          // module's memory grows, so a view would not survive.
          const region = outPtr !== 0 && outLen > 0
            ? Module.HEAPU8.slice(outPtr, outPtr + outLen)
            : new Uint8Array(0);
          return { envelope, bytes: region };
        } finally {
          if (outPtr) Module._l4_free_blob(outPtr);
          if (blobPtr) Module._free(blobPtr);
          Module._free(outCell);
        }
      },

      /** Escape hatch for tests: the raw Emscripten module. */
      _module: Module,
    };
  })();
  return modulePromise;
}

export default loadL4;
