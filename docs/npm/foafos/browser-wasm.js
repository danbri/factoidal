// factoidal — browser ESM entry for the **wasm** bundle.
//
// This is the wasm_of_ocaml-compiled sibling of ./browser.js. Same
// async API; different extraction target under the hood. Use this
// when you need the smaller/faster wasm path (Chrome >= 119,
// Edge >= 119, Node >= 22; Firefox needs Wasm-GC to ship before
// this works there).
//
//   <script type="module">
//     import { query } from 'https://unpkg.com/factoidal/browser-wasm.js';
//     const r = await query(dataTtl,
//       'SELECT * WHERE { ?s ?p ?o }',
//       { entail: 'RDFS' }
//     );
//     console.log(r.results.bindings);
//   </script>
//
// --- How we drive the wasm bundle ---
//
// `factoidal.wasm.js` is a single top-level `(async () => ...)(...)`
// expression emitted by wasm_of_ocaml. It inspects
// `globalThis.process.versions.node` to decide between two paths:
//
//   - Node path: uses `require("node:fs")` + `require("node:path")` +
//     `require("node:fs/promises")` to write stdout, resolve the
//     `.wasm` asset, and (critically) reads CLI args from
//     `globalThis.process.argv`. All real I/O — including the data
//     file at `-d /static/data.ttl` — goes through `f.openSync`
//     etc. NB: unlike the non-wasm bundle, **there is no MlFakeDevice**;
//     `globalThis.jsoo_fs_tmp` is not consulted.
//
//   - Browser path: uses `fetch()` to load the `.wasm` asset and
//     falls back to `console.log` / `console.error` for stdout /
//     stderr. Argv defaults to `["a.out"]` — so we can't drive the
//     CLI at all through the browser branch. For a CLI-shaped
//     entry-point we have to keep the Node branch and shim
//     `require()` + `globalThis.process` ourselves.
//
// We therefore take the **Node branch in every environment** and
// inject a fake `require()` + `process` that back everything with
// in-memory buffers:
//
//   - fake `require("node:fs")` routes `writeSync(1, ...)` and
//     `writeSync(2, ...)` into per-call stdout/stderr arrays;
//   - `openSync`/`readSync`/`fstatSync`/`existsSync` serve up the
//     single `/static/data.<ext>` entry seeded from `dataString`;
//   - fake `require("node:fs/promises")` reads the `.wasm` asset
//     via `fetch()` under a real browser or via the injected
//     `_setWasmAssetFallback()` hook under Node.
//
// Finally, the wasm_of_ocaml IIFE's top-level expression is a
// fire-and-forget async call — its Promise is *discarded* at the
// source level. We inject a single tiny rewrite
// (`;($=>async ` -> `;globalThis.__fwPromise=($=>async `) to
// capture it, then `await` it and delete it. Without this the
// `new Function(src)()` returns `undefined` before the wasm module
// has even finished loading.

const DEFAULT_WASM_URL = new URL('./factoidal.wasm.js', import.meta.url).href;

let _wasmJsUrl = DEFAULT_WASM_URL;
let _wasmJsSrc = null;          // cached transformed source
let _fetchPromise = null;
let _nodeFsFallback = null;     // test-only: (assetSubPath) => Buffer|Uint8Array

// The bundle's entry is an immediately-invoked async factory:
//   ;(<param>=>async <arg>=>{...})(...)
// wasm_of_ocaml minifies <param> differently across versions ('$'
// before mid-2026, 'ag' in 6.4.1) - match the shape, not a fixed
// name, and splice the __fwPromise capture in after the leading ';'.
// (Synced from docs/fstar-extracted/browser-wasm.js, which carried
// this fix first — the npm package copy had drifted behind it.)
const IIFE_RE = /;\((\$|[A-Za-z_$][\w$]*)=>async /;
const IIFE_CAPTURE = ';globalThis.__fwPromise=';

function rewriteBundle(src) {
  const m = IIFE_RE.exec(src);
  if (!m) {
    // Unexpected bundle shape. Bail loudly.
    throw new Error(
      "browser-wasm: could not locate the async IIFE marker in " +
      "factoidal.wasm.js. The bundle shape may have changed."
    );
  }
  return src.slice(0, m.index) + IIFE_CAPTURE + src.slice(m.index + 1);
}

/**
 * Override where `factoidal.wasm.js` is loaded from. The `.wasm`
 * asset in `factoidal.wasm.assets/` is resolved relative to this URL.
 */
export function setFactoidalWasmUrl(url) {
  _wasmJsUrl = url;
  _wasmJsSrc = null;
  _fetchPromise = null;
}

/**
 * Current `factoidal.wasm.js` source URL. Mirrors browser.js's
 * `getFactoidalUrl()` — lets a caller check before overriding so it
 * only pays the cache-reset cost when the URL actually changes.
 */
export function getFactoidalWasmUrl() {
  return _wasmJsUrl;
}

/**
 * Test-only hook. Lets the Node smoke test inject an fs-based
 * reader for the .wasm asset so we don't have to polyfill fetch()
 * across Node versions. Pass `null` to clear.
 *   _setWasmAssetFallback((assetSubPath) => fs.readFileSync(...))
 */
export function _setWasmAssetFallback(reader) {
  _nodeFsFallback = reader;
}

/**
 * Test-only hook to seed the cached (already-rewritten) source
 * without going through fetch(). Used by the Node smoke test.
 */
export function _setFactoidalWasmSource(src) {
  _wasmJsSrc = rewriteBundle(src);
}

function loadFactoidalWasmSource() {
  if (_wasmJsSrc) return Promise.resolve(_wasmJsSrc);
  if (_fetchPromise) return _fetchPromise;
  _fetchPromise = fetch(_wasmJsUrl)
    .then((r) => {
      if (!r.ok) {
        throw new Error(
          `factoidal.wasm.js fetch failed: ${r.status} ${r.statusText}`
        );
      }
      return r.text();
    })
    .then((text) => { _wasmJsSrc = rewriteBundle(text); return _wasmJsSrc; });
  return _fetchPromise;
}

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
};

const OUTPUT_FORMATS = new Set(['json', 'csv', 'tsv', 'xml', 'table', 'ntriples']);
const ENTAIL_VALUES  = new Set(['none', 'RDFS', 'OWL-RL']);

function extForFormat(fmt) {
  const key = String(fmt || 'turtle').toLowerCase();
  if (!(key in DATA_FORMAT_EXT)) {
    throw new TypeError(
      `Unknown dataFormat '${fmt}'. Expected one of: ` +
      Object.keys(DATA_FORMAT_EXT).join(', ')
    );
  }
  return DATA_FORMAT_EXT[key];
}

function assetSubPath(urlLike) {
  const s = typeof urlLike === 'string'
    ? urlLike
    : (urlLike && urlLike.url) || String(urlLike);
  const marker = 'factoidal.wasm.assets/';
  const ix = s.lastIndexOf(marker);
  return ix < 0 ? s : s.slice(ix);
}

// Small helper: reify a Node-ish Stats object (with optional
// bigint mode) for our fake files. Real Node returns BigInt fields
// when called as `statSync(p, { bigint: true })`; the wasm loader
// uses that flag for `file_size`.
function makeStat(size, isFile, opts) {
  const bigint = !!(opts && opts.bigint);
  const toN = (v) => bigint ? BigInt(v) : v;
  return {
    isFile:            () => isFile,
    isDirectory:       () => false,
    isCharacterDevice: () => !isFile,
    isBlockDevice:     () => false,
    isSymbolicLink:    () => false,
    isFIFO:            () => false,
    isSocket:          () => false,
    dev: toN(0), ino: toN(0), mode: toN(0o100644),
    nlink: toN(1), uid: toN(0), gid: toN(0), rdev: toN(0),
    size: toN(size),
    atimeMs: bigint ? 0n : 0,
    mtimeMs: bigint ? 0n : 0,
    ctimeMs: bigint ? 0n : 0,
  };
}

/**
 * Run a SPARQL query against an RDF dataset in memory, using the
 * wasm_of_ocaml bundle.
 *
 * @param {string} dataString
 * @param {string} queryString
 * @param {object} [options]
 * @param {string} [options.dataFormat='turtle']
 * @param {string} [options.entail='none']
 * @param {string} [options.output='json']
 * @returns {Promise<object|string>}
 */
export async function query(dataString, queryString, options) {
  if (typeof dataString !== 'string') {
    throw new TypeError('query: dataString must be a string');
  }
  if (typeof queryString !== 'string') {
    throw new TypeError('query: queryString must be a string');
  }

  const opts       = options || {};
  const dataFormat = opts.dataFormat || 'turtle';
  const entail     = opts.entail     || 'none';
  const output     = opts.output     || 'json';

  if (!ENTAIL_VALUES.has(entail)) {
    throw new TypeError(
      `query: entail must be one of ${[...ENTAIL_VALUES].join(', ')}`
    );
  }
  if (!OUTPUT_FORMATS.has(output)) {
    throw new TypeError(
      `query: output must be one of ${[...OUTPUT_FORMATS].join(', ')}`
    );
  }

  const src = await loadFactoidalWasmSource();

  const ext      = extForFormat(dataFormat);
  const dataPath = '/static/data.' + ext;

  // Seed the fake filesystem with just the one input file.
  const TE = new TextEncoder();
  const dataBytes = TE.encode(dataString);

  // Preserve anything we're about to overwrite so we can roll back
  // cleanly — even on throw.
  const orig = {
    proc:    globalThis.process,
    jsooFs:  globalThis.jsoo_fs_tmp,
    fetch:   globalThis.fetch,
    require: globalThis.require,
    fwPromise: globalThis.__fwPromise,
  };

  const stdoutBuf = [];
  const stderrBuf = [];
  const pushOut = (chunk) => stdoutBuf.push(chunk);
  const pushErr = (chunk) => stderrBuf.push(chunk);

  const argv = [
    'node', 'factoidal',
    '-d', dataPath,
    '-e', queryString,
    '-o', output === 'json' ? 'json' : output,
  ];
  if (entail !== 'none') argv.push('--entail', entail);

  let exitCode = 0;
  const EXIT_SENTINEL = new Error('__factoidal_exit__');
  EXIT_SENTINEL.__factoidalExit = true;

  // ---- fake fs (single-file, read-only, /static/data.<ext>) ----
  const TD = new TextDecoder('utf-8');
  const fakeOpenFds = Object.create(null);
  let nextFd = 100;

  function writeSync(fd, buf, offset, length /*, position */) {
    let s;
    if (typeof buf === 'string') {
      s = buf;
    } else {
      const u8 = (buf instanceof Uint8Array)
        ? buf
        : new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength);
      const start = offset || 0;
      const end   = start + (length === undefined ? u8.length - start : length);
      s = TD.decode(u8.subarray(start, end));
    }
    (fd === 2 ? pushErr : pushOut)(s);
    return length === undefined ? s.length : length;
  }

  function fileForPath(p) {
    if (p === dataPath) return dataBytes;
    return null;
  }

  const fakeFs = {
    constants: {
      R_OK: 4, W_OK: 2, X_OK: 1, F_OK: 0,
      O_RDONLY: 0, O_WRONLY: 1, O_RDWR: 2, O_APPEND: 8, O_CREAT: 512,
      O_TRUNC: 1024, O_EXCL: 2048, O_NONBLOCK: 4096, O_NOCTTY: 8192,
      O_DSYNC: 4194304, O_SYNC: 128,
    },
    writeSync,
    openSync: (p /*, flags, mode */) => {
      const f = fileForPath(String(p));
      if (!f) {
        throw Object.assign(new Error(`ENOENT: no such file or directory, open '${p}'`),
          { code: 'ENOENT', errno: -2, syscall: 'open', path: p });
      }
      const fd = nextFd++;
      fakeOpenFds[fd] = { path: String(p), buf: f, offset: 0 };
      return fd;
    },
    closeSync: (fd) => { delete fakeOpenFds[fd]; },
    readSync: (fd, buf, offset, length, position) => {
      const f = fakeOpenFds[fd];
      if (!f) throw Object.assign(new Error('EBADF'), { code: 'EBADF', errno: -9 });
      const pos = (position === null || position === undefined) ? f.offset : Number(position);
      const remaining = Math.max(0, f.buf.length - pos);
      const n = Math.min(length, remaining);
      for (let i = 0; i < n; i++) buf[offset + i] = f.buf[pos + i];
      if (position === null || position === undefined) f.offset = pos + n;
      return n;
    },
    fsyncSync: () => {},
    existsSync: (p) => fileForPath(String(p)) !== null,
    accessSync: (p) => {
      if (!fileForPath(String(p))) {
        throw Object.assign(new Error(`ENOENT`), { code: 'ENOENT', errno: -2 });
      }
    },
    statSync: (p, o) => {
      const f = fileForPath(String(p));
      if (!f) {
        if (o && o.throwIfNoEntry === false) return undefined;
        throw Object.assign(new Error(`ENOENT`), { code: 'ENOENT', errno: -2 });
      }
      return makeStat(f.length, true, o);
    },
    lstatSync: (p, o) => fakeFs.statSync(p, o),
    fstatSync: (fd, o) => {
      const f = fakeOpenFds[fd];
      return makeStat(f ? f.buf.length : 0, !!f, o);
    },
  };

  // Resolve the .wasm asset: prefer the test-injected reader, else
  // fall back to a fetch() relative to _wasmJsUrl.
  async function readWasmAsset(requestedPath) {
    const sub = assetSubPath(String(requestedPath));
    if (_nodeFsFallback) {
      const bytes = await _nodeFsFallback(sub);
      return bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
    }
    const resolved = new URL(sub, _wasmJsUrl).href;
    const fetchFn = orig.fetch || globalThis.fetch;
    if (!fetchFn) {
      throw new Error(
        "browser-wasm: no fetch() available and no _setWasmAssetFallback() " +
        "injected. In Node <20 or an exotic runtime, set a fallback reader."
      );
    }
    const r = await fetchFn(resolved);
    if (!r.ok) {
      throw new Error(`wasm asset fetch failed: ${r.status} ${r.statusText} (${resolved})`);
    }
    return new Uint8Array(await r.arrayBuffer());
  }

  const fakeRequire = (name) => {
    if (name === 'node:fs')          return fakeFs;
    if (name === 'node:fs/promises') return { readFile: readWasmAsset };
    if (name === 'node:path')        return {
      join:    (...parts) => parts.filter(Boolean).join('/').replace(/\/+/g, '/'),
      dirname: (p)        => String(p).replace(/\/[^/]*$/, '') || '.',
    };
    if (name === 'node:os')            return { tmpdir: () => '/tmp' };
    if (name === 'node:tty')           return { isatty: () => false };
    if (name === 'node:child_process') return { spawnSync: () => ({ status: 0, signal: null }) };
    throw new Error(`browser-wasm shim: unexpected require('${name}')`);
  };
  // `require.main.filename` is read by the bundle. Its `dirname`
  // gets joined onto `factoidal.wasm.assets/foo.wasm`, which we
  // then strip back to the subpath inside readWasmAsset.
  fakeRequire.main = { filename: '/factoidal/main.js' };

  // Faked process. Keeping `versions.node` truthy forces the bundle
  // down its Node branch (which reads argv from process.argv).
  const fakeProc = {
    argv,
    exit: (n) => { exitCode = n | 0; throw EXIT_SENTINEL; },
    stdout: { write: (s) => pushOut(String(s)) },
    stderr: { write: (s) => pushErr(String(s)) },
    platform: 'linux',
    versions: { node: '22.0.0' },
    env: {},
    cpuUsage: () => ({ user: 0, system: 0 }),
    on:       () => {},
    cwd:      () => '/static',
    chdir:    () => {},
  };

  globalThis.process     = fakeProc;
  globalThis.require     = fakeRequire;
  globalThis.jsoo_fs_tmp = undefined; // wasm bundle doesn't read this, but scrub
  delete globalThis.__fwPromise;

  function restoreGlobals() {
    globalThis.process     = orig.proc;
    globalThis.jsoo_fs_tmp = orig.jsooFs;
    globalThis.fetch       = orig.fetch;
    if (orig.require === undefined) delete globalThis.require;
    else                            globalThis.require = orig.require;
    if (orig.fwPromise === undefined) delete globalThis.__fwPromise;
    else                              globalThis.__fwPromise = orig.fwPromise;
  }

  try {
    // Execute the (rewritten) bundle source. This is synchronous —
    // it spawns an async Promise and stashes it on
    // `globalThis.__fwPromise` via our injected rewrite. We then
    // await that Promise to let wasm instantiation + the CLI body
    // actually run.
    (new Function(src))();
    const p = globalThis.__fwPromise;
    if (!p || typeof p.then !== 'function') {
      throw new Error(
        'browser-wasm: __fwPromise was not captured. ' +
        'The bundle shape may have changed.'
      );
    }
    try {
      await p;
    } catch (e) {
      // The CLI typically calls process.exit(0) on success — our
      // exit() throws EXIT_SENTINEL, which propagates up through
      // the async IIFE. That's the normal path; anything else is
      // a real failure.
      if (e !== EXIT_SENTINEL && !(e && e.__factoidalExit)) {
        throw e;
      }
    }
  } finally {
    restoreGlobals();
  }

  const stdout = stdoutBuf.join('');
  const stderr = stderrBuf.join('');

  if (exitCode !== 0) {
    const msg = (stderr || stdout ||
      `factoidal exited with code ${exitCode}`).trim();
    const err = new Error('SPARQL query failed: ' + msg);
    err.exitCode = exitCode;
    err.stderr   = stderr;
    err.stdout   = stdout;
    throw err;
  }

  if (output !== 'json') return stdout;

  const firstBrace = stdout.indexOf('{');
  const lastBrace  = stdout.lastIndexOf('}');
  if (firstBrace < 0 || lastBrace < firstBrace) {
    const err = new Error(
      'factoidal (wasm) did not produce JSON on stdout. Raw output: ' + stdout
    );
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
  const jsonText = stdout.slice(firstBrace, lastBrace + 1);
  try {
    return JSON.parse(jsonText);
  } catch (e) {
    const err = new Error(
      'factoidal (wasm) JSON parse failed: ' + e.message +
      '. Raw output: ' + stdout
    );
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
}

// ---------------------------------------------------------------------
// npm-entry ABI loader (wasm flavor), browser-driven. Mirrors
// browser.js's loadNpmEntry() for the js_of_ocaml npm-entry bundle
// (factoidal-npm-entry.js), but factoidal-npm-entry.wasm.js is
// wasm_of_ocaml's async-IIFE shape -- same as factoidal.wasm.js above
// -- rather than a synchronous eval that registers
// globalThis.factoidalNpmEntry directly. So this loader reuses the
// same Node-branch-forcing + __fwPromise-capture technique query()
// above uses to drive the CLI bundle (see that function's header
// comment for the full rationale), swapped to await the persistent
// ABI object instead of one call's stdout/stderr. Also mirrors
// wasm.js's Node-side loadEntry() (npm/factoidal/wasm.js) -- fetch()
// instead of fs.readFileSync for the source and the .wasm asset, so
// this works in a real browser with no Node require() at all.
//
// Before this loader existed, browser-wasm.js only drove the CLI
// bundle -- openCottas/queryCottas/closeCottas/toCottas (and every
// other npm-entry-only export: SPARQL UPDATE, CONSTRUCT, RDFC-1.0
// canonicalize, SHACL/ShEx/OWL-closure/RML/CSVW/JSON-LD/RIF) were
// unreachable from the wasm browser entry even though browser.js's js
// entry already exposed them via loadNpmEntry(). This closes that gap
// for the in-memory COTTAS bytes store (docs/designissues/2026-07-06-
// inmemory-bytes-store.md) specifically -- the functions below mirror
// browser.js's openCottas/queryCottas/closeCottas/toCottas verbatim,
// against the wasm ABI object instead of the js one.
// ---------------------------------------------------------------------

const DEFAULT_NPM_ENTRY_WASM_URL =
  new URL('./factoidal-npm-entry.wasm.js', import.meta.url).href;

let _npmEntryWasmUrl = DEFAULT_NPM_ENTRY_WASM_URL;
let _npmEntryWasmSrc = null;         // cached (already-rewritten) source
let _npmEntryFetchPromise = null;
let _npmEntryNodeFsFallback = null;  // test-only: (assetSubPath) => Buffer|Uint8Array
let _npmEntryWasmAbiPromise = null;  // cached loadNpmEntryWasm() result

/**
 * Override where `factoidal-npm-entry.wasm.js` is loaded from. The
 * `.wasm` asset in `factoidal-npm-entry.wasm.assets/` is resolved
 * relative to this URL. Mirrors setFactoidalWasmUrl() above.
 */
export function setFactoidalNpmEntryWasmUrl(url) {
  _npmEntryWasmUrl = url;
  _npmEntryWasmSrc = null;
  _npmEntryFetchPromise = null;
  _npmEntryWasmAbiPromise = null;
}

/** Current `factoidal-npm-entry.wasm.js` source URL. */
export function getFactoidalNpmEntryWasmUrl() {
  return _npmEntryWasmUrl;
}

/**
 * Test-only hook. Lets a Node-side test inject an fs-based reader for
 * the npm-entry `.wasm` asset, mirroring `_setWasmAssetFallback()`
 * above for the CLI bundle -- so tests don't have to polyfill fetch()
 * across Node versions.
 *   _setNpmEntryWasmAssetFallback((assetSubPath) => fs.readFileSync(...))
 */
export function _setNpmEntryWasmAssetFallback(reader) {
  _npmEntryNodeFsFallback = reader;
}

/**
 * Test-only hook to seed the cached (already-rewritten) npm-entry wasm
 * source without going through fetch(), mirroring
 * `_setFactoidalWasmSource()` above.
 */
export function _setFactoidalNpmEntryWasmSource(src) {
  _npmEntryWasmSrc = rewriteBundle(src);
  _npmEntryWasmAbiPromise = null;
}

function loadNpmEntryWasmSource() {
  if (_npmEntryWasmSrc) return Promise.resolve(_npmEntryWasmSrc);
  if (_npmEntryFetchPromise) return _npmEntryFetchPromise;
  _npmEntryFetchPromise = fetch(_npmEntryWasmUrl)
    .then((r) => {
      if (!r.ok) {
        throw new Error(
          `factoidal-npm-entry.wasm.js fetch failed: ${r.status} ${r.statusText}`
        );
      }
      return r.text();
    })
    .then((text) => { _npmEntryWasmSrc = rewriteBundle(text); return _npmEntryWasmSrc; });
  return _npmEntryFetchPromise;
}

function npmEntryAssetSubPath(urlLike) {
  const s = typeof urlLike === 'string'
    ? urlLike
    : (urlLike && urlLike.url) || String(urlLike);
  const marker = 'factoidal-npm-entry.wasm.assets/';
  const ix = s.lastIndexOf(marker);
  return ix < 0 ? s : s.slice(ix);
}

/**
 * Fetch + evaluate `factoidal-npm-entry.wasm.js` exactly once,
 * returning the `factoidalNpmEntry` ABI object it registers on
 * globalThis -- the browser-driven counterpart to wasm.js's Node-side
 * `loadEntry()` (npm/factoidal/wasm.js), and the wasm sibling of
 * `loadNpmEntry()` above. Cached: subsequent calls return the same
 * resolved ABI object without re-fetching or re-evaluating the bundle.
 *
 * @returns {Promise<object>} the factoidalNpmEntry ABI object.
 */
export async function loadNpmEntryWasm() {
  if (_npmEntryWasmAbiPromise) return _npmEntryWasmAbiPromise;
  _npmEntryWasmAbiPromise = (async () => {
    const src = await loadNpmEntryWasmSource();

    const orig = {
      proc:      globalThis.process,
      require:   globalThis.require,
      fwPromise: globalThis.__fwPromise,
    };

    // Resolve the .wasm asset: prefer the test-injected reader, else
    // fetch() relative to _npmEntryWasmUrl (same shape as query()'s
    // readWasmAsset above, against the npm-entry bundle's own URL).
    async function readWasmAsset(requestedPath) {
      const sub = npmEntryAssetSubPath(String(requestedPath));
      if (_npmEntryNodeFsFallback) {
        const bytes = await _npmEntryNodeFsFallback(sub);
        return bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
      }
      const resolved = new URL(sub, _npmEntryWasmUrl).href;
      const fetchFn = globalThis.fetch;
      if (!fetchFn) {
        throw new Error(
          'loadNpmEntryWasm: no fetch() available and no ' +
          '_setNpmEntryWasmAssetFallback() injected. In Node <20 or an ' +
          'exotic runtime, set a fallback reader.'
        );
      }
      const r = await fetchFn(resolved);
      if (!r.ok) {
        throw new Error(
          `npm-entry wasm asset fetch failed: ${r.status} ${r.statusText} (${resolved})`);
      }
      return new Uint8Array(await r.arrayBuffer());
    }

    // No CLI data files here -- the entry ABI is a pure
    // string-in/JSON-out interface (parseToDatasetJson/queryDataset/
    // openCottas/... -- see bin/npm-entry/entry_jsoo.ml's file
    // header). `node:fs` is still `require()`d unconditionally by the
    // wasm_of_ocaml runtime whenever it detects the Node branch
    // (`f=g&&require("node:fs")` at the top of the bundle) even
    // though the entry ABI itself never touches a real file --
    // provide an always-ENOENT stub so that unconditional require()
    // doesn't throw "require is not defined" in a real browser (which
    // has no `node:fs` at all).
    // The wasm_of_ocaml runtime's channel writer calls fs.writeSync(fd, ...)
    // directly for stdout/stderr (fd 1/2) rather than process.stdout.write
    // -- the entry ABI is otherwise silent (it returns JSON strings, it
    // doesn't print), but any incidental Printf/logging still routes
    // through here, so writeSync must be a real (if discarding) function
    // rather than absent, or the runtime throws
    // "f.writeSync is not a function" the first time anything writes.
    const fakeFs = {
      constants: {
        R_OK: 4, W_OK: 2, X_OK: 1, F_OK: 0,
        O_RDONLY: 0, O_WRONLY: 1, O_RDWR: 2, O_APPEND: 8, O_CREAT: 512,
        O_TRUNC: 1024, O_EXCL: 2048, O_NONBLOCK: 4096, O_NOCTTY: 8192,
        O_DSYNC: 4194304, O_SYNC: 128,
      },
      writeSync: (fd, buf, offset, length) => {
        return length === undefined
          ? (typeof buf === 'string' ? buf.length : buf.byteLength)
          : length;
      },
      openSync: (p) => {
        throw Object.assign(new Error(`ENOENT: no such file or directory, open '${p}'`),
          { code: 'ENOENT', errno: -2, syscall: 'open', path: p });
      },
      closeSync: () => {},
      readSync: () => 0,
      fsyncSync: () => {},
      existsSync: () => false,
      accessSync: (p) => {
        throw Object.assign(new Error('ENOENT'), { code: 'ENOENT', errno: -2, path: p });
      },
      statSync: (p, o) => {
        if (o && o.throwIfNoEntry === false) return undefined;
        throw Object.assign(new Error('ENOENT'), { code: 'ENOENT', errno: -2, path: p });
      },
      lstatSync(p, o) { return fakeFs.statSync(p, o); },
      fstatSync: (fd, o) => makeStat(0, false, o),
    };

    const fakeRequire = (name) => {
      if (name === 'node:fs')            return fakeFs;
      if (name === 'node:fs/promises')   return { readFile: readWasmAsset };
      if (name === 'node:path')          return {
        join:    (...parts) => parts.filter(Boolean).join('/').replace(/\/+/g, '/'),
        dirname: (p)        => String(p).replace(/\/[^/]*$/, '') || '.',
      };
      if (name === 'node:os')            return { tmpdir: () => '/tmp' };
      if (name === 'node:tty')           return { isatty: () => false };
      if (name === 'node:child_process') return { spawnSync: () => ({ status: 0, signal: null }) };
      throw new Error(`browser-wasm npm-entry shim: unexpected require('${name}')`);
    };
    // Same trick as query()'s fakeRequire.main below: the bundle joins
    // dirname(require.main.filename) onto its relative asset path,
    // which we then strip back to the subpath inside readWasmAsset.
    fakeRequire.main = { filename: '/factoidal/npm-entry.js' };

    // Faked process -- forces the bundle's Node branch (real I/O via
    // require()) rather than its browser branch (fixed argv, no
    // persistent-ABI registration call). No argv-driven CLI runs
    // through this path, so stdout/stderr/exit are inert stubs.
    const fakeProc = {
      argv: ['node', 'factoidal-npm-entry'],
      exit: () => {},
      stdout: { write: () => true },
      stderr: { write: () => true },
      platform: 'linux',
      versions: { node: '22.0.0' },
      env: {},
      cpuUsage: () => ({ user: 0, system: 0 }),
      on:       () => {},
      cwd:      () => '/static',
      chdir:    () => {},
    };

    globalThis.process = fakeProc;
    globalThis.require = fakeRequire;
    delete globalThis.__fwPromise;

    function restoreGlobals() {
      globalThis.process = orig.proc;
      if (orig.require === undefined) delete globalThis.require;
      else                            globalThis.require = orig.require;
      if (orig.fwPromise === undefined) delete globalThis.__fwPromise;
      else                              globalThis.__fwPromise = orig.fwPromise;
    }

    try {
      (new Function(src))();
      const p = globalThis.__fwPromise;
      if (!p || typeof p.then !== 'function') {
        throw new Error(
          'loadNpmEntryWasm: __fwPromise was not captured. ' +
          'The bundle shape may have changed.'
        );
      }
      await p;
    } finally {
      restoreGlobals();
    }

    const abi = globalThis.factoidalNpmEntry;
    if (!abi || typeof abi.queryDataset !== 'function') {
      throw new Error(
        'loadNpmEntryWasm: factoidal-npm-entry.wasm.js loaded but did not ' +
        'register a usable factoidalNpmEntry on globalThis'
      );
    }
    return abi;
  })();
  return _npmEntryWasmAbiPromise;
}

/**
 * Open a COTTAS/Parquet artifact's raw bytes as a queryable, read-only
 * store, on the wasm engine (bin/npm-entry/entry_jsoo.ml's openCottas
 * export, compiled through wasm_of_ocaml). Wasm sibling of browser.js's
 * openCottas() -- see that function's doc comment for the full design
 * rationale (lazy row decode, no heap Dataset materialization).
 *
 * @param {string|Uint8Array|ArrayBuffer} bytes whole `.cottas` file contents
 * @returns {Promise<string>} opaque handle for queryCottas()/closeCottas()
 */
export async function openCottas(bytes) {
  let hex;
  if (typeof bytes === 'string') {
    if (!/^[0-9a-fA-F]*$/.test(bytes) || bytes.length % 2 !== 0) {
      throw new TypeError('openCottas: string input must be an even-length hex string');
    }
    hex = bytes.toLowerCase();
  } else {
    const u8 = bytes instanceof Uint8Array ? bytes
      : bytes instanceof ArrayBuffer ? new Uint8Array(bytes) : null;
    if (!u8) {
      throw new TypeError('openCottas: expected a hex string, Uint8Array, or ArrayBuffer');
    }
    const HEX = '0123456789abcdef';
    const parts = new Array(u8.length);
    for (let i = 0; i < u8.length; i++) {
      parts[i] = HEX[u8[i] >> 4] + HEX[u8[i] & 15];
    }
    hex = parts.join('');
  }
  const abi = await loadNpmEntryWasm();
  if (typeof abi.openCottas !== 'function') {
    throw new Error('openCottas: the loaded factoidal-npm-entry.wasm.js bundle predates the openCottas export');
  }
  const parsed = JSON.parse(abi.openCottas(hex));
  if (!parsed.ok) throw new Error(parsed.error || 'openCottas failed');
  return parsed.handle;
}

/**
 * Run a SPARQL 1.1 query against a store opened by openCottas(), on
 * the wasm engine (bin/npm-entry/entry_jsoo.ml's queryCottas export).
 * No `entail` option and no write overlay (read-only) -- see
 * browser.js's queryCottas() doc comment for the full divergence list
 * from query().
 *
 * @param {string} handle from openCottas()
 * @param {string} sparql
 * @returns {Promise<{ok:true,kind:'select',srj:object}|{ok:true,kind:'ask',boolean:boolean}|{ok:true,kind:'construct',nquads:string}>}
 */
export async function queryCottas(handle, sparql) {
  if (typeof handle !== 'string') {
    throw new TypeError('queryCottas: handle must be the string openCottas() returned');
  }
  if (typeof sparql !== 'string') {
    throw new TypeError('queryCottas: sparql must be a string');
  }
  const abi = await loadNpmEntryWasm();
  if (typeof abi.queryCottas !== 'function') {
    throw new Error('queryCottas: the loaded factoidal-npm-entry.wasm.js bundle predates the queryCottas export');
  }
  const parsed = JSON.parse(abi.queryCottas(handle, sparql));
  if (!parsed.ok) throw new Error(parsed.error || 'queryCottas failed');
  return parsed;
}

/**
 * Release a store opened by openCottas(), on the wasm engine
 * (bin/npm-entry/entry_jsoo.ml's closeCottas export). Drops the
 * handle from the entry bundle's own registry only -- does not evict
 * the underlying byte cache.
 * @param {string} handle
 * @returns {Promise<void>}
 */
export async function closeCottas(handle) {
  const abi = await loadNpmEntryWasm();
  if (typeof abi.closeCottas !== 'function') {
    throw new Error('closeCottas: the loaded factoidal-npm-entry.wasm.js bundle predates the closeCottas export');
  }
  const parsed = JSON.parse(abi.closeCottas(handle));
  if (!parsed.ok) throw new Error(parsed.error || 'closeCottas failed');
}

/**
 * Serialize a dataset-handle N-Quads string to COTTAS/Parquet bytes,
 * on the wasm engine (bin/npm-entry/entry_jsoo.ml's toCottas export;
 * RDF.CottasStore.BaseWriter.serialize_cottas_v2, the same pure `Tot`
 * function `factoidal compact --native-writer` uses). Round-trips
 * into openCottas() byte-for-byte, on either engine (see
 * cottas-bytes-store-wasm.test.js's js/wasm parity test).
 *
 * @param {string} nQuads dataset-handle N-Quads text
 * @returns {Promise<Uint8Array>}
 */
export async function toCottas(nQuads) {
  if (typeof nQuads !== 'string') {
    throw new TypeError('toCottas: nQuads must be a string');
  }
  const abi = await loadNpmEntryWasm();
  if (typeof abi.toCottas !== 'function') {
    throw new Error('toCottas: the loaded factoidal-npm-entry.wasm.js bundle predates the toCottas export');
  }
  const parsed = JSON.parse(abi.toCottas(nQuads));
  if (!parsed.ok) throw new Error(parsed.error || 'toCottas failed');
  const hex = parsed.cottasHex;
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.substr(i * 2, 2), 16);
  return out;
}

export const version = '0.1.0-alpha.0';

export default {
  query, version, setFactoidalWasmUrl, getFactoidalWasmUrl,
  loadNpmEntryWasm, setFactoidalNpmEntryWasmUrl, getFactoidalNpmEntryWasmUrl,
  openCottas, queryCottas, closeCottas, toCottas,
};
