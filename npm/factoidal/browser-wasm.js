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

const IIFE_MARKER = ';($=>async ';
const IIFE_REWRITE = ';globalThis.__fwPromise=($=>async ';

function rewriteBundle(src) {
  const ix = src.indexOf(IIFE_MARKER);
  if (ix < 0) {
    // Unexpected bundle shape. Bail loudly.
    throw new Error(
      "browser-wasm: could not locate the async IIFE marker in " +
      "factoidal.wasm.js. The bundle shape may have changed."
    );
  }
  return src.slice(0, ix) + IIFE_REWRITE + src.slice(ix + IIFE_MARKER.length);
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

export const version = '0.1.0-alpha.0';

export default { query, version, setFactoidalWasmUrl };
