// factoidal — browser ESM entry.
//
// Ship this to the browser as an ES module:
//
//   <script type="module">
//     import { query } from 'https://unpkg.com/factoidal/browser.js';
//     const r = await query(dataTtl, 'SELECT * WHERE { ?s ?p ?o }');
//     console.log(r.results.bindings);
//   </script>
//
// Exposes the same async API as the Node entry point (index.mjs) so a
// single codebase works on either side.
//
// ASSUMPTION: `factoidal.js` is fetched from a URL relative to this
// module — i.e. it sits next to `browser.js` on the same server. That
// is how npm packages are typically shipped by unpkg / jsDelivr, and
// it matches our own GitHub Pages layout under
// `docs/fstar-extracted/`. If you need to load `factoidal.js` from a
// different URL, call `setFactoidalUrl(url)` before `query()`.
//
// The F*-extracted evaluator itself doesn't use fetch, localStorage,
// DOM APIs, or anything else browser-specific — it's pure JavaScript
// that happens to have been authored by a compiler. The only piece of
// browser plumbing is the fake filesystem we prime via
// `globalThis.jsoo_fs_tmp`; see README.md for more on that.

const DEFAULT_URL = new URL('./factoidal.js', import.meta.url).href;

let _factoidalUrl = DEFAULT_URL;
let _factoidalSrc = null;
let _fetchPromise = null;

/**
 * Override where `factoidal.js` is loaded from. Useful for bundlers
 * that can't sit the artifact next to this module.
 */
export function setFactoidalUrl(url) {
  _factoidalUrl = url;
  _factoidalSrc = null;
  _fetchPromise = null;
}

/**
 * Current `factoidal.js` source URL. Lets a caller that wants a
 * non-default bundle (e.g. a per-page `js-url` override, or the
 * source-mapped debug bundle from the `jsoo-debug-bundle` skill)
 * check before calling `setFactoidalUrl()`, so it only pays the
 * cache-reset cost when the URL actually changes.
 */
export function getFactoidalUrl() {
  return _factoidalUrl;
}

function loadFactoidalSource() {
  if (_factoidalSrc) return Promise.resolve(_factoidalSrc);
  if (_fetchPromise) return _fetchPromise;
  _fetchPromise = fetch(_factoidalUrl)
    .then((r) => {
      if (!r.ok) {
        throw new Error(`factoidal.js fetch failed: ${r.status} ${r.statusText}`);
      }
      return r.text();
    })
    .then((text) => { _factoidalSrc = text; return text; });
  return _fetchPromise;
}

const DATA_FORMAT_EXT = {
  turtle:   'ttl',
  ttl:      'ttl',
  ntriples: 'nt',
  nt:       'nt',
  nquads:   'nq',
  nq:       'nq',
  trig:     'trig',
  rdfxml:   'rdf',
  'rdf-xml': 'rdf',
  rdf:      'rdf',
  jsonld:   'jsonld',
  'json-ld': 'jsonld',
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

// ---------------------------------------------------------------------
// #240 byte-encoding convention: under js_of_ocaml use-js-string=true
// (jsoo 6.x default) OCaml strings ARE the host JS strings, using a
// "bytes-as-JS-chars" convention — each JS string char's low byte is
// one OCaml byte, built via String.fromCharCode per UTF-8 byte. Any
// *textual* content handed to the `factoidal.js` bundle (RDF data,
// SPARQL query text) must be UTF-8-encoded and byte-packed into that
// convention, or non-ASCII input desyncs BatUTF8 and throws
// BatUChar.Out_of_range (see #240, and the `jsoo-debug-bundle` skill).
//
// This was previously duplicated in
// docs/fstar-extracted/factoidal-sparql-client.js as an inline
// `jsToBytesAsChars` helper; it now lives here as the one true
// implementation, applied automatically by `query()` / `toRdf()` /
// `canonicalize()` / `queryDataset()` below. It is deliberately NOT
// applied inside `runFactoidalCli()` itself: that primitive's `files`
// contents are sometimes genuinely opaque bytes already packed
// one-char-per-byte by the caller (e.g. the COTTAS/Parquet demo, which
// reads a binary `.parquet` file and packs it itself) — re-encoding
// those through TextEncoder would corrupt them. Callers driving
// `runFactoidalCli()` directly with *text* content should call this
// first, same as the higher-level helpers do internally.
// ---------------------------------------------------------------------
const _textEncoder = (typeof TextEncoder !== 'undefined') ? new TextEncoder() : null;

/**
 * UTF-8-encode a JS string and repack it into the "bytes-as-JS-chars"
 * convention the js_of_ocaml bundle expects for text content (RDF
 * data, SPARQL query text) passed via `jsoo_fs_tmp` or CLI argv. A
 * no-op for pure-ASCII input.
 *
 * @param {string} s
 * @returns {string}
 */
export function encodeTextAsBundleBytes(s) {
  if (typeof s !== 'string') return s;
  let bytes;
  if (_textEncoder) {
    bytes = _textEncoder.encode(s);
  } else {
    // Manual UTF-8 encode for runtimes without TextEncoder.
    const out = [];
    for (let i = 0; i < s.length; i++) {
      const c = s.charCodeAt(i);
      if (c < 0x80) out.push(c);
      else if (c < 0x800) out.push(0xc0 | (c >> 6), 0x80 | (c & 0x3f));
      else if (c < 0xd800 || c >= 0xe000) {
        out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
      } else {
        const hi = c, lo = s.charCodeAt(++i);
        const cp = 0x10000 + (((hi & 0x3ff) << 10) | (lo & 0x3ff));
        out.push(0xf0 | (cp >> 18), 0x80 | ((cp >> 12) & 0x3f),
                 0x80 | ((cp >> 6) & 0x3f), 0x80 | (cp & 0x3f));
      }
    }
    bytes = new Uint8Array(out);
  }
  // Pack bytes into a JS string. fromCharCode.apply blows the arg-list
  // limit on long inputs (~64K), so chunk.
  let r = '';
  for (let i = 0; i < bytes.length; i += 0x4000) {
    r += String.fromCharCode.apply(null, bytes.subarray(i, Math.min(bytes.length, i + 0x4000)));
  }
  return r;
}

/**
 * Run one CLI invocation of the js_of_ocaml `factoidal.js` bundle
 * in-browser: argv + a fake filesystem in, {stdout, stderr, exitCode}
 * out. This is the shared primitive `query()` (and `toRdf()` /
 * `canonicalize()` below) are built on — factored out so callers that
 * need a CLI flag combination this module doesn't wrap yet (or a
 * Node-side driver, e.g. lib/engine-js.js's fs-based equivalent) can
 * still drive the same bundle. See jsonld-playground-client.js for an
 * example of code written against this shape so it runs identically
 * under this browser driver and under Node's fs-based driver.
 *
 * `files` contents are passed through byte-for-byte — no automatic
 * UTF-8/#240 encoding here (see `encodeTextAsBundleBytes()` above);
 * callers driving text content directly through this primitive should
 * apply it themselves first.
 *
 * @param {string[]} args   CLI arguments (after argv[0]/argv[1]).
 * @param {Array<{name: string, content: string}>} files
 *        Documents for the fake filesystem. Names must start with
 *        '/static/'.
 * @param {object} [options]
 * @param {(src: string) => string} [options.transformSource]
 *        Optional hook applied to the fetched bundle source before
 *        each eval, e.g. to splice in the `?jsoo-debug=1` BatUChar
 *        instrumentation the sparql-client web component uses for
 *        #240 diagnostics. Not cached — safe to vary per call.
 * @returns {Promise<{stdout: string, stderr: string, exitCode: number, engineMs: number}>}
 */
export async function runFactoidalCli(args, files, options) {
  const opts = options || {};
  let src = await loadFactoidalSource();
  if (typeof opts.transformSource === 'function') {
    src = opts.transformSource(src);
  }

  // Preserve anything we're about to overwrite.
  const orig = {
    log:    console.log,
    error:  console.error,
    argv:   globalThis.process && globalThis.process.argv,
    exit:   globalThis.process && globalThis.process.exit,
    jsooFs: globalThis.jsoo_fs_tmp,
  };

  const stdoutBuf = [];
  const stderrBuf = [];
  console.log   = (...a) => stdoutBuf.push(a.join(' '));
  console.error = (...a) => stderrBuf.push(a.join(' '));

  globalThis.process      = globalThis.process || {};
  globalThis.process.argv = ['node', 'factoidal', ...args];
  // Mount under `/static/`: that path is an MlFakeDevice in js_of_ocaml
  // both in the browser and under Node. `/tmp/` is only fake in the
  // browser; keeping one path keeps the Node and browser drivers in
  // lockstep.
  globalThis.jsoo_fs_tmp  = (files || []).map((f) => ({
    name: f.name, content: f.content,
  }));

  let exitCode = 0;
  const EXIT_SENTINEL = new Error('__factoidal_exit__');
  globalThis.process.exit = (n) => { exitCode = n | 0; throw EXIT_SENTINEL; };

  function restore() {
    console.log   = orig.log;
    console.error = orig.error;
    if (globalThis.process) {
      globalThis.process.argv = orig.argv;
      globalThis.process.exit = orig.exit;
    }
    globalThis.jsoo_fs_tmp = orig.jsooFs;
  }

  const t0 = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
  try {
    (new Function(src))();
  } catch (e) {
    if (e !== EXIT_SENTINEL) { restore(); throw e; }
  } finally {
    restore();
  }
  const t1 = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();

  return {
    stdout: stdoutBuf.join('\n'),
    stderr: stderrBuf.join('\n'),
    exitCode,
    engineMs: t1 - t0,
  };
}

/**
 * Run a SPARQL query against an RDF dataset in memory. Same shape as
 * the Node entry point. See index.d.ts for the full type.
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

  const ext      = extForFormat(dataFormat);
  const dataPath = '/static/data.' + ext;

  const argv = [
    '-d', dataPath,
    '-e', encodeTextAsBundleBytes(queryString),
    '-o', output === 'json' ? 'json' : output,
  ];
  if (entail !== 'none') argv.push('--entail', entail);

  const { stdout, stderr, exitCode, engineMs } = await runFactoidalCli(
    argv, [{ name: dataPath, content: encodeTextAsBundleBytes(dataString) }]);

  if (exitCode !== 0) {
    const msg =
      (stderr || stdout || `factoidal exited with code ${exitCode}`).trim();
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
      'factoidal did not produce JSON on stdout. Raw output: ' + stdout
    );
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
  const jsonText = stdout.slice(firstBrace, lastBrace + 1);
  try {
    const parsed = JSON.parse(jsonText);
    // Non-enumerable: doesn't perturb JSON.stringify()/Object.keys()
    // for callers that diff this against W3C .srx-derived fixtures,
    // but is readable by callers that want engine-timing observability
    // (e.g. the sparql-client web component's Details/timing panel).
    Object.defineProperty(parsed, 'engineMs', { value: engineMs, enumerable: false });
    return parsed;
  } catch (e) {
    const err = new Error(
      'factoidal JSON parse failed: ' + e.message +
      '. Raw output: ' + stdout
    );
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
}

// Shared plumbing for toRdf() / canonicalize(): both are "parse this
// document, dump N-Quads" CLI invocations differing only in the mode
// flag (--dump-nq vs --canonicalize). Errors (bad syntax, or JSON-LD
// features Parser.JSONLD.fst doesn't yet cover -- e.g. a remote
// @context URL string, since there is no JSONLD.Loader/fetch step)
// surface as a rejected promise carrying the engine's own stderr, so
// callers can render the honest failure instead of inventing one.
async function dumpNQuads(mode, text, options) {
  const opts     = options || {};
  const format   = opts.format || 'jsonld';
  const ext      = extForFormat(format);
  const baseIRI  = opts.baseIRI || '';
  const dataPath = '/static/data.' + ext;

  const argv = [mode, '-d', dataPath];
  if (baseIRI) argv.push('-b', encodeTextAsBundleBytes(baseIRI));

  const { stdout, stderr, exitCode } = await runFactoidalCli(
    argv, [{ name: dataPath, content: encodeTextAsBundleBytes(text) }]);

  if (exitCode !== 0) {
    const msg = (stderr || stdout || `factoidal exited with code ${exitCode}`).trim();
    const err = new Error(`${mode === '--canonicalize' ? 'canonicalize' : 'toRdf'} failed: ${msg}`);
    err.exitCode = exitCode;
    err.stderr   = stderr;
    err.stdout   = stdout;
    throw err;
  }
  return stdout;
}

/**
 * Parse a document to RDF and dump sorted N-Quads (RDF.Canonical's
 * `canonical_nquads` -- sorted, not RDFC-1.0 canonical bnode labels;
 * see canonicalize() for that). Default format is 'jsonld' since this
 * export exists mainly for the JSON-LD playground's "toRdf" step, but
 * any DATA_FORMAT_EXT format works.
 *
 * @param {string} text
 * @param {{format?: string, baseIRI?: string}} [options]
 * @returns {Promise<string>} N-Quads text.
 */
export async function toRdf(text, options) {
  if (typeof text !== 'string') {
    throw new TypeError('toRdf: text must be a string');
  }
  return dumpNQuads('--dump-nq', text, options);
}

/**
 * RDFC-1.0 canonicalization: canonical blank-node labels + sorted
 * canonical N-Quads (RDF.Canonical.fst's canonicalize_to_nquads).
 *
 * @param {string} text
 * @param {{format?: string, baseIRI?: string}} [options]
 * @returns {Promise<string>} canonical N-Quads text.
 */
export async function canonicalize(text, options) {
  if (typeof text !== 'string') {
    throw new TypeError('canonicalize: text must be a string');
  }
  return dumpNQuads('--canonicalize', text, options);
}

// ---------------------------------------------------------------------
// Multi-file / multi-engine dataset queries. `query()` above only
// takes one data string into the default graph. Multi-named-graph
// pages (e.g. the life-sci demos, which load several Wikidata TTL
// files each into their own named graph) need more than that; this
// was previously duplicated per-page in
// docs/fstar-extracted/factoidal-sparql-client.js (`_getFilePayloads` /
// the JS-engine argv-building loop / `payloadsToTriG` for the wasm
// path). It now lives here as the one true implementation.
// ---------------------------------------------------------------------

/**
 * @typedef {object} DatasetFile
 * @property {string} content    Document text.
 * @property {string} [dataFormat='turtle']  One of DATA_FORMAT_EXT's keys.
 * @property {string} [graph]    Named-graph IRI. Omitted/falsy loads
 *   into the default graph (CLI `-d`); otherwise `--named IRI=path`.
 */

// Merge N (graph, content) pairs into one TriG document: directives
// (@prefix/@base/PREFIX/BASE) are hoisted to the top and deduplicated;
// remaining triples are wrapped in `GRAPH <iri> { ... }` for files with
// a graph IRI, or left bare (default-graph triples section) otherwise.
// Used for the wasm engine path, whose query() API takes a single data
// string. Ported verbatim from factoidal-sparql-client.js's
// payloadsToTriG. Assumes Turtle-family (`dataFormat: 'turtle'`) input
// per file — the same assumption the original shim made.
function mergeFilesToTrig(files) {
  const directives = new Set();
  const blocks = [];
  const dirRE = /^\s*(?:@prefix|@base|PREFIX|BASE)\b[^\n]*\.\s*$/i;
  files.forEach((f) => {
    const bodyLines = [];
    (f.content || '').split(/\r?\n/).forEach((line) => {
      if (dirRE.test(line)) directives.add(line.trim());
      else bodyLines.push(line);
    });
    if (f.graph) {
      blocks.push('GRAPH <' + f.graph + '> {\n' + bodyLines.join('\n') + '\n}\n');
    } else {
      blocks.push(bodyLines.join('\n') + '\n');
    }
  });
  return [...directives].join('\n') + '\n\n' + blocks.join('\n');
}

/**
 * Run a SPARQL query against a multi-file, multi-named-graph dataset,
 * on either the js_of_ocaml (`js`, default) or wasm_of_ocaml (`wasm`)
 * extraction target.
 *
 * @param {DatasetFile[]} files
 * @param {string} queryString
 * @param {object} [options]
 * @param {string} [options.entail='none']
 * @param {string} [options.output='json']
 * @param {'js'|'wasm'} [options.engine='js']
 * @param {string} [options.wasmUrl]  Override for browser-wasm.js's
 *   `factoidal.wasm.js` URL (see `setFactoidalWasmUrl`). Only consulted
 *   when `options.engine === 'wasm'`.
 * @param {(src: string) => string} [options.transformSource]  Forwarded
 *   to `runFactoidalCli()` on the js engine path only.
 * @returns {Promise<object|string>}
 */
export async function queryDataset(files, queryString, options) {
  if (!Array.isArray(files) || files.length === 0) {
    throw new TypeError('queryDataset: files must be a non-empty array');
  }
  if (typeof queryString !== 'string') {
    throw new TypeError('queryDataset: queryString must be a string');
  }

  const opts   = options || {};
  const entail = opts.entail || 'none';
  const output = opts.output || 'json';
  const engine = opts.engine || 'js';

  if (!ENTAIL_VALUES.has(entail)) {
    throw new TypeError(`queryDataset: entail must be one of ${[...ENTAIL_VALUES].join(', ')}`);
  }
  if (!OUTPUT_FORMATS.has(output)) {
    throw new TypeError(`queryDataset: output must be one of ${[...OUTPUT_FORMATS].join(', ')}`);
  }

  if (engine === 'wasm') {
    // wasm_of_ocaml's query() only accepts one data string — merge
    // named graphs into TriG first. Dynamically imported so pages that
    // never touch the wasm engine don't pay for loading this module.
    const wasmMod = await import(new URL('./browser-wasm.js', import.meta.url).href);
    // Only reset the module's cached bundle source when the URL
    // actually changes — setFactoidalWasmUrl() unconditionally clears
    // the cache, and this can run once per query.
    if (opts.wasmUrl && typeof wasmMod.setFactoidalWasmUrl === 'function'
        && (typeof wasmMod.getFactoidalWasmUrl !== 'function'
            || wasmMod.getFactoidalWasmUrl() !== opts.wasmUrl)) {
      wasmMod.setFactoidalWasmUrl(opts.wasmUrl);
    }
    const trigText = mergeFilesToTrig(files);
    const t0 = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
    const parsed = await wasmMod.query(trigText, queryString, { dataFormat: 'trig', entail, output });
    const t1 = (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now();
    if (output === 'json' && parsed && typeof parsed === 'object') {
      Object.defineProperty(parsed, 'engineMs', { value: t1 - t0, enumerable: false });
    }
    return parsed;
  }
  if (engine !== 'js') {
    throw new TypeError(`queryDataset: engine must be 'js' or 'wasm', got '${engine}'`);
  }

  // js_of_ocaml path — multi-file via jsoo_fs_tmp, one -d/--named per
  // file, same as the JS-engine branch of the old sparql-client shim.
  const cliFiles = [];
  const argv = [];
  files.forEach((f, i) => {
    const ext  = extForFormat(f.dataFormat || 'turtle');
    const path = '/static/data-' + i + '.' + ext;
    cliFiles.push({ name: path, content: encodeTextAsBundleBytes(f.content || '') });
    if (f.graph) argv.push('--named', f.graph + '=' + path);
    else         argv.push('-d', path);
  });
  argv.push('-e', encodeTextAsBundleBytes(queryString), '-o', output === 'json' ? 'json' : output);
  if (entail !== 'none') argv.push('--entail', entail);

  const { stdout, stderr, exitCode, engineMs } =
    await runFactoidalCli(argv, cliFiles, { transformSource: opts.transformSource });

  if (exitCode !== 0) {
    const msg = (stderr || stdout || `factoidal exited with code ${exitCode}`).trim();
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
    const err = new Error('factoidal did not produce JSON on stdout. Raw output: ' + stdout);
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
  try {
    const parsed = JSON.parse(stdout.slice(firstBrace, lastBrace + 1));
    Object.defineProperty(parsed, 'engineMs', { value: engineMs, enumerable: false });
    return parsed;
  } catch (e) {
    const err = new Error('factoidal JSON parse failed: ' + e.message + '. Raw output: ' + stdout);
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
}

// ---------------------------------------------------------------------
// npm-entry ABI loader (persistent factoidalNpmEntry object, built from
// bin/npm-entry/entry_jsoo.ml -- see that file's header comment for the
// full ABI contract). The CLI bundle above (runFactoidalCli / query /
// toRdf / canonicalize) covers most of the surface with a fresh bundle
// eval per call; a few operations (RIF Core saturation today) are only
// exposed through this persistent ABI, so this loader fetches + evals
// factoidal-npm-entry.js once and reads the `factoidalNpmEntry` object
// it registers on globalThis -- same registration Node's index.js reads
// off `module.exports.factoidalNpmEntry` / `globalThis.factoidalNpmEntry`
// (see npm/factoidal/index.js's loadEntry()).
// ---------------------------------------------------------------------

let _npmEntryUrl = new URL('./factoidal-npm-entry.js', import.meta.url).href;
let _npmEntryPromise = null;

/**
 * Override where `factoidal-npm-entry.js` is loaded from. Same idea as
 * setFactoidalUrl() for the CLI bundle.
 */
export function setFactoidalNpmEntryUrl(url) {
  _npmEntryUrl = url;
  _npmEntryPromise = null;
}

/**
 * Fetch + evaluate factoidal-npm-entry.js exactly once, returning the
 * `factoidalNpmEntry` ABI object it registers on globalThis. Optional:
 * everything the CLI bundle can do works without it.
 *
 * @returns {Promise<object>} the factoidalNpmEntry ABI object.
 */
export async function loadNpmEntry() {
  if (_npmEntryPromise) return _npmEntryPromise;
  _npmEntryPromise = fetch(_npmEntryUrl)
    .then((r) => {
      if (!r.ok) {
        throw new Error(
          `factoidal-npm-entry.js fetch failed: ${r.status} ${r.statusText}`);
      }
      return r.text();
    })
    .then((src) => {
      (new Function(src))();
      const abi = globalThis.factoidalNpmEntry;
      if (!abi) {
        throw new Error(
          'factoidal-npm-entry.js loaded but did not register ' +
          'factoidalNpmEntry on globalThis');
      }
      return abi;
    });
  return _npmEntryPromise;
}

/**
 * RIF Core smoke saturation, run live: the exact premise graph and
 * two-rule program baked into RIF.Core.Eval.fst as smoke_input_graph /
 * smoke_program, saturated via RIF_Core_Eval.fixpoint in the loaded
 * bundle (bin/npm-entry/entry_jsoo.ml's rifSmoke export). No user
 * input -- a fixed capability probe (issue #274).
 *
 * @returns {Promise<{inputNquads:string, saturatedNquads:string,
 *   inputCount:number, derivedCount:number, rounds:number, fuel:number,
 *   engineMs:number}>}
 */
export async function rifSmoke() {
  const abi = await loadNpmEntry();
  if (typeof abi.rifSmoke !== 'function') {
    throw new Error(
      'rifSmoke: the loaded factoidal-npm-entry bundle predates the RIF exports');
  }
  const parsed = JSON.parse(abi.rifSmoke());
  if (!parsed.ok) throw new Error(parsed.error || 'rifSmoke failed');
  return parsed;
}

/**
 * RIF Core forward-chaining saturation over caller-supplied RIF-XML
 * rules and N-Quads premise data (default graph only -- RIF Core has
 * no named-graph notion). Parsed via Parser_RIFXML.parse_rif_program,
 * saturated via RIF_Core_Eval.fixpoint (bin/npm-entry/entry_jsoo.ml's
 * rifEval export). Import directives in the RIF-XML are not resolved;
 * merge any imported data into dataNQuads yourself first.
 *
 * @param {string} rifXml
 * @param {string} dataNQuads
 * @returns {Promise<{inputNquads:string, saturatedNquads:string,
 *   inputCount:number, derivedCount:number, rounds:number, fuel:number,
 *   engineMs:number}>}
 */
export async function rifEval(rifXml, dataNQuads) {
  if (typeof rifXml !== 'string') {
    throw new TypeError('rifEval: rifXml must be a string');
  }
  if (typeof dataNQuads !== 'string') {
    throw new TypeError('rifEval: dataNQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.rifEval !== 'function') {
    throw new Error(
      'rifEval: the loaded factoidal-npm-entry bundle predates the RIF exports');
  }
  const parsed = JSON.parse(abi.rifEval(rifXml, dataNQuads));
  if (!parsed.ok) throw new Error(parsed.error || 'rifEval failed');
  return parsed;
}

/**
 * SHACL Core validation (bin/npm-entry/entry_jsoo.ml's shaclValidate
 * export). dataNQuads/shapesNQuads are dataset-handle N-Quads text
 * (default graph only) -- use toRdf()/canonicalize() above to get
 * there from Turtle or another format.
 *
 * @param {string} dataNQuads
 * @param {string} shapesNQuads
 * @returns {Promise<{ok:true,conforms:boolean,reportNquads:string}>}
 */
export async function shaclValidate(dataNQuads, shapesNQuads) {
  if (typeof dataNQuads !== 'string') {
    throw new TypeError('shaclValidate: dataNQuads must be a string');
  }
  if (typeof shapesNQuads !== 'string') {
    throw new TypeError('shaclValidate: shapesNQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.shaclValidate !== 'function') {
    throw new Error(
      'shaclValidate: the loaded factoidal-npm-entry bundle predates the SHACL export');
  }
  const parsed = JSON.parse(abi.shaclValidate(dataNQuads, shapesNQuads));
  if (!parsed.ok) throw new Error(parsed.error || 'shaclValidate failed');
  return parsed;
}

/**
 * ShEx (Shape Expressions) validation of one focus node against one
 * shape (bin/npm-entry/entry_jsoo.ml's shexValidate export).
 * `focus`/`shapeLabel` are an IRI, or "_:label" for a blank node;
 * `shapeLabel` "" validates against the schema's own `start`.
 *
 * @param {string} dataNQuads
 * @param {string} schemaJson ShExJ (JSON Schema form), as text
 * @param {string} focus
 * @param {string} shapeLabel
 * @returns {Promise<{ok:true,verdict:boolean|null,deferred:boolean}>}
 *   verdict null (deferred:true) means outside this engine's decidable
 *   ShEx fragment -- never a guessed answer.
 */
export async function shexValidate(dataNQuads, schemaJson, focus, shapeLabel) {
  if (typeof dataNQuads !== 'string') {
    throw new TypeError('shexValidate: dataNQuads must be a string');
  }
  if (typeof schemaJson !== 'string') {
    throw new TypeError('shexValidate: schemaJson must be a string');
  }
  if (typeof focus !== 'string') {
    throw new TypeError('shexValidate: focus must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.shexValidate !== 'function') {
    throw new Error(
      'shexValidate: the loaded factoidal-npm-entry bundle predates the ShEx export');
  }
  const parsed = JSON.parse(abi.shexValidate(dataNQuads, schemaJson, focus, shapeLabel || ''));
  if (!parsed.ok) throw new Error(parsed.error || 'shexValidate failed');
  return parsed;
}

/**
 * RDFS or OWL-RL entailment closure (bin/npm-entry/entry_jsoo.ml's
 * owlClosure export). Default graph only.
 *
 * @param {string} dataNQuads
 * @param {'RDFS'|'OWL-RL'} mode
 * @returns {Promise<{ok:true,nquads:string}>}
 */
export async function owlClosure(dataNQuads, mode) {
  if (typeof dataNQuads !== 'string') {
    throw new TypeError('owlClosure: dataNQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.owlClosure !== 'function') {
    throw new Error(
      'owlClosure: the loaded factoidal-npm-entry bundle predates the owlClosure export');
  }
  const parsed = JSON.parse(abi.owlClosure(dataNQuads, mode));
  if (!parsed.ok) throw new Error(parsed.error || 'owlClosure failed');
  return parsed;
}

/**
 * Evaluate an RML mapping graph against one logical source's raw data
 * (bin/npm-entry/entry_jsoo.ml's rmlMap export). Every triples map in
 * `mappingNQuads` reads the SAME `sourceData` -- joins across two
 * different logical sources are out of scope for this entry point.
 *
 * @param {string} mappingNQuads dataset-handle N-Quads for the RML mapping graph
 * @param {string} sourceData raw JSON or CSV text (not RDF)
 * @param {'json'|'csv'} sourceKind
 * @returns {Promise<{ok:true,nquads:string}>}
 */
export async function rmlMap(mappingNQuads, sourceData, sourceKind) {
  if (typeof mappingNQuads !== 'string') {
    throw new TypeError('rmlMap: mappingNQuads must be a string');
  }
  if (typeof sourceData !== 'string') {
    throw new TypeError('rmlMap: sourceData must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.rmlMap !== 'function') {
    throw new Error(
      'rmlMap: the loaded factoidal-npm-entry bundle predates the RML export');
  }
  const parsed = JSON.parse(abi.rmlMap(mappingNQuads, sourceData, sourceKind));
  if (!parsed.ok) throw new Error(parsed.error || 'rmlMap failed');
  return parsed;
}

/**
 * CSVW csv2rdf conversion (bin/npm-entry/entry_jsoo.ml's csvwToRdf
 * export): raw tabular data + an optional CSVW metadata document to
 * N-Quads. Every table in a multi-table `tables` group reads the SAME
 * `csvText`.
 *
 * @param {string} csvText raw RFC 4180 tabular data (not RDF)
 * @param {string} [metadataJson] CSVW metadata document (JSON text);
 *   '' / omitted infers the schema from the CSV's own header row
 * @param {{mode?:'standard'|'minimal',base?:string,url?:string}} [options]
 * @returns {Promise<{ok:true,nquads:string}>}
 */
export async function csvwToRdf(csvText, metadataJson, options) {
  if (typeof csvText !== 'string') {
    throw new TypeError('csvwToRdf: csvText must be a string');
  }
  const meta = metadataJson == null ? '' : metadataJson;
  if (typeof meta !== 'string') {
    throw new TypeError('csvwToRdf: metadataJson must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.csvwToRdf !== 'function') {
    throw new Error(
      'csvwToRdf: the loaded factoidal-npm-entry bundle predates the CSVW export');
  }
  const opts = options || {};
  const optionsJson = JSON.stringify({
    ...(opts.mode ? { mode: String(opts.mode).toLowerCase() } : {}),
    ...(opts.base ? { base: opts.base } : {}),
    ...(opts.url ? { url: opts.url } : {}),
  });
  const parsed = JSON.parse(abi.csvwToRdf(csvText, meta, optionsJson));
  if (!parsed.ok) throw new Error(parsed.error || 'csvwToRdf failed');
  return parsed;
}

/**
 * Parse a JSON-LD document with JSON-LD-specific options
 * (bin/npm-entry/entry_jsoo.ml's jsonldToRdf export) -- plain
 * `toRdf(text, {format:'jsonld'})` above also works now for the
 * common case; this exists for rdfDirection/expandContext/
 * processingMode, which toRdf()'s options have no room for.
 *
 * @param {string} jsonldText
 * @param {{base?:string,rdfDirection?:string,expandContext?:string,
 *   processingMode?:string}} [options]
 * @returns {Promise<{ok:true,nquads:string}>}
 */
export async function jsonldToRdf(jsonldText, options) {
  if (typeof jsonldText !== 'string') {
    throw new TypeError('jsonldToRdf: jsonldText must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.jsonldToRdf !== 'function') {
    throw new Error(
      'jsonldToRdf: the loaded factoidal-npm-entry bundle predates the jsonldToRdf export');
  }
  const opts = options || {};
  const optionsJson = JSON.stringify({
    ...(opts.base ? { base: opts.base } : {}),
    ...(opts.rdfDirection ? { rdfDirection: opts.rdfDirection } : {}),
    ...(opts.expandContext ? { expandContext: opts.expandContext } : {}),
    ...(opts.processingMode ? { processingMode: opts.processingMode } : {}),
  });
  const parsed = JSON.parse(abi.jsonldToRdf(jsonldText, optionsJson));
  if (!parsed.ok) throw new Error(parsed.error || 'jsonldToRdf failed');
  return parsed;
}

// ---------------------------------------------------------------------
// Durable-UPDATE browser persistence (issue #282's browser realisation
// -- see docs/designissues/2026-07-06-browser-persistence.md for the
// full design: v1 architecture decision (IndexedDB, not OPFS -- OPFS
// sync access handles are worker-only and there is no worker-RPC
// layer for the engine yet), the tab-close/crash guarantee mapping,
// and the quota/eviction honesty section).
//
// Every byte written here is exactly what bin/npm-entry/entry_jsoo.ml's
// deltaBatchToHex/deltaMergeApplyBrowser exports produce/consume via
// the F*-extracted, VERIFIED RDF_Store_Columnar_DeltaLog /
// RDF_Store_Columnar_DeltaMerge modules -- this file moves opaque
// hex-encoded bytes into/out of IndexedDB only (rule #11: no RDF/
// SPARQL semantics here). It does NOT call the native delta_log_append/
// _read_all assume-val realisation (that one is wired to Unix syscalls
// which, under js_of_ocaml, hit the in-memory jsoo pseudo-FS -- reset
// on every bundle eval, NOT persistent across a reload); this is a
// wholly separate path.
// ---------------------------------------------------------------------

const DELTA_STORE = 'deltaBatches';
const DEFAULT_DELTA_DB_NAME = 'factoidal-delta-log';

function idbOpen(dbName) {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(dbName, 1);
    req.onupgradeneeded = () => {
      const db = req.result;
      if (!db.objectStoreNames.contains(DELTA_STORE)) {
        db.createObjectStore(DELTA_STORE, { keyPath: 'seq' });
      }
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error || new Error('indexedDB.open failed'));
    req.onblocked = () => reject(new Error('indexedDB.open blocked (another tab holds an open connection at an older version)'));
  });
}

function reqToPromise(req) {
  return new Promise((resolve, reject) => {
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error || new Error('IndexedDB request failed'));
  });
}

/**
 * Open (creating if needed) a browser-persistent delta log backed by
 * IndexedDB. Returns a handle to pass to the other deltaLog* functions
 * below. Data written through this handle survives page reloads and
 * browser restarts -- subject to the browser's own storage-eviction
 * policy under storage pressure (see the design doc's quota/eviction
 * section); this function does not itself call
 * `navigator.storage.persist()` (a named, not-yet-wired gap -- call it
 * yourself first if you need the "exempt from eviction" request made).
 *
 * @param {string} [dbName='factoidal-delta-log']
 * @returns {Promise<{dbName: string}>}
 */
export async function deltaLogOpen(dbName) {
  const name = dbName || DEFAULT_DELTA_DB_NAME;
  const db = await idbOpen(name);
  db.close();
  return { dbName: name };
}

/**
 * Translate one SPARQL Update (INSERT DATA / DELETE DATA / CLEAR /
 * DROP / CREATE -- the same subset the native --rw commit path
 * accepts; anything else rejects rather than silently no-op'ing) into
 * a delta_batch, serialize it (F*-verified,
 * RDF_Store_Columnar_DeltaLog.serialize_delta_batch), and durably
 * append it as one IndexedDB record. The commit point is the
 * transaction's own 'complete' event.
 *
 * @param {{dbName: string}} handle from deltaLogOpen()
 * @param {string} sparqlUpdate
 * @param {{epoch?: number}} [options]
 * @returns {Promise<{seq: number, opCount: number}>}
 */
export async function deltaLogAppend(handle, sparqlUpdate, options) {
  if (!handle || typeof handle.dbName !== 'string') {
    throw new TypeError('deltaLogAppend: handle must be the object deltaLogOpen() returned');
  }
  if (typeof sparqlUpdate !== 'string') {
    throw new TypeError('deltaLogAppend: sparqlUpdate must be a string');
  }
  const opts = options || {};
  const epoch = opts.epoch || 0;
  const abi = await loadNpmEntry();
  if (typeof abi.deltaBatchToHex !== 'function') {
    throw new Error('deltaLogAppend: the loaded factoidal-npm-entry bundle predates the delta-log export');
  }

  const db = await idbOpen(handle.dbName);
  try {
    const seq = await reqToPromise(db.transaction(DELTA_STORE, 'readonly').objectStore(DELTA_STORE).count());

    const parsed = JSON.parse(abi.deltaBatchToHex(sparqlUpdate, String(seq), String(epoch)));
    if (!parsed.ok) throw new Error(parsed.error || 'deltaBatchToHex failed');

    await new Promise((resolve, reject) => {
      // `durability: 'strict'` matters here, not just as a knob: Chrome
      // changed ITS OWN DEFAULT from 'strict' to 'relaxed' from Chrome
      // 121 onward (matching Firefox/Safari's prior behavior) for
      // throughput -- under 'relaxed', `oncomplete` can fire once
      // changes reach the OS write buffer, before an actual disk flush
      // (the buffer is "typically flushed every couple seconds", per
      // Chrome's own devs blog). That is a materially weaker commit
      // point than the native design's `fsync`-gated "committed means
      // durable" promise (durable-update-design.md §3.3 step 3) -- so
      // this call requests 'strict' explicitly rather than silently
      // inheriting a browser's relaxed default, which would make the
      // design doc's own honesty claim (§1.3: "the durability strength
      // is whatever the browser's IndexedDB implementation guarantees")
      // wrong in the weaker direction without anyone choosing that.
      const tx = db.transaction(DELTA_STORE, 'readwrite', { durability: 'strict' });
      tx.objectStore(DELTA_STORE).put({ seq, epoch, hex: parsed.hex });
      tx.oncomplete = () => resolve();
      tx.onerror = () => reject(tx.error || new Error('IndexedDB write failed'));
      tx.onabort = () => reject(tx.error || new Error('IndexedDB write aborted'));
    });

    return { seq, opCount: parsed.opCount };
  } finally {
    db.close();
  }
}

/**
 * Read every committed batch back from IndexedDB, in seq order, as a
 * newline-joined hex-blob string (the wire format deltaLogMerge()
 * consumes). Exposed mainly for debugging and torn-write test setup;
 * deltaLogMerge() below is the normal read path.
 *
 * @param {{dbName: string}} handle
 * @returns {Promise<string>}
 */
export async function deltaLogReadAllHex(handle) {
  const db = await idbOpen(handle.dbName);
  try {
    const all = await reqToPromise(db.transaction(DELTA_STORE, 'readonly').objectStore(DELTA_STORE).getAll());
    all.sort((a, b) => a.seq - b.seq);
    return all.map((r) => r.hex).join('\n');
  } finally {
    db.close();
  }
}

/**
 * Read back the durable log and merge it onto a base dataset (parse +
 * merge-on-read, RDF_Store_Columnar_DeltaMerge.apply_entries_ref via
 * the deltaMergeApplyBrowser ABI export) -- the "reload the page, read
 * the log back, reproduce the updated dataset" proof. A batch record
 * that fails to parse (a torn/corrupt write) is silently skipped,
 * never partially applied -- see the design doc's torn-write section.
 *
 * @param {{dbName: string}} handle
 * @param {string} baseNQuads dataset-handle N-Quads text (the pre-update graph)
 * @returns {Promise<string>} merged N-Quads text
 */
export async function deltaLogMerge(handle, baseNQuads) {
  if (!handle || typeof handle.dbName !== 'string') {
    throw new TypeError('deltaLogMerge: handle must be the object deltaLogOpen() returned');
  }
  if (typeof baseNQuads !== 'string') {
    throw new TypeError('deltaLogMerge: baseNQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.deltaMergeApplyBrowser !== 'function') {
    throw new Error('deltaLogMerge: the loaded factoidal-npm-entry bundle predates the delta-log export');
  }
  const hexBlobs = await deltaLogReadAllHex(handle);
  const parsed = JSON.parse(abi.deltaMergeApplyBrowser(baseNQuads, hexBlobs));
  if (!parsed.ok) throw new Error(parsed.error || 'deltaMergeApplyBrowser failed');
  return parsed.nquads;
}

/**
 * Delete a browser-persistent delta log entirely (test/demo cleanup;
 * not part of the durability story -- this is a deliberate wipe, not
 * an eviction).
 *
 * @param {{dbName: string}} handle
 * @returns {Promise<void>}
 */
export async function deltaLogDestroy(handle) {
  if (!handle || typeof handle.dbName !== 'string') {
    throw new TypeError('deltaLogDestroy: handle must be the object deltaLogOpen() returned');
  }
  await new Promise((resolve, reject) => {
    const req = indexedDB.deleteDatabase(handle.dbName);
    req.onsuccess = () => resolve();
    req.onerror = () => reject(req.error || new Error('indexedDB.deleteDatabase failed'));
    req.onblocked = () => reject(new Error('indexedDB.deleteDatabase blocked (another open connection)'));
  });
}

/**
 * TEST-ONLY: corrupt the most recently written batch record by
 * truncating its hex string, simulating a torn/partial write. Ordinary
 * IndexedDB transactions are atomic (see the design doc's §2 table --
 * this failure mode has no natural browser-native trigger the way a
 * killed `write()` syscall does natively); this pokes the store
 * directly to exercise the delta-log parser's checksum/length framing
 * the same way the native crash-harness pattern does for the on-disk
 * log. Returns false if the store is empty.
 *
 * @param {{dbName: string}} handle
 * @returns {Promise<boolean>}
 */
export async function _deltaLogCorruptLastForTest(handle) {
  const db = await idbOpen(handle.dbName);
  try {
    const all = await reqToPromise(db.transaction(DELTA_STORE, 'readonly').objectStore(DELTA_STORE).getAll());
    if (all.length === 0) return false;
    all.sort((a, b) => a.seq - b.seq);
    const last = all[all.length - 1];
    const truncated = last.hex.slice(0, Math.max(0, last.hex.length - 8));
    await new Promise((resolve, reject) => {
      const tx = db.transaction(DELTA_STORE, 'readwrite');
      tx.objectStore(DELTA_STORE).put({ seq: last.seq, epoch: last.epoch, hex: truncated });
      tx.oncomplete = () => resolve();
      tx.onerror = () => reject(tx.error || new Error('IndexedDB corrupt-for-test write failed'));
    });
    return true;
  } finally {
    db.close();
  }
}

// Best-effort version export for the browser. Consumers that care
// about the exact version should import from the package root (which
// reads package.json).
export const version = '0.1.0-alpha.0';

export default {
  query, toRdf, canonicalize, runFactoidalCli, setFactoidalUrl, getFactoidalUrl,
  encodeTextAsBundleBytes, queryDataset, version,
  loadNpmEntry, setFactoidalNpmEntryUrl, rifSmoke, rifEval,
  shaclValidate, shexValidate, owlClosure, rmlMap, jsonldToRdf,
  deltaLogOpen, deltaLogAppend, deltaLogReadAllHex, deltaLogMerge,
  deltaLogDestroy, _deltaLogCorruptLastForTest,
};
