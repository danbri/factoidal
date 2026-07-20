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

// RDF 1.2 opt-in via a "*12" format name (turtle12/ttl12/nt12/nquads12/
// trig12/...): strip the "12" suffix to the base ext and flag rdf12 so
// the caller adds the CLI's --rdf12 flag (Mode_12 loaders: triple terms
// <<( )>>, ~ reifiers, {| |} annotations, directional literals). A plain
// format name stays RDF 1.1.
function extAnd12(fmt) {
  const key = String(fmt || 'turtle').toLowerCase();
  const m = /^(.+)12$/.exec(key);
  if (m && (m[1] in DATA_FORMAT_EXT)) {
    return { ext: DATA_FORMAT_EXT[m[1]], rdf12: true };
  }
  return { ext: extForFormat(key), rdf12: false };
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
  // SPARQL 1.2 opt-in: {sparql12:true} or {version:'1.2'} parses the
  // query with the tokenize_12 parser (--sparql12) and loads the data in
  // Mode_12 (--rdf12), so triple-term patterns / TRIPLE / isTRIPLE /
  // lang-dir builtins work. Default stays SPARQL 1.1, byte-identical.
  const sparql12   = opts.sparql12 === true || String(opts.version || '') === '1.2';

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

  const { ext, rdf12 } = extAnd12(dataFormat);
  const dataPath = '/static/data.' + ext;

  const argv = [
    '-d', dataPath,
    '-e', encodeTextAsBundleBytes(queryString),
    '-o', output === 'json' ? 'json' : output,
  ];
  // A 1.2 query's data (triple terms) must load in Mode_12; --sparql12
  // switches the query parser. Adding --rdf12 to 1.1 data is harmless
  // (the Mode_12 loader is a superset).
  if (rdf12 || sparql12) argv.push('--rdf12');
  if (sparql12) argv.push('--sparql12');
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
  const { ext, rdf12 } = extAnd12(format);
  const baseIRI  = opts.baseIRI || '';
  const dataPath = '/static/data.' + ext;

  const argv = [mode, '-d', dataPath];
  if (rdf12) argv.push('--rdf12');
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
 * @param {string} schemaJson the schema, as text -- either ShExJ (a JSON
 *   Schema document) or ShExC (the compact human-readable syntax).
 *   Dispatch rule: the first non-whitespace character decides the
 *   format -- '{' means ShExJ, anything else is parsed as ShExC (no
 *   valid ShExC document starts with '{' after whitespace).
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

// ---------------------------------------------------------------------
// VC Data Integrity crypto (eddsa-rdfc-2022) — bin/npm-entry/
// entry_jsoo.ml's vc* exports, realising VC_DataIntegrity's four crypto
// assume vals via HACL*'s OWN official WebAssembly build.
//
// INIT (browser): unlike the Node entry (which auto-awaits initHacl()),
// a browser page MUST initialise the HACL* wasm backend itself before
// the first VC call — the hacl-wasm URL is page-specific. Serve the
// `hacl-wasm/` directory next to your page and, from hacl-init.js,
// `await initHacl({ apiUrl: '/path/to/hacl-wasm/api.js' })` once; that
// stashes the ready backend on globalThis.__factoidalHacl, which the
// bundle's synchronous stubs read. If the backend is NOT initialised,
// the F* assume-val stub throws, `guarded` returns {ok:false}, and
// these wrappers throw — a verify NEVER silently succeeds
// uninitialised (#286, the throw-on-uninit contract). See
// skills/node-crypto-haclstar-vc-wasm-build.
// ---------------------------------------------------------------------

/**
 * SHA-256 of a message string's bytes, as a lowercase hex digest
 * (VC_DataIntegrity.hash_sha256_hex, HACL* SHA-2).
 * @param {string} message
 * @returns {Promise<{ok:true, sha256:string}>}
 */
export async function vcSha256Hex(message) {
  if (typeof message !== 'string') {
    throw new TypeError('vcSha256Hex: message must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.vcSha256Hex !== 'function') {
    throw new Error('vcSha256Hex: the loaded factoidal-npm-entry bundle predates the VC crypto exports');
  }
  const parsed = JSON.parse(abi.vcSha256Hex(message));
  if (!parsed.ok) throw new Error(parsed.error || 'vcSha256Hex failed');
  return parsed;
}

/**
 * Derive the Ed25519 public key from a 32-byte secret key (hex).
 * @param {string} secretKeyHex
 * @returns {Promise<{ok:true, publicKeyHex:string}>}
 */
export async function vcEd25519SecretToPublic(secretKeyHex) {
  if (typeof secretKeyHex !== 'string') {
    throw new TypeError('vcEd25519SecretToPublic: secretKeyHex must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.vcEd25519SecretToPublic !== 'function') {
    throw new Error('vcEd25519SecretToPublic: the loaded factoidal-npm-entry bundle predates the VC crypto exports');
  }
  const parsed = JSON.parse(abi.vcEd25519SecretToPublic(secretKeyHex));
  if (!parsed.ok) throw new Error(parsed.error || 'vcEd25519SecretToPublic failed');
  return parsed;
}

/**
 * Ed25519 signature over a hex-encoded message.
 * @param {string} secretKeyHex 32-byte secret key, hex
 * @param {string} messageHex the message to sign, hex
 * @returns {Promise<{ok:true, signatureHex:string}>}
 */
export async function vcEd25519Sign(secretKeyHex, messageHex) {
  if (typeof secretKeyHex !== 'string' || typeof messageHex !== 'string') {
    throw new TypeError('vcEd25519Sign: secretKeyHex and messageHex must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.vcEd25519Sign !== 'function') {
    throw new Error('vcEd25519Sign: the loaded factoidal-npm-entry bundle predates the VC crypto exports');
  }
  const parsed = JSON.parse(abi.vcEd25519Sign(secretKeyHex, messageHex));
  if (!parsed.ok) throw new Error(parsed.error || 'vcEd25519Sign failed');
  return parsed;
}

/**
 * Ed25519 verification. Wrong key, tampered signature, altered
 * message, or a malformed-length input all report valid:false — never
 * an exception-hidden true.
 * @param {string} publicKeyHex
 * @param {string} messageHex
 * @param {string} signatureHex
 * @returns {Promise<{ok:true, valid:boolean}>}
 */
export async function vcEd25519Verify(publicKeyHex, messageHex, signatureHex) {
  if (typeof publicKeyHex !== 'string' || typeof messageHex !== 'string' ||
      typeof signatureHex !== 'string') {
    throw new TypeError('vcEd25519Verify: publicKeyHex, messageHex and signatureHex must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.vcEd25519Verify !== 'function') {
    throw new Error('vcEd25519Verify: the loaded factoidal-npm-entry bundle predates the VC crypto exports');
  }
  const parsed = JSON.parse(abi.vcEd25519Verify(publicKeyHex, messageHex, signatureHex));
  if (!parsed.ok) throw new Error(parsed.error || 'vcEd25519Verify failed');
  return parsed;
}

/**
 * Create an eddsa-rdfc-2022 Data Integrity proofValue over
 * already-canonicalized inputs (RDFC-1.0 canonical N-Quads).
 * @param {string} secretKeyHex
 * @param {string} canonicalDocument canonical N-Quads of the document
 * @param {string} canonicalConfig canonical N-Quads of the proof config
 * @returns {Promise<{ok:true, proofValue:string}>} multibase-z (base58btc)
 */
export async function vcEddsaCreateFromCanonical(secretKeyHex, canonicalDocument, canonicalConfig) {
  if (typeof secretKeyHex !== 'string' || typeof canonicalDocument !== 'string' ||
      typeof canonicalConfig !== 'string') {
    throw new TypeError('vcEddsaCreateFromCanonical: all three arguments must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.vcEddsaCreateFromCanonical !== 'function') {
    throw new Error('vcEddsaCreateFromCanonical: the loaded factoidal-npm-entry bundle predates the VC crypto exports');
  }
  const parsed = JSON.parse(abi.vcEddsaCreateFromCanonical(secretKeyHex, canonicalDocument, canonicalConfig));
  if (!parsed.ok) throw new Error(parsed.error || 'vcEddsaCreateFromCanonical failed');
  return parsed;
}

/**
 * Verify an eddsa-rdfc-2022 proofValue against canonical inputs. Wrong
 * key, tampered document/config, or tampered proofValue all report
 * verified:false.
 * @param {string} publicKeyHex
 * @param {string} canonicalDocument canonical N-Quads of the document
 * @param {string} canonicalConfig canonical N-Quads of the proof config
 * @param {string} proofValue the multibase-z proofValue to check
 * @returns {Promise<{ok:true, verified:boolean}>}
 */
export async function vcEddsaVerifyFromCanonical(publicKeyHex, canonicalDocument, canonicalConfig, proofValue) {
  if (typeof publicKeyHex !== 'string' || typeof canonicalDocument !== 'string' ||
      typeof canonicalConfig !== 'string' || typeof proofValue !== 'string') {
    throw new TypeError('vcEddsaVerifyFromCanonical: all four arguments must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.vcEddsaVerifyFromCanonical !== 'function') {
    throw new Error('vcEddsaVerifyFromCanonical: the loaded factoidal-npm-entry bundle predates the VC crypto exports');
  }
  const parsed = JSON.parse(abi.vcEddsaVerifyFromCanonical(publicKeyHex, canonicalDocument, canonicalConfig, proofValue));
  if (!parsed.ok) throw new Error(parsed.error || 'vcEddsaVerifyFromCanonical failed');
  return parsed;
}

/**
 * Resolve a `did:key:z6Mk...` identifier to its DID Document as RDF
 * (bin/npm-entry/entry_jsoo.ml's didKeyResolve export -> the verified
 * DID_Key.did_key_document, formal/fstar/DID.Key.fst). Pure and offline:
 * a did:key IS a multibase+multicodec Ed25519 public key, so resolution
 * is total function application -- no network, no registry.
 *
 * Scope: Ed25519 (the `z6Mk...` prefix, multicodec 0xed01) only. The
 * X25519 `keyAgreement` verification method is deferred (curve
 * conversion, not byte encoding). A non-Ed25519 did:key rejects.
 *
 * @param {string} didString e.g. "did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK"
 * @returns {Promise<{ok:true,did:string,nquads:string}>} `nquads` is the
 *   DID Document as N-Triples (verificationMethod, controller,
 *   publicKeyMultibase, authentication, assertionMethod,
 *   capabilityInvocation, capabilityDelegation).
 */
export async function didKeyResolve(didString) {
  if (typeof didString !== 'string') {
    throw new TypeError('didKeyResolve: didString must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.didKeyResolve !== 'function') {
    throw new Error(
      'didKeyResolve: the loaded factoidal-npm-entry bundle predates the did:key export');
  }
  const parsed = JSON.parse(abi.didKeyResolve(didString));
  if (!parsed.ok) throw new Error(parsed.error || 'didKeyResolve failed');
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
 * OWL tableau materialisation (bin/npm-entry/entry_jsoo.ml's
 * tableauMaterialise export -> formal/fstar/Tableau.fst's
 * tableau_materialise). Default graph only.
 *
 * @param {string} dataNQuads
 * @returns {Promise<{ok:true,nquads:string,addedCount:number}>}
 */
export async function tableauMaterialise(dataNQuads) {
  if (typeof dataNQuads !== 'string') {
    throw new TypeError('tableauMaterialise: dataNQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.tableauMaterialise !== 'function') {
    throw new Error(
      'tableauMaterialise: the loaded factoidal-npm-entry bundle predates the tableauMaterialise export');
  }
  const parsed = JSON.parse(abi.tableauMaterialise(dataNQuads));
  if (!parsed.ok) throw new Error(parsed.error || 'tableauMaterialise failed');
  return parsed;
}

/**
 * OWL DL inconsistency verdict (bin/npm-entry/entry_jsoo.ml's
 * tableauDlInconsistent export): the RL -> tableau -> RL ->
 * is_inconsistent DL pipeline, with `rlAlone` the plain OWL-RL verdict
 * on the same input for comparison. Default graph only.
 *
 * @param {string} dataNQuads
 * @returns {Promise<{ok:true,inconsistent:boolean,rlAlone:boolean}>}
 */
export async function tableauDlInconsistent(dataNQuads) {
  if (typeof dataNQuads !== 'string') {
    throw new TypeError('tableauDlInconsistent: dataNQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.tableauDlInconsistent !== 'function') {
    throw new Error(
      'tableauDlInconsistent: the loaded factoidal-npm-entry bundle predates the tableauDlInconsistent export');
  }
  const parsed = JSON.parse(abi.tableauDlInconsistent(dataNQuads));
  if (!parsed.ok) throw new Error(parsed.error || 'tableauDlInconsistent failed');
  return parsed;
}

/**
 * OWL DL consistency verdict via the verified clash-detecting tableau
 * (bin/npm-entry/entry_jsoo.ml's owlIsConsistent export ->
 * Tableau.Refute.tableau_consistent over the OWL-RL closure). Default
 * graph only. `consistent` is true|false|null (null = budget-out, with
 * `reason` naming the fuel cap -- never a silent false).
 *
 * @param {string} dataNQuads
 * @param {string} [optsJson] '' or a JSON object {"fuel":"<nat>"}
 * @returns {Promise<{ok:true,consistent:boolean|null,reason?:string}>}
 */
export async function owlIsConsistent(dataNQuads, optsJson) {
  if (typeof dataNQuads !== 'string') {
    throw new TypeError('owlIsConsistent: dataNQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.owlIsConsistent !== 'function') {
    throw new Error(
      'owlIsConsistent: the loaded factoidal-npm-entry bundle predates the owlIsConsistent export');
  }
  const parsed = JSON.parse(abi.owlIsConsistent(dataNQuads, optsJson || ''));
  if (!parsed.ok) throw new Error(parsed.error || 'owlIsConsistent failed');
  return parsed;
}

/**
 * OWL entailment check via the verified engine (bin/npm-entry/
 * entry_jsoo.ml's owlEntails export): the OWL-RL closure path
 * (`via:"closure"`) then negate-and-refute (`via:"refutation"`).
 * Default graph only. `entailed` is true|false|null (null = budget-out,
 * `reason` names the fuel cap).
 *
 * @param {string} premiseNQuads
 * @param {string} conclusionNQuads
 * @param {string} [optsJson] '' or a JSON object {"fuel":"<nat>"}
 * @returns {Promise<{ok:true,entailed:boolean|null,via:string,reason?:string}>}
 */
export async function owlEntails(premiseNQuads, conclusionNQuads, optsJson) {
  if (typeof premiseNQuads !== 'string' || typeof conclusionNQuads !== 'string') {
    throw new TypeError('owlEntails: premiseNQuads and conclusionNQuads must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.owlEntails !== 'function') {
    throw new Error(
      'owlEntails: the loaded factoidal-npm-entry bundle predates the owlEntails export');
  }
  const parsed = JSON.parse(abi.owlEntails(premiseNQuads, conclusionNQuads, optsJson || ''));
  if (!parsed.ok) throw new Error(parsed.error || 'owlEntails failed');
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

/**
 * Serialize an RDF dataset (N-Quads text) as an expanded-form JSON-LD
 * document -- the reverse of jsonldToRdf (bin/npm-entry/entry_jsoo.ml's
 * jsonldFromRdf export -> the verified JSONLD.FromRdf.from_rdf). The
 * returned `jsonld` string is JCS-canonical JSON.
 *
 * @param {string} nquads  N-Quads text
 * @param {{useNativeTypes?:boolean,useRdfType?:boolean}} [options]
 * @returns {Promise<{ok:true,jsonld:string}>}
 */
export async function jsonldFromRdf(nquads, options) {
  if (typeof nquads !== 'string') {
    throw new TypeError('jsonldFromRdf: nquads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.jsonldFromRdf !== 'function') {
    throw new Error(
      'jsonldFromRdf: the loaded factoidal-npm-entry bundle predates the jsonldFromRdf export');
  }
  const opts = options || {};
  const optionsJson = JSON.stringify({
    ...(opts.useNativeTypes ? { useNativeTypes: true } : {}),
    ...(opts.useRdfType ? { useRdfType: true } : {}),
  });
  const parsed = JSON.parse(abi.jsonldFromRdf(nquads, optionsJson));
  if (!parsed.ok) throw new Error(parsed.error || 'jsonldFromRdf failed');
  return parsed;
}

/**
 * Test whether an XML document is well-formed (bin/npm-entry/
 * entry_jsoo.ml's xmlWellformed export -> Parser_XML.parse_xml_document,
 * the accept/reject signal bin/xml-runner drives against W3C xmlconf).
 * The byte-oriented parser has no DOCTYPE/DTD production, so a document
 * containing a DOCTYPE reports wellformed:false.
 *
 * @param {string} xmlText
 * @returns {Promise<{ok:true,wellformed:boolean}>}
 */
export async function xmlWellformed(xmlText) {
  if (typeof xmlText !== 'string') {
    throw new TypeError('xmlWellformed: xmlText must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.xmlWellformed !== 'function') {
    throw new Error(
      'xmlWellformed: the loaded factoidal-npm-entry bundle predates the xmlWellformed export');
  }
  const parsed = JSON.parse(abi.xmlWellformed(xmlText));
  if (!parsed.ok) throw new Error(parsed.error || 'xmlWellformed failed');
  return parsed;
}

/**
 * Evaluate an XPath 1.0 expression over an XML document (bin/npm-entry/
 * entry_jsoo.ml's xpathEval export -> XPath_Eval.eval_xpath_from_root,
 * the Stage-1 engine tests/unit/xpath_tests.ml drives). The result
 * envelope carries `resultType` ('nodeset'|'string'|'number'|'boolean')
 * plus the value: for a node-set, `count`, `stringValue`, and a `nodes`
 * array of {kind,name,value}; otherwise a scalar `value`.
 *
 * @param {string} xmlText
 * @param {string} xpathExpr
 * @returns {Promise<object>}
 */
export async function xpathEval(xmlText, xpathExpr) {
  if (typeof xmlText !== 'string' || typeof xpathExpr !== 'string') {
    throw new TypeError('xpathEval: xmlText and xpathExpr must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.xpathEval !== 'function') {
    throw new Error(
      'xpathEval: the loaded factoidal-npm-entry bundle predates the xpathEval export');
  }
  const parsed = JSON.parse(abi.xpathEval(xmlText, xpathExpr));
  if (!parsed.ok) throw new Error(parsed.error || 'xpathEval failed');
  return parsed;
}

/**
 * Open a COTTAS/Parquet artifact's raw bytes as a queryable, read-only
 * store (bin/npm-entry/entry_jsoo.ml's openCottas export;
 * docs/designissues/2026-07-06-inmemory-bytes-store.md, browser call
 * site). Rows decode lazily as queryCottas() touches them -- the
 * corpus is never parsed into a heap dataset (that would defeat the
 * memory win the design doc measures).
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
    // Array-join, not per-byte string concat -- the concat loop
    // allocates millions of intermediate strings on a corpus-scale
    // artifact (same fix as lib/api.js's bytesToHex).
    const HEX = '0123456789abcdef';
    const parts = new Array(u8.length);
    for (let i = 0; i < u8.length; i++) {
      parts[i] = HEX[u8[i] >> 4] + HEX[u8[i] & 15];
    }
    hex = parts.join('');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.openCottas !== 'function') {
    throw new Error('openCottas: the loaded factoidal-npm-entry bundle predates the openCottas export');
  }
  const parsed = JSON.parse(abi.openCottas(hex));
  if (!parsed.ok) throw new Error(parsed.error || 'openCottas failed');
  return parsed.handle;
}

/**
 * Run a SPARQL 1.1 query against a store opened by openCottas()
 * (bin/npm-entry/entry_jsoo.ml's queryCottas export). No `entail`
 * option and no write overlay (read-only) -- see entry_jsoo.ml's
 * queryCottas doc comment for the full divergence list from query().
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
  const abi = await loadNpmEntry();
  if (typeof abi.queryCottas !== 'function') {
    throw new Error('queryCottas: the loaded factoidal-npm-entry bundle predates the queryCottas export');
  }
  const parsed = JSON.parse(abi.queryCottas(handle, encodeTextAsBundleBytes(sparql)));
  if (!parsed.ok) throw new Error(parsed.error || 'queryCottas failed');
  return parsed;
}

/**
 * Release a store opened by openCottas() (bin/npm-entry/entry_jsoo.ml's
 * closeCottas export). Drops the handle from the entry bundle's own
 * registry only -- does not evict the underlying byte cache (design
 * doc "Open decisions" item 1: no eviction API exists yet).
 * @param {string} handle
 * @returns {Promise<void>}
 */
export async function closeCottas(handle) {
  const abi = await loadNpmEntry();
  if (typeof abi.closeCottas !== 'function') {
    throw new Error('closeCottas: the loaded factoidal-npm-entry bundle predates the closeCottas export');
  }
  const parsed = JSON.parse(abi.closeCottas(handle));
  if (!parsed.ok) throw new Error(parsed.error || 'closeCottas failed');
}

// ---------------------------------------------------------------------
// Typed engine functions (#74 npm FP surface, browser side). Each is a
// thin, JSON-in/JSON-out wrapper over one F*-extracted engine exposed
// by entry_jsoo.ml through loadNpmEntry() -- the same ABI shape
// npm/factoidal/lib/api.js's Node-side wrappers use (duplicated here
// deliberately: browser.js is hand-maintained ESM with no access to
// lib/api.js's CommonJS/node: requires -- see this file's header
// comment). No logic lives on the JS side; the transform/eval/
// validate/CAS math is all verified F*. All need the npm-entry bundle.
// ---------------------------------------------------------------------

/**
 * XSLT 1.0 transform (entry_jsoo.ml's xsltTransform export ->
 * XSLT.Transform.transform). Applies `stylesheetXml` to `sourceXml`
 * and returns the serialized result tree.
 *
 * @param {string} stylesheetXml
 * @param {string} sourceXml
 * @returns {Promise<string>}
 */
export async function xsltTransform(stylesheetXml, sourceXml) {
  if (typeof stylesheetXml !== 'string' || typeof sourceXml !== 'string') {
    throw new TypeError('xsltTransform: stylesheetXml and sourceXml must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.xsltTransform !== 'function') {
    throw new Error('xsltTransform: the loaded factoidal-npm-entry bundle predates the XSLT export');
  }
  const parsed = JSON.parse(abi.xsltTransform(stylesheetXml, sourceXml));
  if (!parsed.ok) throw new Error(parsed.error || 'xsltTransform failed');
  return parsed.output;
}

/**
 * Evaluate a Content MathML document (entry_jsoo.ml's mathmlEval
 * export -> MathML.Content.eval_doc_env). `bindings` maps ci-variable
 * names to value strings; pass {} (or omit) for a closed expression.
 *
 * @param {string} contentMathmlXml
 * @param {Record<string,string>} [bindings]
 * @returns {Promise<{kind:'rat',num:number,den:number}|{kind:'bool',value:boolean}|{kind:'undef',reason:string}>}
 */
export async function mathmlEval(contentMathmlXml, bindings) {
  if (typeof contentMathmlXml !== 'string') {
    throw new TypeError('mathmlEval: contentMathmlXml must be a string');
  }
  const b = bindings || {};
  const abi = await loadNpmEntry();
  if (typeof abi.mathmlEval !== 'function') {
    throw new Error('mathmlEval: the loaded factoidal-npm-entry bundle predates the mathmlEval export');
  }
  const parsed = JSON.parse(abi.mathmlEval(contentMathmlXml, JSON.stringify(b)));
  if (!parsed.ok) throw new Error(parsed.error || 'mathmlEval failed');
  return parsed.value;
}

/**
 * XForms recalculate (entry_jsoo.ml's xformsRecalc export ->
 * XForms.Bind.recalculate): apply the model binds to `instanceXml`,
 * returning the recomputed instance and a validity report per bound
 * node.
 *
 * @param {string} instanceXml
 * @param {Array<{id?:string,target:string,calculate?:string,constraint?:string,relevant?:string,required?:string,readonly?:string,type?:string}>} binds
 * @returns {Promise<{instance:string,validity:Array<object>}>}
 */
export async function xformsRecalc(instanceXml, binds) {
  if (typeof instanceXml !== 'string') {
    throw new TypeError('xformsRecalc: instanceXml must be a string');
  }
  if (!Array.isArray(binds)) {
    throw new TypeError('xformsRecalc: binds must be an array');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.xformsRecalc !== 'function') {
    throw new Error('xformsRecalc: the loaded factoidal-npm-entry bundle predates the xformsRecalc export');
  }
  const parsed = JSON.parse(abi.xformsRecalc(instanceXml, JSON.stringify(binds)));
  if (!parsed.ok) throw new Error(parsed.error || 'xformsRecalc failed');
  return { instance: parsed.instance, validity: parsed.validity };
}

/**
 * JSON Schema (draft-07) validation (entry_jsoo.ml's
 * jsonSchemaValidate export -> JSONSchema.Validate.validate). The
 * verified validator gives a definite pass/fail/unsupported verdict
 * rather than a per-keyword error list.
 *
 * @param {string} schemaJson
 * @param {string} instanceJson
 * @returns {Promise<{valid:boolean,result:'pass'|'fail'|'unsupported',errors:string[]}>}
 */
export async function jsonSchemaValidate(schemaJson, instanceJson) {
  if (typeof schemaJson !== 'string' || typeof instanceJson !== 'string') {
    throw new TypeError('jsonSchemaValidate: schemaJson and instanceJson must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.jsonSchemaValidate !== 'function') {
    throw new Error('jsonSchemaValidate: the loaded factoidal-npm-entry bundle predates the jsonSchemaValidate export');
  }
  const parsed = JSON.parse(abi.jsonSchemaValidate(schemaJson, instanceJson));
  if (!parsed.ok) throw new Error(parsed.error || 'jsonSchemaValidate failed');
  return { valid: !!parsed.valid, result: parsed.result, errors: parsed.errors || [] };
}

/**
 * Schematron validation (entry_jsoo.ml's schematronValidate export ->
 * Schematron.Validate.validate): every finding (failed assert, fired
 * report, indeterminate) in pattern-then-document order.
 *
 * @param {string} schematronXml
 * @param {string} instanceXml
 * @returns {Promise<{findings:Array<{type:string,context:string,test:string,message:string,path:string,reason?:string}>}>}
 */
export async function schematronValidate(schematronXml, instanceXml) {
  if (typeof schematronXml !== 'string' || typeof instanceXml !== 'string') {
    throw new TypeError('schematronValidate: schematronXml and instanceXml must be strings');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.schematronValidate !== 'function') {
    throw new Error('schematronValidate: the loaded factoidal-npm-entry bundle predates the schematronValidate export');
  }
  const parsed = JSON.parse(abi.schematronValidate(schematronXml, instanceXml));
  if (!parsed.ok) throw new Error(parsed.error || 'schematronValidate failed');
  return { findings: parsed.findings };
}

// TOAN -- a small exact-CAS surface over Math.Expr (E_Int/E_Rat/E_Bool/
// E_Sym/E_App). Callers pass an expression as the JSON codec
//   {int:n} | {rat:[n,d]} | {bool:b} | {sym:name} | {app:name,args:[...]}
// and receive Content MathML for the result (via MathML.Present).
async function toanCall(fnName, what, ...args) {
  const abi = await loadNpmEntry();
  if (typeof abi[fnName] !== 'function') {
    throw new Error(`${fnName}: the loaded factoidal-npm-entry bundle predates the ${what} export`);
  }
  const parsed = JSON.parse(abi[fnName](...args));
  if (!parsed.ok) throw new Error(parsed.error || `${fnName} failed`);
  return parsed.mathml;
}

/** Finite summation of `bodyExpr[idx:=lo..hi]`, simplified, as Content MathML. */
export async function toanSummation(bodyExpr, idx, lo, hi) {
  if (typeof idx !== 'string') throw new TypeError('toanSummation: idx must be a string');
  return toanCall('toanSummation', 'TOAN summation',
    JSON.stringify(bodyExpr), idx, String(lo), String(hi));
}

/** Finite product of `bodyExpr[idx:=lo..hi]`, simplified, as Content MathML. */
export async function toanProduct(bodyExpr, idx, lo, hi) {
  if (typeof idx !== 'string') throw new TypeError('toanProduct: idx must be a string');
  return toanCall('toanProduct', 'TOAN product',
    JSON.stringify(bodyExpr), idx, String(lo), String(hi));
}

/** Canonical simplification of `expr`, as Content MathML. */
export async function toanSimplify(expr) {
  return toanCall('toanSimplify', 'TOAN simplify', JSON.stringify(expr));
}

/** Derivative of `expr` w.r.t. `variable`, as Content MathML. */
export async function toanDiff(expr, variable) {
  if (typeof variable !== 'string') throw new TypeError('toanDiff: variable must be a string');
  return toanCall('toanDiff', 'TOAN diff', JSON.stringify(expr), variable);
}

/** `expr[variable := value]` simplified, as Content MathML. */
export async function toanSubst(expr, variable, value) {
  if (typeof variable !== 'string') throw new TypeError('toanSubst: variable must be a string');
  return toanCall('toanSubst', 'TOAN subst',
    JSON.stringify(expr), variable, JSON.stringify(value));
}

// Matrix / vector algebra over exact rationals (Math.Matrix). A matrix
// is a JSON array of rows; a vector a JSON array of cells; a cell is
// an integer or a [num,den] pair. Results render via
// Math.Matrix.mres_to_string ("undef" carries a `reason`).
async function matrixCall(fnName, what, ...jsonArgs) {
  const abi = await loadNpmEntry();
  if (typeof abi[fnName] !== 'function') {
    throw new Error(`${fnName}: the loaded factoidal-npm-entry bundle predates the ${what} export`);
  }
  const parsed = JSON.parse(abi[fnName](...jsonArgs.map((a) => JSON.stringify(a))));
  if (!parsed.ok) throw new Error(parsed.error || `${fnName} failed`);
  return { result: parsed.result, reason: parsed.reason || '' };
}

/** Exact determinant of a square matrix (Math.Matrix.dyn_determinant). */
export async function matrixDeterminant(matrix) {
  if (!Array.isArray(matrix)) throw new TypeError('matrixDeterminant: matrix must be an array of rows');
  return matrixCall('matrixDeterminant', 'matrix determinant', matrix);
}

/** Dot product of two vectors (Math.Matrix.dyn_scalarproduct). */
export async function matrixScalarProduct(a, b) {
  if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixScalarProduct: a and b must be arrays');
  return matrixCall('matrixScalarProduct', 'vector scalar product', a, b);
}

/** Cross product of two 3-vectors (Math.Matrix.dyn_vectorproduct). */
export async function matrixVectorProduct(a, b) {
  if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixVectorProduct: a and b must be arrays');
  return matrixCall('matrixVectorProduct', 'vector cross product', a, b);
}

/** Outer product of two vectors (Math.Matrix.dyn_outerproduct). */
export async function matrixOuterProduct(a, b) {
  if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixOuterProduct: a and b must be arrays');
  return matrixCall('matrixOuterProduct', 'vector outer product', a, b);
}

// A `scaled` value as entry_jsoo.ml's scaledJson envelope decodes it:
// {mantissa,scale,decimal} strings straight off the wire.
function scaledFromJson(s) {
  return { mantissa: s.mantissa, scale: s.scale, decimal: s.decimal };
}

/**
 * n+1 evenly spaced samples of the logistic sigmoid
 * L / (1 + exp(-k*(x - x0))) over [xmin, xmax] (entry_jsoo.ml's
 * sigmoidPoints export -> Math.Sigmoid.sigmoid_points). All arithmetic
 * -- argument reduction, the truncated Taylor series, repeated
 * squaring, and the x samples themselves -- runs as exact rational
 * arithmetic inside Math.Sigmoid.fst; see that module's header for the
 * documented error bound on the returned (rounded) values. This
 * wrapper only marshals JSON; it never computes exp itself.
 *
 * @param {{k:number|string,x0:number|string,l:number|string,
 *   xmin:number|string,xmax:number|string,n:number|string}} params
 * @returns {Promise<Array<{x:{mantissa:string,scale:string,decimal:string},
 *   y:{mantissa:string,scale:string,decimal:string}}>>}
 */
export async function sigmoidPoints(params) {
  if (!params || typeof params !== 'object') {
    throw new TypeError('sigmoidPoints: params must be an object');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.sigmoidPoints !== 'function') {
    throw new Error('sigmoidPoints: the loaded factoidal-npm-entry bundle predates the sigmoidPoints export');
  }
  const wire = {
    k: String(params.k), x0: String(params.x0), l: String(params.l),
    xmin: String(params.xmin), xmax: String(params.xmax), n: String(params.n),
  };
  const parsed = JSON.parse(abi.sigmoidPoints(JSON.stringify(wire)));
  if (!parsed.ok) throw new Error(parsed.error || 'sigmoidPoints failed');
  return parsed.points.map((p) => ({ x: scaledFromJson(p.x), y: scaledFromJson(p.y) }));
}

/**
 * Presentation MathML for the sigmoid formula L / (1 + exp(-k*(x - x0))),
 * engine-serialized (entry_jsoo.ml's sigmoidFormulaMathml export ->
 * MathML.Present.to_presentation_mathml applied to a fixed Math.Expr.
 * expr) -- never hand-written MathML.
 *
 * @returns {Promise<string>} a `<math>...</math>` Presentation MathML document
 */
export async function sigmoidFormulaMathml() {
  const abi = await loadNpmEntry();
  if (typeof abi.sigmoidFormulaMathml !== 'function') {
    throw new Error('sigmoidFormulaMathml: the loaded factoidal-npm-entry bundle predates the sigmoidFormulaMathml export');
  }
  const parsed = JSON.parse(abi.sigmoidFormulaMathml());
  if (!parsed.ok) throw new Error(parsed.error || 'sigmoidFormulaMathml failed');
  return parsed.mathml;
}

// ---------------------------------------------------------------------
// HDT (Header-Dictionary-Triples): query a read-only binary RDF
// artifact's raw bytes via the CLI's `--data-hdt` backend
// (factoidal_cli.ml, HDT.Triples.fst and the parser modules around
// it). No npm-entry ABI bundle needed -- this is a CLI-only
// capability, built on runFactoidalCli() exactly the way query() is,
// so a hub cell no longer needs to build the --data-hdt argv and fake
// filesystem entry by hand (see docs/web/hub/24-hdt-header-dictionary-
// triples.md's earlier revision for what this replaces). Default
// graph only, SELECT/ASK only (no CONSTRUCT, no named graphs -- HDTQ
// is a separate, deferred extension; see factoidal_cli.ml's --data-hdt
// help text).
// ---------------------------------------------------------------------

let _hdtSeq = 0;

/**
 * Run a SPARQL 1.1 query against an HDT artifact's raw bytes. Same
 * output shape as query(): parsed SPARQL Results JSON when
 * `options.output` is 'json' (default), the raw output string
 * otherwise.
 *
 * @param {Uint8Array|ArrayBuffer|string} hdtBytes whole .hdt file
 *   contents -- a Uint8Array/ArrayBuffer is packed automatically into
 *   the fake filesystem's one-char-per-byte convention; a string is
 *   assumed already packed.
 * @param {string} sparql a SELECT or ASK query
 * @param {{output?: 'json'|'table'|'csv'|'ntriples'}} [options]
 * @returns {Promise<object|string>}
 */
export async function queryHdt(hdtBytes, sparql, options) {
  if (typeof sparql !== 'string') {
    throw new TypeError('queryHdt: sparql must be a string');
  }
  const opts = options || {};
  const output = opts.output || 'json';
  if (!OUTPUT_FORMATS.has(output)) {
    throw new TypeError(`queryHdt: output must be one of ${[...OUTPUT_FORMATS].join(', ')}`);
  }

  let content;
  if (typeof hdtBytes === 'string') {
    content = hdtBytes;
  } else {
    const u8 = hdtBytes instanceof Uint8Array ? hdtBytes
      : hdtBytes instanceof ArrayBuffer ? new Uint8Array(hdtBytes) : null;
    if (!u8) {
      throw new TypeError('queryHdt: hdtBytes must be a Uint8Array, ArrayBuffer, or an already-packed string');
    }
    let s = '';
    for (let i = 0; i < u8.length; i += 0x4000) {
      s += String.fromCharCode.apply(null, u8.subarray(i, Math.min(u8.length, i + 0x4000)));
    }
    content = s;
  }

  const path = '/static/hdt' + (_hdtSeq++) + '.hdt';
  const { stdout, stderr, exitCode, engineMs } = await runFactoidalCli(
    ['--data-hdt', path, '-e', encodeTextAsBundleBytes(sparql), '-o', output === 'json' ? 'json' : output],
    [{ name: path, content }]);

  if (exitCode !== 0) {
    const msg = (stderr || stdout || `factoidal exited with code ${exitCode}`).trim();
    const err = new Error('HDT query failed: ' + msg);
    err.exitCode = exitCode;
    err.stderr = stderr;
    err.stdout = stdout;
    throw err;
  }

  if (output !== 'json') return stdout;

  const firstBrace = stdout.indexOf('{');
  const lastBrace = stdout.lastIndexOf('}');
  if (firstBrace < 0 || lastBrace < firstBrace) {
    const err = new Error('factoidal did not produce JSON on stdout. Raw output: ' + stdout);
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
  const jsonText = stdout.slice(firstBrace, lastBrace + 1);
  try {
    const parsed = JSON.parse(jsonText);
    Object.defineProperty(parsed, 'engineMs', { value: engineMs, enumerable: false });
    return parsed;
  } catch (e) {
    const err = new Error('factoidal JSON parse failed: ' + e.message + '. Raw output: ' + stdout);
    err.stdout = stdout;
    err.stderr = stderr;
    throw err;
  }
}

/**
 * Serialize a dataset-handle N-Quads string to COTTAS/Parquet bytes via
 * the native writer (bin/npm-entry/entry_jsoo.ml's toCottas export;
 * RDF.CottasStore.BaseWriter.serialize_cottas_v2, the same pure `Tot`
 * function `factoidal compact --native-writer` uses). Round-trips into
 * openCottas() byte-for-byte.
 *
 * @param {string} nQuads dataset-handle N-Quads text (see toRdf() to get here from another format)
 * @returns {Promise<Uint8Array>}
 */
export async function toCottas(nQuads) {
  if (typeof nQuads !== 'string') {
    throw new TypeError('toCottas: nQuads must be a string');
  }
  const abi = await loadNpmEntry();
  if (typeof abi.toCottas !== 'function') {
    throw new Error('toCottas: the loaded factoidal-npm-entry bundle predates the toCottas export');
  }
  const parsed = JSON.parse(abi.toCottas(nQuads));
  if (!parsed.ok) throw new Error(parsed.error || 'toCottas failed');
  const hex = parsed.cottasHex;
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.substr(i * 2, 2), 16);
  return out;
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
  shaclValidate, shexValidate, didKeyResolve, owlClosure,
  tableauMaterialise, tableauDlInconsistent, owlIsConsistent, owlEntails, rmlMap, jsonldToRdf,
  jsonldFromRdf, xmlWellformed, xpathEval,
  deltaLogOpen, deltaLogAppend, deltaLogReadAllHex, deltaLogMerge,
  deltaLogDestroy, _deltaLogCorruptLastForTest,
  openCottas, queryCottas, closeCottas, toCottas,
  xsltTransform, mathmlEval, xformsRecalc, jsonSchemaValidate, schematronValidate,
  toanSummation, toanProduct, toanSimplify, toanDiff, toanSubst,
  matrixDeterminant, matrixScalarProduct, matrixVectorProduct, matrixOuterProduct,
  vcSha256Hex, vcEd25519SecretToPublic, vcEd25519Sign, vcEd25519Verify,
  vcEddsaCreateFromCanonical, vcEddsaVerifyFromCanonical,
  queryHdt,
};
