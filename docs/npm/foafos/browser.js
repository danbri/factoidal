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
 * @param {string[]} args   CLI arguments (after argv[0]/argv[1]).
 * @param {Array<{name: string, content: string}>} files
 *        Documents for the fake filesystem. Names must start with
 *        '/static/'.
 * @returns {Promise<{stdout: string, stderr: string, exitCode: number}>}
 */
export async function runFactoidalCli(args, files) {
  const src = await loadFactoidalSource();

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

  try {
    (new Function(src))();
  } catch (e) {
    if (e !== EXIT_SENTINEL) { restore(); throw e; }
  } finally {
    restore();
  }

  return {
    stdout: stdoutBuf.join('\n'),
    stderr: stderrBuf.join('\n'),
    exitCode,
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
    '-e', queryString,
    '-o', output === 'json' ? 'json' : output,
  ];
  if (entail !== 'none') argv.push('--entail', entail);

  const { stdout, stderr, exitCode } =
    await runFactoidalCli(argv, [{ name: dataPath, content: dataString }]);

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
    return JSON.parse(jsonText);
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
  if (baseIRI) argv.push('-b', baseIRI);

  const { stdout, stderr, exitCode } =
    await runFactoidalCli(argv, [{ name: dataPath, content: text }]);

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

// Best-effort version export for the browser. Consumers that care
// about the exact version should import from the package root (which
// reads package.json).
export const version = '0.1.0-alpha.0';

export default {
  query, toRdf, canonicalize, runFactoidalCli, setFactoidalUrl, version,
};
