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

  const src = await loadFactoidalSource();

  const ext      = extForFormat(dataFormat);
  // Mount under `/static/`: that path is an MlFakeDevice in js_of_ocaml
  // both in the browser and under Node. `/tmp/` is only fake in the
  // browser; keeping one path keeps the Node and browser drivers in
  // lockstep.
  const dataPath = '/static/data.' + ext;

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
  console.log   = (...args) => stdoutBuf.push(args.join(' '));
  console.error = (...args) => stderrBuf.push(args.join(' '));

  const argv = [
    'node', 'factoidal',
    '-d', dataPath,
    '-e', queryString,
    '-o', output === 'json' ? 'json' : output,
  ];
  if (entail !== 'none') argv.push('--entail', entail);

  globalThis.process     = globalThis.process || {};
  globalThis.process.argv = argv;
  globalThis.jsoo_fs_tmp  = [{ name: dataPath, content: dataString }];

  let exitCode = 0;
  const EXIT_SENTINEL = new Error('__factoidal_exit__');
  globalThis.process.exit = (n) => { exitCode = n | 0; throw EXIT_SENTINEL; };

  try {
    (new Function(src))();
  } catch (e) {
    if (e !== EXIT_SENTINEL) {
      // Restore before rethrowing.
      console.log   = orig.log;
      console.error = orig.error;
      if (globalThis.process) {
        globalThis.process.argv = orig.argv;
        globalThis.process.exit = orig.exit;
      }
      globalThis.jsoo_fs_tmp = orig.jsooFs;
      throw e;
    }
  } finally {
    console.log   = orig.log;
    console.error = orig.error;
    if (globalThis.process) {
      globalThis.process.argv = orig.argv;
      globalThis.process.exit = orig.exit;
    }
    globalThis.jsoo_fs_tmp = orig.jsooFs;
  }

  const stdout = stdoutBuf.join('\n');
  const stderr = stderrBuf.join('\n');

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

// Best-effort version export for the browser. Consumers that care
// about the exact version should import from the package root (which
// reads package.json).
export const version = '0.1.0-alpha.0';

export default { query, version, setFactoidalUrl };
