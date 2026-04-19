// factoidal — formally-verified SPARQL 1.1 + RDF 1.1
//
// CommonJS entry point. Wraps the js_of_ocaml-compiled `factoidal.js`
// (F*-extracted OCaml → JavaScript) in a clean Node API.
//
// The underlying engine is a single-shot CLI — argv in, stdout out.
// We drive it by:
//   1. Writing the input data into js_of_ocaml's fake filesystem
//      (globalThis.jsoo_fs_tmp, drained at engine startup).
//   2. Setting globalThis.process.argv to the flags we want.
//   3. Overriding console.log/.error to capture stdout/stderr.
//   4. Running the CLI source via `new Function(src)()`, catching the
//      synthetic exit we inject into process.exit.
//
// The API is `async` so a future wasm path (or async regex / HTTP
// SERVICE) can slot in without changing callers.
//
// See README.md for usage examples.

'use strict';

const fs = require('node:fs');
const path = require('node:path');

// Lazy-loaded cache of the factoidal.js source. We load once and reuse.
let _factoidalSrc = null;
function loadFactoidalSource() {
  if (_factoidalSrc !== null) return _factoidalSrc;
  const artifact = path.join(__dirname, 'factoidal.js');
  if (!fs.existsSync(artifact)) {
    throw new Error(
      "factoidal.js not found next to index.js. Run 'npm run build' " +
      "from npm/factoidal/, or in the repo root run " +
      "'formal/fstar/build-ocaml.sh npm' to populate this module."
    );
  }
  _factoidalSrc = fs.readFileSync(artifact, 'utf8');
  return _factoidalSrc;
}

// Package metadata.
const pkg = require('./package.json');
const version = pkg.version;

// Data format tags accepted on the options object. We accept the
// upstream CLI names so users can mentally map 1:1 with `factoidal -d`.
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
  if (!fmt) return 'ttl';
  const key = String(fmt).toLowerCase();
  if (!(key in DATA_FORMAT_EXT)) {
    throw new TypeError(
      `Unknown dataFormat '${fmt}'. Expected one of: ` +
      Object.keys(DATA_FORMAT_EXT).join(', ')
    );
  }
  return DATA_FORMAT_EXT[key];
}

/**
 * Run a SPARQL query against an RDF dataset, in memory.
 *
 * @param {string} dataString   RDF data serialized as Turtle (default),
 *                              N-Triples, N-Quads, TriG, or RDF/XML.
 * @param {string} queryString  SPARQL 1.1 query text. SELECT, ASK,
 *                              CONSTRUCT, DESCRIBE supported.
 * @param {object} [options]
 * @param {string} [options.dataFormat='turtle']  Tag for `dataString`.
 *                                                Accepts: 'turtle',
 *                                                'ntriples', 'nquads',
 *                                                'trig', 'rdfxml'.
 * @param {string} [options.entail='none']        'none' | 'RDFS' | 'OWL-RL'.
 * @param {string} [options.output='json']        'json' | 'csv' | 'tsv'
 *                                                | 'xml' | 'table'
 *                                                | 'ntriples'.
 *                                                When 'json', the
 *                                                returned promise
 *                                                resolves to a parsed
 *                                                SPARQL Results JSON
 *                                                object. Otherwise it
 *                                                resolves to the raw
 *                                                string.
 * @returns {Promise<object|string>}
 */
function query(dataString, queryString, options) {
  // Accept promises-all-the-way so a future wasm/async path doesn't
  // break callers.
  return Promise.resolve().then(() => {
    if (typeof dataString !== 'string') {
      throw new TypeError('query: dataString must be a string');
    }
    if (typeof queryString !== 'string') {
      throw new TypeError('query: queryString must be a string');
    }
    const opts = options || {};
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

    const ext = extForFormat(dataFormat);
    // Under Node, js_of_ocaml's root device is the real filesystem, so
    // jsoo_fs_tmp can only register files under `/static/` (which is
    // the MlFakeDevice mount-point baked into the runtime). Under a
    // browser it's the other way around — root is MlFakeDevice — but
    // `/static/` is always fake, so it works in both environments.
    const dataPath = '/static/data.' + ext;

    // ------------------------------------------------------------------
    // Save globals we're about to clobber so parallel work in the same
    // process isn't disturbed (this is still not reentrancy-safe — two
    // concurrent calls will collide — but it doesn't leak state to the
    // caller's console.log).
    // ------------------------------------------------------------------
    const orig = {
      argv:   globalThis.process ? globalThis.process.argv : undefined,
      exit:   globalThis.process ? globalThis.process.exit : undefined,
      jsooFs: globalThis.jsoo_fs_tmp,
    };

    // Under Node, js_of_ocaml's runtime opens real fds 1/2 with
    // `require('fs').openSync(1, ...)` and then writes via
    // `fs.writeSync(fd, <Uint8Array>, ...)` — bypassing both
    // `console.log` and `process.stdout.write`. To capture the CLI's
    // output cleanly we proxy the `require` we hand the bundle so that
    // `require('fs')` returns an fs module whose `writeSync` routes fd
    // 1 into our stdout buffer and fd 2 into our stderr buffer.
    // Everything else on the fs module is pass-through so the bundle's
    // other I/O (e.g. seeking, stat) works unchanged.
    const stdoutChunks = [];
    const stderrChunks = [];
    function asUtf8(data) {
      if (typeof data === 'string') return data;
      if (data && typeof data.toString === 'function') {
        try { return Buffer.from(data).toString('utf8'); }
        catch (_) { return String(data); }
      }
      return String(data);
    }
    const realFs     = require('node:fs');
    const patchedFs  = new Proxy(realFs, {
      get(target, prop, receiver) {
        if (prop === 'writeSync') {
          return function proxyWriteSync(fd, chunk, ...rest) {
            if (fd === 1) { stdoutChunks.push(asUtf8(chunk)); return asUtf8(chunk).length; }
            if (fd === 2) { stderrChunks.push(asUtf8(chunk)); return asUtf8(chunk).length; }
            return target.writeSync(fd, chunk, ...rest);
          };
        }
        return Reflect.get(target, prop, receiver);
      },
    });
    function wrappedRequire(name) {
      if (name === 'fs' || name === 'node:fs') return patchedFs;
      return require(name);
    }

    // Map our `output` to the CLI's -o flag. `json` stays `json`; the
    // CLI's other formats (csv/tsv/xml/table/ntriples) are passed
    // through unchanged.
    const cliOutput =
      output === 'json'     ? 'json'     :
      output === 'csv'      ? 'csv'      :
      output === 'tsv'      ? 'tsv'      :
      output === 'xml'      ? 'xml'      :
      output === 'ntriples' ? 'ntriples' :
      /* table */             'table';

    const argv = [
      'node', 'factoidal',
      '-d', dataPath,
      '-e', queryString,
      '-o', cliOutput,
    ];
    if (entail !== 'none') argv.push('--entail', entail);

    globalThis.process      = globalThis.process || {};
    globalThis.process.argv = argv;
    globalThis.jsoo_fs_tmp  = [{ name: dataPath, content: dataString }];

    // Intercept process.exit so we don't actually kill Node when the
    // CLI is done. We re-throw a private sentinel and catch it below.
    let exitCode = 0;
    const EXIT_SENTINEL = new Error('__factoidal_exit__');
    globalThis.process.exit = (n) => { exitCode = n | 0; throw EXIT_SENTINEL; };

    try {
      const src = loadFactoidalSource();
      // Evaluate the CLI bundle. It reads argv + jsoo_fs_tmp, runs,
      // then either returns normally (exit 0) or calls process.exit(N).
      //
      // js_of_ocaml's generated code calls `require('fs')` directly
      // to back both the node-fs device and the stdout/stderr
      // channels. A bare `new Function(src)()` strips the enclosing
      // module's require, so we pass in our wrapped version that
      // intercepts fs.writeSync for fds 1/2.
      (new Function('require', src))(wrappedRequire);
    } catch (e) {
      if (e !== EXIT_SENTINEL) {
        // Real failure from the bundle. Restore everything before
        // propagating so the caller's process is left clean.
        if (globalThis.process) {
          globalThis.process.argv = orig.argv;
          globalThis.process.exit = orig.exit;
        }
        globalThis.jsoo_fs_tmp = orig.jsooFs;
        throw e;
      }
    } finally {
      if (globalThis.process) {
        globalThis.process.argv = orig.argv;
        globalThis.process.exit = orig.exit;
      }
      globalThis.jsoo_fs_tmp = orig.jsooFs;
    }

    const stdout = stdoutChunks.join('');
    const stderr = stderrChunks.join('');

    if (exitCode !== 0) {
      const msg =
        (stderr || stdout || `factoidal exited with code ${exitCode}`)
          .trim();
      const err = new Error('SPARQL query failed: ' + msg);
      err.exitCode = exitCode;
      err.stderr   = stderr;
      err.stdout   = stdout;
      throw err;
    }

    if (output !== 'json') return stdout;

    // Parse JSON results. The CLI may prepend a line like "Loaded N
    // triples." on stderr, not stdout, so stdout should be pure JSON.
    // Be defensive: find the first '{' and the last '}' in case stray
    // lines slip in.
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
  });
}

module.exports = {
  query,
  version,
};
