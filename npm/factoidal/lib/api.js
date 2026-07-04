// factoidal — public API layer, shared by index.js (js_of_ocaml) and
// wasm.js (wasm_of_ocaml).
//
// Two ways to reach the engine, tried in order:
//
//   1. The npm-entry ABI bundle (factoidal-npm-entry.js /
//      factoidal-npm-entry.wasm.js — built from bin/npm-entry/
//      entry_jsoo.ml). A persistent, function-call ABI: strings in,
//      JSON out. Supports everything including CONSTRUCT, UPDATE and
//      RDFC-1.0 canonicalization.
//
//   2. The single-shot CLI bundle (factoidal.js / factoidal.wasm.js),
//      driven argv-style via lib/engine-js.js / lib/engine-wasm.js.
//      Covers parse / SELECT / ASK / serialize today; CONSTRUCT and
//      UPDATE are not reachable through the CLI surface, and
//      canonicalize requires a bundle built after the `factoidal
//      canonicalize` subcommand landed.
//
// Operations that need the npm-entry bundle throw an Error whose
// message contains "pending npm-entry build" when only the CLI bundle
// is available. All semantic work happens inside the F*-extracted
// engine either way; this layer only shapes arguments and results.

'use strict';

const {
  Dataset,
  dataFactory,
  termFromSrj,
} = require('../rdfjs.js');

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

// Canonical format tag for the npm-entry ABI (RDF_Format.format_of_string
// accepts these names directly).
const DATA_FORMAT_TAG = {
  ttl: 'turtle', nt: 'ntriples', nq: 'nquads', trig: 'trig', rdf: 'rdfxml',
};

const ENTAIL_VALUES = new Set(['none', 'RDFS', 'OWL-RL']);

function extForFormat(fmt) {
  const key = String(fmt || 'turtle').toLowerCase();
  if (!(key in DATA_FORMAT_EXT)) {
    throw new TypeError(
      `Unknown format '${fmt}'. Expected one of: ` +
      Object.keys(DATA_FORMAT_EXT).join(', ')
    );
  }
  return DATA_FORMAT_EXT[key];
}

function engineError(prefix, res) {
  const msg = (res.stderr || res.stdout ||
    `factoidal exited with code ${res.exitCode}`).trim();
  const err = new Error(`${prefix}: ${msg}`);
  err.exitCode = res.exitCode;
  err.stderr = res.stderr;
  err.stdout = res.stdout;
  return err;
}

function pendingError(what) {
  return new Error(
    `${what} needs the factoidal-npm-entry bundle, which is not present ` +
    '— pending npm-entry build (formal/fstar/build-ocaml.sh js + npm ' +
    'with bin/npm-entry/entry_jsoo.ml wired in; see bin/npm-entry/README.md).'
  );
}

// Extract the JSON object from CLI stdout defensively (a stray line
// must not break the parse).
function jsonFromStdout(stdout, what) {
  const first = stdout.indexOf('{');
  const last = stdout.lastIndexOf('}');
  if (first < 0 || last < first) {
    const err = new Error(`${what}: engine did not produce JSON: ${stdout}`);
    err.stdout = stdout;
    throw err;
  }
  return JSON.parse(stdout.slice(first, last + 1));
}

// Detect the query form for result-shape dispatch. IRIs and comments
// are blanked first so '#' inside a PREFIX IRI cannot hide the verb.
// The engine's SPARQL parser remains the authority — this only picks
// the output shape.
function sniffQueryForm(sparql) {
  const cleaned = String(sparql)
    .replace(/<[^>]*>/g, ' ')
    .replace(/#[^\n]*/g, ' ');
  const m = cleaned.match(/\b(select|ask|construct|describe)\b/i);
  return m ? m[1].toLowerCase() : 'select';
}

// SRJ bindings -> Array<Map<string, Term>>
function bindingsFromSrj(srj) {
  const rows = (srj && srj.results && srj.results.bindings) || [];
  return rows.map((row) => {
    const map = new Map();
    for (const [name, term] of Object.entries(row)) {
      map.set(name, termFromSrj(term));
    }
    return map;
  });
}

/**
 * Build the public API around a driver.
 *
 * @param {object} driver
 * @param {(args: string[], files: Array<{name,content}>) =>
 *         ({stdout,stderr,exitCode}|Promise)} driver.runCli
 * @param {() => (object|null|Promise<object|null>)} driver.loadEntry
 *        Returns the npm-entry ABI object (factoidalNpmEntry) or null.
 * @param {string} driver.engineName  'js' | 'wasm' (error messages).
 */
function buildApi(driver) {
  let parseCounter = 0;
  let entryCache; // undefined = not tried; null = unavailable

  async function entry() {
    if (entryCache === undefined) {
      try {
        entryCache = (await driver.loadEntry()) || null;
      } catch (_) {
        entryCache = null;
      }
    }
    return entryCache;
  }

  async function run(args, files) {
    return driver.runCli(args, files);
  }

  function entryResult(jsonText, what) {
    const r = JSON.parse(jsonText);
    if (!r.ok) throw new Error(`${what}: ${r.error}`);
    return r;
  }

  function freshBnodePrefix() {
    return `p${parseCounter++}_`;
  }

  // Normalize the `data` argument of query/update/serialize/
  // canonicalize into engine inputs. Accepts a Dataset, a raw string
  // (with options.format, default turtle), or an array of those —
  // each element is loaded as its own document so blank-node labels
  // stay document-scoped (the per-document renaming is F*'s
  // RDF.Dataset.Merge.rename_dataset_bnodes, applied at engine load).
  function toDocs(data, options) {
    const opts = options || {};
    const items = Array.isArray(data) ? data : [data];
    return items.map((item, i) => {
      if (item instanceof Dataset) {
        return { ext: 'nq', content: item.toNQuads() };
      }
      if (typeof item === 'string') {
        return { ext: extForFormat(opts.format), content: item };
      }
      if (item && typeof item.text === 'string') {
        return { ext: extForFormat(item.format || opts.format), content: item.text };
      }
      throw new TypeError(
        `data[${i}]: expected a Dataset, a string, or {text, format}`);
    });
  }

  function docsToCliFiles(docs) {
    const files = [];
    const flags = [];
    docs.forEach((d, i) => {
      const name = `/static/data${i}.${d.ext}`;
      files.push({ name, content: d.content });
      flags.push('-d', name);
    });
    return { files, flags };
  }

  // Everything below is async so both drivers (sync jsoo, async wasm)
  // and both paths (entry, CLI) share one shape.

  /**
   * Parse one RDF document into a Dataset.
   * @param {string} text
   * @param {{format?: string, baseIRI?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function parse(text, options) {
    if (typeof text !== 'string') {
      throw new TypeError('parse: text must be a string');
    }
    const opts = options || {};
    const ext = extForFormat(opts.format);
    const baseIRI = opts.baseIRI || '';
    const bnodePrefix = freshBnodePrefix();

    const e = await entry();
    if (e) {
      const r = entryResult(
        e.parseToDatasetJson(text, DATA_FORMAT_TAG[ext], baseIRI), 'parse');
      return Dataset.fromNQuads(r.nquads, { blankNodePrefix: bnodePrefix });
    }

    const name = `/static/data.${ext}`;
    const args = ['--dump-nq', '-d', name];
    if (baseIRI) args.push('-b', baseIRI);
    const res = await run(args, [{ name, content: text }]);
    if (res.exitCode !== 0) throw engineError('parse failed', res);
    return Dataset.fromNQuads(res.stdout, { blankNodePrefix: bnodePrefix });
  }

  /**
   * Run a SPARQL 1.1 query.
   * @param {Dataset|string|Array} data
   * @param {string} sparql
   * @param {{format?: string, entail?: 'none'|'RDFS'|'OWL-RL'}} [options]
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   *   SELECT -> Bindings[] (Map of variable name -> RDF/JS Term),
   *   ASK -> boolean, CONSTRUCT -> Dataset.
   */
  async function query(data, sparql, options) {
    if (typeof sparql !== 'string') {
      throw new TypeError('query: sparql must be a string');
    }
    const opts = options || {};
    const entail = opts.entail || 'none';
    if (!ENTAIL_VALUES.has(entail)) {
      throw new TypeError(
        `query: entail must be one of ${[...ENTAIL_VALUES].join(', ')}`);
    }
    const form = sniffQueryForm(sparql);
    const docs = toDocs(data, opts);

    // The npm-entry ABI covers all query forms but has no entailment
    // parameter; entailment closure stays on the CLI path.
    const e = entail === 'none' ? await entry() : null;
    if (e) {
      // The ABI's dataset handle is N-Quads: normalize non-N-Quads
      // documents through parseToDatasetJson first (each document
      // separately, preserving per-document blank-node scoping in F*).
      let nq = '';
      for (const d of docs) {
        if (d.ext === 'nq') { nq += d.content; continue; }
        const r = entryResult(
          e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
          'query(parse)');
        nq += r.nquads;
      }
      const r = entryResult(e.queryDataset(nq, sparql), 'query');
      if (r.kind === 'ask') return r.boolean;
      if (r.kind === 'construct') {
        return Dataset.fromNQuads(r.nquads, {
          blankNodePrefix: freshBnodePrefix(),
        });
      }
      return bindingsFromSrj(r.srj);
    }

    if (form === 'construct' || form === 'describe') {
      throw pendingError(`${form.toUpperCase()} queries`);
    }

    const { files, flags } = docsToCliFiles(docs);
    const args = [...flags, '-e', sparql, '-o', 'json'];
    if (entail !== 'none') args.push('--entail', entail);
    const res = await run(args, files);
    if (res.exitCode !== 0) throw engineError('query failed', res);
    const srj = jsonFromStdout(res.stdout, 'query');
    if (form === 'ask' || typeof srj.boolean === 'boolean') {
      return !!srj.boolean;
    }
    return bindingsFromSrj(srj);
  }

  /**
   * Apply a SPARQL 1.1 Update to a dataset, returning the new Dataset.
   * Needs the npm-entry bundle.
   * @param {Dataset|string|Array} data
   * @param {string} updateText
   * @param {{format?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function update(data, updateText, options) {
    if (typeof updateText !== 'string') {
      throw new TypeError('update: updateText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('SPARQL UPDATE');
    const docs = toDocs(data, options);
    let nq = '';
    for (const d of docs) {
      if (d.ext === 'nq') { nq += d.content; continue; }
      const r = entryResult(
        e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
        'update(parse)');
      nq += r.nquads;
    }
    const r = entryResult(e.updateDataset(nq, updateText), 'update');
    return Dataset.fromNQuads(r.nquads, {
      blankNodePrefix: freshBnodePrefix(),
    });
  }

  /**
   * Serialize a dataset (engine-produced bytes, sorted N-Quads order).
   * @param {Dataset|string|Array} data
   * @param {{format?: 'nquads'|'ntriples', inputFormat?: string}} [options]
   * @returns {Promise<string>}
   */
  async function serialize(data, options) {
    const opts = options || {};
    const outFormat = String(opts.format || 'nquads').toLowerCase();
    if (outFormat !== 'nquads' && outFormat !== 'ntriples') {
      throw new TypeError(
        "serialize: format must be 'nquads' or 'ntriples' " +
        '(turtle output is pending npm-entry build)');
    }
    const docs = toDocs(data, { format: opts.inputFormat });

    if (outFormat === 'nquads') {
      const e = await entry();
      if (e && docs.every((d) => d.ext === 'nq')) {
        const nq = docs.map((d) => d.content).join('');
        return entryResult(e.serializeNQuads(nq), 'serialize').nquads;
      }
    }

    const { files, flags } = docsToCliFiles(docs);
    const mode = outFormat === 'nquads' ? '--dump-nq' : '--dump';
    const res = await run([mode, ...flags], files);
    if (res.exitCode !== 0) throw engineError('serialize failed', res);
    return res.stdout;
  }

  /**
   * RDFC-1.0 canonicalization: canonical blank-node labels + sorted
   * canonical N-Quads.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<string>}
   */
  async function canonicalize(data, options) {
    const docs = toDocs(data, options);

    const e = await entry();
    if (e) {
      let nq = '';
      for (const d of docs) {
        if (d.ext === 'nq') { nq += d.content; continue; }
        const r = entryResult(
          e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
          'canonicalize(parse)');
        nq += r.nquads;
      }
      return entryResult(e.canonicalizeToNQuads(nq), 'canonicalize').nquads;
    }

    const { files, flags } = docsToCliFiles(docs);
    const res = await run(['--canonicalize', ...flags], files);
    if (res.exitCode !== 0) {
      if (/unknown option/.test(res.stderr || '')) {
        throw new Error(
          'canonicalize: this engine bundle predates the --canonicalize ' +
          'flag — pending npm-entry build (rebuild via ' +
          'formal/fstar/build-ocaml.sh js + npm).');
      }
      throw engineError('canonicalize failed', res);
    }
    return res.stdout;
  }

  /**
   * Feature probe, for tests and downstream capability checks.
   * @returns {Promise<{entry: boolean, construct: boolean,
   *   update: boolean, canonicalize: boolean}>}
   */
  let capsCache = null;
  async function capabilities() {
    if (capsCache) return capsCache;
    capsCache = capabilitiesUncached();
    return capsCache;
  }

  async function capabilitiesUncached() {
    const e = await entry();
    if (e) {
      return { entry: true, construct: true, update: true, canonicalize: true };
    }
    // Probe --canonicalize support on the CLI bundle with a 1-quad doc.
    let canon = false;
    try {
      const res = await run(
        ['--canonicalize', '-d', '/static/cap.nq'],
        [{ name: '/static/cap.nq',
           content: '<http://x/s> <http://x/p> "o" .\n' }]);
      canon = res.exitCode === 0;
    } catch (_) { canon = false; }
    return { entry: false, construct: false, update: false, canonicalize: canon };
  }

  return {
    parse,
    query,
    update,
    serialize,
    canonicalize,
    capabilities,
    Dataset,
    dataFactory,
  };
}

module.exports = { buildApi, sniffQueryForm, bindingsFromSrj };
