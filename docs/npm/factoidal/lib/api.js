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
  jsonld:    'jsonld',
  'json-ld': 'jsonld',
  // RDF 1.2 opt-in: these select the engine's Mode_12 parsers (triple
  // terms <<( s p o )>>, ~ reifiers, {| |} annotations, VERSION,
  // directional literals "x"@lang--dir). Only reachable via the
  // npm-entry bundle (the entry ABI routes the *12 tag to
  // Parser_*.*_mode Mode_12); the plain names above stay Mode_11 so 1.1
  // output is byte-identical.
  turtle12:   'ttl12',
  ttl12:      'ttl12',
  ntriples12: 'nt12',
  nt12:       'nt12',
  nquads12:   'nq12',
  nq12:       'nq12',
  trig12:     'trig12',
};

// Canonical format tag for the npm-entry ABI. The plain tags are what
// RDF_Format.format_of_string accepts directly; the *12 tags are
// intercepted by entry_jsoo's parse_text_to_dataset (before
// format_of_string) to select Mode_12.
const DATA_FORMAT_TAG = {
  ttl: 'turtle', nt: 'ntriples', nq: 'nquads', trig: 'trig', rdf: 'rdfxml',
  jsonld: 'jsonld',
  ttl12: 'turtle12', nt12: 'ntriples12', nq12: 'nquads12', trig12: 'trig12',
};

const ENTAIL_VALUES = new Set(['none', 'RDFS', 'OWL-RL', 'x-rdfscore', 'x-rdfsplus']);

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

// Pack raw bytes into the one-char-per-byte string js_of_ocaml's fake
// filesystem (runCli's `files` argument) expects for BINARY content --
// the same convention browser.js's HDT/COTTAS example cells built by
// hand before queryHdt() existed (String.fromCharCode per byte).
// Distinct from bytesToHex below (the npm-entry ABI's string-only wire
// format for openCottas/toCottas): this is for the CLI's file-based
// backends (--data-hdt), which read from the CLI bundle's fake
// filesystem, not the ABI.
function bytesToLatin1(bytesLike, who) {
  if (typeof bytesLike === 'string') return bytesLike; // already packed
  let u8;
  if (bytesLike instanceof Uint8Array) u8 = bytesLike;
  else if (bytesLike instanceof ArrayBuffer) u8 = new Uint8Array(bytesLike);
  else {
    throw new TypeError(
      `${who}: expected a Uint8Array, Buffer, ArrayBuffer, or an already-packed string`);
  }
  let out = '';
  for (let i = 0; i < u8.length; i += 0x4000) {
    out += String.fromCharCode.apply(null, u8.subarray(i, Math.min(u8.length, i + 0x4000)));
  }
  return out;
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

  // ---------------------------------------------------------------
  // SPARQL 1.1 §17.6 extension functions — issue #463.
  // https://github.com/danbri/factoidal/issues/463
  //
  // Comunica-style: the caller registers (possibly async) JS functions
  // keyed by absolute IRI; a query using an unregistered IRI gets the
  // spec-required error (in expression position: the row's value
  // errors — unbound in SELECT/BIND, row dropped in FILTER).
  //
  // The F*-extracted evaluator is synchronous, so async functions are
  // bridged with a bounded re-evaluation trampoline: each engine call
  // reaches extBridge synchronously; a cache miss on an async function
  // records the promise, returns a pending marker (an engine-side
  // error in THAT pass), and after the pass every pending promise is
  // awaited into the cache and the query re-runs. The per-(iri, args)
  // memoisation is also what honors the F* purity assumption on the
  // extension_function_call hook — within one evaluation every call
  // with the same arguments sees one stable answer.
  //
  // The user function receives an array of SRJ-style term objects
  // ({type:'uri'|'literal'|'bnode', value, datatype?, 'xml:lang'?};
  // {type:'error'} for an errored argument) and returns a term object,
  // a JS primitive (boolean / number / string), a Promise of either,
  // or null/undefined (= error). Thrown errors and rejections map to
  // the §17.6 error too.
  // ---------------------------------------------------------------
  const EXT_PENDING_MARKER = '__FACTOIDAL_EXT_PENDING__';
  const EXT_MAX_ROUNDS = 25;
  const extFunctions = new Map();    // iri -> user fn
  const extInstalled = new Set();    // iris registered into the ABI
  let extCache = new Map();          // key -> normalized result (or null)
  let extPending = [];               // [{key, promise}] for this pass

  function extBridge(iriJs, argsJsonJs) {
    // Called SYNCHRONOUSLY from inside the engine.
    const iri = String(iriJs);
    const argsJson = String(argsJsonJs);
    const key = iri + ' ' + argsJson;
    if (extCache.has(key)) return extCache.get(key);
    const fn = extFunctions.get(iri);
    if (!fn) return null;
    let out;
    try {
      out = fn(JSON.parse(argsJson));
    } catch (_e) {
      extCache.set(key, null);
      return null;
    }
    if (out && typeof out.then === 'function') {
      extPending.push({ key, promise: out });
      return EXT_PENDING_MARKER;
    }
    out = out === undefined ? null : out;
    extCache.set(key, out);
    return out;
  }

  async function extEnsureInstalled(what) {
    const e = await entry();
    if (!e) return null;
    if (typeof e.registerExtensionFunction !== 'function') {
      throw new Error(
        `${what}: this npm-entry bundle predates extension functions ` +
        '(issue #463) — rebuild build-ocaml.sh js + npm.');
    }
    for (const iri of extFunctions.keys()) {
      if (!extInstalled.has(iri)) {
        entryResult(e.registerExtensionFunction(iri, extBridge),
          'registerExtensionFunction');
        extInstalled.add(iri);
      }
    }
    return e;
  }

  /**
   * Register a custom SPARQL extension function (SPARQL 1.1 §17.6).
   * @param {string} iri absolute IRI the function is invoked by
   * @param {(args: object[]) => any} fn sync or async; see the block
   *   comment above for the argument/return contract
   */
  async function registerExtensionFunction(iri, fn) {
    if (typeof iri !== 'string' || !/^[A-Za-z][A-Za-z0-9+.-]*:/.test(iri)) {
      throw new TypeError(
        'registerExtensionFunction: iri must be an absolute IRI string');
    }
    if (typeof fn !== 'function') {
      throw new TypeError('registerExtensionFunction: fn must be a function');
    }
    extFunctions.set(iri, fn);
    await extEnsureInstalled('registerExtensionFunction');
  }

  /** Remove one registered extension function. */
  async function unregisterExtensionFunction(iri) {
    extFunctions.delete(iri);
    const e = await entry();
    if (e && typeof e.unregisterExtensionFunction === 'function'
        && extInstalled.has(iri)) {
      entryResult(e.unregisterExtensionFunction(iri),
        'unregisterExtensionFunction');
      extInstalled.delete(iri);
    }
  }

  /** Remove every registered extension function. */
  async function clearExtensionFunctions() {
    extFunctions.clear();
    const e = await entry();
    if (e && typeof e.clearExtensionFunctions === 'function') {
      entryResult(e.clearExtensionFunctions(), 'clearExtensionFunctions');
    }
    extInstalled.clear();
  }

  /**
   * Bind a SPARQL SERVICE endpoint IRI to a local graph snapshot, so
   * SERVICE <iri> { ... } (and LATERAL { SERVICE ... }) queries
   * resolve against it in-process — the same registry the W3C
   * federated-query suite uses (qt:serviceData). `data` is a Dataset,
   * a raw RDF string (options.format, default turtle), or an array of
   * those. The snapshot is the payload's default graph.
   */
  async function registerServiceEndpoint(iri, data, options) {
    if (typeof iri !== 'string' || !/^[A-Za-z][A-Za-z0-9+.-]*:/.test(iri)) {
      throw new TypeError(
        'registerServiceEndpoint: iri must be an absolute IRI string');
    }
    const e = await entry();
    if (!e || typeof e.registerServiceEndpoint !== 'function') {
      throw new Error(
        'registerServiceEndpoint: this npm-entry bundle predates SERVICE ' +
        'endpoint registration — rebuild build-ocaml.sh js + npm.');
    }
    const docs = toDocs(data, options);
    const nq = docsToEntryNQuads(e, docs, 'registerServiceEndpoint');
    return entryResult(e.registerServiceEndpoint(iri, nq),
      'registerServiceEndpoint');
  }

  /** Remove every registered SERVICE endpoint snapshot. */
  async function clearServiceEndpoints() {
    const e = await entry();
    if (e && typeof e.clearServiceEndpoints === 'function') {
      entryResult(e.clearServiceEndpoints(), 'clearServiceEndpoints');
    }
  }

  // Run one synchronous engine pass, re-running until no NEW async
  // extension results are pending. With no registered functions this
  // is exactly one pass with zero overhead beyond the length check.
  async function withExtensionRounds(runOnce) {
    extCache = new Map(); // per-evaluation memo (purity contract)
    for (let round = 0; ; round++) {
      extPending = [];
      const result = runOnce();
      if (extPending.length === 0) return result;
      if (round >= EXT_MAX_ROUNDS) {
        throw new Error(
          'extension functions: async resolution did not converge ' +
          `within ${EXT_MAX_ROUNDS} evaluation rounds`);
      }
      const pend = extPending;
      extPending = [];
      await Promise.all(pend.map(async ({ key, promise }) => {
        try {
          const v = await promise;
          extCache.set(key, v === undefined ? null : v);
        } catch (_e) {
          extCache.set(key, null);
        }
      }));
    }
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

  // Normalize toDocs() output into one concatenated N-Quads "dataset
  // handle" string via the entry ABI -- the same per-document
  // parseToDatasetJson-then-concatenate shape query()/update()/
  // canonicalize() each already inline. Needs the entry bundle (the
  // caller must have already checked `e` is non-null); factored out
  // here for the SHACL/ShEx/OWL-closure/RML wrappers below, which all
  // hand the engine a dataset-handle N-Quads string rather than raw
  // Turtle (consistent with every other entry ABI call).
  function docsToEntryNQuads(e, docs, what) {
    let nq = '';
    for (const d of docs) {
      if (d.ext === 'nq') { nq += d.content; continue; }
      const r = entryResult(
        e.parseToDatasetJson(d.content, DATA_FORMAT_TAG[d.ext], ''),
        `${what}(parse)`);
      nq += r.nquads;
    }
    return nq;
  }

  // A ShEx focus/shape-label argument is either a raw string (an IRI,
  // or "_:label" for a blank node -- the entry ABI's own convention)
  // or an RDF/JS term (NamedNode/BlankNode); accepting both lets a
  // caller pass a term straight out of a query() binding.
  function shexTermToString(t, who) {
    if (typeof t === 'string') return t;
    if (t && typeof t.termType === 'string') {
      if (t.termType === 'BlankNode') return `_:${t.value}`;
      if (t.termType === 'NamedNode') return t.value;
      throw new TypeError(`${who}: expected an IRI or blank node term`);
    }
    throw new TypeError(`${who}: expected a string or an RDF/JS term`);
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
   * @param {{format?: string, entail?: 'none'|'RDFS'|'OWL-RL'|'x-rdfscore'|'x-rdfsplus'}} [options]
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
    // x-ikl-* is NOT IMPLEMENTED. It is not withheld by policy.
    //
    // CORRECTION 2026-08-26: this comment previously cited the owner's
    // direction-B ruling (danbri/factoidal#618) as the reason. That
    // ruling was about the IKL-to-RDF projection, not this regime
    // family, and citing it here misstated a decision the owner did
    // not make. The family is the OWNER'S design
    // (danbri/factoidal#581); its Lean dispatch was deleted on
    // 2026-08-26 as collateral of the projection purge
    // (danbri/factoidal#626), not as its target. The semantics
    // survived -- Unified/ClBridge.lean's asserted_merge_sound is the
    // regime's soundness statement -- so restoring it is a dispatch
    // branch, not a redesign. Checked explicitly (not just left out of
    // ENTAIL_VALUES below) so a future ENTAIL_VALUES edit can't
    // reopen this without deliberately removing this check too; see
    // test/select.test.js's regression test.
    if (/^x-ikl/i.test(entail)) {
      throw new TypeError(
        `query: entail '${entail}' is not implemented. The x-ikl-* ` +
        "entailment regimes are the owner's design " +
        "(danbri/factoidal#581); the Lean engine's dispatch for them " +
        'was deleted on 2026-08-26 as collateral of the IKL-to-RDF ' +
        'projection purge (danbri/factoidal#626). This is not a ' +
        'policy exclusion.');
    }
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
      // SPARQL 1.2 opt-in: {sparql12:true} or {version:'1.2'} routes to
      // the entry's queryDataset12 (tokenize_12 parser: triple-term
      // patterns, TRIPLE/isTRIPLE/SUBJECT/PREDICATE/OBJECT, VERSION,
      // lang-dir builtins). Default stays SPARQL 1.1, byte-identical.
      const sparql12 = opts.sparql12 === true || String(opts.version || '') === '1.2';
      if (sparql12 && typeof e.queryDataset12 !== 'function') {
        throw new Error(
          'SPARQL 1.2 requested but this npm-entry bundle predates ' +
          'queryDataset12 — rebuild build-ocaml.sh js + npm.');
      }
      const r = await withExtensionRounds(() => entryResult(
        (sparql12 ? e.queryDataset12 : e.queryDataset)(nq, sparql), 'query'));
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
   * Run a SPARQL 1.1 query against a read-only HDT (Header-Dictionary-
   * Triples) artifact's raw bytes -- factoidal_cli.ml's `--data-hdt`
   * backend (HDT.Triples.fst and the parser modules around it), driven
   * through the same CLI bundle every other function in this file
   * uses. No npm-entry bundle needed -- this is a CLI-only capability.
   * Default graph only, SELECT/ASK only (no CONSTRUCT, no named graphs
   * -- see factoidal_cli.ml's --data-hdt help text).
   * @param {Uint8Array|ArrayBuffer|Buffer|string} hdtBytes whole .hdt
   *   file contents (a string is assumed already packed one-char-per-
   *   byte, the fake-filesystem convention runCli's `files` expects)
   * @param {string} sparql a SELECT or ASK query
   * @returns {Promise<Array<Map<string, object>>|boolean>}
   */
  async function queryHdt(hdtBytes, sparql) {
    if (typeof sparql !== 'string') {
      throw new TypeError('queryHdt: sparql must be a string');
    }
    const form = sniffQueryForm(sparql);
    if (form === 'construct' || form === 'describe') {
      throw new TypeError(
        `queryHdt: ${form.toUpperCase()} is not supported over --data-hdt (SELECT/ASK only)`);
    }
    const content = bytesToLatin1(hdtBytes, 'queryHdt');
    const name = `/static/hdt${parseCounter++}.hdt`;
    const res = await run(['--data-hdt', name, '-e', sparql, '-o', 'json'], [{ name, content }]);
    if (res.exitCode !== 0) throw engineError('queryHdt failed', res);
    const srj = jsonFromStdout(res.stdout, 'queryHdt');
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
    const opts = options || {};
    const sparql12 = opts.sparql12 === true || String(opts.version || '') === '1.2';
    if (sparql12 && typeof e.updateDataset12 !== 'function') {
      throw new Error(
        'SPARQL 1.2 UPDATE requested but this npm-entry bundle predates ' +
        'updateDataset12 — rebuild build-ocaml.sh js + npm.');
    }
    const r = entryResult(
      (sparql12 ? e.updateDataset12 : e.updateDataset)(nq, updateText), 'update');
    return Dataset.fromNQuads(r.nquads, {
      blankNodePrefix: freshBnodePrefix(),
    });
  }

  /**
   * Serialize a dataset (engine-produced bytes, sorted N-Quads order).
   * @param {Dataset|string|Array} data
   * @param {{format?: 'nquads'|'ntriples'|'turtle', inputFormat?: string}} [options]
   * @returns {Promise<string>}
   *   'turtle' (prefix-compacted, subject-grouped — entry_jsoo.ml's
   *   serializeTurtle -> RDF_Turtle_Serialize.turtle_of_graph_auto)
   *   needs the npm-entry bundle and flattens every named graph into
   *   the default graph (Turtle has no named-graph notion); use
   *   'nquads' when graph names must survive.
   */
  async function serialize(data, options) {
    const opts = options || {};
    const rawOut = String(opts.format || 'nquads').toLowerCase();
    const outFormat = rawOut === 'ttl' ? 'turtle' : rawOut;
    if (outFormat !== 'nquads' && outFormat !== 'ntriples' && outFormat !== 'turtle') {
      throw new TypeError(
        "serialize: format must be 'nquads', 'ntriples', or 'turtle'");
    }
    const docs = toDocs(data, { format: opts.inputFormat });

    if (outFormat === 'turtle') {
      const e = await entry();
      if (!e) throw pendingError('Turtle serialization');
      requireEntryFn(e, 'serializeTurtle', 'Turtle serialization');
      const nq = docsToEntryNQuads(e, docs, 'serialize(turtle)');
      return entryResult(e.serializeTurtle(nq), 'serialize').turtle;
    }

    if (outFormat === 'nquads') {
      const e = await entry();
      if (e) {
        // Non-N-Quads documents normalize through parseToDatasetJson
        // (docsToEntryNQuads), same as the turtle branch above — so
        // entry-only drivers (e.g. l4-core.js) serve this path too.
        const nq = docs.every((d) => d.ext === 'nq')
          ? docs.map((d) => d.content).join('')
          : docsToEntryNQuads(e, docs, 'serialize(nquads)');
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
   * Enumerate the named graphs of an already-parsed Dataset.
   *
   * Graphs-api design (docs/designissues/2026-07-05-graphs-api-design.md
   * section 1.3): DatasetCore.match(null,null,null,graphNode) already
   * gives per-graph read access, but match() alone cannot answer "what
   * graph names exist" -- this is exactly that enumeration, and only
   * that: it walks quads already produced by the F*-verified parser, so
   * it needs no engine round-trip (no new RDF/SPARQL semantics, rule
   * #11 stays satisfied trivially).
   *
   * @param {Dataset} dataset
   * @returns {Array<[iri: string, graph: Dataset]>}
   *   default graph excluded, first-seen order.
   */
  function graphs(dataset) {
    if (!(dataset instanceof Dataset)) {
      throw new TypeError('graphs: expected a Dataset');
    }
    const seen = new Map(); // iri -> graph term (first occurrence)
    for (const q of dataset) {
      const g = q.graph;
      if (!g || g.termType === 'DefaultGraph') continue;
      if (!seen.has(g.value)) seen.set(g.value, g);
    }
    const out = [];
    for (const [iri, gTerm] of seen) {
      out.push([iri, dataset.match(null, null, null, gTerm)]);
    }
    return out;
  }

  /**
   * RDFC-1.0 canonical hash of a single graph -- the graph-scoped
   * sibling of canonicalize(), gated via capabilities() the same way
   * (docs/designissues/2026-07-05-graphs-api-design.md section 1.3).
   * Accepts a whole dataset or (more usually) one entry of graphs()'s
   * output; either way, every quad's graph component is dropped before
   * canonicalizing, matching RDF.Canonical.fst's
   * canonicalize_named_graph, which projects the named graph into
   * `{ ds_default = g; ds_named = [] }` before reusing
   * canonicalize_to_nquads unmodified.
   *
   * @param {Dataset} datasetOrGraph
   * @returns {Promise<string>} canonical N-Quads text for that graph alone.
   */
  async function canonicalHash(datasetOrGraph) {
    if (!(datasetOrGraph instanceof Dataset)) {
      throw new TypeError(
        'canonicalHash: expected a Dataset (e.g. one entry of graphs())');
    }
    const asDefaultGraph = new Dataset(
      datasetOrGraph.toArray().map(
        (q) => dataFactory.quad(q.subject, q.predicate, q.object)));
    return canonicalize(asDefaultGraph.toNQuads(), { format: 'nquads' });
  }

  // Some loaded entry bundles predate one of these exports (e.g. an
  // older/stale wasm-target build) -- `e` itself is truthy (loadEntry
  // succeeded), but `e[fnName]` is undefined, which would otherwise
  // surface as a confusing "e.shaclValidate is not a function". Fail
  // with the same pendingError() shape callers already expect from a
  // missing bundle.
  function requireEntryFn(e, fnName, what) {
    if (typeof e[fnName] !== 'function') throw pendingError(what);
  }

  /**
   * SHACL Core validation. Needs the npm-entry bundle (SHACL_Validation
   * is only linked into the entry/CLI bundles, not exposed on the
   * argv-driven CLI surface today).
   * @param {Dataset|string|Array} data
   * @param {Dataset|string|Array} shapes
   * @param {{format?: string}} [options] applies to both data and shapes
   * @returns {Promise<{conforms: boolean, report: Dataset}>}
   *   report is SHACL_Validation.validation_report_to_graph's graph
   *   (sh:conforms + one sh:ValidationResult per violation).
   */
  async function shaclValidate(data, shapes, options) {
    const e = await entry();
    if (!e) throw pendingError('SHACL validation');
    requireEntryFn(e, 'shaclValidate', 'SHACL validation');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'shaclValidate(data)');
    const shapesNq = docsToEntryNQuads(e, toDocs(shapes, options), 'shaclValidate(shapes)');
    const r = entryResult(e.shaclValidate(dataNq, shapesNq), 'shaclValidate');
    return {
      conforms: r.conforms,
      report: Dataset.fromNQuads(r.reportNquads, {
        blankNodePrefix: freshBnodePrefix(),
      }),
    };
  }

  /**
   * ShEx (Shape Expressions) validation of one focus node against one
   * shape. Needs the npm-entry bundle.
   * @param {Dataset|string|Array} data
   * @param {string} schemaJson the schema, as text -- either ShExJ (a
   *   JSON Schema document) or ShExC (the compact human-readable
   *   syntax; formal/fstar/Parser.ShExC.fst). Dispatch rule: the schema
   *   text's first non-whitespace character decides the format -- '{'
   *   means ShExJ, anything else is parsed as ShExC. No separate flag
   *   or file-extension hint is needed; a schema whose ShExC text
   *   happens to start with whitespace then '{' would misdetect, but no
   *   valid ShExC document starts that way (ShExC always opens with a
   *   directive keyword, a shape label, or START).
   * @param {string|{termType,value}} focus an IRI, "_:label", or an
   *   RDF/JS NamedNode/BlankNode term
   * @param {string|{termType,value}|null} [shape] a shape label (same
   *   shapes as focus); omit/null to validate against the schema's own `start`
   * @param {{format?: string}} [options]
   * @returns {Promise<boolean|null>} null means "deferred" -- outside
   *   this engine's decidable ShEx fragment, never a guessed answer
   *   (see formal/fstar/ShEx.Validation.fst's file header).
   */
  async function shexValidate(data, schemaJson, focus, shape, options) {
    const e = await entry();
    if (!e) throw pendingError('ShEx validation');
    requireEntryFn(e, 'shexValidate', 'ShEx validation');
    if (typeof schemaJson !== 'string') {
      throw new TypeError('shexValidate: schemaJson must be a string');
    }
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'shexValidate(data)');
    const focusStr = shexTermToString(focus, 'shexValidate(focus)');
    const shapeStr = shape == null ? '' : shexTermToString(shape, 'shexValidate(shape)');
    const r = entryResult(
      e.shexValidate(dataNq, schemaJson, focusStr, shapeStr), 'shexValidate');
    return r.verdict;
  }

  const OWL_CLOSURE_MODES = { rdfs: 'RDFS', 'owl-rl': 'OWL-RL', owlrl: 'OWL-RL', owl_rl: 'OWL-RL' };

  function normalizeClosureMode(mode) {
    const canonical = OWL_CLOSURE_MODES[String(mode || '').toLowerCase()];
    if (!canonical) {
      throw new TypeError(
        `owlClosure: mode must be 'RDFS' or 'OWL-RL' (got '${mode}')`);
    }
    return canonical;
  }

  /**
   * RDFS or OWL-RL entailment closure, materialized as a new Dataset
   * (input triples + derived triples). Needs the npm-entry bundle.
   * Scope cut: only the default graph is closed over (same cut
   * fn.js's entail() documents for its own CLI-path implementation).
   * @param {Dataset|string|Array} data
   * @param {'RDFS'|'OWL-RL'} mode
   * @param {{format?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function owlClosure(data, mode, options) {
    const e = await entry();
    if (!e) throw pendingError('OWL/RDFS closure');
    requireEntryFn(e, 'owlClosure', 'OWL/RDFS closure');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'owlClosure(data)');
    const r = entryResult(
      e.owlClosure(dataNq, normalizeClosureMode(mode)), 'owlClosure');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * The CERTIFIED core-RDFS closure (RDF.Entailment.RDFS.
   * RhoDFClosure.fst's `rho_df_closure`): rdfs2/3/5/7/9/11 only, with
   * the machine-checked decides-iff (docs/theorem-registry.md).
   * "corerdfs" is this project's API name for the fragment the
   * literature calls ρdf — subPropertyOf/subClassOf/type/domain/range,
   * per Muñoz, Pérez & Gutierrez, "Simple and Efficient Minimal
   * RDFS", J. Web Semantics 7(3), 2009. `rhoDfClosure` remains as an
   * alias so code can be grepped against the theorem registry.
   * Returns the raw certified result, not a Dataset: the N-Triples
   * text is the object the theorems talk about.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{ok: boolean, ntriples: string}>}
   */
  async function coreRdfsClosure(data, options) {
    const e = await entry();
    if (!e) throw pendingError('certified core-RDFS closure');
    requireEntryFn(e, 'rhoDfClosure', 'certified core-RDFS closure');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'coreRdfsClosure(data)');
    return entryResult(e.rhoDfClosure(dataNq), 'coreRdfsClosure');
  }
  /** Literature-name alias for coreRdfsClosure (ρdf; see above). */
  const rhoDfClosure = coreRdfsClosure;

  /**
   * Decidable core-RDFS fragment check (`is_rho_df_frag`, tied by an
   * F* lemma to the prop the regime theorems quantify over): does the
   * certified path's guarantee apply to this data? Naming: see
   * coreRdfsClosure above. `rhoDfFragmentCheck` remains as an alias.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{ok: boolean, fragment: boolean}>}
   */
  async function coreRdfsCheck(data, options) {
    const e = await entry();
    if (!e) throw pendingError('core-RDFS fragment check');
    requireEntryFn(e, 'rhoDfFragmentCheck', 'core-RDFS fragment check');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'coreRdfsCheck(data)');
    return entryResult(e.rhoDfFragmentCheck(dataNq), 'coreRdfsCheck');
  }
  /** Literature-name alias for coreRdfsCheck (ρdf; see above). */
  const rhoDfFragmentCheck = coreRdfsCheck;

  /**
   * RDFS-Plus closure (RDF.Entailment.RDFSPlus.fst's
   * `rdfs_plus_closure`): the full RDFS step plus the practical OWL
   * subset -- owl:sameAs (symmetry/transitivity/substitution),
   * owl:inverseOf, Symmetric/Transitive/Functional/
   * InverseFunctionalProperty, equivalentClass/Property. The tier the
   * literature calls RDFS-Plus (Allemang & Hendler, "Semantic Web for
   * the Working Ontologist", 2008) or RDFS++ (AllegroGraph). Claim
   * level, weaker than coreRdfsClosure's and stated exactly: every OWL
   * row runs under a PROVED licensing + truth lemma (per-rule
   * certificates in the theorem registry); no chain-level completeness
   * is claimed -- owl:sameAs equality breaks the Herbrand argument the
   * corerdfs completeness theorem uses.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{ok: boolean, ntriples: string, rounds: number}>}
   */
  async function rdfsPlusClosure(data, options) {
    const e = await entry();
    if (!e) throw pendingError('RDFS-Plus closure');
    requireEntryFn(e, 'rdfsPlusClosure', 'RDFS-Plus closure');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'rdfsPlusClosure(data)');
    return entryResult(e.rdfsPlusClosure(dataNq), 'rdfsPlusClosure');
  }

  /**
   * OWL tableau materialisation (formal/fstar/Tableau.fst's
   * `tableau_materialise`): add `i rdf:type <ClassExpression>` for
   * every individual the model-construction reasoner can prove is a
   * member of an OWL class expression (someValuesFrom / hasValue /
   * unionOf / intersectionOf, and the named class an equivalentClass
   * restriction defines). This is the same F* function the SPARQL 1.1
   * entailment-regime suite runs under the DL regime. Needs the
   * npm-entry bundle. Default graph only (same scope cut as owlClosure).
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{dataset: Dataset, addedCount: number}>}
   *   dataset is input + tableau-derived triples; addedCount is how many
   *   the tableau added.
   */
  async function tableauMaterialise(data, options) {
    const e = await entry();
    if (!e) throw pendingError('OWL tableau materialisation');
    requireEntryFn(e, 'tableauMaterialise', 'OWL tableau materialisation');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'tableauMaterialise(data)');
    const r = entryResult(e.tableauMaterialise(dataNq), 'tableauMaterialise');
    return {
      dataset: Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() }),
      addedCount: r.addedCount,
    };
  }

  /**
   * OWL DL inconsistency verdict. Replays bin/owl-runner's DL pipeline
   * (OWL-RL closure -> Tableau.tableau_materialise -> OWL-RL closure ->
   * is_inconsistent). `rlAlone` is the plain OWL-RL verdict on the same
   * input, so a caller can see the DL>=RL cases the tableau adds: a
   * disjointness clash reached only after the tableau materialises a
   * restriction membership the Datalog closure never derives. Needs the
   * npm-entry bundle. Default graph only.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<{inconsistent: boolean, rlAlone: boolean}>}
   */
  async function tableauDlInconsistent(data, options) {
    const e = await entry();
    if (!e) throw pendingError('OWL tableau DL inconsistency check');
    requireEntryFn(e, 'tableauDlInconsistent', 'OWL tableau DL inconsistency check');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'tableauDlInconsistent(data)');
    const r = entryResult(e.tableauDlInconsistent(dataNq), 'tableauDlInconsistent');
    return { inconsistent: r.inconsistent, rlAlone: r.rlAlone };
  }

  /**
   * OWL DL consistency verdict via the verified clash-detecting tableau
   * (formal/fstar/Tableau.Refute.fst's `tableau_consistent` over the
   * OWL-RL closure -- the same pure verified chain bin/owl-runner runs
   * under `--regime dl`, minus its native-only z3 counting oracle, which
   * the JS bundle cannot spawn). Needs the npm-entry bundle. Default
   * graph only (same scope cut as tableauDlInconsistent).
   *
   * Three-valued and honest: `consistent` is `false` (a clash on every
   * tableau branch), `true` (a model was constructed with no clash), or
   * `null` -- the refuter ran out of budget before deciding, with
   * `reason` naming the fuel cap. `null` is never collapsed to `false`.
   *
   * @param {Dataset|string|Array} data the ontology + ABox graph
   * @param {{format?: string, fuel?: number|string}} [options] format
   *   parses `data` (default 'turtle'); fuel overrides the refutation
   *   budget (default 20000).
   * @returns {Promise<{consistent: boolean|null, reason?: string}>}
   */
  async function owlIsConsistent(data, options) {
    const e = await entry();
    if (!e) throw pendingError('OWL DL consistency check');
    requireEntryFn(e, 'owlIsConsistent', 'OWL DL consistency check');
    const opts = options || {};
    const dataNq = docsToEntryNQuads(e, toDocs(data, opts), 'owlIsConsistent(data)');
    const optsJson = JSON.stringify(opts.fuel != null ? { fuel: String(opts.fuel) } : {});
    const r = entryResult(e.owlIsConsistent(dataNq, optsJson), 'owlIsConsistent');
    return r.reason === undefined
      ? { consistent: r.consistent }
      : { consistent: r.consistent, reason: r.reason };
  }

  /**
   * OWL entailment check: does `premise` entail `conclusion`? Two
   * verified paths, mirroring bin/owl-runner's PositiveEntailment
   * dispatch: `via: "closure"` when every conclusion triple is in the
   * OWL-RL closure of the premise; `via: "refutation"` when the negated
   * conclusion (Tableau.Refute's `negation_goals`) is refuted on every
   * goal by the clash-detecting tableau. Needs the npm-entry bundle.
   * Default graph only. Verified-only chain (no z3).
   *
   * Three-valued: `entailed` is `true`, `false`, or `null` (a refutation
   * goal exhausted its fuel budget -- indeterminate, never a silent
   * `false`; `reason` names the cap).
   *
   * @param {Dataset|string|Array} premise
   * @param {Dataset|string|Array} conclusion
   * @param {{format?: string, fuel?: number|string}} [options] format
   *   parses both graphs (default 'turtle'); fuel overrides the
   *   refutation budget (default 20000).
   * @returns {Promise<{entailed: boolean|null, via: 'closure'|'refutation', reason?: string}>}
   */
  async function owlEntails(premise, conclusion, options) {
    const e = await entry();
    if (!e) throw pendingError('OWL entailment check');
    requireEntryFn(e, 'owlEntails', 'OWL entailment check');
    const opts = options || {};
    const premiseNq = docsToEntryNQuads(e, toDocs(premise, opts), 'owlEntails(premise)');
    const conclusionNq = docsToEntryNQuads(e, toDocs(conclusion, opts), 'owlEntails(conclusion)');
    const optsJson = JSON.stringify(opts.fuel != null ? { fuel: String(opts.fuel) } : {});
    const r = entryResult(e.owlEntails(premiseNq, conclusionNq, optsJson), 'owlEntails');
    return r.reason === undefined
      ? { entailed: r.entailed, via: r.via }
      : { entailed: r.entailed, via: r.via, reason: r.reason };
  }

  /**
   * Evaluate an RML mapping graph against one logical source's raw
   * data, returning the generated triples as a Dataset. Needs the
   * npm-entry bundle. Scope cut (documented, not silent): every
   * triples map in `mapping` reads the SAME `sourceData` -- joins
   * across two DIFFERENT logical sources are not reachable through
   * this one-source entry point (see bin/rml-runner/rml_runner.ml for
   * the full multi-source join driver).
   * @param {Dataset|string|Array} mapping the RML mapping graph (Turtle by default)
   * @param {string} sourceData raw JSON or CSV text (not RDF)
   * @param {'json'|'csv'} sourceKind
   * @param {{format?: string}} [options] applies to `mapping`
   * @returns {Promise<Dataset>}
   */
  async function rmlMap(mapping, sourceData, sourceKind, options) {
    const e = await entry();
    if (!e) throw pendingError('RML mapping evaluation');
    requireEntryFn(e, 'rmlMap', 'RML mapping evaluation');
    if (typeof sourceData !== 'string') {
      throw new TypeError('rmlMap: sourceData must be a string');
    }
    const kind = String(sourceKind || '').toLowerCase();
    if (kind !== 'json' && kind !== 'csv') {
      throw new TypeError("rmlMap: sourceKind must be 'json' or 'csv'");
    }
    const mappingNq = docsToEntryNQuads(e, toDocs(mapping, options), 'rmlMap(mapping)');
    const r = entryResult(e.rmlMap(mappingNq, sourceData, kind), 'rmlMap');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * CSVW csv2rdf conversion (w3.org/TR/csv2rdf): convert tabular data
   * plus an optional CSVW metadata document into a Dataset. Needs the
   * npm-entry bundle. Scope cut (documented, not silent -- mirrors
   * rmlMap's one-source cut): every table in a multi-table `tables`
   * group reads the SAME `csvText`. Datatype `format` facets,
   * list-valued (`separator`) cells, and full inherited-property
   * propagation are not yet implemented -- see
   * docs/designissues/2026-07-05-csvw-program-plan.md for measured
   * coverage.
   * @param {string} csvText raw RFC 4180 tabular data (not RDF)
   * @param {string} [metadataJson] CSVW metadata document (JSON text);
   *   '' / omitted infers the schema from the CSV's own header row
   * @param {{mode?: 'standard'|'minimal', base?: string, url?: string}}
   *   [options] mode defaults to 'standard' (full csvw:TableGroup/
   *   Table/Row wrapper); base is the resolution base IRI (default
   *   'file:///'); url is the tabular file's own URL used when the
   *   metadata carries none (default 'table.csv') -- cell predicates
   *   default to `<tableUrl>#<colName>`, so url shapes every emitted
   *   predicate IRI.
   * @returns {Promise<Dataset>}
   */
  async function csvwToRdf(csvText, metadataJson, options) {
    if (typeof csvText !== 'string') {
      throw new TypeError('csvwToRdf: csvText must be a string');
    }
    const meta = metadataJson == null ? '' : metadataJson;
    if (typeof meta !== 'string') {
      throw new TypeError('csvwToRdf: metadataJson must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('CSVW csv2rdf conversion');
    requireEntryFn(e, 'csvwToRdf', 'CSVW csv2rdf conversion');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.mode ? { mode: String(opts.mode).toLowerCase() } : {}),
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.url ? { url: opts.url } : {}),
    });
    const r = entryResult(e.csvwToRdf(csvText, meta, optionsJson), 'csvwToRdf');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * Parse a JSON-LD document into a Dataset, with JSON-LD-specific
   * options `parse()` has no room for. Needs the npm-entry bundle
   * (plain `parse(text, {format:'jsonld'})` also works now -- see
   * bin/npm-entry/entry_jsoo.ml's parseToDatasetJson JSON-LD fix --
   * this exists for callers that need rdfDirection/expandContext/
   * processingMode).
   * @param {string} jsonldText
   * @param {{base?: string, rdfDirection?: string, expandContext?: string,
   *   processingMode?: string}} [options]
   * @returns {Promise<Dataset>}
   */
  async function jsonldToRdf(jsonldText, options) {
    if (typeof jsonldText !== 'string') {
      throw new TypeError('jsonldToRdf: jsonldText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('jsonldToRdf');
    requireEntryFn(e, 'jsonldToRdf', 'jsonldToRdf');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.base ? { base: opts.base } : {}),
      ...(opts.rdfDirection ? { rdfDirection: opts.rdfDirection } : {}),
      ...(opts.expandContext ? { expandContext: opts.expandContext } : {}),
      ...(opts.processingMode ? { processingMode: opts.processingMode } : {}),
    });
    const r = entryResult(e.jsonldToRdf(jsonldText, optionsJson), 'jsonldToRdf');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * RIF Core forward-chaining saturation, materialized as a new
   * Dataset (input triples + derived triples, default graph only --
   * RIF Core has no named-graph notion). Needs the npm-entry bundle.
   * @param {Dataset|string|Array} data the premise graph
   * @param {string} rifRulesXml a RIF Core XML rule document
   * @param {{format?: string}} [options] applies to `data`
   * @returns {Promise<Dataset>}
   */
  async function rifEval(data, rifRulesXml, options) {
    const e = await entry();
    if (!e) throw pendingError('RIF Core evaluation');
    requireEntryFn(e, 'rifEval', 'RIF Core evaluation');
    if (typeof rifRulesXml !== 'string') {
      throw new TypeError('rifEval: rifRulesXml must be a string');
    }
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'rifEval(data)');
    const r = entryResult(e.rifEval(rifRulesXml, dataNq), 'rifEval');
    return Dataset.fromNQuads(r.saturatedNquads, {
      blankNodePrefix: freshBnodePrefix(),
    });
  }

  /**
   * Serialize an RDF dataset as an expanded-form JSON-LD document --
   * the reverse of jsonldToRdf (entry_jsoo.ml's jsonldFromRdf export ->
   * the verified JSONLD.FromRdf.from_rdf). Returns the parsed JSON-LD
   * value (an array of node objects). Needs the npm-entry bundle.
   * @param {Dataset|string|Array} data
   * @param {{useNativeTypes?:boolean,useRdfType?:boolean,format?:string}} [options]
   * @returns {Promise<any>} the JSON-LD document (JCS-canonical, parsed)
   */
  async function jsonldFromRdf(data, options) {
    const e = await entry();
    if (!e) throw pendingError('jsonldFromRdf');
    requireEntryFn(e, 'jsonldFromRdf', 'jsonldFromRdf');
    const dataNq = docsToEntryNQuads(e, toDocs(data, options), 'jsonldFromRdf(data)');
    const opts = options || {};
    const optionsJson = JSON.stringify({
      ...(opts.useNativeTypes ? { useNativeTypes: true } : {}),
      ...(opts.useRdfType ? { useRdfType: true } : {}),
    });
    const r = entryResult(e.jsonldFromRdf(dataNq, optionsJson), 'jsonldFromRdf');
    return JSON.parse(r.jsonld);
  }

  /**
   * did:key resolution (entry_jsoo.ml's didKeyResolve export -> the
   * verified DID_Key.did_key_document). Resolves a did:key:z6Mk...
   * (Ed25519) to its DID Document, returned as a Dataset. Needs the
   * npm-entry bundle.
   * @param {string} didString a did:key URI
   * @returns {Promise<Dataset>} the DID Document as RDF
   */
  async function didKeyResolve(didString) {
    if (typeof didString !== 'string') {
      throw new TypeError('didKeyResolve: didString must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('didKeyResolve');
    requireEntryFn(e, 'didKeyResolve', 'did:key resolution');
    const r = entryResult(e.didKeyResolve(didString), 'didKeyResolve');
    return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
  }

  /**
   * Test whether an XML document is well-formed (entry_jsoo.ml's
   * xmlWellformed export -> Parser_XML.parse_xml_document, the
   * accept/reject signal bin/xml-runner drives against W3C xmlconf).
   * The byte-oriented parser has no DOCTYPE/DTD production, so a
   * document containing a DOCTYPE reports false. Needs the npm-entry
   * bundle.
   * @param {string} xmlText
   * @returns {Promise<boolean>}
   */
  async function xmlWellformed(xmlText) {
    if (typeof xmlText !== 'string') {
      throw new TypeError('xmlWellformed: xmlText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('xmlWellformed');
    requireEntryFn(e, 'xmlWellformed', 'XML well-formedness');
    const r = entryResult(e.xmlWellformed(xmlText), 'xmlWellformed');
    return !!r.wellformed;
  }

  /**
   * Evaluate an XPath 1.0 expression over an XML document (entry_jsoo.ml's
   * xpathEval export -> XPath_Eval.eval_xpath_from_root). Returns the
   * result envelope: `resultType` ('nodeset'|'string'|'number'|'boolean')
   * plus, for a node-set, `count`/`stringValue`/`nodes`, else a scalar
   * `value`. Needs the npm-entry bundle.
   * @param {string} xmlText
   * @param {string} xpathExpr
   * @returns {Promise<object>}
   */
  async function xpathEval(xmlText, xpathExpr) {
    if (typeof xmlText !== 'string' || typeof xpathExpr !== 'string') {
      throw new TypeError('xpathEval: xmlText and xpathExpr must be strings');
    }
    const e = await entry();
    if (!e) throw pendingError('xpathEval');
    requireEntryFn(e, 'xpathEval', 'XPath evaluation');
    return entryResult(e.xpathEval(xmlText, xpathExpr), 'xpathEval');
  }

  /**
   * Parse Common Logic Interchange Format text (ISO/IEC 24707:2018),
   * with the IKL `that`-operator extension (entry_jsoo.ml's clParse
   * export -> L4Factoidal's CL/Clif.lean reader). Reads CLIF into a CL
   * syntax tree and reports its shape; it never produces RDF -- the
   * IKL-to-RDF projection that used to accompany it is deleted
   * (danbri/factoidal#626). Lean 4 only: formal/fstar has no CL/IKL parser, so this
   * function is absent from index.js/wasm.js -- see capabilities() /
   * factoidal/select's capability table.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, sentences: number, pureCL: boolean,
   *   normalized: string}>} `pureCL` is a DIALECT flag, not a validity
   *   or quality signal: true while the text stays inside ISO/IEC
   *   24707 Common Logic, false once it uses IKL's `that` operator.
   *   Both values are returned only for text that parsed; a CLIF text
   *   that fails to parse rejects instead (e.g. a bare `(that S)` used
   *   as a proposition rather than a term -- see the GUIDE).
   */
  async function clParse(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clParse: clifText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('clParse');
    requireEntryFn(e, 'clParse', 'Common Logic / IKL parse');
    return entryResult(e.clParse(clifText), 'clParse');
  }

  /**
   * Read Common Logic Interchange Format text and write it back out in
   * the canonical spacing of the CLIF writer (entry_jsoo.ml's
   * clSerialize export -> L4Factoidal's CL/Clif.lean reader/writer
   * pair). Lean 4 only: formal/fstar has no CL/IKL parser, so this
   * function is absent from index.js/wasm.js -- see capabilities() /
   * factoidal/select's capability table.
   *
   * `roundTripProved` is always `false`. The round-trip lemma
   * `clif_roundTrip` (`CL/ClifAdequacy.lean`) is an OPEN lemma: the
   * fragment boundary `marksLexable` is MEASURED, not proved. The
   * field is in the envelope, unmodified, so a caller does not have to
   * go and find that out.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, clif: string, sentences: number,
   *   roundTripProved: false}>}
   */
  async function clSerialize(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clSerialize: clifText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('clSerialize');
    requireEntryFn(e, 'clSerialize', 'Common Logic / IKL serialize');
    return entryResult(e.clSerialize(clifText), 'clSerialize');
  }

  /**
   * Alpha-normalise Common Logic Interchange Format text: the canonical
   * representative of each sentence's bound-variable-renaming
   * equivalence class (entry_jsoo.ml's clAlphaNorm export ->
   * L4Factoidal's `CL/Alpha.lean`, `Sentence.alphaNorm`). Bound names
   * become `v1`, `v2`, ... in traversal order, so two sentences that
   * differ only in bound-variable names produce byte-identical output
   * -- IKL GUIDE Appendix B condition (1): renaming a bound variable
   * does not change the proposition expressed. Lean 4 only: formal/fstar
   * has no CL/IKL parser, so this function is absent from
   * index.js/wasm.js -- see capabilities() / factoidal/select's
   * capability table.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, clif: string, sentences: number}>}
   */
  async function clAlphaNorm(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clAlphaNorm: clifText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('clAlphaNorm');
    requireEntryFn(e, 'clAlphaNorm', 'Common Logic / IKL alpha-normalise');
    return entryResult(e.clAlphaNorm(clifText), 'clAlphaNorm');
  }

  /**
   * Hayes's satisfiability-preserving reduction of IKL to Common Logic
   * (entry_jsoo.ml's clNormalize export -> L4Factoidal's
   * `CL/Normalize.lean`, `normalizeText`; danbri/factoidal#625), over a
   * whole text: one head text and one shared tail, with the
   * proposition-name counter running across the text. Lean 4 only:
   * formal/fstar has no CL/IKL parser, so this function is absent from
   * index.js/wasm.js -- see capabilities() / factoidal/select's
   * capability table.
   *
   * Two limits, both real, both in the answer, neither hidden:
   *  - `preserves: "satisfiability"` -- the reduction preserves
   *    satisfiability, NOT equivalence. It suits entailment and
   *    consistency testing; it is not a transformation to apply to
   *    data you intend to keep.
   *  - `noIntrusion` IS the proof hypothesis `CL.noIntrSs [] []`
   *    decides, not a paraphrase of it. The transformation runs either
   *    way; when `noIntrusion` is `false`, the output is still
   *    produced, but `tails_satisfiable` / `normalize_preserves` do
   *    not cover that case.
   * @param {string} clifText
   * @returns {Promise<{ok: boolean, head: string[], tail: string[],
   *   clif: string, sentences: number, thatCount: number,
   *   noIntrusion: boolean, preserves: 'satisfiability',
   *   provedUnder: string}>}
   */
  async function clNormalize(clifText) {
    if (typeof clifText !== 'string') {
      throw new TypeError('clNormalize: clifText must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('clNormalize');
    requireEntryFn(e, 'clNormalize', 'Common Logic / IKL normalize');
    return entryResult(e.clNormalize(clifText), 'clNormalize');
  }

  // clFiniteSat (entry_jsoo.ml's clFiniteSat -> L4Factoidal's
  // CL/FiniteSatTheorems.lean) is DEFERRED, not excluded, from this
  // typed layer (owner decision, 2026-08-26): it takes a caller-supplied
  // finite-interpretation JSON encoding (see Wasm/Ops/CL.lean's header
  // for the wire format) that has no user yet, and a typed wrapper here
  // would freeze that shape before anyone knows whether it is right. It
  // stays reachable through the raw dispatch ABI (`l4.call('clFiniteSat',
  // [interpJson, clifText])` / factoidal/select's `call('clFiniteSat',
  // ...)`), which needs no shape commitment on this layer.

  // -----------------------------------------------------------------
  // VC Data Integrity crypto (eddsa-rdfc-2022) — HACL* wasm backend.
  // entry_jsoo.ml's vc* exports realise VC_DataIntegrity's four crypto
  // assume vals via HACL*'s OWN official WebAssembly build. The wasm
  // backend MUST be initialised before the first primitive runs, or
  // the assume-val stub throws and `guarded` returns {ok:false} — a
  // verify NEVER silently succeeds uninitialised (#286, the
  // throw-on-uninit contract, which entryResult() preserves by
  // throwing on {ok:false}).
  //
  // Init story (Node js + wasm engines): these wrappers AUTO-AWAIT
  // initHacl() on the first VC call, via the optional driver.initCrypto
  // hook (idempotent + memoized) — a caller never has to remember the
  // init step. If the driver supplies no initCrypto hook (or init
  // rejects), the primitive's own honest {ok:false} error surfaces
  // rather than a false "valid". Browsers can't auto-init (the
  // hacl-wasm URL is page-specific) — browser.js documents explicit
  // init there. See skills/node-crypto-haclstar-vc-wasm-build.
  // -----------------------------------------------------------------

  let cryptoInitPromise;
  async function ensureCrypto() {
    if (typeof driver.initCrypto !== 'function') return;
    if (!cryptoInitPromise) {
      cryptoInitPromise = Promise.resolve()
        .then(() => driver.initCrypto())
        .catch((err) => { cryptoInitPromise = undefined; throw err; });
    }
    await cryptoInitPromise;
  }

  async function vcEntry(fnName, what) {
    const e = await entry();
    if (!e) throw pendingError(what);
    requireEntryFn(e, fnName, what);
    await ensureCrypto();
    return e;
  }

  /**
   * SHA-256 of a message string's bytes, as a lowercase hex digest
   * (entry_jsoo.ml's vcSha256Hex -> VC_DataIntegrity.hash_sha256_hex,
   * HACL* SHA-2). Needs the npm-entry bundle + the HACL* wasm backend
   * (auto-initialised).
   * @param {string} message the message whose bytes are hashed
   * @returns {Promise<string>} 64-char hex digest
   */
  async function vcSha256Hex(message) {
    if (typeof message !== 'string') {
      throw new TypeError('vcSha256Hex: message must be a string');
    }
    const e = await vcEntry('vcSha256Hex', 'VC SHA-256');
    return entryResult(e.vcSha256Hex(message), 'vcSha256Hex').sha256;
  }

  /**
   * Derive the Ed25519 public key from a 32-byte secret key
   * (entry_jsoo.ml's vcEd25519SecretToPublic -> HACL* Ed25519).
   * @param {string} secretKeyHex 32-byte secret key, hex
   * @returns {Promise<string>} 32-byte public key, hex
   */
  async function vcEd25519SecretToPublic(secretKeyHex) {
    if (typeof secretKeyHex !== 'string') {
      throw new TypeError('vcEd25519SecretToPublic: secretKeyHex must be a string');
    }
    const e = await vcEntry('vcEd25519SecretToPublic', 'VC Ed25519 key derivation');
    return entryResult(
      e.vcEd25519SecretToPublic(secretKeyHex), 'vcEd25519SecretToPublic').publicKeyHex;
  }

  /**
   * Ed25519 signature over a hex-encoded message (entry_jsoo.ml's
   * vcEd25519Sign -> HACL* Ed25519).
   * @param {string} secretKeyHex 32-byte secret key, hex
   * @param {string} messageHex the message to sign, hex
   * @returns {Promise<string>} 64-byte signature, hex
   */
  async function vcEd25519Sign(secretKeyHex, messageHex) {
    if (typeof secretKeyHex !== 'string' || typeof messageHex !== 'string') {
      throw new TypeError('vcEd25519Sign: secretKeyHex and messageHex must be strings');
    }
    const e = await vcEntry('vcEd25519Sign', 'VC Ed25519 sign');
    return entryResult(e.vcEd25519Sign(secretKeyHex, messageHex), 'vcEd25519Sign').signatureHex;
  }

  /**
   * Ed25519 verification (entry_jsoo.ml's vcEd25519Verify -> HACL*
   * Ed25519). A wrong key, tampered signature, altered message, or a
   * malformed-length input all return false — never an
   * exception-hidden true.
   * @param {string} publicKeyHex 32-byte public key, hex
   * @param {string} messageHex the message, hex
   * @param {string} signatureHex the 64-byte signature, hex
   * @returns {Promise<boolean>}
   */
  async function vcEd25519Verify(publicKeyHex, messageHex, signatureHex) {
    if (typeof publicKeyHex !== 'string' || typeof messageHex !== 'string' ||
        typeof signatureHex !== 'string') {
      throw new TypeError(
        'vcEd25519Verify: publicKeyHex, messageHex and signatureHex must be strings');
    }
    const e = await vcEntry('vcEd25519Verify', 'VC Ed25519 verify');
    return !!entryResult(
      e.vcEd25519Verify(publicKeyHex, messageHex, signatureHex), 'vcEd25519Verify').valid;
  }

  /**
   * Create an eddsa-rdfc-2022 Data Integrity proofValue over an
   * already-canonicalized document + proof config (entry_jsoo.ml's
   * vcEddsaCreateFromCanonical -> VC_DataIntegrity.eddsa_rdfc_2022_
   * create_from_canonical). The two canonical inputs are RDFC-1.0
   * canonical N-Quads (see canonicalize()).
   * @param {string} secretKeyHex 32-byte secret key, hex
   * @param {string} canonicalDocument canonical N-Quads of the document
   * @param {string} canonicalConfig canonical N-Quads of the proof config
   * @returns {Promise<string>} the multibase-z (base58btc) proofValue
   */
  async function vcEddsaCreateFromCanonical(secretKeyHex, canonicalDocument, canonicalConfig) {
    if (typeof secretKeyHex !== 'string' || typeof canonicalDocument !== 'string' ||
        typeof canonicalConfig !== 'string') {
      throw new TypeError(
        'vcEddsaCreateFromCanonical: secretKeyHex, canonicalDocument and canonicalConfig must be strings');
    }
    const e = await vcEntry('vcEddsaCreateFromCanonical', 'VC eddsa-rdfc-2022 proof creation');
    return entryResult(
      e.vcEddsaCreateFromCanonical(secretKeyHex, canonicalDocument, canonicalConfig),
      'vcEddsaCreateFromCanonical').proofValue;
  }

  /**
   * Verify an eddsa-rdfc-2022 proofValue against canonical inputs
   * (entry_jsoo.ml's vcEddsaVerifyFromCanonical ->
   * VC_DataIntegrity.eddsa_rdfc_2022_verify_from_canonical). Wrong
   * key, tampered document/config, or tampered proofValue all return
   * false.
   * @param {string} publicKeyHex 32-byte public key, hex
   * @param {string} canonicalDocument canonical N-Quads of the document
   * @param {string} canonicalConfig canonical N-Quads of the proof config
   * @param {string} proofValue the multibase-z proofValue to check
   * @returns {Promise<boolean>}
   */
  async function vcEddsaVerifyFromCanonical(publicKeyHex, canonicalDocument, canonicalConfig, proofValue) {
    if (typeof publicKeyHex !== 'string' || typeof canonicalDocument !== 'string' ||
        typeof canonicalConfig !== 'string' || typeof proofValue !== 'string') {
      throw new TypeError(
        'vcEddsaVerifyFromCanonical: publicKeyHex, canonicalDocument, canonicalConfig and proofValue must be strings');
    }
    const e = await vcEntry('vcEddsaVerifyFromCanonical', 'VC eddsa-rdfc-2022 proof verification');
    return !!entryResult(
      e.vcEddsaVerifyFromCanonical(publicKeyHex, canonicalDocument, canonicalConfig, proofValue),
      'vcEddsaVerifyFromCanonical').verified;
  }

  /**
   * VC Data Model 2.0 structural conformance check (entry_jsoo.ml's
   * vcCheckCredential -> VC_Credential.vc_check_from_string, 117 pass,
   * 0 fail on the offline vc_stage1 fixture suite). Pure structural
   * validation — no crypto, so this does NOT go through vcEntry/
   * ensureCrypto. `v2ctxJson` is the vendored VCDM v2 base context
   * document's raw JSON text (third_party/contexts/credentials-v2.jsonld,
   * `@context` value included — the F* side parses the whole document
   * and only reads its own @context field) and `credentialJson` is the
   * raw JSON text of the VC/VP document under test.
   * @param {string} v2ctxJson vendored credentials-v2.jsonld text
   * @param {string} credentialJson the VC/VP document's raw JSON text
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckCredential(v2ctxJson, credentialJson) {
    if (typeof v2ctxJson !== 'string' || typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckCredential: v2ctxJson and credentialJson must be strings');
    }
    const e = await entry();
    if (!e) throw pendingError('vcCheckCredential');
    requireEntryFn(e, 'vcCheckCredential', 'VC Data Model 2.0 structural check');
    const r = entryResult(e.vcCheckCredential(v2ctxJson, credentialJson), 'vcCheckCredential');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  /**
   * credentialSubject presence/shape check, VERSION-AGNOSTIC (Track A1,
   * docs/designissues/2026-07-11-vc-canivc-eecc-plan.md) —
   * entry_jsoo.ml's vcCheckCredentialSubject ->
   * VC_Credential.vc_check_credential_subject_from_string. Unlike
   * vcCheckCredential above, this does NOT require the VCDM 2.0 base
   * @context to be first (or present at all) — it only checks that a
   * credential-shaped document (type includes "VerifiableCredential")
   * has a present, non-empty credentialSubject. Used for documents
   * under a non-VCDM-2.0 @context (e.g. the vc-di-eddsa Data Integrity
   * conformance suite's legacy VC 1.1 fixtures) where the full
   * vcCheckCredential's @context sentinel would (correctly) reject the
   * document for an unrelated reason.
   * @param {string} credentialJson the VC/VP document's raw JSON text
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckCredentialSubject(credentialJson) {
    if (typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckCredentialSubject: credentialJson must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('vcCheckCredentialSubject');
    requireEntryFn(e, 'vcCheckCredentialSubject', 'credentialSubject presence check');
    const r = entryResult(e.vcCheckCredentialSubject(credentialJson), 'vcCheckCredentialSubject');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  /**
   * DATA_LOSS_DETECTION_ERROR check (Track A1, same plan doc) —
   * entry_jsoo.ml's vcCheckNoDataLoss ->
   * VC_Credential.vc_check_no_data_loss_from_string. Rejects a
   * credential-shaped document whose `type`/`@type` entries or
   * `credentialSubject` property keys include one that a lenient
   * JSON-LD processor would silently drop (VC Data Integrity spec,
   * "Securing Data Losslessly"). `credentialJson` MUST already have
   * any remote @context IRI the caller recognizes inlined to the real
   * context object — this engine build has no remote-context loader
   * registered, so a still-remote IRI string in "@context" fails
   * context processing honestly rather than silently skipping the
   * check.
   * @param {string} credentialJson the VC/VP document's raw JSON text,
   *   @context already inlined
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckNoDataLoss(credentialJson) {
    if (typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckNoDataLoss: credentialJson must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('vcCheckNoDataLoss');
    requireEntryFn(e, 'vcCheckNoDataLoss', 'DATA_LOSS_DETECTION_ERROR check');
    const r = entryResult(e.vcCheckNoDataLoss(credentialJson), 'vcCheckNoDataLoss');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  /**
   * relatedResource digest verification (VCDM 2.0 §5.3, vc20-api Track
   * A4) — entry_jsoo.ml's vcCheckRelatedResourceDigests ->
   * VC_Credential.vc_check_related_resource_digests_from_string. The
   * engine does no I/O, so the caller supplies a known-resource digest
   * registry: a JSON array of {"id": <resource URL>, "digestsHex":
   * [<lowercase hex>, ...]} entries computed from the caller's VENDORED
   * copies of each resource's content bytes. A relatedResource entry
   * whose id is in the registry and whose declared digestSRI/
   * digestMultibase matches none of that id's digests is rejected (the
   * spec's digest-mismatch error); an id absent from the registry, or a
   * digest algorithm the registry contract doesn't cover (anything
   * outside sha256/sha384), is unverifiable offline and passes. All
   * decode/match semantics are F*-verified (VC.Credential.fst).
   * @param {string} registryJson the digest registry's raw JSON text
   * @param {string} credentialJson the VC/VP document's raw JSON text
   * @returns {Promise<{valid: boolean, reason?: string}>}
   */
  async function vcCheckRelatedResourceDigests(registryJson, credentialJson) {
    if (typeof registryJson !== 'string' || typeof credentialJson !== 'string') {
      throw new TypeError('vcCheckRelatedResourceDigests: registryJson and credentialJson must be strings');
    }
    const e = await entry();
    if (!e) throw pendingError('vcCheckRelatedResourceDigests');
    requireEntryFn(e, 'vcCheckRelatedResourceDigests', 'relatedResource digest check');
    const r = entryResult(e.vcCheckRelatedResourceDigests(registryJson, credentialJson), 'vcCheckRelatedResourceDigests');
    return r.valid ? { valid: true } : { valid: false, reason: r.reason };
  }

  // -----------------------------------------------------------------
  // Typed "engine" functions (#74 npm FP surface). Each is a pure,
  // string/JSON-in, JSON-out wrapper over one F*-extracted engine
  // exposed by entry_jsoo.ml. No logic lives on the JS side — the
  // transform/eval/validate/CAS math is all verified F*; these bind
  // the entry ABI to a typed Promise. All need the npm-entry bundle.
  // -----------------------------------------------------------------

  /**
   * XSLT 1.0 transform (entry_jsoo.ml's xsltTransform export ->
   * XSLT.Transform.transform). Applies `stylesheetXml` to `sourceXml`
   * and returns the serialized result tree. Needs the npm-entry bundle.
   * @param {string} stylesheetXml an XSLT stylesheet document
   * @param {string} sourceXml the source XML document
   * @returns {Promise<string>} the transform output (serialized XML/text)
   */
  async function xsltTransform(stylesheetXml, sourceXml) {
    if (typeof stylesheetXml !== 'string' || typeof sourceXml !== 'string') {
      throw new TypeError('xsltTransform: stylesheetXml and sourceXml must be strings');
    }
    const e = await entry();
    if (!e) throw pendingError('xsltTransform');
    requireEntryFn(e, 'xsltTransform', 'XSLT transform');
    const r = entryResult(e.xsltTransform(stylesheetXml, sourceXml), 'xsltTransform');
    return r.output;
  }

  /**
   * Evaluate a Content MathML document (entry_jsoo.ml's mathmlEval
   * export -> MathML.Content.eval_doc_env). `bindings` maps
   * ci-variable names to value strings; pass {} for a closed
   * expression. Returns the exact numeric/boolean value or an
   * `undef` reason (division-by-zero, type error, ...). Needs the
   * npm-entry bundle.
   * @param {string} contentMathmlXml
   * @param {Record<string,string>} [bindings]
   * @returns {Promise<{kind:'rat',num:number,den:number}|{kind:'bool',value:boolean}|{kind:'undef',reason:string}>}
   */
  async function mathmlEval(contentMathmlXml, bindings) {
    if (typeof contentMathmlXml !== 'string') {
      throw new TypeError('mathmlEval: contentMathmlXml must be a string');
    }
    const b = bindings || {};
    if (typeof b !== 'object') {
      throw new TypeError('mathmlEval: bindings must be an object');
    }
    const e = await entry();
    if (!e) throw pendingError('mathmlEval');
    requireEntryFn(e, 'mathmlEval', 'MathML evaluation');
    const r = entryResult(
      e.mathmlEval(contentMathmlXml, JSON.stringify(b)), 'mathmlEval');
    return r.value;
  }

  /**
   * XForms recalculate (entry_jsoo.ml's xformsRecalc export ->
   * XForms.Bind.recalculate). Applies the model binds (calculate,
   * constraint, relevant, required, readonly, type MIPs) to the
   * instance and returns the recomputed instance plus a validity
   * report per bound node. Needs the npm-entry bundle.
   * @param {string} instanceXml the XForms instance document
   * @param {Array<{id?:string,target:string,calculate?:string,constraint?:string,relevant?:string,required?:string,readonly?:string,type?:string}>} binds
   * @returns {Promise<{instance:string,validity:Array<object>}>}
   */
  async function xformsRecalc(instanceXml, binds) {
    if (typeof instanceXml !== 'string') {
      throw new TypeError('xformsRecalc: instanceXml must be a string');
    }
    if (!Array.isArray(binds)) {
      throw new TypeError('xformsRecalc: binds must be an array');
    }
    const e = await entry();
    if (!e) throw pendingError('xformsRecalc');
    requireEntryFn(e, 'xformsRecalc', 'XForms recalculate');
    const r = entryResult(
      e.xformsRecalc(instanceXml, JSON.stringify(binds)), 'xformsRecalc');
    return { instance: r.instance, validity: r.validity };
  }

  /**
   * JSON Schema (draft-07) validation (entry_jsoo.ml's
   * jsonSchemaValidate export -> JSONSchema.Validate.validate).
   * Returns the verdict — the verified validator gives a definite
   * pass/fail/unsupported, not a per-keyword error list, so `errors`
   * carries a single reason string when not a definite pass. Needs
   * the npm-entry bundle.
   * @param {string} schemaJson the schema document (JSON text)
   * @param {string} instanceJson the instance document (JSON text)
   * @returns {Promise<{valid:boolean,result:'pass'|'fail'|'unsupported',errors:string[]}>}
   */
  async function jsonSchemaValidate(schemaJson, instanceJson) {
    if (typeof schemaJson !== 'string' || typeof instanceJson !== 'string') {
      throw new TypeError('jsonSchemaValidate: schemaJson and instanceJson must be strings');
    }
    const e = await entry();
    if (!e) throw pendingError('jsonSchemaValidate');
    requireEntryFn(e, 'jsonSchemaValidate', 'JSON Schema validation');
    const r = entryResult(
      e.jsonSchemaValidate(schemaJson, instanceJson), 'jsonSchemaValidate');
    return { valid: !!r.valid, result: r.result, errors: r.errors || [] };
  }

  /**
   * Schematron validation (entry_jsoo.ml's schematronValidate export
   * -> Schematron.Validate.validate). Returns every finding (failed
   * assert, fired report, indeterminate) in pattern-then-document
   * order. Needs the npm-entry bundle.
   * @param {string} schematronXml the Schematron schema document
   * @param {string} instanceXml the instance document to check
   * @returns {Promise<{findings:Array<{type:string,context:string,test:string,message:string,path:string,reason?:string}>}>}
   */
  async function schematronValidate(schematronXml, instanceXml) {
    if (typeof schematronXml !== 'string' || typeof instanceXml !== 'string') {
      throw new TypeError('schematronValidate: schematronXml and instanceXml must be strings');
    }
    const e = await entry();
    if (!e) throw pendingError('schematronValidate');
    requireEntryFn(e, 'schematronValidate', 'Schematron validation');
    const r = entryResult(
      e.schematronValidate(schematronXml, instanceXml), 'schematronValidate');
    return { findings: r.findings };
  }

  // TOAN — a small exact-CAS surface over Math.Expr (E_Int/E_Rat/E_Bool/
  // E_Sym/E_App). Callers pass an expression as the JSON codec
  //   {int:n} | {rat:[n,d]} | {bool:b} | {sym:name} | {app:name,args:[...]}
  // and receive Content MathML for the result (via MathML.Present).
  async function toanCall(fnName, what, ...args) {
    const e = await entry();
    if (!e) throw pendingError(fnName);
    requireEntryFn(e, fnName, what);
    const r = entryResult(e[fnName](...args), fnName);
    return r.mathml;
  }

  /**
   * Symbolic finite summation (entry_jsoo.ml's toanSummation ->
   * Math.Series.summation): sum of `body[idx:=lo..hi]`, simplified,
   * as Content MathML. Needs the npm-entry bundle.
   * @param {object} bodyExpr the summand, in the expr JSON codec
   * @param {string} idx the summation index symbol
   * @param {number} lo inclusive lower bound
   * @param {number} hi inclusive upper bound
   * @returns {Promise<string>} Content MathML
   */
  async function toanSummation(bodyExpr, idx, lo, hi) {
    if (typeof idx !== 'string') throw new TypeError('toanSummation: idx must be a string');
    return toanCall('toanSummation', 'TOAN summation',
      JSON.stringify(bodyExpr), idx, String(lo), String(hi));
  }

  /**
   * Symbolic finite product (entry_jsoo.ml's toanProduct ->
   * Math.Series.finite_product). Same shape as {@link toanSummation}.
   * @param {object} bodyExpr the factor, in the expr JSON codec
   * @param {string} idx the product index symbol
   * @param {number} lo inclusive lower bound
   * @param {number} hi inclusive upper bound
   * @returns {Promise<string>} Content MathML
   */
  async function toanProduct(bodyExpr, idx, lo, hi) {
    if (typeof idx !== 'string') throw new TypeError('toanProduct: idx must be a string');
    return toanCall('toanProduct', 'TOAN product',
      JSON.stringify(bodyExpr), idx, String(lo), String(hi));
  }

  /**
   * Canonical simplification (entry_jsoo.ml's toanSimplify ->
   * Math.Simplify.simplify) of an expression, as Content MathML.
   * @param {object} expr in the expr JSON codec
   * @returns {Promise<string>} Content MathML
   */
  async function toanSimplify(expr) {
    return toanCall('toanSimplify', 'TOAN simplify', JSON.stringify(expr));
  }

  /**
   * Symbolic differentiation (entry_jsoo.ml's toanDiff ->
   * Math.Diff.diff) of `expr` w.r.t. `variable`, as Content MathML.
   * @param {object} expr in the expr JSON codec
   * @param {string} variable the differentiation variable
   * @returns {Promise<string>} Content MathML
   */
  async function toanDiff(expr, variable) {
    if (typeof variable !== 'string') throw new TypeError('toanDiff: variable must be a string');
    return toanCall('toanDiff', 'TOAN diff', JSON.stringify(expr), variable);
  }

  /**
   * Substitution (entry_jsoo.ml's toanSubst -> Math.Subst.subst):
   * `expr[variable := value]`, simplified, as Content MathML.
   * @param {object} expr in the expr JSON codec
   * @param {string} variable the symbol to replace
   * @param {object} value the replacement, in the expr JSON codec
   * @returns {Promise<string>} Content MathML
   */
  async function toanSubst(expr, variable, value) {
    if (typeof variable !== 'string') throw new TypeError('toanSubst: variable must be a string');
    return toanCall('toanSubst', 'TOAN subst',
      JSON.stringify(expr), variable, JSON.stringify(value));
  }

  // Matrix / vector algebra over exact rationals (Math.Matrix). A
  // matrix is a JSON array of rows; a vector a JSON array of cells;
  // a cell is an integer or a [num,den] pair. Results render via
  // Math.Matrix.mres_to_string ("undef" carries a `reason`).
  async function matrixCall(fnName, what, ...jsonArgs) {
    const e = await entry();
    if (!e) throw pendingError(fnName);
    requireEntryFn(e, fnName, what);
    const r = entryResult(e[fnName](...jsonArgs.map((a) => JSON.stringify(a))), fnName);
    return { result: r.result, reason: r.reason || '' };
  }

  /**
   * Determinant of a square matrix (entry_jsoo.ml's matrixDeterminant
   * -> Math.Matrix.dyn_determinant), exact.
   * @param {Array<Array<number|[number,number]>>} matrix
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixDeterminant(matrix) {
    if (!Array.isArray(matrix)) throw new TypeError('matrixDeterminant: matrix must be an array of rows');
    return matrixCall('matrixDeterminant', 'matrix determinant', matrix);
  }

  /**
   * Dot / scalar product of two vectors (entry_jsoo.ml's
   * matrixScalarProduct -> Math.Matrix.dyn_scalarproduct).
   * @param {Array<number|[number,number]>} a
   * @param {Array<number|[number,number]>} b
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixScalarProduct(a, b) {
    if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixScalarProduct: a and b must be arrays');
    return matrixCall('matrixScalarProduct', 'vector scalar product', a, b);
  }

  /**
   * Cross product of two 3-vectors (entry_jsoo.ml's
   * matrixVectorProduct -> Math.Matrix.dyn_vectorproduct).
   * @param {Array<number|[number,number]>} a
   * @param {Array<number|[number,number]>} b
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixVectorProduct(a, b) {
    if (!Array.isArray(a) || !Array.isArray(b)) throw new TypeError('matrixVectorProduct: a and b must be arrays');
    return matrixCall('matrixVectorProduct', 'vector cross product', a, b);
  }

  /**
   * Outer product of two vectors (entry_jsoo.ml's matrixOuterProduct
   * -> Math.Matrix.dyn_outerproduct).
   * @param {Array<number|[number,number]>} a
   * @param {Array<number|[number,number]>} b
   * @returns {Promise<{result:string,reason:string}>}
   */
  async function matrixOuterProduct(a, b) {
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
   * sigmoidPoints -> Math.Sigmoid.sigmoid_points). All arithmetic --
   * argument reduction, the truncated Taylor series, repeated
   * squaring, and the x samples themselves -- runs as exact rational
   * arithmetic inside Math.Sigmoid.fst; see that module's header for
   * the documented error bound on the returned (rounded) values. This
   * wrapper only marshals JSON; it never computes exp itself.
   * @param {{k:number|string,x0:number|string,l:number|string,
   *   xmin:number|string,xmax:number|string,n:number|string}} params
   * @returns {Promise<Array<{x:{mantissa:string,scale:string,decimal:string},
   *   y:{mantissa:string,scale:string,decimal:string}}>>}
   */
  async function sigmoidPoints(params) {
    if (!params || typeof params !== 'object') {
      throw new TypeError('sigmoidPoints: params must be an object');
    }
    const e = await entry();
    if (!e) throw pendingError('sigmoid points');
    requireEntryFn(e, 'sigmoidPoints', 'sigmoid points');
    const wire = {
      k: String(params.k), x0: String(params.x0), l: String(params.l),
      xmin: String(params.xmin), xmax: String(params.xmax), n: String(params.n),
    };
    const r = entryResult(e.sigmoidPoints(JSON.stringify(wire)), 'sigmoid points');
    return r.points.map((p) => ({ x: scaledFromJson(p.x), y: scaledFromJson(p.y) }));
  }

  /**
   * Presentation MathML for the sigmoid formula L / (1 + exp(-k*(x - x0))),
   * engine-serialized (entry_jsoo.ml's sigmoidFormulaMathml ->
   * MathML.Present.to_presentation_mathml applied to a fixed
   * Math.Expr.expr) -- never hand-written MathML.
   * @returns {Promise<string>} a `<math>...</math>` Presentation MathML document
   */
  async function sigmoidFormulaMathml() {
    const e = await entry();
    if (!e) throw pendingError('sigmoid formula MathML');
    requireEntryFn(e, 'sigmoidFormulaMathml', 'sigmoid formula MathML');
    const r = entryResult(e.sigmoidFormulaMathml(), 'sigmoid formula MathML');
    return r.mathml;
  }

  // -----------------------------------------------------------------
  // In-memory COTTAS bytes store (docs/designissues/2026-07-06-
  // inmemory-bytes-store.md, stage 5). Needs the npm-entry bundle
  // (bin/npm-entry/entry_jsoo.ml's openCottas/queryCottas/closeCottas/
  // toCottas exports). Unlike every other operation in this file, the
  // "dataset" here is NOT an in-heap Dataset: openCottas() returns an
  // opaque handle string naming an entry the F*-verified COTTAS/Parquet
  // reader decodes lazily, row-group by row-group, as queryCottas()
  // touches it -- the whole point of the design (heap-store parity
  // would defeat the memory win the design doc measures). See
  // queryCottas's doc comment for the query-shape/entailment/write
  // divergences from query() this implies.
  // -----------------------------------------------------------------

  // Accept a hex string, a Uint8Array/Buffer, or a plain ArrayBuffer;
  // normalize to the lowercase hex string the entry ABI's string-only
  // wire contract requires (same "strings in, JSON out" ABI every
  // other entry export uses -- see entry_jsoo.ml's file header).
  function bytesToHex(bytesLike, who) {
    if (typeof bytesLike === 'string') {
      if (!/^[0-9a-fA-F]*$/.test(bytesLike) || bytesLike.length % 2 !== 0) {
        throw new TypeError(`${who}: string input must be an even-length hex string`);
      }
      return bytesLike.toLowerCase();
    }
    let u8;
    if (bytesLike instanceof Uint8Array) u8 = bytesLike;
    else if (bytesLike instanceof ArrayBuffer) u8 = new Uint8Array(bytesLike);
    else {
      throw new TypeError(
        `${who}: expected a hex string, Uint8Array, Buffer, or ArrayBuffer`);
    }
    // Buffer's native hex codec when available (Node); a per-byte
    // string-concat loop allocates millions of intermediate strings on
    // a corpus-scale artifact (it measurably dominated the bytes-store
    // path's RSS at 50,000 quads before this branch existed).
    if (typeof Buffer !== 'undefined' && typeof Buffer.from === 'function') {
      return Buffer.from(u8.buffer, u8.byteOffset, u8.byteLength).toString('hex');
    }
    const HEX = '0123456789abcdef';
    const parts = new Array(u8.length);
    for (let i = 0; i < u8.length; i++) {
      parts[i] = HEX[u8[i] >> 4] + HEX[u8[i] & 15];
    }
    return parts.join('');
  }

  function hexToBytes(hex) {
    const out = new Uint8Array(hex.length / 2);
    for (let i = 0; i < out.length; i++) {
      out[i] = parseInt(hex.substr(i * 2, 2), 16);
    }
    return out;
  }

  /**
   * Open a COTTAS/Parquet artifact's raw bytes as a queryable,
   * read-only store -- the in-memory-bytes-store design's browser call
   * site. Needs the npm-entry bundle. The store is NOT materialized
   * into a heap Dataset: rows are decoded lazily by queryCottas() as a
   * query actually touches them (measured 64-161 B/quad in the design
   * doc's native numbers, vs. ~877 B/quad for a fully-parsed heap
   * Dataset of the same data).
   *
   * @param {string|Uint8Array|ArrayBuffer} bytes whole `.cottas` file contents
   * @returns {Promise<string>} an opaque handle for queryCottas()/closeCottas()
   */
  async function openCottas(bytes) {
    const e = await entry();
    if (!e) throw pendingError('openCottas (in-memory COTTAS bytes store)');
    requireEntryFn(e, 'openCottas', 'openCottas');
    const hex = bytesToHex(bytes, 'openCottas');
    const r = entryResult(e.openCottas(hex), 'openCottas');
    return r.handle;
  }

  /**
   * Run a SPARQL 1.1 query against a store opened by openCottas().
   * Needs the npm-entry bundle.
   *
   * Divergences from query() (documented, not silent):
   *  - No `entail` option -- bare COTTAS bytes carry no closure step.
   *  - No write/--delta-log overlay -- read-only (design doc §2.4's
   *    write-overlay story composes at the native store_caps layer;
   *    it is not wired into this browser ABI).
   *  - A query SHAPE the backend executor can't push down (rare; the
   *    same honest-failure posture the native `--data-cottas` CLI path
   *    has for run_select_query_backend_dataset/run_ask_query_backend_
   *    dataset returning None) rejects with an Error rather than
   *    silently falling back to a full materialize -- that fallback
   *    would defeat the store's whole memory argument.
   *  - DESCRIBE is not supported (same cut queryDataset's ABI has).
   *
   * @param {string} handle from openCottas()
   * @param {string} sparql
   * @returns {Promise<Array<Map<string, object>>|boolean|Dataset>}
   *   SELECT -> Bindings[], ASK -> boolean, CONSTRUCT -> Dataset
   *   (materialized once, via SPARQL11_Store.materialize_dataset_backend
   *   -- see entry_jsoo.ml's queryCottas doc comment for why CONSTRUCT
   *   alone pays that cost).
   */
  async function queryCottas(handle, sparql) {
    if (typeof handle !== 'string') {
      throw new TypeError('queryCottas: handle must be the string openCottas() returned');
    }
    if (typeof sparql !== 'string') {
      throw new TypeError('queryCottas: sparql must be a string');
    }
    const e = await entry();
    if (!e) throw pendingError('queryCottas');
    requireEntryFn(e, 'queryCottas', 'queryCottas');
    const r = entryResult(e.queryCottas(handle, sparql), 'queryCottas');
    if (r.kind === 'ask') return r.boolean;
    if (r.kind === 'construct') {
      return Dataset.fromNQuads(r.nquads, { blankNodePrefix: freshBnodePrefix() });
    }
    return bindingsFromSrj(r.srj);
  }

  /**
   * Release a store opened by openCottas(). Drops the handle from this
   * process's registry only -- it does NOT evict the underlying byte
   * cache the entry bundle keeps for the process's lifetime (design
   * doc "Open decisions" item 1: no eviction API exists yet). A page
   * that opens many short-lived stores still grows that cache for the
   * tab's lifetime; this is a documented limitation, not a silent leak.
   * @param {string} handle
   * @returns {Promise<void>}
   */
  async function closeCottas(handle) {
    if (typeof handle !== 'string') {
      throw new TypeError('closeCottas: handle must be the string openCottas() returned');
    }
    const e = await entry();
    if (!e) throw pendingError('closeCottas');
    requireEntryFn(e, 'closeCottas', 'closeCottas');
    entryResult(e.closeCottas(handle), 'closeCottas');
  }

  /**
   * Serialize a dataset to COTTAS/Parquet bytes via the native writer
   * (RDF.CottasStore.BaseWriter.serialize_cottas_v2 -- the SAME pure
   * `Tot` F* function `factoidal compact --native-writer` uses), for a
   * caller to persist (IndexedDB/OPFS) or offer as a download. Needs
   * the npm-entry bundle. Round-trips through openCottas(): the bytes
   * this returns are valid input to openCottas() and to the native
   * `--data-cottas`/`--data-cottas-mem` CLI flags, byte-for-byte.
   * @param {Dataset|string|Array} data
   * @param {{format?: string}} [options]
   * @returns {Promise<Uint8Array>}
   */
  async function toCottas(data, options) {
    const e = await entry();
    if (!e) throw pendingError('toCottas (native COTTAS serialization)');
    requireEntryFn(e, 'toCottas', 'toCottas');
    const nq = docsToEntryNQuads(e, toDocs(data, options), 'toCottas');
    const r = entryResult(e.toCottas(nq), 'toCottas');
    return hexToBytes(r.cottasHex);
  }

  /**
   * Feature probe, for tests and downstream capability checks.
   * @returns {Promise<{entry: boolean, construct: boolean,
   *   update: boolean, canonicalize: boolean, graphs: boolean,
   *   canonicalHash: boolean, shacl: boolean, shex: boolean,
   *   owlClosure: boolean, rml: boolean, csvw: boolean, jsonld: boolean,
   *   rif: boolean}>}
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
      return {
        entry: true, construct: true, update: true, canonicalize: true,
        graphs: true, canonicalHash: true,
        // Per-function probes, not a blanket `true` -- an older/stale
        // loaded bundle (e.g. a wasm-target build that predates one of
        // these exports) reports its ACTUAL surface rather than
        // over-promising (see requireEntryFn's doc comment above).
        shacl: typeof e.shaclValidate === 'function',
        shex: typeof e.shexValidate === 'function',
        owlClosure: typeof e.owlClosure === 'function',
        tableau: typeof e.tableauMaterialise === 'function' &&
          typeof e.tableauDlInconsistent === 'function',
        rml: typeof e.rmlMap === 'function',
        csvw: typeof e.csvwToRdf === 'function',
        jsonld: typeof e.jsonldToRdf === 'function',
        jsonldFromRdf: typeof e.jsonldFromRdf === 'function',
        didKey: typeof e.didKeyResolve === 'function',
        xml: typeof e.xmlWellformed === 'function',
        xpath: typeof e.xpathEval === 'function',
        rif: typeof e.rifEval === 'function',
        xslt: typeof e.xsltTransform === 'function',
        mathml: typeof e.mathmlEval === 'function',
        xforms: typeof e.xformsRecalc === 'function',
        jsonSchema: typeof e.jsonSchemaValidate === 'function',
        schematron: typeof e.schematronValidate === 'function',
        toan: typeof e.toanSummation === 'function',
        matrix: typeof e.matrixDeterminant === 'function',
        sigmoid: typeof e.sigmoidPoints === 'function' &&
          typeof e.sigmoidFormulaMathml === 'function',
        cottasBytesStore: typeof e.openCottas === 'function' &&
          typeof e.queryCottas === 'function' && typeof e.toCottas === 'function',
        // VC Data Integrity crypto surface (probed, not blanket-true --
        // an older bundle predates the vc* exports). The HACL* wasm
        // backend still has to be initialised at call time; this flag
        // only reports that the ABI exports exist.
        vcCrypto: typeof e.vcEd25519Verify === 'function' &&
          typeof e.vcEddsaVerifyFromCanonical === 'function',
      };
    }
    // Probe --canonicalize support on the CLI bundle with a 1-quad doc.
    // canonicalHash rides the same engine support as canonicalize (it is
    // canonicalize() applied to one graph's triples); graphs() is pure
    // JS enumeration and needs no engine at all.
    let canon = false;
    try {
      const res = await run(
        ['--canonicalize', '-d', '/static/cap.nq'],
        [{ name: '/static/cap.nq',
           content: '<http://x/s> <http://x/p> "o" .\n' }]);
      canon = res.exitCode === 0;
    } catch (_) { canon = false; }
    return {
      entry: false, construct: false, update: false, canonicalize: canon,
      graphs: true, canonicalHash: canon,
      shacl: false, shex: false, owlClosure: false, tableau: false, rml: false,
      csvw: false, jsonld: false, jsonldFromRdf: false, didKey: false,
      xml: false, xpath: false, rif: false, cottasBytesStore: false,
      xslt: false, mathml: false, xforms: false, jsonSchema: false,
      schematron: false, toan: false, matrix: false, sigmoid: false, vcCrypto: false,
    };
  }

  return {
    parse,
    query,
    queryHdt,
    update,
    registerExtensionFunction,
    unregisterExtensionFunction,
    clearExtensionFunctions,
    registerServiceEndpoint,
    clearServiceEndpoints,
    serialize,
    canonicalize,
    graphs,
    canonicalHash,
    shaclValidate,
    shexValidate,
    owlClosure,
    coreRdfsClosure,
    coreRdfsCheck,
    rdfsPlusClosure,
    rhoDfClosure,
    rhoDfFragmentCheck,
    tableauMaterialise,
    tableauDlInconsistent,
    owlIsConsistent,
    owlEntails,
    rmlMap,
    csvwToRdf,
    jsonldToRdf,
    jsonldFromRdf,
    didKeyResolve,
    xmlWellformed,
    xpathEval,
    clParse,
    clSerialize,
    clAlphaNorm,
    clNormalize,
    rifEval,
    xsltTransform,
    mathmlEval,
    xformsRecalc,
    jsonSchemaValidate,
    schematronValidate,
    toanSummation,
    toanProduct,
    toanSimplify,
    toanDiff,
    toanSubst,
    matrixDeterminant,
    matrixScalarProduct,
    matrixVectorProduct,
    matrixOuterProduct,
    sigmoidPoints,
    sigmoidFormulaMathml,
    vcSha256Hex,
    vcEd25519SecretToPublic,
    vcEd25519Sign,
    vcEd25519Verify,
    vcEddsaCreateFromCanonical,
    vcEddsaVerifyFromCanonical,
    vcCheckCredential,
    vcCheckCredentialSubject,
    vcCheckNoDataLoss,
    vcCheckRelatedResourceDigests,
    openCottas,
    queryCottas,
    closeCottas,
    toCottas,
    capabilities,
    Dataset,
    dataFactory,
  };
}

module.exports = { buildApi, sniffQueryForm, bindingsFromSrj };
