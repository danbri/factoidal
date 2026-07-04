// jsonld-playground-client.mjs
// ---------------------------------------------------------------------
// Engine-call logic for demo-jsonld-playground.html, factored out of
// the page so it is importable and testable under Node without a DOM
// -- same rationale as factoidal-sparql-client.js, but that file is a
// <custom-element> (needs `document`); this one is plain functions
// over a driver, so `tests/web-demos/jsonld_playground_smoke.sh` can
// exercise the exact same toRdf()/canonicalize() calls the page makes.
// Plain ESM (`.mjs`) so Node treats it as a module regardless of the
// nearest package.json's "type" field, matching how a browser
// <script type="module"> loads it regardless of extension.
//
// buildJsonLdPlayground(driver) follows the same dependency-injection
// shape as npm/factoidal/lib/api.js's buildApi(driver): the caller
// supplies a `runCli(args, files) -> {stdout, stderr, exitCode}`
// primitive and this module supplies the JSON-LD-specific argv/format
// plumbing on top. Two drivers exist in this repo already:
//   - browser: npm/factoidal/browser.js's runFactoidalCli (fetch-based,
//     used by demo-jsonld-playground.html against the Pages-mirrored
//     npm package at ../npm/foafos/browser.js);
//   - Node: npm/factoidal/lib/engine-js.js's runCli (fs-based, used by
//     the smoke test below).
// Both drive the same factoidal.js CLI bundle, so a pass under Node is
// real evidence the browser path works too, modulo the fetch-vs-fs
// engine-loading difference.
//
// !! NO RDF/JSON-LD SEMANTIC LOGIC HERE !! All deserialization lives in
// formal/fstar/Parser.JSONLD.fst + JSONLD.Context.fst + JSONLD.Expand.fst;
// all canonicalization lives in formal/fstar/RDF.Canonical.fst. This
// file only shapes CLI arguments and reformats the N-Quads text the
// F*-verified serializer already produced (RDF.Pretty / RDF.Canonical),
// the same "client-side reformatting only" contract documented in
// factoidal-sparql-client.js's CSV/TSV helpers.
// ---------------------------------------------------------------------

'use strict';

// ---------------------------------------------------------------------
// The playground's preloaded example. FOAF-ish, deliberately exercising
// several of the features JSONLD.Context.fst / JSONLD.Expand.fst /
// Parser.JSONLD.fst cover (per CLAUDE.md: "expanded form + inline
// contexts + @reverse + container maps + base resolution"):
//   - an inline @context (term -> IRI map, no remote fetch needed);
//   - "@base" relative-IRI resolution (alice/bob/carol/eve -> absolute);
//   - a term-level "@type": "@id" coercion (homepage, knows, knownBy);
//   - a "@container": "@set" property (knows: [bob, carol]);
//   - a term-level "@reverse" mapping (knownBy: eve -> triple emitted
//     as eve foaf:knows alice, subject/object swapped).
// Exported so demo-jsonld-playground.html and
// tests/web-demos/jsonld_playground_smoke.sh run the exact same
// document -- no drift between what the page shows and what the smoke
// test asserts against.
// ---------------------------------------------------------------------
export const SAMPLE_JSONLD = `{
  "@context": {
    "@base": "http://example.org/",
    "foaf": "http://xmlns.com/foaf/0.1/",
    "name": "foaf:name",
    "homepage": {"@id": "foaf:homepage", "@type": "@id"},
    "knows": {"@id": "foaf:knows", "@type": "@id", "@container": "@set"},
    "knownBy": {"@reverse": "foaf:knows", "@type": "@id"}
  },
  "@id": "alice",
  "@type": "foaf:Person",
  "name": "Alice",
  "homepage": "https://alice.example/",
  "knows": ["bob", "carol"],
  "knownBy": "eve"
}
`;

// A remote-context example -- deliberately NOT supported. JSONLD.Expand
// has no JSONLD.Loader/fetch step, so a bare URL string @context is
// parsed correctly as JSON but rejected by Parser.JSONLD.parse_jsonld.
// The playground's "Remote-context example (unsupported)" button loads
// this to demonstrate the honest failure path rather than only ever
// showing success cases.
export const SAMPLE_JSONLD_REMOTE_CONTEXT = `{
  "@context": "https://schema.org/",
  "@id": "http://example.org/alice",
  "@type": "Person",
  "name": "Alice"
}
`;

/**
 * @param {{runCli: (args: string[], files: Array<{name:string,content:string}>) =>
 *   ({stdout:string,stderr:string,exitCode:number}|Promise<{stdout:string,stderr:string,exitCode:number}>)}} driver
 */
export function buildJsonLdPlayground(driver) {
  function nowMs() {
    if (typeof performance !== 'undefined' && performance.now) return performance.now();
    return Date.now();
  }

  async function run(args, files) {
    return driver.runCli(args, files);
  }

  function checkOk(res, what) {
    if (res.exitCode !== 0) {
      const msg = (res.stderr || res.stdout || `exited ${res.exitCode}`).trim();
      const err = new Error(`${what}: ${msg}`);
      err.exitCode = res.exitCode;
      err.stderr = res.stderr;
      err.stdout = res.stdout;
      throw err;
    }
  }

  /**
   * JSON-LD toRdf: parse the document and dump sorted N-Quads.
   * Honest-failure contract: if the document uses a feature Phase 1-3b
   * of the JSON-LD program doesn't cover yet (most commonly a remote
   * @context URL string -- there is no JSONLD.Loader/fetch step), the
   * engine's own parse failure is what rejects this promise. Never
   * synthesize output the engine didn't produce.
   *
   * @param {string} jsonldText
   * @param {{baseIRI?: string}} [options]
   * @returns {Promise<{nquads: string, ms: number}>}
   */
  async function toRdf(jsonldText, options) {
    const opts = options || {};
    const t0 = nowMs();
    const args = ['--dump-nq', '-d', '/static/input.jsonld'];
    if (opts.baseIRI) args.push('-b', opts.baseIRI);
    const res = await run(args, [{ name: '/static/input.jsonld', content: jsonldText }]);
    checkOk(res, 'toRdf');
    return { nquads: res.stdout, ms: nowMs() - t0 };
  }

  /**
   * RDFC-1.0 canonicalization of the JSON-LD document's RDF form.
   *
   * @param {string} jsonldText
   * @param {{baseIRI?: string}} [options]
   * @returns {Promise<{nquads: string, ms: number}>}
   */
  async function canonicalize(jsonldText, options) {
    const opts = options || {};
    const t0 = nowMs();
    const args = ['--canonicalize', '-d', '/static/input.jsonld'];
    if (opts.baseIRI) args.push('-b', opts.baseIRI);
    const res = await run(args, [{ name: '/static/input.jsonld', content: jsonldText }]);
    checkOk(res, 'canonicalize');
    return { nquads: res.stdout, ms: nowMs() - t0 };
  }

  return { toRdf, canonicalize };
}

// ---------------------------------------------------------------------
// N-Quads -> {subject, predicate, object, graph} rows, for the
// playground's "Table" tab. Pure string splitting over text the F*
// serializer already produced -- no RDF interpretation.
// ---------------------------------------------------------------------

/**
 * @param {string} nquads
 * @returns {Array<{subject:string, predicate:string, object:string, graph:string|null}>}
 */
export function parseNQuadsToRows(nquads) {
  const rows = [];
  const lines = (nquads || '').split('\n');
  for (const raw of lines) {
    const line = raw.trim();
    if (!line) continue;
    const terms = splitNQuadTerms(line);
    if (terms.length < 3) continue;
    rows.push({
      subject: terms[0],
      predicate: terms[1],
      object: terms[2],
      graph: terms[3] || null,
    });
  }
  return rows;
}

// Tokenize one N-Quads line's terms (the trailing " ." is stripped
// first). Handles <iri>, _:bnode, and "literal" with an optional
// @lang or ^^<datatype> suffix, including backslash-escaped quotes
// inside the literal.
function splitNQuadTerms(line) {
  const body = line.endsWith('.') ? line.slice(0, -1).trim() : line;
  const terms = [];
  const n = body.length;
  let i = 0;
  while (i < n) {
    while (i < n && /\s/.test(body[i])) i++;
    if (i >= n) break;
    if (body[i] === '<') {
      const end = body.indexOf('>', i);
      if (end < 0) break;
      terms.push(body.slice(i, end + 1));
      i = end + 1;
    } else if (body[i] === '"') {
      let j = i + 1;
      let esc = false;
      while (j < n) {
        if (esc) { esc = false; j++; continue; }
        if (body[j] === '\\') { esc = true; j++; continue; }
        if (body[j] === '"') { j++; break; }
        j++;
      }
      let end = j;
      if (body[end] === '@') {
        end++;
        while (end < n && /[A-Za-z0-9-]/.test(body[end])) end++;
      } else if (body[end] === '^' && body[end + 1] === '^') {
        end += 2;
        if (body[end] === '<') {
          const dtEnd = body.indexOf('>', end);
          end = dtEnd < 0 ? n : dtEnd + 1;
        }
      }
      terms.push(body.slice(i, end));
      i = end;
    } else if (body.startsWith('_:', i)) {
      let j = i + 2;
      while (j < n && !/\s/.test(body[j])) j++;
      terms.push(body.slice(i, j));
      i = j;
    } else {
      let j = i;
      while (j < n && !/\s/.test(body[j])) j++;
      terms.push(body.slice(i, j));
      i = j;
    }
  }
  return terms;
}
