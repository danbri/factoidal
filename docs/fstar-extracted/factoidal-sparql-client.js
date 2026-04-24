// factoidal-sparql-client.js
// ---------------------------------------------------------------------
// Custom Element v1 + Shadow DOM wrapper around the Factoidal verified
// SPARQL engine (factoidal.js / factoidal.wasm.js).
//
// This is the tentative first cut — see
//   docs/designissues/2026-04-23-sparql-client-web-component.md
// for the design rationale. Logic was ported from
// docs/fstar-extracted/demo-lifesci.html (the known-good production demo).
//
// Usage:
//
//   <script type="module" src="./factoidal-sparql-client.js"></script>
//   <factoidal-sparql-client
//       engines="js,wasm"
//       default-engine="js"
//       src-data='[{"url":"./data.ttl","graph":"urn:x:main"}]'>
//     <factoidal-query name="count" label="Count triples">
//       SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }
//     </factoidal-query>
//   </factoidal-sparql-client>
//
// No build step, no deps outside the engine bundles + browser-wasm.js.
// ---------------------------------------------------------------------

'use strict';

// ---------------------------------------------------------------------
// <factoidal-query> — light-DOM child used to declare queries inline.
// Rendered as nothing; its `name`, `label`, and textContent feed the
// parent orchestrator's query list.
// ---------------------------------------------------------------------
class FactoidalQuery extends HTMLElement {
  connectedCallback() {
    // Hide; we're metadata, not UI.
    this.style.display = 'none';
    // Signal to the parent to re-read.
    const host = this.closest('factoidal-sparql-client');
    if (host && typeof host._queriesChanged === 'function') host._queriesChanged();
  }
}
if (!customElements.get('factoidal-query')) {
  customElements.define('factoidal-query', FactoidalQuery);
}

// ---------------------------------------------------------------------
// Styles for the orchestrator's shadow DOM. Kept self-contained so the
// component works without any page CSS.
// ---------------------------------------------------------------------
const STYLES = `
:host {
  display: block;
  --fc-fg: #222;
  --fc-muted: #666;
  --fc-bg: #fff;
  --fc-surface: #f7f7f7;
  --fc-border: #e0e0e0;
  --fc-brand: #2d6a4f;
  --fc-brand-dark: #1b4332;
  --fc-error: #c0392b;
  --fc-ok: #2d6a4f;
  font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
  color: var(--fc-fg);
  line-height: 1.5;
}
* { box-sizing: border-box; }
.row { display: flex; gap: 1em; margin: 0.8em 0; align-items: center; flex-wrap: wrap; }
label { font-weight: 600; color: var(--fc-muted); font-size: 0.9em; }
select, button {
  font: inherit; padding: 0.4em 0.7em;
  border: 1px solid var(--fc-border);
  background: var(--fc-bg); border-radius: 4px;
}
button {
  background: var(--fc-brand); color: #fff;
  border-color: var(--fc-brand-dark);
  cursor: pointer; font-weight: 600;
  transition: transform 0.05s, background 0.1s, box-shadow 0.1s;
}
button:disabled { opacity: 0.6; cursor: wait; }
button.run-btn:active:not(:disabled) {
  transform: scale(0.96);
  background: var(--fc-brand-dark);
}
@keyframes runPulse {
  0%   { box-shadow: 0 0 0 0    rgba(45, 106, 79, 0.75); }
  60%  { box-shadow: 0 0 0 14px rgba(45, 106, 79, 0); }
  100% { box-shadow: 0 0 0 0    rgba(45, 106, 79, 0); }
}
button.run-btn.running {
  animation: runPulse 1.2s ease-out infinite;
  background: var(--fc-brand-dark);
  cursor: wait;
  opacity: 1;
}
@keyframes spin { to { transform: rotate(360deg); } }
.spinner {
  display: inline-block; width: 0.9em; height: 0.9em;
  border: 2px solid var(--fc-border);
  border-top-color: var(--fc-brand);
  border-radius: 50%;
  animation: spin 0.7s linear infinite;
  vertical-align: -0.18em; margin-right: 0.35em;
}
.radio-group {
  position: relative;
  display: inline-flex; border: 1px solid var(--fc-border);
  border-radius: 4px; overflow: hidden; background: var(--fc-bg);
}
.radio-group input[type="radio"] {
  position: absolute; width: 1px; height: 1px; margin: -1px;
  padding: 0; clip: rect(0 0 0 0); overflow: hidden;
  white-space: nowrap; border: 0;
}
.radio-group label {
  cursor: pointer; padding: 0.45em 0.9em; font-weight: 500;
  font-size: 0.9em; color: var(--fc-fg); user-select: none;
  display: inline-flex; align-items: center; min-height: 32px;
  transition: background 0.1s;
}
.radio-group label + label { border-left: 1px solid var(--fc-border); }
.radio-group label:hover { background: var(--fc-surface); }
.radio-group label:has(input:checked) {
  background: var(--fc-brand); color: #fff; font-weight: 600;
}
.radio-group label:focus-within {
  outline: 2px solid var(--fc-brand); outline-offset: -2px;
}
textarea {
  width: 100%; min-height: 10em;
  font: 0.92em/1.45 ui-monospace, Menlo, Consolas, monospace;
  padding: 0.7em; border: 1px solid var(--fc-border);
  border-radius: 4px; resize: vertical;
}
.status {
  font-size: 0.9em; color: var(--fc-muted);
  padding: 0.3em 0.6em;
  background: var(--fc-surface); border-radius: 4px;
}
.status.ok  { color: var(--fc-ok); }
.status.err { color: var(--fc-error); }
.out { margin-top: 1em; }
.out.empty {
  color: var(--fc-muted); padding: 1em; text-align: center;
  background: var(--fc-surface); border-radius: 4px;
}
.out.error { color: var(--fc-error); }
table.results {
  border-collapse: collapse; width: 100%; font-size: 0.92em;
}
table.results th, table.results td {
  border: 1px solid var(--fc-border); padding: 0.3em 0.6em;
  vertical-align: top; text-align: left;
}
table.results th {
  background: var(--fc-surface); font-weight: 600;
  position: relative; user-select: none;
}
table.results th .col-menu-btn {
  float: right; border: none; background: transparent; color: var(--fc-muted);
  cursor: pointer; padding: 0 0.3em; margin-left: 0.4em;
  font-weight: 700; font-size: 1em; border-radius: 2px;
}
table.results th .col-menu-btn:hover { background: var(--fc-border); color: var(--fc-fg); }
table.results td {
  font-family: ui-monospace, Menlo, Consolas, monospace;
}
table.results td.num  { text-align: right; font-variant-numeric: tabular-nums; }
table.results td.date { white-space: nowrap; color: var(--fc-fg); }
table.results th.num  { text-align: right; }
.view-tabs {
  display: inline-flex; border: 1px solid var(--fc-border); border-radius: 4px;
  overflow: hidden; background: var(--fc-bg); margin-right: 0.5em;
}
.view-tabs button {
  background: transparent; color: var(--fc-fg); font-weight: 500;
  border: 0; border-radius: 0; padding: 0.3em 0.7em;
  font-size: 0.88em; cursor: pointer;
}
.view-tabs button + button { border-left: 1px solid var(--fc-border); }
.view-tabs button.active {
  background: var(--fc-brand); color: #fff; font-weight: 600;
}
.download-links {
  display: inline-flex; gap: 0.4em; font-size: 0.85em;
  color: var(--fc-muted); align-items: center;
}
.download-links a {
  color: var(--fc-brand-dark); text-decoration: none;
  padding: 0.15em 0.5em; border: 1px solid var(--fc-border);
  border-radius: 3px; background: var(--fc-bg);
}
.download-links a:hover { background: var(--fc-surface); }
.hidden-cols-note {
  display: inline-block; margin-left: 0.5em; font-size: 0.85em;
  color: var(--fc-muted);
}
.hidden-cols-note a {
  color: var(--fc-brand-dark); cursor: pointer; text-decoration: underline;
}
pre.raw-json {
  background: var(--fc-surface); border: 1px solid var(--fc-border);
  padding: 0.8em; border-radius: 4px; white-space: pre-wrap;
  word-break: break-word; max-height: 32em; overflow: auto;
  font: 0.85em/1.4 ui-monospace, Menlo, Consolas, monospace;
}
pre.raw-csv {
  background: var(--fc-surface); border: 1px solid var(--fc-border);
  padding: 0.8em; border-radius: 4px; white-space: pre;
  overflow: auto; max-height: 32em;
  font: 0.85em/1.4 ui-monospace, Menlo, Consolas, monospace;
}
.result-meta {
  margin-top: 0.5em; color: var(--fc-muted); font-size: 0.85em;
}
.timing-summary {
  margin-top: 0.4em; color: var(--fc-muted); font-size: 0.85em;
}
.timing-summary .num {
  font-variant-numeric: tabular-nums; font-weight: 600;
  color: var(--fc-fg);
}
.timing-detail { font-size: 0.88em; color: var(--fc-muted); }
.timing-detail .timing-head {
  font-weight: 600; color: var(--fc-fg); margin-bottom: 0.4em;
}
.timing-detail ul {
  list-style: none; margin: 0.2em 0 0; padding: 0;
  display: grid; grid-template-columns: auto 1fr auto;
  gap: 0.15em 0.8em; align-items: baseline;
}
.timing-detail ul li { display: contents; }
.timing-detail .tl { color: var(--fc-fg); }
.timing-detail .tr {
  font-variant-numeric: tabular-nums; text-align: right;
}
.timing-detail .bar {
  background: var(--fc-brand); height: 0.55em;
  border-radius: 2px; align-self: center; min-width: 2px;
}
.timing-detail .bar.cached {
  background: var(--fc-border); height: 0.35em;
}
@keyframes progressStripe {
  0%   { background-position: 0 0; }
  100% { background-position: 48px 0; }
}
.out.running {
  color: var(--fc-fg); background: var(--fc-surface);
  border: 1px solid var(--fc-border); border-radius: 4px;
  padding: 2em 1em; text-align: center;
  position: relative; overflow: hidden;
}
.out.running .progress-bar {
  height: 8px; border-radius: 4px; margin: 0.6em auto 0;
  max-width: 420px;
  background-image: linear-gradient(
    45deg,
    var(--fc-brand) 25%, var(--fc-brand-dark) 25%,
    var(--fc-brand-dark) 50%, var(--fc-brand) 50%,
    var(--fc-brand) 75%, var(--fc-brand-dark) 75%
  );
  background-size: 24px 24px;
  animation: progressStripe 0.6s linear infinite;
}
.out.running .progress-label { font-weight: 600; font-size: 1.05em; }
.out.running .progress-sub {
  font-size: 0.85em; color: var(--fc-muted); margin-top: 0.2em;
}
pre.raw-error {
  background: #fff6f4; border: 1px solid #f0c0c0; padding: 0.8em;
  border-radius: 4px; white-space: pre-wrap; word-break: break-word;
}
details { margin-top: 1em; }
summary { cursor: pointer; color: var(--fc-muted); font-size: 0.9em; }
`;

// ---------------------------------------------------------------------
// Helpers: IRI abbreviation, binding render, format helpers. Ported
// verbatim from demo-lifesci.html (with prefix set configurable later).
// ---------------------------------------------------------------------
const DEFAULT_PREFIXES = [
  ['http://www.w3.org/1999/02/22-rdf-syntax-ns#', 'rdf:'],
  ['http://www.w3.org/2000/01/rdf-schema#',       'rdfs:'],
  ['http://www.w3.org/2001/XMLSchema#',           'xsd:'],
  ['http://www.wikidata.org/entity/',             'wd:'],
  ['http://www.wikidata.org/prop/direct/',        'wdt:'],
  ['https://bioschemas.org/',                     'bio:'],
  ['https://schema.org/',                         'schema:'],
];

function abbrev(iri) {
  for (const [ns, px] of DEFAULT_PREFIXES) {
    if (iri.startsWith(ns)) return px + iri.slice(ns.length);
  }
  return '<' + iri + '>';
}

function formatMs(ms) {
  if (ms == null) return '—';
  if (ms < 1) return '<1 ms';
  if (ms < 1000) return ms.toFixed(0) + ' ms';
  return (ms / 1000).toFixed(2) + ' s';
}
function formatBytes(n) {
  if (n == null) return '';
  if (n < 1024) return n + ' B';
  if (n < 1024 * 1024) return (n / 1024).toFixed(1) + ' KB';
  return (n / (1024 * 1024)).toFixed(2) + ' MB';
}

// ---------------------------------------------------------------------
// TriG-merge: the WASM path only accepts a single data string, so when
// we have multiple named-graph TTL files we fold them into a TriG doc.
// Pull @prefix/@base/PREFIX/BASE to the top (dedup'd), wrap remainder
// in GRAPH <iri> { ... }.
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Result serialization helpers. These operate on the JSON result
// object already produced by the F* engine (via -o json or
// browser-wasm.js). They do NOT interpret RDF semantics — they just
// reformat whatever the engine serialized. Per CLAUDE.md rule #10,
// anything semantic must live in F*.
// ---------------------------------------------------------------------

// Classify xsd datatype IRIs into UI hints (numeric / date / plain).
// We do not coerce values or do arithmetic — this is a *rendering*
// hint only (right-align numbers, show date in a readable format).
const NUMERIC_XSD = new Set([
  'http://www.w3.org/2001/XMLSchema#integer',
  'http://www.w3.org/2001/XMLSchema#decimal',
  'http://www.w3.org/2001/XMLSchema#double',
  'http://www.w3.org/2001/XMLSchema#float',
  'http://www.w3.org/2001/XMLSchema#long',
  'http://www.w3.org/2001/XMLSchema#int',
  'http://www.w3.org/2001/XMLSchema#short',
  'http://www.w3.org/2001/XMLSchema#byte',
  'http://www.w3.org/2001/XMLSchema#nonNegativeInteger',
  'http://www.w3.org/2001/XMLSchema#positiveInteger',
  'http://www.w3.org/2001/XMLSchema#nonPositiveInteger',
  'http://www.w3.org/2001/XMLSchema#negativeInteger',
  'http://www.w3.org/2001/XMLSchema#unsignedLong',
  'http://www.w3.org/2001/XMLSchema#unsignedInt',
  'http://www.w3.org/2001/XMLSchema#unsignedShort',
  'http://www.w3.org/2001/XMLSchema#unsignedByte',
]);
const DATE_XSD = new Set([
  'http://www.w3.org/2001/XMLSchema#date',
  'http://www.w3.org/2001/XMLSchema#dateTime',
  'http://www.w3.org/2001/XMLSchema#dateTimeStamp',
  'http://www.w3.org/2001/XMLSchema#gYear',
  'http://www.w3.org/2001/XMLSchema#gYearMonth',
]);

function bindingKind(b) {
  if (!b) return 'empty';
  if (b.type === 'uri')  return 'uri';
  if (b.type === 'bnode') return 'bnode';
  // literal
  const dt = b.datatype;
  if (dt && NUMERIC_XSD.has(dt)) return 'num';
  if (dt && DATE_XSD.has(dt))    return 'date';
  return 'literal';
}

// Majority kind across non-empty cells in a column — used to decide
// th/td alignment classes. Majority, not "all", so mixed columns with
// occasional nulls still line up.
function inferColumnKind(bindings, varName) {
  const counts = { num: 0, date: 0, uri: 0, literal: 0, bnode: 0 };
  let total = 0;
  for (const row of bindings) {
    const b = row[varName];
    if (!b) continue;
    total++;
    counts[bindingKind(b)] = (counts[bindingKind(b)] || 0) + 1;
  }
  if (!total) return 'empty';
  let best = 'literal', bestN = -1;
  for (const k of Object.keys(counts)) {
    if (counts[k] > bestN) { best = k; bestN = counts[k]; }
  }
  return best;
}

// Render xsd:dateTime / xsd:date etc. in a slightly more human form.
// Keep the raw ISO string on title= so copy-paste still works.
function prettyDate(v) {
  // xsd:gYear just "2024" — leave alone.
  if (/^[+-]?\d{4}$/.test(v)) return v;
  // xsd:gYearMonth "2024-03" — leave alone.
  if (/^[+-]?\d{4}-\d{2}$/.test(v)) return v;
  // Full date or dateTime. Use Date.parse; if browser can't, return as-is.
  const t = Date.parse(v);
  if (isNaN(t)) return v;
  // Show YYYY-MM-DD for pure dates; YYYY-MM-DD HH:MM(:SS) for dateTimes.
  if (/^\d{4}-\d{2}-\d{2}$/.test(v)) {
    return v;
  }
  try {
    const d = new Date(t);
    const iso = d.toISOString();
    return iso.slice(0, 19).replace('T', ' ') + 'Z';
  } catch (_) { return v; }
}

// ----- Flat-string serializers for CSV/TSV (W3C "SPARQL 1.1 Query
// Results CSV and TSV Formats"-shaped, minus the strict escaping rules
// which must ultimately come from F*. These are *client-side only*,
// used for the "Copy as CSV" / "Download CSV" UI affordance; they do
// not replace the engine's -o csv output which is the canonical form
// once implemented.) -----
function csvEscape(s) {
  if (s == null) return '';
  const needsQ = /[,"\r\n]/.test(s);
  const esc = s.replace(/"/g, '""');
  return needsQ ? '"' + esc + '"' : esc;
}
// Flat-string rendering of a binding for delimited output. The W3C
// "SPARQL 1.1 Query Results CSV Format" is lossy (datatype + lang
// info dropped); the TSV format preserves them in N-Triples-ish
// syntax. We follow those conventions here.
function bindingToCSVString(b) {
  if (!b) return '';
  if (b.type === 'uri')   return b.value;
  if (b.type === 'bnode') return '_:' + b.value;
  // literal: lexical form only, per W3C CSV spec.
  return b.value;
}
function bindingToTSVString(b) {
  if (!b) return '';
  if (b.type === 'uri')   return '<' + b.value + '>';
  if (b.type === 'bnode') return '_:' + b.value;
  // literal: N-Triples-ish (quoted lexical form + optional lang/dt).
  const esc = '"' + b.value.replace(/\\/g, '\\\\').replace(/"/g, '\\"')
                          .replace(/\t/g, '\\t').replace(/\r/g, '\\r')
                          .replace(/\n/g, '\\n') + '"';
  if (b['xml:lang']) return esc + '@' + b['xml:lang'];
  if (b.datatype && b.datatype !== 'http://www.w3.org/2001/XMLSchema#string') {
    return esc + '^^<' + b.datatype + '>';
  }
  return esc;
}
function resultsToCSV(json) {
  if (typeof json.boolean === 'boolean') return 'boolean\r\n' + json.boolean + '\r\n';
  const vars = (json.head && json.head.vars) || [];
  const bindings = (json.results && json.results.bindings) || [];
  const out = [];
  out.push(vars.map(csvEscape).join(','));
  bindings.forEach(row => {
    out.push(vars.map(v => csvEscape(bindingToCSVString(row[v]))).join(','));
  });
  return out.join('\r\n') + '\r\n';
}
function resultsToTSV(json) {
  if (typeof json.boolean === 'boolean') return '?boolean\n' + json.boolean + '\n';
  const vars = (json.head && json.head.vars) || [];
  const bindings = (json.results && json.results.bindings) || [];
  const out = [];
  out.push(vars.map(v => '?' + v).join('\t'));
  bindings.forEach(row => {
    // bindingToTSVString already N-Triples-escapes literals; URIs are
    // angle-wrapped and contain no tabs. No further escaping needed.
    out.push(vars.map(v => bindingToTSVString(row[v])).join('\t'));
  });
  return out.join('\n') + '\n';
}

function payloadsToTriG(payloads) {
  const directives = new Set();
  const blocks = [];
  const dirRE = /^\s*(?:@prefix|@base|PREFIX|BASE)\b[^\n]*\.\s*$/i;
  payloads.forEach(p => {
    const bodyLines = [];
    p.content.split(/\r?\n/).forEach(line => {
      if (dirRE.test(line)) directives.add(line.trim());
      else bodyLines.push(line);
    });
    // Payloads without a declared named-graph IRI drop into the
    // default graph (bare braces in TriG — the triples section before
    // any GRAPH block). This matches the `-d` fallback on the JS
    // engine path.
    if (p.graph) {
      blocks.push(
        'GRAPH <' + p.graph + '> {\n' +
        bodyLines.join('\n') +
        '\n}\n'
      );
    } else {
      blocks.push(bodyLines.join('\n') + '\n');
    }
  });
  return [...directives].join('\n') + '\n\n' + blocks.join('\n');
}

// ---------------------------------------------------------------------
// Main orchestrator element.
// ---------------------------------------------------------------------
class FactoidalSparqlClient extends HTMLElement {

  static get observedAttributes() {
    return ['src-data', 'engines', 'default-engine',
            'logics', 'default-logic', 'entail',
            'js-url', 'wasm-url', 'queries', 'warm'];
  }

  constructor() {
    super();

    this._shadow = this.attachShadow({ mode: 'open' });

    // Internal state
    this._filePayloads = null;
    this._fileTimings  = {};        // { url: { ms, bytes, cached } }
    this._engineSources = { js: null, wasm: null };
    this._enginePromises = { js: null, wasm: null };
    this._engineTimings  = { js: null, wasm: null };
    this._queries = [];
    this._queriesFromProp = null;   // queries set via JS property
    this._rendered = false;

    // Results state (view selector + hidden columns). Populated by
    // _renderResultsJSON and consumed by _refreshResultsTable so users
    // can switch views and hide/show columns without re-running.
    this._lastJson = null;          // last results JSON payload
    this._viewMode = 'table';       // one of: table | json | csv | tsv
    this._hiddenCols = new Set();

    // Bind so we can attach/detach by identity
    this._onRunClick = this._onRunClick.bind(this);
    this._onQueryChange = this._onQueryChange.bind(this);
    this._onQueryKeydown = this._onQueryKeydown.bind(this);
  }

  // -----------------------------------------------------------------
  // Attribute / property plumbing
  // -----------------------------------------------------------------
  attributeChangedCallback(name, _oldv, _newv) {
    if (!this._rendered) return;
    // For most attributes, a simple full re-sync of UI is fine.
    if (name === 'queries' || name === 'src-data'
        || name === 'engines' || name === 'default-engine') {
      this._syncFromAttributes();
      this._renderQueryList();
      this._renderEngineToggle();
    }
    if (name === 'logics' || name === 'default-logic' || name === 'entail') {
      this._renderLogicToggle();
    }
  }

  get queries() {
    return this._queriesFromProp || this._queries.slice();
  }
  set queries(v) {
    this._queriesFromProp = Array.isArray(v) ? v : null;
    if (this._rendered) {
      this._syncFromAttributes();
      this._renderQueryList();
    }
  }

  get srcData() {
    try {
      const raw = this.getAttribute('src-data');
      return raw ? JSON.parse(raw) : [];
    } catch (e) { return []; }
  }
  set srcData(v) {
    if (Array.isArray(v)) {
      this.setAttribute('src-data', JSON.stringify(v));
    }
  }

  get engines() {
    const raw = (this.getAttribute('engines') || 'js,wasm').toLowerCase();
    return raw.split(',').map(s => s.trim()).filter(Boolean);
  }

  get defaultEngine() {
    const e = (this.getAttribute('default-engine') || 'js').toLowerCase();
    return this.engines.includes(e) ? e : this.engines[0] || 'js';
  }

  // Entailment regime ("Logic") — runtime-switchable radio, parallel to
  // the engine picker. `logics` lists the options to show; if omitted
  // we offer the full set (none / RDFS / OWL-RL). `default-logic` picks
  // the initial selection; legacy `entail` attribute is accepted as a
  // back-compat synonym for `default-logic`.
  get logics() {
    const raw = this.getAttribute('logics');
    if (raw) {
      return raw.split(',').map(s => s.trim()).filter(Boolean);
    }
    return ['none', 'RDFS', 'OWL-RL'];
  }

  get defaultLogic() {
    const raw = (this.getAttribute('default-logic')
              || this.getAttribute('entail')
              || 'none');
    const opts = this.logics;
    // Normalise: case-insensitive lookup, fallback to first option.
    const hit = opts.find(o => o.toLowerCase() === raw.toLowerCase());
    return hit || opts[0] || 'none';
  }

  // Kept for back-compat with early callers that read `entail` as a
  // static setting. Returns the currently-selected Logic radio value
  // when the UI has been rendered; otherwise falls back to the
  // attribute-derived default.
  get entail() {
    if (this._logicBox) {
      const r = this._logicBox.querySelector('input[name="fc-logic"]:checked');
      if (r) return r.value;
    }
    return this.defaultLogic;
  }

  get jsUrl() {
    return this.getAttribute('js-url') || './factoidal.js';
  }
  get wasmUrl() {
    return this.getAttribute('wasm-url') || './factoidal.wasm.js';
  }

  // Called by <factoidal-query> children on connect.
  _queriesChanged() {
    if (!this._rendered) return;
    this._syncFromAttributes();
    this._renderQueryList();
  }

  _syncFromAttributes() {
    // Merge queries from: JS property, `queries` attr, light-DOM children.
    const fromProp = this._queriesFromProp;
    let fromAttr = [];
    try {
      const raw = this.getAttribute('queries');
      if (raw) fromAttr = JSON.parse(raw);
    } catch (e) { /* ignore malformed */ }

    const fromChildren = [];
    this.querySelectorAll('factoidal-query').forEach(el => {
      const key = el.getAttribute('name') || el.getAttribute('key');
      if (!key) return;
      fromChildren.push({
        key,
        label: el.getAttribute('label') || key,
        body: (el.textContent || '').trim() + '\n',
      });
    });

    // Precedence: light-DOM children > property > attribute.
    const byKey = new Map();
    (fromAttr || []).forEach(q => { if (q && q.key) byKey.set(q.key, q); });
    (fromProp || []).forEach(q => { if (q && q.key) byKey.set(q.key, q); });
    fromChildren.forEach(q => byKey.set(q.key, q));
    this._queries = [...byKey.values()];
  }

  // -----------------------------------------------------------------
  // Lifecycle
  // -----------------------------------------------------------------
  connectedCallback() {
    if (this._rendered) return;
    this._rendered = true;
    this._syncFromAttributes();
    this._build();

    if (this.hasAttribute('warm')) this._warm();
  }

  _warm() {
    this._getFilePayloads().catch(() => {});
    if (this.engines.includes('js'))   this._getEngineSource('js').catch(() => {});
    if (this.engines.includes('wasm')) this._getEngineSource('wasm').catch(() => {});
  }

  // -----------------------------------------------------------------
  // DOM construction
  // -----------------------------------------------------------------
  _build() {
    const style = document.createElement('style');
    style.textContent = STYLES;
    this._shadow.appendChild(style);

    // Status / control row
    const row1 = document.createElement('div');
    row1.className = 'row';

    const lbl = document.createElement('label');
    lbl.htmlFor = 'fc-query-select';
    lbl.textContent = 'Query';
    row1.appendChild(lbl);

    this._querySelect = document.createElement('select');
    this._querySelect.id = 'fc-query-select';
    this._querySelect.setAttribute('part', 'query-select');
    this._querySelect.addEventListener('change', this._onQueryChange);
    row1.appendChild(this._querySelect);

    this._runBtn = document.createElement('button');
    this._runBtn.type = 'button';
    this._runBtn.className = 'run-btn';
    this._runBtn.textContent = 'Run';
    this._runBtn.setAttribute('part', 'run-button');
    this._runBtn.addEventListener('click', this._onRunClick);
    row1.appendChild(this._runBtn);

    this._engineBox = document.createElement('span');
    this._engineBox.className = 'radio-group';
    this._engineBox.setAttribute('role', 'radiogroup');
    this._engineBox.setAttribute('aria-label', 'Engine');
    row1.appendChild(this._engineBox);

    this._logicBox = document.createElement('span');
    this._logicBox.className = 'radio-group';
    this._logicBox.setAttribute('role', 'radiogroup');
    this._logicBox.setAttribute('aria-label', 'Logic (entailment regime)');
    row1.appendChild(this._logicBox);

    this._statusEl = document.createElement('span');
    this._statusEl.className = 'status';
    this._statusEl.setAttribute('part', 'status');
    this._statusEl.textContent = 'Loading engine…';
    row1.appendChild(this._statusEl);

    this._shadow.appendChild(row1);

    // Query textarea
    this._queryEl = document.createElement('textarea');
    this._queryEl.setAttribute('part', 'query-editor');
    this._queryEl.id = 'fc-query';
    this._queryEl.setAttribute('spellcheck', 'false');
    this._queryEl.setAttribute('autocapitalize', 'off');
    this._queryEl.setAttribute('autocorrect', 'off');
    this._queryEl.addEventListener('keydown', this._onQueryKeydown);
    this._queryEl.title =
      'Ctrl+Enter (Cmd+Enter on macOS) to run. Shift+Enter for newline.';
    this._shadow.appendChild(this._queryEl);

    // Output region
    this._outEl = document.createElement('div');
    this._outEl.className = 'out empty';
    this._outEl.setAttribute('part', 'results');
    this._outEl.textContent = 'Pick a query and click Run.';
    this._shadow.appendChild(this._outEl);

    // Details / timing breakdown
    this._detailsBlock = document.createElement('details');
    const summary = document.createElement('summary');
    summary.textContent = 'Details';
    this._detailsBlock.appendChild(summary);
    this._timingDetails = document.createElement('div');
    this._timingDetails.setAttribute('part', 'timing-detail');
    this._timingDetails.textContent = 'No query has run yet.';
    this._detailsBlock.appendChild(this._timingDetails);
    this._shadow.appendChild(this._detailsBlock);

    this._renderQueryList();
    this._renderEngineToggle();
    this._renderLogicToggle();
    this._statusEl.textContent = 'Ready (engines will load on first run).';
    this._statusEl.className = 'status ok';
  }

  _renderQueryList() {
    if (!this._querySelect) return;
    const prevKey = this._querySelect.value;

    // Sort by leading "NN — " if present, then alphabetical.
    const sorted = this._queries.slice().sort((a, b) => {
      const na = /^(\d+)/.exec(a.label || '');
      const nb = /^(\d+)/.exec(b.label || '');
      if (na && nb) return parseInt(na[1], 10) - parseInt(nb[1], 10);
      if (na) return -1;
      if (nb) return 1;
      return (a.label || '').localeCompare(b.label || '');
    });

    this._querySelect.innerHTML = '';
    sorted.forEach(q => {
      const opt = document.createElement('option');
      opt.value = q.key;
      opt.textContent = q.label || q.key;
      this._querySelect.appendChild(opt);
    });

    if (sorted.length) {
      const k = sorted.some(q => q.key === prevKey) ? prevKey : sorted[0].key;
      this._querySelect.value = k;
      this._loadQuery();
    } else {
      this._queryEl.value = '';
    }
  }

  _renderEngineToggle() {
    const engines = this.engines;
    const def = this.defaultEngine;
    this._engineBox.innerHTML = '';

    // If only one engine, still render a single label for clarity.
    engines.forEach(e => {
      const label = document.createElement('label');
      label.title = e === 'wasm'
        ? 'wasm_of_ocaml — needs Wasm-GC (Chrome/Edge 119+, Node 22+)'
        : 'js_of_ocaml — widest browser support';
      const input = document.createElement('input');
      input.type = 'radio';
      input.name = 'fc-engine';
      input.value = e;
      input.checked = (e === def);
      const span = document.createElement('span');
      span.textContent = e.toUpperCase();
      label.appendChild(input);
      label.appendChild(span);
      this._engineBox.appendChild(label);
    });
  }

  _currentEngine() {
    const r = this._engineBox.querySelector('input[name="fc-engine"]:checked');
    return r ? r.value : this.defaultEngine;
  }

  _renderLogicToggle() {
    if (!this._logicBox) return;
    const logics = this.logics;
    const def = this.defaultLogic;
    this._logicBox.innerHTML = '';

    // Label prefix — "Logic:" before the radios so screen readers and
    // sighted users both see what this row of buttons is for.
    const lab = document.createElement('span');
    lab.className = 'radio-group-label';
    lab.textContent = 'Logic:';
    lab.setAttribute('aria-hidden', 'true');
    this._logicBox.appendChild(lab);

    logics.forEach(l => {
      const label = document.createElement('label');
      label.title =
        l === 'RDFS'   ? 'RDFS entailment closure + reflexivity axioms'
      : l === 'OWL-RL' ? 'OWL 2 RL Datalog subset (includes RDFS)'
      :                  'No entailment — query the raw data';
      const input = document.createElement('input');
      input.type = 'radio';
      input.name = 'fc-logic';
      input.value = l;
      input.checked = (l === def);
      const span = document.createElement('span');
      // "none" → "None" for display; keep RDFS / OWL-RL as-is.
      span.textContent = l === 'none' ? 'None' : l;
      label.appendChild(input);
      label.appendChild(span);
      this._logicBox.appendChild(label);
    });
  }

  _onQueryChange() {
    this._loadQuery();
  }

  _onQueryKeydown(ev) {
    // Ctrl+Enter / Cmd+Enter from inside the textarea → run.
    // Plain Enter still inserts a newline (default behaviour).
    if (ev.key === 'Enter' && (ev.ctrlKey || ev.metaKey)) {
      ev.preventDefault();
      if (!this._runBtn.disabled) this._runBtn.click();
    }
  }

  _loadQuery() {
    const k = this._querySelect.value;
    const q = this._queries.find(x => x.key === k) || this._queries[0];
    this._queryEl.value = q ? q.body : '';
  }

  // -----------------------------------------------------------------
  // Fetch + cache: data files
  // -----------------------------------------------------------------
  async _getFilePayloads() {
    const files = this.srcData;
    // Assign a default VFS path per file if one isn't specified.
    files.forEach((f, i) => {
      if (!f.vfs) {
        // /tmp/file-0.ttl style; safe default for jsoo_fs_tmp.
        const urlBase = (f.url || '').split('/').pop() || ('file-' + i + '.ttl');
        f.vfs = '/tmp/' + urlBase;
      }
    });
    if (this._filePayloads) {
      this._filePayloads.forEach(p => {
        this._fileTimings[p.url] = { ...this._fileTimings[p.url], cached: true };
      });
      return this._filePayloads;
    }
    const results = await Promise.all(files.map(async f => {
      const t0 = performance.now();
      const r = await fetch(f.url);
      if (!r.ok) throw new Error('fetch ' + f.url + ': ' + r.status);
      const content = await r.text();
      this._fileTimings[f.url] = {
        ms: performance.now() - t0,
        bytes: content.length,
        cached: false,
      };
      return { ...f, content };
    }));
    this._filePayloads = results;
    return results;
  }

  // -----------------------------------------------------------------
  // Fetch + cache: engine source bundles (js and/or wasm loader text)
  // -----------------------------------------------------------------
  _getEngineSource(which) {
    if (this._engineSources[which]) {
      if (this._engineTimings[which]) this._engineTimings[which].cached = true;
      return Promise.resolve(this._engineSources[which]);
    }
    if (this._enginePromises[which]) return this._enginePromises[which];
    const url = which === 'wasm' ? this.wasmUrl : this.jsUrl;
    const t0 = performance.now();
    this._enginePromises[which] = fetch(url)
      .then(r => {
        if (!r.ok) throw new Error('fetch ' + url + ': ' + r.status);
        return r.text();
      })
      .then(t => {
        this._engineSources[which] = t;
        this._engineTimings[which] = {
          ms: performance.now() - t0,
          bytes: t.length,
          cached: false,
        };
        return t;
      });
    return this._enginePromises[which];
  }

  // -----------------------------------------------------------------
  // Results rendering
  // -----------------------------------------------------------------
  _renderBinding(b) {
    const td = document.createElement('td');
    if (!b) { td.textContent = ''; return td; }
    if (b.type === 'uri') {
      const a = document.createElement('a');
      a.href = b.value; a.target = '_blank'; a.rel = 'noopener';
      a.textContent = abbrev(b.value);
      td.appendChild(a);
    } else {
      td.textContent = b.value;
      if (b['xml:lang']) td.textContent += '@' + b['xml:lang'];
      else if (b.datatype && b.datatype !== 'http://www.w3.org/2001/XMLSchema#string') {
        td.textContent += '  ^^' + abbrev(b.datatype);
      }
    }
    return td;
  }

  _renderResultsJSON(json) {
    // Cache json + reset column-visibility state; then render whichever
    // view is currently selected.
    this._lastJson = json;
    this._hiddenCols = new Set();
    this._refreshResultsView();
  }

  // Re-render the results area from cached JSON using _viewMode and
  // _hiddenCols. No engine run; this is a cheap DOM rebuild so view
  // switches feel instant.
  _refreshResultsView() {
    const json = this._lastJson;
    this._outEl.className = 'out';
    this._outEl.innerHTML = '';
    if (!json) {
      this._outEl.className = 'out empty';
      this._outEl.textContent = 'Pick a query and click Run.';
      return;
    }

    // View selector + download bar sit above the rendered body.
    this._outEl.appendChild(this._renderViewTabs());
    this._outEl.appendChild(this._renderDownloadBar(json));

    if (typeof json.boolean === 'boolean') {
      const body = document.createElement('div');
      body.style.marginTop = '0.6em';
      body.textContent = json.boolean ? 'Yes' : 'No';
      this._outEl.appendChild(body);
      return;
    }

    const vars = (json.head && json.head.vars) || [];
    const bindings = (json.results && json.results.bindings) || [];

    switch (this._viewMode) {
      case 'json':
        this._outEl.appendChild(this._renderJSONView(json));
        break;
      case 'csv':
        this._outEl.appendChild(this._renderDelimView(resultsToCSV(json)));
        break;
      case 'tsv':
        this._outEl.appendChild(this._renderDelimView(resultsToTSV(json)));
        break;
      case 'table':
      default:
        this._outEl.appendChild(this._renderTableView(vars, bindings));
        break;
    }

    const meta = document.createElement('div');
    meta.className = 'result-meta';
    meta.textContent = bindings.length + ' result' + (bindings.length === 1 ? '' : 's');
    if (this._lastTimingSummary && this._lastTimingSummary.html) {
      // Re-attach the previously-rendered timing summary so view
      // switches don't lose it.
      const tpl = document.createElement('template');
      tpl.innerHTML = this._lastTimingSummary.html;
      if (tpl.content.firstChild) meta.appendChild(tpl.content.firstChild);
    }
    this._outEl.appendChild(meta);
  }

  _renderTableView(vars, bindings) {
    const frag = document.createDocumentFragment();
    const visibleVars = vars.filter(v => !this._hiddenCols.has(v));
    // Per-column kind inference, used for th/td alignment classes and
    // for a lightweight "humanize" of xsd:date/dateTime.
    const kinds = {};
    visibleVars.forEach(v => { kinds[v] = inferColumnKind(bindings, v); });

    const table = document.createElement('table');
    table.className = 'results';
    table.setAttribute('part', 'results-table');

    const thead = document.createElement('thead');
    const hrow = document.createElement('tr');
    visibleVars.forEach(v => {
      const th = document.createElement('th');
      const k = kinds[v];
      if (k === 'num') th.classList.add('num');
      th.dataset.kind = k;
      const label = document.createElement('span');
      label.textContent = '?' + v;
      th.appendChild(label);
      // Wikidata-query-results-style per-column menu (hide for now;
      // extensible later for sort/filter).
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'col-menu-btn';
      btn.title = 'Hide column ?' + v;
      btn.setAttribute('aria-label', 'Hide column ?' + v);
      btn.textContent = 'x';
      btn.addEventListener('click', (ev) => {
        ev.stopPropagation();
        this._hiddenCols.add(v);
        this._refreshResultsView();
      });
      th.appendChild(btn);
      hrow.appendChild(th);
    });
    thead.appendChild(hrow);
    table.appendChild(thead);

    const tbody = document.createElement('tbody');
    bindings.forEach(row => {
      const tr = document.createElement('tr');
      visibleVars.forEach(v => {
        const td = this._renderBinding(row[v]);
        const k = bindingKind(row[v]);
        if (k === 'num' && row[v]) {
          // Strip the datatype suffix the default renderer adds;
          // the column header already implies it and right-align
          // + tabular-nums makes the type visually clear.
          td.classList.add('num');
          td.title = 'xsd:' + (row[v].datatype || '').split('#').pop();
          td.textContent = row[v].value;
        }
        if (k === 'date' && row[v]) {
          td.classList.add('date');
          td.title = row[v].value;
          td.textContent = prettyDate(row[v].value);
        }
        tr.appendChild(td);
      });
      tbody.appendChild(tr);
    });
    table.appendChild(tbody);
    frag.appendChild(table);

    if (this._hiddenCols.size) {
      const note = document.createElement('div');
      note.className = 'hidden-cols-note';
      const hidden = [...this._hiddenCols].map(v => '?' + v).join(', ');
      note.textContent = 'Hidden: ' + hidden + ' ';
      const unhide = document.createElement('a');
      unhide.textContent = '(show all)';
      unhide.addEventListener('click', () => {
        this._hiddenCols = new Set();
        this._refreshResultsView();
      });
      note.appendChild(unhide);
      frag.appendChild(note);
    }
    return frag;
  }

  _renderJSONView(json) {
    const pre = document.createElement('pre');
    pre.className = 'raw-json';
    pre.textContent = JSON.stringify(json, null, 2);
    return pre;
  }

  _renderDelimView(text) {
    const pre = document.createElement('pre');
    pre.className = 'raw-csv';
    pre.textContent = text;
    return pre;
  }

  _renderViewTabs() {
    const box = document.createElement('span');
    box.className = 'view-tabs';
    box.setAttribute('part', 'view-tabs');
    box.setAttribute('role', 'tablist');
    const modes = [
      ['table', 'Table'],
      ['json',  'JSON'],
      ['csv',   'CSV'],
      ['tsv',   'TSV'],
    ];
    modes.forEach(([mode, label]) => {
      const b = document.createElement('button');
      b.type = 'button';
      b.textContent = label;
      b.setAttribute('role', 'tab');
      b.setAttribute('aria-selected', String(this._viewMode === mode));
      if (this._viewMode === mode) b.classList.add('active');
      b.addEventListener('click', () => {
        this._viewMode = mode;
        this._refreshResultsView();
      });
      box.appendChild(b);
    });
    return box;
  }

  _renderDownloadBar(json) {
    const wrap = document.createElement('span');
    wrap.className = 'download-links';
    const base = 'factoidal-results';
    const dl = (label, text, mime, ext) => {
      const a = document.createElement('a');
      a.textContent = label;
      a.download = base + '.' + ext;
      const blob = new Blob([text], { type: mime });
      a.href = URL.createObjectURL(blob);
      return a;
    };
    const jsonText = JSON.stringify(json, null, 2);
    wrap.appendChild(document.createTextNode('Download:'));
    wrap.appendChild(dl('JSON', jsonText, 'application/sparql-results+json', 'json'));
    wrap.appendChild(dl('CSV',  resultsToCSV(json), 'text/csv', 'csv'));
    wrap.appendChild(dl('TSV',  resultsToTSV(json), 'text/tab-separated-values', 'tsv'));
    return wrap;
  }

  _renderRawError(text) {
    this._outEl.className = 'out error';
    this._outEl.innerHTML = '';
    const pre = document.createElement('pre');
    pre.className = 'raw-error';
    pre.textContent = text;
    this._outEl.appendChild(pre);
  }

  _buildPhases(engineName, runMs) {
    const out = [];
    const es = this._engineTimings[engineName];
    out.push({
      label: 'Engine bundle (' + engineName + ')',
      ms:     es ? es.ms : 0,
      bytes:  es ? es.bytes : null,
      cached: es ? es.cached : true,
    });
    (this.srcData || []).forEach(f => {
      const t = this._fileTimings[f.url];
      const name = (f.url || '').split('/').pop();
      out.push({
        label: 'Fetch ' + name,
        ms:     t ? t.ms : 0,
        bytes:  t ? t.bytes : null,
        cached: t ? t.cached : true,
      });
    });
    out.push({ label: 'Query run (parse + eval + serialize)', ms: runMs });
    return out;
  }

  _renderTimingSummary(totalMs, engineName, runMs) {
    const el = document.createElement('div');
    el.className = 'timing-summary';
    el.innerHTML =
      'Done on ' + engineName.toUpperCase()
      + ' — query <span class="num">' + formatMs(runMs) + '</span>'
      + ', total <span class="num">' + formatMs(totalMs) + '</span>';
    return el;
  }

  _renderTimingDetail(totalMs, engineName, runMs, phases) {
    const fallback = Math.max(totalMs, 1);
    const el = document.createElement('div');
    el.className = 'timing-detail';
    const head = document.createElement('div');
    head.className = 'timing-head';
    head.textContent = formatMs(totalMs) + ' total on ' + engineName.toUpperCase()
                     + ' — query run ' + formatMs(runMs);
    el.appendChild(head);
    const ul = document.createElement('ul');
    phases.forEach(p => {
      const li = document.createElement('li');
      const tl = document.createElement('span');
      tl.className = 'tl';
      tl.textContent = p.label + (p.bytes != null ? ' (' + formatBytes(p.bytes) + ')' : '');
      const bar = document.createElement('span');
      bar.className = 'bar' + (p.cached ? ' cached' : '');
      bar.style.width = Math.max(2, Math.round(220 * ((p.ms || 0) / fallback))) + 'px';
      const tr = document.createElement('span');
      tr.className = 'tr';
      tr.textContent = p.cached ? 'cached' : formatMs(p.ms);
      li.appendChild(tl); li.appendChild(bar); li.appendChild(tr);
      ul.appendChild(li);
    });
    el.appendChild(ul);
    return el;
  }

  _renderTimingBoth(totalMs, engineName, runMs) {
    const phases = this._buildPhases(engineName, runMs);
    // Cache the inner HTML so view switches can re-attach the summary
    // without re-running the query.
    this._lastTimingSummary = {
      html: this._renderTimingSummary(totalMs, engineName, runMs).outerHTML,
    };
    const meta = this._outEl.querySelector('.result-meta');
    const summary = this._renderTimingSummary(totalMs, engineName, runMs);
    if (meta) meta.appendChild(summary);
    else this._outEl.appendChild(summary);
    this._timingDetails.innerHTML = '';
    this._timingDetails.appendChild(
      this._renderTimingDetail(totalMs, engineName, runMs, phases));
    return phases;
  }

  // -----------------------------------------------------------------
  // The Run handler — faithful port of demo-lifesci.html's runBtn click.
  // -----------------------------------------------------------------
  async _onRunClick() {
    const engine = this._currentEngine();
    const queryText = this._queryEl.value;

    // Reset stale timing summary from any prior run; it's re-populated
    // on the success paths via _renderTimingBoth.
    this._lastTimingSummary = null;

    this.dispatchEvent(new CustomEvent('factoidal:query-start', {
      bubbles: true, composed: true,
      detail: { engine, query: queryText },
    }));

    // === IMMEDIATE synchronous feedback ===
    const originalLabel = this._runBtn.textContent;
    this._runBtn.disabled = true;
    this._runBtn.classList.add('running');
    this._runBtn.setAttribute('aria-busy', 'true');
    this._runBtn.textContent = 'Running…';
    this._statusEl.className = 'status';
    this._statusEl.innerHTML =
      '<span class="spinner" aria-hidden="true"></span>Running on ' + engine.toUpperCase() + '…';
    this._outEl.className = 'out running';
    this._outEl.innerHTML =
      '<div class="progress-label">Running on ' + engine.toUpperCase() + '…</div>' +
      '<div class="progress-sub">Fetching data, parsing, evaluating…</div>' +
      '<div class="progress-bar" role="progressbar" aria-label="query in progress"></div>';
    // Yield one animation frame so the "Running…" state paints before we
    // hog the main thread with parse+eval.
    await new Promise(r => requestAnimationFrame(() => r()));

    const runStart = performance.now();
    let statusFinalised = false;
    const finaliseStatus = (text, cls) => {
      this._statusEl.textContent = text;
      this._statusEl.className = cls;
      statusFinalised = true;
    };
    const cleanup = () => {
      this._runBtn.disabled = false;
      this._runBtn.classList.remove('running');
      this._runBtn.removeAttribute('aria-busy');
      this._runBtn.textContent = originalLabel;
      if (!statusFinalised) finaliseStatus('Ready.', 'status ok');
      if (this._outEl.classList.contains('running')) {
        this._outEl.className = 'out empty';
        this._outEl.textContent = '';
      }
    };

    try {
      const payloads = await this._getFilePayloads();

      // ----------------------------------------------------------------
      // WASM path — via browser-wasm.js's query() API. Merge n TTL files
      // into one TriG string since that API takes a single data string.
      // ----------------------------------------------------------------
      if (engine === 'wasm') {
        try {
          const modUrl = new URL('./browser-wasm.js', this._resolveBaseUrl()).href;
          const mod = await import(modUrl);
          if (typeof mod.setFactoidalWasmUrl === 'function') {
            mod.setFactoidalWasmUrl(
              new URL(this.wasmUrl, this._resolveBaseUrl()));
          }
          const trigData = payloadsToTriG(payloads);
          const qT0 = performance.now();
          const parsed = await mod.query(trigData, queryText, {
            dataFormat: 'trig',
            entail: this.entail,
          });
          const qMs = performance.now() - qT0;
          finaliseStatus('Done on WASM in ' + qMs.toFixed(0) + ' ms', 'status ok');
          this._renderResultsJSON(parsed);
          const totalMs = performance.now() - runStart;
          const phases = this._renderTimingBoth(totalMs, 'wasm', qMs);
          this.dispatchEvent(new CustomEvent('factoidal:query-done', {
            bubbles: true, composed: true,
            detail: { engine, query: queryText, results: parsed, runMs: qMs, totalMs, phases },
          }));
        } catch (e) {
          finaliseStatus('WASM error: ' + (e && e.message || e), 'status err');
          this._renderRawError((e && e.message ? e.message : String(e))
                               + (e && e.stderr ? '\n\n' + e.stderr : ''));
          this.dispatchEvent(new CustomEvent('factoidal:query-error', {
            bubbles: true, composed: true,
            detail: { engine, query: queryText, error: e },
          }));
        }
        cleanup();
        return;
      }

      // ----------------------------------------------------------------
      // JS path — js_of_ocaml IIFE runner; multi-file via jsoo_fs_tmp.
      // ----------------------------------------------------------------
      const src = await this._getEngineSource('js');
      const buf = [];
      const origLog = console.log, origErr = console.error;
      console.log   = (...a) => buf.push(a.join(' '));
      console.error = (...a) => buf.push(a.join(' '));

      globalThis.jsoo_fs_tmp = payloads.map(p => ({ name: p.vfs, content: p.content }));
      globalThis.process = globalThis.process || {};
      const argv = ['node', 'factoidal'];
      payloads.forEach(p => {
        // If the src-data entry specifies a named-graph IRI, load it
        // that way. Otherwise fall back to -d (default graph). The
        // previous unconditional --named p.graph=... pushed the literal
        // "undefined=..." for graph-less payloads, which caused the
        // landing-page single-TTL demos to return 0 rows.
        if (p.graph) {
          argv.push('--named', p.graph + '=' + p.vfs);
        } else {
          argv.push('-d', p.vfs);
        }
      });
      argv.push('-e', queryText, '-o', 'json');
      // Forward the runtime Logic selection. factoidal CLI accepts
      // --entail {none|RDFS|OWL-RL} (case-insensitive). "none" is the
      // default; skip the flag in that case for a tidier argv.
      {
        const regime = this.entail;  // reads the Logic radio
        if (regime && regime.toLowerCase() !== 'none') {
          argv.push('--entail', regime);
        }
      }
      globalThis.process.argv = argv;

      let exitCode = 0;
      const origExit = globalThis.process.exit;
      globalThis.process.exit = (n) => { exitCode = n | 0; throw new Error('__exit__'); };

      const qT0 = performance.now();
      try {
        (new Function(src))();
      } catch (e) {
        if (!e || e.message !== '__exit__') {
          buf.push('\n[factoidal-sparql-client] ' + (e && e.message || e));
          exitCode = 1;
        }
      } finally {
        globalThis.process.exit = origExit;
      }
      const qMs = performance.now() - qT0;

      console.log = origLog; console.error = origErr;
      const out = buf.join('\n').replace(/\n+$/, '');

      if (exitCode !== 0) {
        finaliseStatus('JS error after ' + qMs.toFixed(0) + ' ms', 'status err');
        this._renderRawError(out || '(no output, exit ' + exitCode + ')');
        this.dispatchEvent(new CustomEvent('factoidal:query-error', {
          bubbles: true, composed: true,
          detail: { engine, query: queryText, error: new Error(out || 'exit ' + exitCode) },
        }));
        cleanup();
        return;
      }

      const first = out.indexOf('{'), last = out.lastIndexOf('}');
      if (first < 0 || last < first) {
        this._renderRawError(out);
        this.dispatchEvent(new CustomEvent('factoidal:query-error', {
          bubbles: true, composed: true,
          detail: { engine, query: queryText, error: new Error('no JSON on stdout') },
        }));
        cleanup();
        return;
      }
      let parsed;
      try { parsed = JSON.parse(out.slice(first, last + 1)); }
      catch {
        this._renderRawError(out);
        this.dispatchEvent(new CustomEvent('factoidal:query-error', {
          bubbles: true, composed: true,
          detail: { engine, query: queryText, error: new Error('malformed JSON on stdout') },
        }));
        cleanup();
        return;
      }
      finaliseStatus('Done on JS in ' + qMs.toFixed(0) + ' ms', 'status ok');
      this._renderResultsJSON(parsed);
      const totalMs = performance.now() - runStart;
      const phases = this._renderTimingBoth(totalMs, 'js', qMs);
      this.dispatchEvent(new CustomEvent('factoidal:query-done', {
        bubbles: true, composed: true,
        detail: { engine, query: queryText, results: parsed, runMs: qMs, totalMs, phases },
      }));
    } catch (e) {
      finaliseStatus('Error: ' + (e && e.message || e), 'status err');
      this._renderRawError(e && e.stack || String(e));
      this.dispatchEvent(new CustomEvent('factoidal:query-error', {
        bubbles: true, composed: true,
        detail: { engine, query: queryText, error: e },
      }));
    } finally {
      cleanup();
    }
  }

  // Anchor for relative imports (browser-wasm.js, factoidal.wasm.js).
  // This module is loaded via a <script type="module" src="...">; we
  // resolve sibling URLs against this file's own URL so the consumer
  // doesn't have to think about it.
  _resolveBaseUrl() {
    return new URL(import.meta.url);
  }
}

if (!customElements.get('factoidal-sparql-client')) {
  customElements.define('factoidal-sparql-client', FactoidalSparqlClient);
}

export { FactoidalSparqlClient, FactoidalQuery };
