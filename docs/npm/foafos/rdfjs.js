// factoidal — RDF/JS data model + N-Quads token converters.
//
// Implements the RDF/JS Data Model specification
// (https://rdf.js.org/data-model-spec/): DataFactory producing
// NamedNode / BlankNode / Literal / Variable / DefaultGraph / Quad
// terms with spec-compliant `termType` / `value` / `language` /
// `datatype` and `.equals()`. Self-contained — no runtime deps.
//
// Also provides converters between RDF/JS quads and the engine's
// N-Quads token strings, which are the package's dataset interchange
// handle (the F*-extracted engine parses and serializes N-Quads; the
// converters below only tokenize/untokenize the engine's own output —
// full RDF parsing of user input always goes through the engine, per
// repo rule #4 "parsers belong in F*").
//
// Escaping mirrors the F* serializer RDF.NQuads.Serialize.escape_char
// exactly: \\ \" \n \r \t (and nothing else) are escaped on output;
// unescaping additionally accepts the full N-Triples ECHAR + UCHAR set
// (\t \b \n \r \f \" \' \\ \uXXXX \UXXXXXXXX) since engine input may
// legally contain them.

'use strict';

const XSD_STRING = 'http://www.w3.org/2001/XMLSchema#string';
const RDF_LANGSTRING =
  'http://www.w3.org/1999/02/22-rdf-syntax-ns#langString';

// ---------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------

class NamedNode {
  constructor(iri) {
    this.termType = 'NamedNode';
    this.value = iri;
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'NamedNode' &&
      other.value === this.value;
  }
}

class BlankNode {
  constructor(label) {
    this.termType = 'BlankNode';
    this.value = label;
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'BlankNode' &&
      other.value === this.value;
  }
}

class Literal {
  constructor(value, language, datatype) {
    this.termType = 'Literal';
    this.value = value;
    this.language = language || '';
    this.datatype = datatype ||
      new NamedNode(language ? RDF_LANGSTRING : XSD_STRING);
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'Literal' &&
      other.value === this.value &&
      other.language === this.language &&
      !!other.datatype && other.datatype.value === this.datatype.value;
  }
}

class Variable {
  constructor(name) {
    this.termType = 'Variable';
    this.value = name;
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'Variable' &&
      other.value === this.value;
  }
}

class DefaultGraph {
  constructor() {
    this.termType = 'DefaultGraph';
    this.value = '';
    Object.freeze(this);
  }
  equals(other) {
    return !!other && other.termType === 'DefaultGraph';
  }
}

const DEFAULT_GRAPH = new DefaultGraph();

class Quad {
  constructor(subject, predicate, object, graph) {
    // Per spec, a Quad is itself a Term with termType 'Quad', value ''.
    this.termType = 'Quad';
    this.value = '';
    this.subject = subject;
    this.predicate = predicate;
    this.object = object;
    this.graph = graph || DEFAULT_GRAPH;
    Object.freeze(this);
  }
  equals(other) {
    return !!other &&
      (other.termType === 'Quad' || other.termType === undefined) &&
      this.subject.equals(other.subject) &&
      this.predicate.equals(other.predicate) &&
      this.object.equals(other.object) &&
      this.graph.equals(other.graph);
  }
}

// ---------------------------------------------------------------------
// DataFactory
// ---------------------------------------------------------------------

let blankNodeCounter = 0;

const dataFactory = {
  namedNode(value) {
    return new NamedNode(String(value));
  },
  blankNode(label) {
    return new BlankNode(
      label !== undefined && label !== null
        ? String(label)
        : 'fjs_b' + (blankNodeCounter++)
    );
  },
  literal(value, languageOrDatatype) {
    const v = String(value);
    if (languageOrDatatype === undefined || languageOrDatatype === null) {
      return new Literal(v, '', null);
    }
    if (typeof languageOrDatatype === 'string') {
      return new Literal(v, languageOrDatatype, null);
    }
    // A NamedNode datatype.
    if (languageOrDatatype.termType === 'NamedNode') {
      if (languageOrDatatype.value === RDF_LANGSTRING) {
        // langString without a language tag is not constructible; treat
        // as plain string per the most defensive reading of the spec.
        return new Literal(v, '', null);
      }
      return new Literal(v, '', new NamedNode(languageOrDatatype.value));
    }
    throw new TypeError(
      'literal: second argument must be a language string or a NamedNode'
    );
  },
  variable(name) {
    return new Variable(String(name));
  },
  defaultGraph() {
    return DEFAULT_GRAPH;
  },
  quad(subject, predicate, object, graph) {
    return new Quad(subject, predicate, object, graph);
  },
  fromTerm(original) {
    if (!original || typeof original.termType !== 'string') {
      throw new TypeError('fromTerm: not a term');
    }
    switch (original.termType) {
      case 'NamedNode':    return new NamedNode(original.value);
      case 'BlankNode':    return new BlankNode(original.value);
      case 'Variable':     return new Variable(original.value);
      case 'DefaultGraph': return DEFAULT_GRAPH;
      case 'Literal':
        return new Literal(
          original.value,
          original.language || '',
          original.language
            ? null
            : new NamedNode(
                (original.datatype && original.datatype.value) || XSD_STRING)
        );
      case 'Quad':         return dataFactory.fromQuad(original);
      default:
        throw new TypeError(`fromTerm: unknown termType '${original.termType}'`);
    }
  },
  fromQuad(original) {
    if (!original || !original.subject) {
      throw new TypeError('fromQuad: not a quad');
    }
    return new Quad(
      dataFactory.fromTerm(original.subject),
      dataFactory.fromTerm(original.predicate),
      dataFactory.fromTerm(original.object),
      original.graph ? dataFactory.fromTerm(original.graph) : DEFAULT_GRAPH
    );
  },
};

// ---------------------------------------------------------------------
// SPARQL Results JSON term -> RDF/JS term
// ---------------------------------------------------------------------

/**
 * Convert a SPARQL 1.1 Results JSON term object
 * ({type:'uri'|'bnode'|'literal'|'typed-literal', value, 'xml:lang',
 * datatype}) into an RDF/JS term.
 */
function termFromSrj(t) {
  if (!t || typeof t.type !== 'string') {
    throw new TypeError('termFromSrj: not a results-JSON term');
  }
  switch (t.type) {
    case 'uri':
      return dataFactory.namedNode(t.value);
    case 'bnode':
      return dataFactory.blankNode(t.value);
    case 'literal':
    case 'typed-literal': {
      const lang = t['xml:lang'];
      if (lang) return dataFactory.literal(t.value, lang);
      if (t.datatype) {
        return dataFactory.literal(t.value, dataFactory.namedNode(t.datatype));
      }
      return dataFactory.literal(t.value);
    }
    default:
      throw new TypeError(`termFromSrj: unknown term type '${t.type}'`);
  }
}

// ---------------------------------------------------------------------
// N-Quads token output (mirrors RDF.NQuads.Serialize.escape_char)
// ---------------------------------------------------------------------

function escapeLiteral(s) {
  let out = '';
  for (const ch of s) {
    switch (ch) {
      case '\\': out += '\\\\'; break;
      case '"':  out += '\\"';  break;
      case '\n': out += '\\n';  break;
      case '\r': out += '\\r';  break;
      case '\t': out += '\\t';  break;
      default:   out += ch;
    }
  }
  return out;
}

/** Serialize one RDF/JS term to its N-Quads token. */
function termToNQuads(term) {
  switch (term.termType) {
    case 'NamedNode':
      return '<' + term.value + '>';
    case 'BlankNode':
      return '_:' + term.value;
    case 'Literal': {
      const body = '"' + escapeLiteral(term.value) + '"';
      if (term.language) return body + '@' + term.language;
      if (term.datatype && term.datatype.value !== XSD_STRING) {
        return body + '^^<' + term.datatype.value + '>';
      }
      return body;
    }
    case 'DefaultGraph':
      return '';
    default:
      throw new TypeError(
        `termToNQuads: cannot serialize termType '${term.termType}'`);
  }
}

/** Serialize one RDF/JS quad to an N-Quads line (with trailing " .\n"). */
function quadToNQuads(quad) {
  const g = quad.graph && quad.graph.termType !== 'DefaultGraph'
    ? ' ' + termToNQuads(quad.graph)
    : '';
  return termToNQuads(quad.subject) + ' ' +
    termToNQuads(quad.predicate) + ' ' +
    termToNQuads(quad.object) + g + ' .\n';
}

/** Serialize an iterable of quads to an N-Quads document. */
function quadsToNQuads(quads) {
  let out = '';
  for (const q of quads) out += quadToNQuads(q);
  return out;
}

// ---------------------------------------------------------------------
// N-Quads token input.
//
// A line tokenizer for the engine's own N-Quads output (and canonical
// N-Quads generally): one statement per line, terms separated by
// whitespace, ECHAR/UCHAR escapes inside literals. This is a token
// reader for a machine-generated regular syntax, not a general RDF
// parser — user documents in any syntax go through the engine.
// ---------------------------------------------------------------------

const UNESCAPE_MAP = {
  't': '\t', 'b': '\b', 'n': '\n', 'r': '\r', 'f': '\f',
  '"': '"', "'": "'", '\\': '\\',
};

function unescapeLiteral(s, lineNo) {
  if (s.indexOf('\\') < 0) return s;
  let out = '';
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c !== '\\') { out += c; continue; }
    const e = s[++i];
    if (e in UNESCAPE_MAP) { out += UNESCAPE_MAP[e]; continue; }
    if (e === 'u') {
      out += String.fromCodePoint(parseInt(s.slice(i + 1, i + 5), 16));
      i += 4;
      continue;
    }
    if (e === 'U') {
      out += String.fromCodePoint(parseInt(s.slice(i + 1, i + 9), 16));
      i += 8;
      continue;
    }
    throw new SyntaxError(
      `N-Quads line ${lineNo}: bad escape '\\${e}'`);
  }
  return out;
}

// Read one term starting at s[i]; returns [term, nextIndex].
function readTerm(s, i, lineNo, factory) {
  const c = s[i];
  if (c === '<') {
    const end = s.indexOf('>', i + 1);
    if (end < 0) throw new SyntaxError(`N-Quads line ${lineNo}: unclosed IRI`);
    return [factory.namedNode(s.slice(i + 1, end)), end + 1];
  }
  if (c === '_' && s[i + 1] === ':') {
    let j = i + 2;
    while (j < s.length && !/\s/.test(s[j])) j++;
    return [factory.blankNode(s.slice(i + 2, j)), j];
  }
  if (c === '"') {
    // Scan to the closing unescaped quote.
    let j = i + 1;
    for (;;) {
      if (j >= s.length) {
        throw new SyntaxError(`N-Quads line ${lineNo}: unclosed literal`);
      }
      if (s[j] === '\\') { j += 2; continue; }
      if (s[j] === '"') break;
      j++;
    }
    const lex = unescapeLiteral(s.slice(i + 1, j), lineNo);
    j++; // past closing quote
    if (s[j] === '@') {
      let k = j + 1;
      while (k < s.length && !/\s/.test(s[k])) k++;
      return [factory.literal(lex, s.slice(j + 1, k)), k];
    }
    if (s[j] === '^' && s[j + 1] === '^' && s[j + 2] === '<') {
      const end = s.indexOf('>', j + 3);
      if (end < 0) {
        throw new SyntaxError(`N-Quads line ${lineNo}: unclosed datatype IRI`);
      }
      return [
        factory.literal(lex, factory.namedNode(s.slice(j + 3, end))),
        end + 1,
      ];
    }
    return [factory.literal(lex), j];
  }
  throw new SyntaxError(
    `N-Quads line ${lineNo}: unexpected character '${c}' at column ${i + 1}`);
}

function skipWs(s, i) {
  while (i < s.length && (s[i] === ' ' || s[i] === '\t')) i++;
  return i;
}

/**
 * Tokenize one N-Quads statement line into an RDF/JS quad.
 * Returns null for blank/comment lines.
 */
function nquadsLineToQuad(line, lineNo, factory) {
  const f = factory || dataFactory;
  let i = skipWs(line, 0);
  if (i >= line.length || line[i] === '#') return null;
  const terms = [];
  while (terms.length < 4) {
    const [term, next] = readTerm(line, i, lineNo, f);
    terms.push(term);
    i = skipWs(line, next);
    if (line[i] === '.') break;
  }
  if (line[i] !== '.') {
    throw new SyntaxError(`N-Quads line ${lineNo}: missing terminating '.'`);
  }
  if (terms.length < 3) {
    throw new SyntaxError(`N-Quads line ${lineNo}: fewer than 3 terms`);
  }
  return f.quad(terms[0], terms[1], terms[2], terms[3] || f.defaultGraph());
}

/**
 * Tokenize an engine-emitted N-Quads document into RDF/JS quads.
 *
 * options.blankNodePrefix — prepended to every blank-node label, used
 * by parse() to keep labels from separate parse calls distinct (blank
 * node identity is document-scoped; the prefix is bookkeeping, the
 * semantic per-document renaming lives in F*
 * RDF.Dataset.Merge.rename_dataset_bnodes).
 */
function nquadsToQuads(text, options) {
  const opts = options || {};
  const factory = opts.factory || dataFactory;
  const f = opts.blankNodePrefix
    ? {
        ...factory,
        blankNode: (label) => factory.blankNode(
          label === undefined || label === null
            ? undefined
            : opts.blankNodePrefix + label),
      }
    : factory;
  const quads = [];
  const lines = String(text).split('\n');
  for (let n = 0; n < lines.length; n++) {
    const q = nquadsLineToQuad(lines[n].replace(/\r$/, ''), n + 1, f);
    if (q) quads.push(q);
  }
  return quads;
}

// ---------------------------------------------------------------------
// Dataset — a minimal RDF/JS DatasetCore over an in-memory quad array.
// ---------------------------------------------------------------------

class Dataset {
  constructor(quads) {
    this._quads = [];
    if (quads) for (const q of quads) this.add(q);
  }
  get size() {
    return this._quads.length;
  }
  add(quad) {
    if (!this.has(quad)) this._quads.push(quad);
    return this;
  }
  delete(quad) {
    const ix = this._quads.findIndex((q) => q.equals(quad));
    if (ix >= 0) this._quads.splice(ix, 1);
    return this;
  }
  has(quad) {
    return this._quads.some((q) => q.equals(quad));
  }
  match(subject, predicate, object, graph) {
    const out = new Dataset();
    for (const q of this._quads) {
      if (subject   && !subject.equals(q.subject))     continue;
      if (predicate && !predicate.equals(q.predicate)) continue;
      if (object    && !object.equals(q.object))       continue;
      if (graph     && !graph.equals(q.graph))         continue;
      out._quads.push(q);
    }
    return out;
  }
  [Symbol.iterator]() {
    return this._quads[Symbol.iterator]();
  }
  toArray() {
    return this._quads.slice();
  }
  /** N-Quads text — the engine interchange handle. */
  toNQuads() {
    return quadsToNQuads(this._quads);
  }
  toString() {
    return this.toNQuads();
  }
  static fromNQuads(text, options) {
    return new Dataset(nquadsToQuads(text, options));
  }
}

module.exports = {
  dataFactory,
  NamedNode,
  BlankNode,
  Literal,
  Variable,
  DefaultGraph,
  Quad,
  Dataset,
  termFromSrj,
  termToNQuads,
  quadToNQuads,
  quadsToNQuads,
  nquadsToQuads,
  XSD_STRING,
  RDF_LANGSTRING,
};
