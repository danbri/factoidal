// RDF Parsers for JavaScript — ported from Rust (rdf-wasm)
// N-Triples + Turtle parsers that produce graph structures compatible
// with the F*-extracted SPARQL engine.
//
// These parsers are standalone JavaScript — no dependencies on the F* extraction.
// They produce plain JS objects matching the F*-extracted types.

'use strict';

// ============================================================================
// RDF Types (matching F*-extracted RDF_Graph_Executable types)
// ============================================================================

const XSD_STRING = 'http://www.w3.org/2001/XMLSchema#string';
const XSD_INTEGER = 'http://www.w3.org/2001/XMLSchema#integer';
const XSD_DECIMAL = 'http://www.w3.org/2001/XMLSchema#decimal';
const XSD_DOUBLE = 'http://www.w3.org/2001/XMLSchema#double';
const XSD_BOOLEAN = 'http://www.w3.org/2001/XMLSchema#boolean';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const RDF_FIRST = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#first';
const RDF_REST = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#rest';
const RDF_NIL = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#nil';
const RDF_LANG_STRING = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#langString';

let _bnodeCounter = 0;
function freshBNode() { return '_:b' + (_bnodeCounter++); }
function resetBNodes() { _bnodeCounter = 0; }

function iri(s) { return { tag: 'T_IRI', value: s }; }
function bnode(id) { return { tag: 'T_BNode', value: id }; }
function literal(lex, dt, lang) {
  return {
    tag: 'T_Literal',
    value: { lexical_form: lex, datatype: dt || XSD_STRING, lang_tag: lang || null }
  };
}
function subject_iri(s) { return { tag: 'S_IRI', value: s }; }
function subject_bnode(id) { return { tag: 'S_BNode', value: id }; }

function makeTriple(s, p, o) { return { s, p, o }; }

// ============================================================================
// N-Triples Parser
// ============================================================================

function parseNTriples(input) {
  const graph = [];
  const bnodeLabels = {};
  const lines = input.split('\n');

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum].trim();
    if (line === '' || line.startsWith('#')) continue;

    try {
      const triple = parseNTLine(line, bnodeLabels);
      if (triple) graph.push(triple);
    } catch (e) {
      throw new Error(`Line ${lineNum + 1}: ${e.message}`);
    }
  }
  return graph;
}

function parseNTLine(line, bnodeLabels) {
  let pos = 0;
  const skipWS = () => { while (pos < line.length && (line[pos] === ' ' || line[pos] === '\t')) pos++; };
  const peek = () => pos < line.length ? line[pos] : null;
  const advance = () => pos < line.length ? line[pos++] : null;

  skipWS();
  if (pos >= line.length) return null;

  // Parse subject
  let s;
  if (peek() === '<') {
    const iriStr = parseIriRef();
    s = subject_iri(iriStr);
  } else if (peek() === '_') {
    const label = parseBnodeLabel();
    if (!bnodeLabels[label]) bnodeLabels[label] = freshBNode();
    s = subject_bnode(bnodeLabels[label]);
  } else {
    throw new Error("Expected '<' or '_:' for subject");
  }

  skipWS();

  // Parse predicate
  if (peek() !== '<') throw new Error("Expected '<' for predicate");
  const p = parseIriRef();

  skipWS();

  // Parse object
  let o;
  if (peek() === '<') {
    o = iri(parseIriRef());
  } else if (peek() === '_') {
    const label = parseBnodeLabel();
    if (!bnodeLabels[label]) bnodeLabels[label] = freshBNode();
    o = bnode(bnodeLabels[label]);
  } else if (peek() === '"') {
    o = parseLiteral();
  } else {
    throw new Error("Expected '<', '_:', or '\"' for object");
  }

  skipWS();
  if (peek() === '.') pos++;

  return makeTriple(s, p, o);

  function parseIriRef() {
    if (advance() !== '<') throw new Error("Expected '<'");
    let result = '';
    while (true) {
      const c = advance();
      if (c === null) throw new Error('Unterminated IRI');
      if (c === '>') break;
      if (c === '\\') {
        const esc = advance();
        if (esc === 'u') { result += parseHexEsc(4); }
        else if (esc === 'U') { result += parseHexEsc(8); }
        else throw new Error(`Invalid IRI escape: \\${esc}`);
      } else {
        result += c;
      }
    }
    return result;
  }

  function parseBnodeLabel() {
    if (advance() !== '_') throw new Error("Expected '_'");
    if (advance() !== ':') throw new Error("Expected ':'");
    let label = '';
    while (pos < line.length) {
      const c = line[pos];
      if (/[a-zA-Z0-9_\-.]/.test(c)) {
        label += c;
        pos++;
      } else {
        break;
      }
    }
    // Remove trailing dots (statement terminator)
    while (label.endsWith('.')) label = label.slice(0, -1);
    if (!label) throw new Error('Empty blank node label');
    return label;
  }

  function parseLiteral() {
    if (advance() !== '"') throw new Error('Expected \'"\'');
    let lex = '';
    while (true) {
      const c = advance();
      if (c === null) throw new Error('Unterminated literal');
      if (c === '"') break;
      if (c === '\\') {
        const esc = advance();
        if (esc === 't') lex += '\t';
        else if (esc === 'b') lex += '\b';
        else if (esc === 'n') lex += '\n';
        else if (esc === 'r') lex += '\r';
        else if (esc === 'f') lex += '\f';
        else if (esc === '"') lex += '"';
        else if (esc === "'") lex += "'";
        else if (esc === '\\') lex += '\\';
        else if (esc === 'u') lex += parseHexEsc(4);
        else if (esc === 'U') lex += parseHexEsc(8);
        else throw new Error(`Invalid escape: \\${esc}`);
      } else {
        lex += c;
      }
    }

    if (peek() === '@') {
      pos++;
      let lang = '';
      while (pos < line.length && /[a-zA-Z0-9\-]/.test(line[pos])) {
        lang += line[pos++];
      }
      return literal(lex, RDF_LANG_STRING, lang);
    } else if (peek() === '^' && line[pos + 1] === '^') {
      pos += 2;
      const dt = parseIriRef();
      return literal(lex, dt, null);
    } else {
      return literal(lex, XSD_STRING, null);
    }
  }

  function parseHexEsc(n) {
    let hex = '';
    for (let i = 0; i < n; i++) {
      const c = advance();
      if (!c || !/[0-9a-fA-F]/.test(c)) throw new Error('Invalid hex digit');
      hex += c;
    }
    return String.fromCodePoint(parseInt(hex, 16));
  }
}

// ============================================================================
// Turtle Parser
// ============================================================================

function parseTurtle(input, baseIRI) {
  const parser = new TurtleParser(input, baseIRI);
  return parser.parse();
}

class TurtleParser {
  constructor(input, baseIRI) {
    this.input = input;
    this.pos = 0;
    this.prefixes = {};
    this.base = baseIRI || null;
    this.graph = [];
    this.bnodeLabels = {};
  }

  peek() { return this.pos < this.input.length ? this.input[this.pos] : null; }
  advance() { return this.pos < this.input.length ? this.input[this.pos++] : null; }
  atEnd() { return this.pos >= this.input.length; }

  err(msg) { return new Error(`Turtle parse error at ${this.pos}: ${msg}`); }

  expect(ch) {
    if (this.advance() !== ch) throw this.err(`Expected '${ch}'`);
  }

  startsWith(s) { return this.input.startsWith(s, this.pos); }

  matchKeywordCI(kw) {
    if (this.pos + kw.length > this.input.length) return false;
    return this.input.substring(this.pos, this.pos + kw.length).toLowerCase() === kw.toLowerCase();
  }

  skipWS() {
    while (true) {
      while (!this.atEnd() && /[\s]/.test(this.peek())) this.pos++;
      if (this.peek() === '#') {
        while (!this.atEnd() && this.peek() !== '\n' && this.peek() !== '\r') this.pos++;
      } else {
        break;
      }
    }
  }

  resolveIRI(iriStr) {
    if (iriStr.includes(':') && !iriStr.startsWith('#')) return iriStr;
    if (this.base) {
      if (iriStr.startsWith('#')) return this.base + iriStr;
      if (iriStr === '') return this.base;
      const idx = this.base.lastIndexOf('/');
      if (idx >= 0) return this.base.substring(0, idx) + '/' + iriStr;
      return this.base + iriStr;
    }
    return iriStr;
  }

  parseIriRef() {
    this.expect('<');
    let result = '';
    while (true) {
      const c = this.advance();
      if (c === null) throw this.err('Unterminated IRI');
      if (c === '>') break;
      if (c === '\\') {
        const esc = this.advance();
        if (esc === 'u') result += this.parseHexEsc(4);
        else if (esc === 'U') result += this.parseHexEsc(8);
        else throw this.err(`Invalid IRI escape: \\${esc}`);
      } else if (c === ' ' || c.charCodeAt(0) < 0x20) {
        throw this.err(`Invalid character in IRI: U+${c.charCodeAt(0).toString(16).padStart(4,'0')}`);
      } else {
        result += c;
      }
    }
    return this.resolveIRI(result);
  }

  parseHexEsc(n) {
    let hex = '';
    for (let i = 0; i < n; i++) {
      const c = this.advance();
      if (!c || !/[0-9a-fA-F]/.test(c)) throw this.err('Invalid hex digit');
      hex += c;
    }
    return String.fromCodePoint(parseInt(hex, 16));
  }

  parsePrefixedName() {
    let prefix = '';
    while (!this.atEnd()) {
      const ch = this.peek();
      if (ch === ':') break;
      if (isPnCharsBaseUnicode(ch) || ch === '_' || ch === '-' || ch === '.' || /[0-9]/.test(ch)) {
        prefix += ch;
        this.pos++;
      } else {
        break;
      }
    }
    this.expect(':');
    const local = this.parsePnLocal();
    const ns = this.prefixes[prefix];
    if (ns === undefined) throw this.err(`Undefined prefix: '${prefix}:'`);
    return ns + local;
  }

  parsePnLocal() {
    let local = '';
    // First char
    const ch = this.peek();
    if (ch === '\\') {
      this.pos++;
      const c = this.advance();
      if (c && isPnLocalEsc(c)) local += c;
      else throw this.err(`Invalid escape in PN_LOCAL`);
    } else if (ch === '%') {
      local += this.parsePercentEncoded();
    } else if (ch && (isPnCharsUUnicode(ch) || ch === ':' || /[0-9]/.test(ch))) {
      local += ch;
      this.pos++;
    } else {
      return local;
    }

    while (!this.atEnd()) {
      const ch = this.peek();
      if (ch === '\\') {
        this.pos++;
        const c = this.advance();
        if (c && isPnLocalEsc(c)) local += c;
        else throw this.err('Invalid escape in PN_LOCAL');
      } else if (ch === '%') {
        local += this.parsePercentEncoded();
      } else if (ch === '.') {
        const save = this.pos;
        this.pos++;
        const next = this.peek();
        if (next && (isPnCharsUnicode(next) || next === ':' || next === '.' || next === '%' || next === '\\')) {
          local += '.';
        } else {
          this.pos = save;
          break;
        }
      } else if (ch && (isPnCharsUnicode(ch) || ch === ':')) {
        local += ch;
        this.pos++;
      } else {
        break;
      }
    }
    return local;
  }

  parsePercentEncoded() {
    this.expect('%');
    let s = '%';
    for (let i = 0; i < 2; i++) {
      const c = this.advance();
      if (!c || !/[0-9a-fA-F]/.test(c)) throw this.err('Invalid percent encoding');
      s += c;
    }
    return s;
  }

  parseString() {
    if (this.startsWith('"""')) { this.pos += 3; return this.parseLongString('"'); }
    if (this.startsWith("'''")) { this.pos += 3; return this.parseLongString("'"); }
    const quote = this.advance();
    if (quote !== '"' && quote !== "'") throw this.err('Expected quote');
    let s = '';
    while (true) {
      const c = this.advance();
      if (c === null) throw this.err('Unterminated string');
      if (c === quote) break;
      if (c === '\\') { s += this.parseStringEscape(); }
      else { s += c; }
    }
    return s;
  }

  parseLongString(quote) {
    let s = '';
    while (true) {
      if (this.atEnd()) throw this.err('Unterminated long string');
      if (this.peek() === quote && this.input[this.pos+1] === quote && this.input[this.pos+2] === quote) {
        this.pos += 3;
        break;
      }
      const c = this.advance();
      if (c === '\\') { s += this.parseStringEscape(); }
      else { s += c; }
    }
    return s;
  }

  parseStringEscape() {
    const c = this.advance();
    if (c === 't') return '\t';
    if (c === 'b') return '\b';
    if (c === 'n') return '\n';
    if (c === 'r') return '\r';
    if (c === 'f') return '\f';
    if (c === '"') return '"';
    if (c === "'") return "'";
    if (c === '\\') return '\\';
    if (c === 'u') return this.parseHexEsc(4);
    if (c === 'U') return this.parseHexEsc(8);
    throw this.err(`Invalid escape: \\${c}`);
  }

  parseBnodeLabel() {
    this.expect('_');
    this.expect(':');
    let label = '';
    const ch = this.peek();
    if (!ch || (!isPnCharsU(ch) && !/[0-9]/.test(ch))) throw this.err('Expected blank node label');
    label += ch;
    this.pos++;
    while (!this.atEnd()) {
      const ch = this.peek();
      if (ch === '.') {
        if (this.pos + 1 < this.input.length) {
          const next = this.input[this.pos + 1];
          if (isPnChars(next) || next === '.') { label += '.'; this.pos++; continue; }
        }
        break;
      } else if (isPnChars(ch)) {
        label += ch;
        this.pos++;
      } else {
        break;
      }
    }
    if (!this.bnodeLabels[label]) this.bnodeLabels[label] = freshBNode();
    return this.bnodeLabels[label];
  }

  parseIRI() {
    if (this.peek() === '<') return this.parseIriRef();
    return this.parsePrefixedName();
  }

  parseSubject() {
    this.skipWS();
    const ch = this.peek();
    if (ch === '<') return subject_iri(this.parseIriRef());
    if (ch === '_') return subject_bnode(this.parseBnodeLabel());
    if (ch === '(') {
      const t = this.parseCollection();
      if (t.tag === 'T_IRI') return subject_iri(t.value);
      if (t.tag === 'T_BNode') return subject_bnode(t.value);
      throw this.err('Collection head cannot be a literal');
    }
    if (ch === '[') return subject_bnode(this.parseBlankNodePropertyList());
    if (ch === ':' || isPnCharsBaseUnicode(ch)) return subject_iri(this.parsePrefixedName());
    throw this.err('Expected subject');
  }

  parsePredicate() {
    this.skipWS();
    if (this.peek() === 'a') {
      const next = this.input[this.pos + 1];
      if (next === undefined || next === ' ' || next === '\t' || next === '\n' || next === '\r') {
        this.pos++;
        return RDF_TYPE;
      }
    }
    return this.parseIRI();
  }

  parseObject() {
    this.skipWS();
    const ch = this.peek();
    if (ch === '<') return iri(this.parseIriRef());
    if (ch === '_') return bnode(this.parseBnodeLabel());
    if (ch === '"' || ch === "'") return this.parseLiteralValue();
    if (ch === '(') return this.parseCollection();
    if (ch === '[') return bnode(this.parseBlankNodePropertyList());
    if (ch === '+' || ch === '-') return this.parseNumericLiteral();
    if (ch === '.' && this.pos + 1 < this.input.length && /[0-9]/.test(this.input[this.pos+1]))
      return this.parseNumericLiteral();
    if (/[0-9]/.test(ch)) return this.parseNumericLiteral();
    if (this.startsWith('true')) {
      const after = this.input[this.pos + 4];
      if (!after || !isPnChars(after)) {
        this.pos += 4;
        return literal('true', XSD_BOOLEAN, null);
      }
    }
    if (this.startsWith('false')) {
      const after = this.input[this.pos + 5];
      if (!after || !isPnChars(after)) {
        this.pos += 5;
        return literal('false', XSD_BOOLEAN, null);
      }
    }
    if (ch === ':' || isPnCharsBaseUnicode(ch)) return iri(this.parsePrefixedName());
    throw this.err('Expected object');
  }

  parseLiteralValue() {
    const lex = this.parseString();
    if (this.peek() === '@') {
      this.pos++;
      let lang = '';
      while (!this.atEnd() && /[a-zA-Z0-9\-]/.test(this.peek())) {
        lang += this.advance();
      }
      return literal(lex, RDF_LANG_STRING, lang);
    } else if (this.peek() === '^' && this.input[this.pos + 1] === '^') {
      this.pos += 2;
      const dt = this.parseIRI();
      return literal(lex, dt, null);
    } else {
      return literal(lex, XSD_STRING, null);
    }
  }

  parseNumericLiteral() {
    const start = this.pos;
    if (this.peek() === '+' || this.peek() === '-') this.pos++;
    let hasDot = false, hasExp = false, hasIntPart = false;
    while (!this.atEnd() && /[0-9]/.test(this.peek())) { hasIntPart = true; this.pos++; }
    if (this.peek() === '.') {
      if (this.pos + 1 < this.input.length && /[0-9]/.test(this.input[this.pos+1])) {
        hasDot = true;
        this.pos++;
        while (!this.atEnd() && /[0-9]/.test(this.peek())) this.pos++;
      } else if (!hasIntPart) {
        hasDot = true;
        this.pos++;
        let hasFrac = false;
        while (!this.atEnd() && /[0-9]/.test(this.peek())) { hasFrac = true; this.pos++; }
        if (!hasFrac) throw this.err('Invalid numeric literal');
      } else {
        const afterDot = this.input[this.pos + 1];
        if (afterDot === 'e' || afterDot === 'E') { hasDot = true; this.pos++; }
      }
    }
    if (this.peek() === 'e' || this.peek() === 'E') {
      hasExp = true;
      this.pos++;
      if (this.peek() === '+' || this.peek() === '-') this.pos++;
      let hasExpDigits = false;
      while (!this.atEnd() && /[0-9]/.test(this.peek())) { hasExpDigits = true; this.pos++; }
      if (!hasExpDigits) throw this.err('Exponent requires digits');
    }
    const text = this.input.substring(start, this.pos);
    const dt = hasExp ? XSD_DOUBLE : hasDot ? XSD_DECIMAL : XSD_INTEGER;
    return literal(text, dt, null);
  }

  parseCollection() {
    this.expect('(');
    this.skipWS();
    if (this.peek() === ')') { this.pos++; return iri(RDF_NIL); }
    const items = [];
    while (true) {
      this.skipWS();
      if (this.peek() === ')') { this.pos++; break; }
      items.push(this.parseObject());
    }
    const nodes = items.map(() => freshBNode());
    for (let i = 0; i < items.length; i++) {
      this.graph.push(makeTriple(subject_bnode(nodes[i]), RDF_FIRST, items[i]));
      const restObj = i + 1 < nodes.length ? bnode(nodes[i+1]) : iri(RDF_NIL);
      this.graph.push(makeTriple(subject_bnode(nodes[i]), RDF_REST, restObj));
    }
    return bnode(nodes[0]);
  }

  parseBlankNodePropertyList() {
    this.expect('[');
    const id = freshBNode();
    const subj = subject_bnode(id);
    this.skipWS();
    if (this.peek() !== ']') this.parsePredicateObjectList(subj);
    this.skipWS();
    this.expect(']');
    return id;
  }

  parsePredicateObjectList(subject) {
    while (true) {
      this.skipWS();
      if (this.peek() === ']' || this.peek() === '.' || this.atEnd()) break;
      const pred = this.parsePredicate();
      this.parseObjectList(subject, pred);
      this.skipWS();
      if (this.peek() === ';') {
        while (this.peek() === ';') { this.pos++; this.skipWS(); }
        continue;
      } else {
        break;
      }
    }
  }

  parseObjectList(subject, predicate) {
    while (true) {
      const obj = this.parseObject();
      this.graph.push(makeTriple(subject, predicate, obj));
      this.skipWS();
      if (this.peek() === ',') { this.pos++; } else { break; }
    }
  }

  parsePrefixDirective() {
    const isAtPrefix = this.startsWith('@prefix');
    if (isAtPrefix) this.pos += 7;
    else if (this.matchKeywordCI('prefix')) this.pos += 6;
    else throw this.err('Expected @prefix or PREFIX');
    this.skipWS();
    let prefix = '';
    while (!this.atEnd() && this.peek() !== ':' && !/[\s]/.test(this.peek())) {
      prefix += this.advance();
    }
    this.expect(':');
    this.skipWS();
    const iriStr = this.parseIriRef();
    this.skipWS();
    if (this.peek() === '.') this.pos++;
    this.prefixes[prefix] = iriStr;
  }

  parseBaseDirective() {
    const isAtBase = this.startsWith('@base');
    if (isAtBase) this.pos += 5;
    else if (this.matchKeywordCI('base')) this.pos += 4;
    else throw this.err('Expected @base or BASE');
    this.skipWS();
    const iriStr = this.parseIriRef();
    this.skipWS();
    if (isAtBase && this.peek() === '.') this.pos++;
    this.base = iriStr;
  }

  parse() {
    while (true) {
      this.skipWS();
      if (this.atEnd()) break;

      if (this.startsWith('@prefix')) { this.parsePrefixDirective(); continue; }
      if (this.startsWith('@base')) { this.parseBaseDirective(); continue; }
      if (this.matchKeywordCI('prefix') && /[\s]/.test(this.input[this.pos + 6] || '')) {
        this.parsePrefixDirective(); continue;
      }
      if (this.matchKeywordCI('base')) {
        const after = this.input[this.pos + 4];
        if (after === ' ' || after === '\t' || after === '\n' || after === '\r') {
          this.parseBaseDirective(); continue;
        }
      }

      const subject = this.parseSubject();
      this.skipWS();
      if (this.peek() === '.') { this.pos++; continue; }
      this.parsePredicateObjectList(subject);
      this.skipWS();
      if (this.peek() === '.') this.pos++;
      else if (!this.atEnd()) throw this.err("Expected '.' at end of statement");
    }
    return this.graph;
  }
}

// ============================================================================
// Character Classification Helpers
// ============================================================================

function isPnCharsBaseUnicode(ch) {
  if (!ch) return false;
  const c = ch.charCodeAt(0);
  return /[a-zA-Z]/.test(ch)
    || (c >= 0x00C0 && c <= 0x00D6) || (c >= 0x00D8 && c <= 0x00F6)
    || (c >= 0x00F8 && c <= 0x02FF) || (c >= 0x0370 && c <= 0x037D)
    || (c >= 0x037F && c <= 0x1FFF) || (c >= 0x200C && c <= 0x200D)
    || (c >= 0x2070 && c <= 0x218F) || (c >= 0x2C00 && c <= 0x2FEF)
    || (c >= 0x3001 && c <= 0xD7FF) || (c >= 0xF900 && c <= 0xFDCF)
    || (c >= 0xFDF0 && c <= 0xFFFD);
}

function isPnCharsUUnicode(ch) { return isPnCharsBaseUnicode(ch) || ch === '_'; }

function isPnCharsUnicode(ch) {
  if (!ch) return false;
  const c = ch.charCodeAt(0);
  return isPnCharsUUnicode(ch) || ch === '-' || /[0-9]/.test(ch)
    || c === 0x00B7 || (c >= 0x0300 && c <= 0x036F) || (c >= 0x203F && c <= 0x2040);
}

function isPnCharsU(ch) { return /[a-zA-Z_]/.test(ch); }
function isPnChars(ch) { return /[a-zA-Z0-9_\-]/.test(ch); }

function isPnLocalEsc(c) {
  return '_~.-!$&\'()*+,;=/?#@%'.includes(c);
}

// ============================================================================
// SRXML Parser (SPARQL Results XML)
// ============================================================================

function parseSRXML(xml) {
  // Minimal parser for SPARQL Results XML format
  const results = [];
  const vars = [];

  // Extract variable names
  const varRegex = /<variable\s+name="([^"]+)"/g;
  let m;
  while ((m = varRegex.exec(xml)) !== null) vars.push(m[1]);

  // Extract results
  const resultRegex = /<result>([\s\S]*?)<\/result>/g;
  while ((m = resultRegex.exec(xml)) !== null) {
    const bindings = {};
    const bindingRegex = /<binding\s+name="([^"]+)">([\s\S]*?)<\/binding>/g;
    let bm;
    while ((bm = bindingRegex.exec(m[1])) !== null) {
      const name = bm[1];
      const value = bm[2].trim();
      if (value.startsWith('<uri>')) {
        bindings[name] = iri(value.replace(/<\/?uri>/g, '').trim());
      } else if (value.startsWith('<bnode>')) {
        bindings[name] = bnode('_:' + value.replace(/<\/?bnode>/g, '').trim());
      } else if (value.startsWith('<literal')) {
        const langMatch = value.match(/xml:lang="([^"]+)"/);
        const dtMatch = value.match(/datatype="([^"]+)"/);
        const lexMatch = value.match(/<literal[^>]*>([\s\S]*?)<\/literal>/);
        const lex = lexMatch ? lexMatch[1] : '';
        const lang = langMatch ? langMatch[1] : null;
        const dt = dtMatch ? dtMatch[1] : (lang ? RDF_LANG_STRING : XSD_STRING);
        bindings[name] = literal(lex, dt, lang);
      }
    }
    results.push(bindings);
  }

  // Check for boolean result (ASK queries)
  const boolMatch = xml.match(/<boolean>(true|false)<\/boolean>/);
  if (boolMatch) return { type: 'boolean', value: boolMatch[1] === 'true' };

  return { type: 'bindings', vars, results };
}

// ============================================================================
// Graph Comparison (isomorphism check for N-Triples tests)
// ============================================================================

function termToString(t) {
  if (t.tag === 'T_IRI') return `<${t.value}>`;
  if (t.tag === 'T_BNode') return t.value;
  const l = t.value;
  if (l.lang_tag) return `"${l.lexical_form}"@${l.lang_tag}`;
  if (l.datatype === XSD_STRING) return `"${l.lexical_form}"`;
  return `"${l.lexical_form}"^^<${l.datatype}>`;
}

function subjectToString(s) {
  if (s.tag === 'S_IRI') return `<${s.value}>`;
  return s.value;
}

function tripleToString(t) {
  return `${subjectToString(t.s)} <${t.p}> ${termToString(t.o)} .`;
}

function graphsIsomorphic(g1, g2) {
  // Simple comparison: same number of triples, and for non-bnode triples, exact match
  if (g1.length !== g2.length) return false;

  // Separate bnode and non-bnode triples
  const isBnode = (s) => s.tag === 'S_BNode';
  const hasBnode = (t) => isBnode(t.s) || t.o.tag === 'T_BNode';

  const concrete1 = g1.filter(t => !hasBnode(t)).map(tripleToString).sort();
  const concrete2 = g2.filter(t => !hasBnode(t)).map(tripleToString).sort();

  if (concrete1.length !== concrete2.length) return false;
  for (let i = 0; i < concrete1.length; i++) {
    if (concrete1[i] !== concrete2[i]) return false;
  }

  // For bnode triples, just check count matches (simple approximation)
  const bnode1 = g1.filter(t => hasBnode(t));
  const bnode2 = g2.filter(t => hasBnode(t));
  return bnode1.length === bnode2.length;
}

// ============================================================================
// Exports
// ============================================================================

if (typeof module !== 'undefined') {
  module.exports = {
    parseNTriples, parseTurtle, parseSRXML,
    graphsIsomorphic, termToString, subjectToString, tripleToString,
    iri, bnode, literal, subject_iri, subject_bnode, makeTriple,
    resetBNodes, freshBNode,
    XSD_STRING, XSD_INTEGER, XSD_DECIMAL, XSD_DOUBLE, XSD_BOOLEAN,
    RDF_TYPE, RDF_FIRST, RDF_REST, RDF_NIL, RDF_LANG_STRING,
  };
}
