#!/usr/bin/env node
// W3C Test Harness — runs real W3C N-Triples and Turtle test files
// against the JavaScript parsers ported from Rust.
//
// Usage: node w3c-real-tests.js

'use strict';

const fs = require('fs');
const path = require('path');
const { parseNTriples, parseTurtle, resetBNodes } = require('./rdf-parsers.js');

const TESTS_BASE = path.resolve(__dirname, '../../../tests/w3c/rdf/rdf11');
const NT_DIR = path.join(TESTS_BASE, 'rdf-n-triples');
const TTL_DIR = path.join(TESTS_BASE, 'rdf-turtle');

let totalPass = 0, totalFail = 0, totalSkip = 0;
const suiteResults = [];

function runSuite(name, fn) {
  const before = { pass: totalPass, fail: totalFail };
  console.log(`\n=== ${name} ===`);
  fn();
  const p = totalPass - before.pass;
  const f = totalFail - before.fail;
  suiteResults.push({ name, pass: p, total: p + f });
  console.log(`  -- ${name}: ${p}/${p+f} --`);
}

// ============================================================================
// N-Triples Tests
// ============================================================================

// Positive tests: files that should parse without error
const NT_POSITIVE = [
  'comment_following_triple.nt',
  'langtagged_string.nt',
  'lantag_with_subtag.nt',
  'literal.nt',
  'literal_all_controls.nt',
  'literal_all_punctuation.nt',
  'literal_ascii_boundaries.nt',
  'literal_false.nt',
  'literal_true.nt',
  'literal_with_BACKSPACE.nt',
  'literal_with_CARRIAGE_RETURN.nt',
  'literal_with_CHARACTER_TABULATION.nt',
  'literal_with_FORM_FEED.nt',
  'literal_with_LINE_FEED.nt',
  'literal_with_REVERSE_SOLIDUS.nt',
  'literal_with_UTF8_boundaries.nt',
  'literal_with_diacritics.nt',
  'literal_with_numeric_escape4.nt',
  'literal_with_numeric_escape8.nt',
  'literal_with_squote.nt',
  'minimal_whitespace.nt',
  'nt-syntax-bnode-01.nt',
  'nt-syntax-bnode-02.nt',
  'nt-syntax-bnode-03.nt',
  'nt-syntax-datatypes-01.nt',
  'nt-syntax-datatypes-02.nt',
  'nt-syntax-str-esc-01.nt',
  'nt-syntax-str-esc-02.nt',
  'nt-syntax-str-esc-03.nt',
  'nt-syntax-string-01.nt',
  'nt-syntax-string-02.nt',
  'nt-syntax-string-03.nt',
  'nt-syntax-subm-01.nt',
  'nt-syntax-uri-01.nt',
  'nt-syntax-uri-02.nt',
  'nt-syntax-uri-03.nt',
  'nt-syntax-uri-04.nt',
];

// Negative tests: files that should fail to parse
const NT_NEGATIVE = [
  'nt-syntax-bad-base-01.nt',
  'nt-syntax-bad-esc-01.nt',
  'nt-syntax-bad-esc-02.nt',
  'nt-syntax-bad-esc-03.nt',
  'nt-syntax-bad-lang-01.nt',
  'nt-syntax-bad-num-01.nt',
  'nt-syntax-bad-num-02.nt',
  'nt-syntax-bad-num-03.nt',
  'nt-syntax-bad-prefix-01.nt',
  'nt-syntax-bad-string-01.nt',
  'nt-syntax-bad-string-02.nt',
  'nt-syntax-bad-string-03.nt',
  'nt-syntax-bad-string-04.nt',
  'nt-syntax-bad-string-05.nt',
  'nt-syntax-bad-string-06.nt',
  'nt-syntax-bad-string-07.nt',
  'nt-syntax-bad-struct-01.nt',
  'nt-syntax-bad-struct-02.nt',
  'nt-syntax-bad-uri-01.nt',
  'nt-syntax-bad-uri-02.nt',
  'nt-syntax-bad-uri-03.nt',
  'nt-syntax-bad-uri-04.nt',
  'nt-syntax-bad-uri-05.nt',
  'nt-syntax-bad-uri-06.nt',
  'nt-syntax-bad-uri-07.nt',
  'nt-syntax-bad-uri-08.nt',
  'nt-syntax-bad-uri-09.nt',
];

function testNTriplesPositive() {
  for (const file of NT_POSITIVE) {
    const filepath = path.join(NT_DIR, file);
    if (!fs.existsSync(filepath)) { totalSkip++; continue; }
    try {
      resetBNodes();
      const input = fs.readFileSync(filepath, 'utf8');
      parseNTriples(input);
      totalPass++;
      // console.log(`  PASS: ${file}`);
    } catch (e) {
      totalFail++;
      console.log(`  FAIL: ${file} — ${e.message}`);
    }
  }
}

function testNTriplesNegative() {
  for (const file of NT_NEGATIVE) {
    const filepath = path.join(NT_DIR, file);
    if (!fs.existsSync(filepath)) { totalSkip++; continue; }
    try {
      resetBNodes();
      const input = fs.readFileSync(filepath, 'utf8');
      parseNTriples(input);
      totalFail++;
      console.log(`  FAIL: ${file} — should have rejected but parsed OK`);
    } catch (e) {
      totalPass++;
      // console.log(`  PASS: ${file} (rejected: ${e.message})`);
    }
  }
}

// ============================================================================
// Turtle Tests
// ============================================================================

// Positive syntax tests
const TTL_POSITIVE_SYNTAX = [];
const TTL_NEGATIVE_SYNTAX = [];
const TTL_EVAL = [];

// Dynamically find Turtle test files
function findTurtleTests() {
  if (!fs.existsSync(TTL_DIR)) return;
  const files = fs.readdirSync(TTL_DIR);

  for (const f of files) {
    if (f.startsWith('turtle-syntax-') && f.endsWith('.ttl')) {
      if (f.includes('-bad-')) TTL_NEGATIVE_SYNTAX.push(f);
      else TTL_POSITIVE_SYNTAX.push(f);
    }
    if (f.startsWith('turtle-eval-') && f.endsWith('.ttl')) {
      TTL_EVAL.push(f);
    }
    // Also include turtle-subm-* tests
    if (f.startsWith('turtle-subm-') && f.endsWith('.ttl')) {
      TTL_EVAL.push(f);
    }
  }
  TTL_POSITIVE_SYNTAX.sort();
  TTL_NEGATIVE_SYNTAX.sort();
  TTL_EVAL.sort();
}

function testTurtlePositiveSyntax() {
  for (const file of TTL_POSITIVE_SYNTAX) {
    const filepath = path.join(TTL_DIR, file);
    try {
      resetBNodes();
      const input = fs.readFileSync(filepath, 'utf8');
      // Determine base IRI from filename
      const base = `http://www.w3.org/2013/TurtleTests/${file}`;
      parseTurtle(input, base);
      totalPass++;
    } catch (e) {
      totalFail++;
      console.log(`  FAIL: ${file} — ${e.message}`);
    }
  }
}

function testTurtleNegativeSyntax() {
  for (const file of TTL_NEGATIVE_SYNTAX) {
    const filepath = path.join(TTL_DIR, file);
    try {
      resetBNodes();
      const input = fs.readFileSync(filepath, 'utf8');
      const base = `http://www.w3.org/2013/TurtleTests/${file}`;
      parseTurtle(input, base);
      totalFail++;
      console.log(`  FAIL: ${file} — should have rejected but parsed OK`);
    } catch (e) {
      totalPass++;
    }
  }
}

function testTurtleEval() {
  for (const file of TTL_EVAL) {
    const filepath = path.join(TTL_DIR, file);
    // Expected output is .nt file with same base name
    const ntFile = file.replace('.ttl', '.nt');
    const ntPath = path.join(TTL_DIR, ntFile);

    if (!fs.existsSync(ntPath)) {
      // No expected output — just test that it parses
      try {
        resetBNodes();
        const input = fs.readFileSync(filepath, 'utf8');
        const base = `http://www.w3.org/2013/TurtleTests/${file}`;
        parseTurtle(input, base);
        totalPass++;
      } catch (e) {
        totalFail++;
        console.log(`  FAIL: ${file} — ${e.message}`);
      }
      continue;
    }

    try {
      resetBNodes();
      const ttlInput = fs.readFileSync(filepath, 'utf8');
      const base = `http://www.w3.org/2013/TurtleTests/${file}`;
      const ttlGraph = parseTurtle(ttlInput, base);

      resetBNodes();
      const ntInput = fs.readFileSync(ntPath, 'utf8');
      const ntGraph = parseNTriples(ntInput);

      // Compare triple counts
      if (ttlGraph.length === ntGraph.length) {
        totalPass++;
      } else {
        totalFail++;
        console.log(`  FAIL: ${file} — got ${ttlGraph.length} triples, expected ${ntGraph.length}`);
      }
    } catch (e) {
      totalFail++;
      console.log(`  FAIL: ${file} — ${e.message}`);
    }
  }
}

// ============================================================================
// Main
// ============================================================================

console.log('=== W3C Real Test Suite — JS Parsers (ported from Rust) ===');

findTurtleTests();

runSuite(`N-Triples positive (${NT_POSITIVE.length})`, testNTriplesPositive);
runSuite(`N-Triples negative (${NT_NEGATIVE.length})`, testNTriplesNegative);
runSuite(`Turtle positive syntax (${TTL_POSITIVE_SYNTAX.length})`, testTurtlePositiveSyntax);
runSuite(`Turtle negative syntax (${TTL_NEGATIVE_SYNTAX.length})`, testTurtleNegativeSyntax);
runSuite(`Turtle eval (${TTL_EVAL.length})`, testTurtleEval);

console.log('\n========================================');
console.log('Suite Results:');
for (const s of suiteResults) {
  console.log(`  ${s.name.padEnd(45)} ${s.pass}/${s.total}`);
}
console.log('========================================');
const total = totalPass + totalFail;
console.log(`TOTAL: ${totalPass}/${total} passed (${totalFail} failed, ${totalSkip} skipped)`);
console.log('========================================');

// JSON output
console.log('\n<!-- JSON_RESULTS');
console.log(JSON.stringify({
  passed: totalPass, total, failed: totalFail, skipped: totalSkip,
  suites: suiteResults
}));
console.log('JSON_RESULTS -->');

process.exit(totalFail > 0 ? 1 : 0);
