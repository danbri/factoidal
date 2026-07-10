// Three-way ShExC agreement table: our F*-extracted Parser.ShExC vs the
// vendored tree-sitter-shexc grammar (third_party/tree-sitter-shexc,
// a comparison probe -- see its PROVENANCE.md) vs the shexTest corpus's
// expected verdict.
//
// Inputs (produced by run.sh):
//   argv[2] = our shex_runner --negative-syntax -v output (per-entry lines)
//   argv[3] = our shex_runner --differential output (unsupported/mismatch lines)
//
// Corpus walked directly:
//   positives  = third_party/testing/shex/schemas/*.shex with a same-basename
//                .json twin (exactly the differential mode's own pair rule),
//                expected verdict ACCEPT;
//   negatives  = every sx:shex fixture in
//                third_party/testing/shex/negativeSyntax/manifest.ttl,
//                expected verdict REJECT.
//
// tree-sitter "rejects" a file when its parse tree contains ERROR or
// MISSING nodes (rootNode.hasError covers both).
//
// This is an ADVISORY probe (not a dashboard suite): the output is an
// agreement table plus a per-file disagreement list for triage.

'use strict';
const fs = require('fs');
const path = require('path');

const here = __dirname;
const repoRoot = path.resolve(here, '..', '..');
const schemasDir = path.join(repoRoot, 'third_party/testing/shex/schemas');
const negDir = path.join(repoRoot, 'third_party/testing/shex/negativeSyntax');

// --- tree-sitter parser over the vendored grammar --------------------
const Parser = require('tree-sitter');
// The native language object is not extensible; tree-sitter's JS layer
// caches generated node subclasses as properties on whatever object is
// passed to setLanguage, so wrap it in a plain object first.
const binding = require(path.join(here, '.build/build/Release/tree_sitter_shexc_binding.node'));
const language = Object.assign({}, binding);
const tsParser = new Parser();
tsParser.setLanguage(language);

function treeSitterAccepts(text) {
  const tree = tsParser.parse(text);
  return !tree.rootNode.hasError;
}

// --- corpus enumeration ----------------------------------------------
function positiveBases() {
  return fs.readdirSync(schemasDir)
    .filter((f) => f.endsWith('.shex'))
    .map((f) => f.slice(0, -'.shex'.length))
    .filter((b) => fs.existsSync(path.join(schemasDir, b + '.json')))
    .sort();
}

function negativeEntries() {
  // (name, fixture-file) pairs from the manifest. The manifest is
  // machine-written with one `sx:shex <file>` line per entry; this is a
  // probe harness, so a line-oriented scrape is acceptable here (the
  // conformance runner, shex_runner --negative-syntax, walks the
  // manifest through the real F*-extracted Turtle parser).
  const text = fs.readFileSync(path.join(negDir, 'manifest.ttl'), 'utf8');
  const entries = [];
  let name = null;
  for (const line of text.split('\n')) {
    const nm = line.match(/^\s*mf:name\s+"([^"]+)"/);
    if (nm) { name = nm[1]; continue; }
    const sx = line.match(/^\s*sx:shex\s+<([^>]+)>/);
    if (sx && name) { entries.push({ name, file: sx[1] }); name = null; }
  }
  return entries;
}

// --- our parser's verdicts, scraped from shex_runner output ----------
function ourNegativeVerdicts(negOutputPath) {
  // PASS (rejected) / PASS-EXC -> reject; FAIL (wrongly accepted) -> accept.
  const verdicts = new Map();
  const text = fs.readFileSync(negOutputPath, 'utf8');
  for (const line of text.split('\n')) {
    let m;
    if ((m = line.match(/^\s+PASS \(rejected\): (.+)$/))) verdicts.set(m[1], 'reject');
    else if ((m = line.match(/^\s+PASS-EXC \(rejected via exception .*\): (.+)$/))) verdicts.set(m[1], 'reject');
    else if ((m = line.match(/^\s+FAIL \(wrongly accepted\): (.+)$/))) verdicts.set(m[1], 'accept');
  }
  return verdicts;
}

function ourPositiveRejects(diffOutputPath) {
  // The differential mode prints per-file lines only for non-EQUAL pairs;
  // "unsupported: <base> -- Parser_ShExC.parse_shexc_schema returned None"
  // is our parser rejecting a positive fixture. Twin-decode failures and
  // AST mismatches are still ACCEPTS (the .shex side parsed).
  const rejects = new Set();
  const text = fs.readFileSync(diffOutputPath, 'utf8');
  for (const line of text.split('\n')) {
    const m = line.match(/^\s+unsupported: (\S+) -- Parser_ShExC\.parse_shexc_schema returned None/);
    if (m) rejects.add(m[1]);
  }
  return rejects;
}

// --- main -------------------------------------------------------------
function main() {
  const negOutputPath = process.argv[2];
  const diffOutputPath = process.argv[3];
  if (!negOutputPath || !diffOutputPath) {
    console.error('usage: node three-way.js <our-negative.txt> <our-differential.txt>');
    process.exit(2);
  }

  const rows = []; // {file, expected, ours, ts}

  const ourNeg = ourNegativeVerdicts(negOutputPath);
  for (const { name, file } of negativeEntries()) {
    const p = path.join(negDir, file);
    if (!fs.existsSync(p)) continue;
    const ours = ourNeg.get(name) || 'unknown';
    const ts = treeSitterAccepts(fs.readFileSync(p, 'utf8')) ? 'accept' : 'reject';
    rows.push({ file: 'negativeSyntax/' + file, expected: 'reject', ours, ts });
  }

  const ourPosRejects = ourPositiveRejects(diffOutputPath);
  for (const base of positiveBases()) {
    const p = path.join(schemasDir, base + '.shex');
    const ours = ourPosRejects.has(base) ? 'reject' : 'accept';
    const ts = treeSitterAccepts(fs.readFileSync(p, 'utf8')) ? 'accept' : 'reject';
    rows.push({ file: 'schemas/' + base + '.shex', expected: 'accept', ours, ts });
  }

  // Agreement table over (expected, ours, ts).
  const counts = new Map();
  for (const r of rows) {
    const k = `${r.expected}|${r.ours}|${r.ts}`;
    counts.set(k, (counts.get(k) || 0) + 1);
  }
  console.log('=== ShExC three-way agreement: expected x Parser.ShExC x tree-sitter-shexc ===');
  console.log(`files: ${rows.length} (${rows.filter((r) => r.expected === 'accept').length} positive schemas, ` +
    `${rows.filter((r) => r.expected === 'reject').length} negativeSyntax fixtures)\n`);
  console.log('expected  | ours    | tree-sitter | files');
  console.log('----------+---------+-------------+------');
  for (const k of [...counts.keys()].sort()) {
    const [e, o, t] = k.split('|');
    console.log(`${e.padEnd(9)} | ${o.padEnd(7)} | ${t.padEnd(11)} | ${counts.get(k)}`);
  }

  const disagreements = rows.filter((r) => r.ours !== r.ts || r.ours !== r.expected || r.ts !== r.expected);
  console.log(`\nPer-file rows where any of the three disagree (${disagreements.length}):`);
  for (const r of disagreements) {
    console.log(`  ${r.file}: expected=${r.expected} ours=${r.ours} tree-sitter=${r.ts}`);
  }
  // Advisory probe: always exit 0 (disagreements are triage input, not a gate).
}

main();
