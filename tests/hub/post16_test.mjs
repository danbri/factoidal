// Pins the live cell in docs/web/hub/16-the-verified-in-fstar-story.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed) — mirrors npm/factoidal/test's own harness style.
// This post is mostly prose (the F* story, quoted qualifiers, commit
// citations); the one live cell is a static pretty() table of the
// extraction pipeline, which this file pins for shape and content.

import { extractObservableCells, runObservableCell, pretty } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const POST_FILE = '16-the-verified-in-fstar-story.md';

const cells = extractObservableCells(POST_FILE);

test('post16: post has at least 1 live cell', () => {
  assert.ok(cells.length >= 1, `expected >= 1 live cell, found ${cells.length}`);
});

test('post16 cell 1 (extraction pipeline table): four targets, native/js/wasm/C, in order', async () => {
  // No `fn`/`Factoidal` dependency -- this cell is pure static data
  // rendered through pretty(), so it needs no bindings beyond pretty
  // itself, and runs identically in the browser and here.
  const result = await runObservableCell(cells[0], { pretty });
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['target', 'command', 'output', 'status']);
  assert.equal(result.rows.length, 4);
  const targets = result.rows.map((r) => r[0]);
  assert.deepEqual(targets, [
    'Native (OCaml)',
    'JavaScript (js_of_ocaml)',
    'WebAssembly (wasm_of_ocaml)',
    'C (KaRaMeL)',
  ]);
});

// ---------------------------------------------------------------------
// Direct checks on the prose claims this post makes: the quoted
// RDF.Term.fsti banner and the freshly-measured module/line/assume-val
// counts are read from the real tree, not typed from memory.
// ---------------------------------------------------------------------

test('post16: the quoted RDF.Term.fsti banner text matches the real file', async () => {
  const fs = await import('node:fs');
  const path = await import('node:path');
  const { fileURLToPath } = await import('node:url');
  const __dirname = path.dirname(fileURLToPath(import.meta.url));
  const fstiPath = path.join(__dirname, '..', '..', 'formal', 'fstar', 'RDF.Term.fsti');
  const text = fs.readFileSync(fstiPath, 'utf8');
  assert.match(text, /module RDF\.Term/);
  assert.match(text, /If you know RDF but not F\*: skim the `\/\/\/` comments; concepts run/);
  assert.match(text, /uninterrupted from "Blank nodes" to the "Appendix" divider below\./);
});

test('post16: the standing Iron Rule #11 qualifier is quoted verbatim from CLAUDE.md', async () => {
  const fs = await import('node:fs');
  const path = await import('node:path');
  const { fileURLToPath } = await import('node:url');
  const __dirname = path.dirname(fileURLToPath(import.meta.url));

  // Normalize away markdown line-wrapping/bold markers so a
  // hand-wrapped source paragraph and a single-line blockquote can be
  // compared for the same underlying sentence.
  const normalize = (s) => s
    .replace(/\*\*/g, '')
    .replace(/^>\s*/gm, '')
    .replace(/\s+/g, ' ')
    .replace(/-\s+/g, '-')
    .trim();

  const claudeMdPath = path.join(__dirname, '..', '..', 'CLAUDE.md');
  const claudeMd = fs.readFileSync(claudeMdPath, 'utf8');
  const claudeMdMatch = claudeMd.match(
    /the qualifier "([^"]*optimization\s+layers being migrated back to F\\\*[^"]*)"/);
  assert.ok(claudeMdMatch, 'CLAUDE.md must still contain the quoted Iron Rule #11 qualifier');

  const postPath = path.join(__dirname, '..', '..', 'docs', 'web', 'hub', POST_FILE);
  const post = fs.readFileSync(postPath, 'utf8');
  const postMatch = post.match(
    /> (parser and algebra spec[\s\S]*?fstar-purity-unwind\.md\))/);
  assert.ok(postMatch, 'the post must quote the Iron Rule #11 qualifier as a blockquote');

  assert.equal(normalize(postMatch[1]), normalize(claudeMdMatch[1]),
    'the post\'s quoted qualifier must match CLAUDE.md\'s wording exactly');
});

test('post16: the freshly-measured F* module/line/assume-val counts are at least what the post claims', async () => {
  const fs = await import('node:fs');
  const path = await import('node:path');
  const { fileURLToPath } = await import('node:url');
  const __dirname = path.dirname(fileURLToPath(import.meta.url));
  const fstarDir = path.join(__dirname, '..', '..', 'formal', 'fstar');
  const entries = fs.readdirSync(fstarDir).filter((f) => f.endsWith('.fst') || f.endsWith('.fsti'));
  assert.ok(entries.length >= 139, `expected >= 139 F* modules, found ${entries.length}`);
  let totalLines = 0;
  let assumeValCount = 0;
  let modulesWithAssumeVal = 0;
  for (const f of entries) {
    const text = fs.readFileSync(path.join(fstarDir, f), 'utf8');
    const lines = text.split('\n').length;
    totalLines += lines;
    const matches = text.match(/^assume val/gm) || [];
    assumeValCount += matches.length;
    if (matches.length > 0) modulesWithAssumeVal++;
  }
  assert.ok(totalLines >= 75573, `expected >= 75573 total lines, found ${totalLines}`);
  assert.ok(assumeValCount >= 151, `expected >= 151 assume val declarations, found ${assumeValCount}`);
  assert.ok(modulesWithAssumeVal >= 22, `expected >= 22 modules with assume val, found ${modulesWithAssumeVal}`);
});
