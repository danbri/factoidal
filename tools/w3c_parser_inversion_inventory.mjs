#!/usr/bin/env node
// Extract an inversion inventory from the parser implementations.
//
// This is the first step toward running the parsers "backwards": make the
// grammar knowledge embedded in F*/Lean recursive-descent code visible as a
// graph of productions, calls, expected terminals, and negative boundaries.
//
// The output is intentionally mechanical JSON. A reverse generator can consume
// this graph by attaching emitters to productions and then walking outward from
// roots such as parse_turtle_doc, parse_trig_doc, readTriple11, or pSelectBody.

import fs from "node:fs";
import os from "node:os";
import path from "node:path";

const ROOT = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");

const SOURCES = [
  {
    format: "sparql",
    family: "SPARQL 1.1 Query",
    language: "fstar",
    file: "formal/fstar/SPARQL11.Parser.fst",
    roots: ["parse_sparql", "parse_select_query", "parse_prologue", "parse_select_body", "parse_ask_body", "parse_construct_body"],
  },
  {
    format: "turtle",
    family: "Turtle",
    language: "fstar",
    file: "formal/fstar/Parser.Turtle.fst",
    roots: ["parse_turtle_doc", "parse_turtle_statement", "parse_turtle_subject", "parse_turtle_predicate", "parse_turtle_object"],
  },
  {
    format: "trig",
    family: "TriG",
    language: "fstar",
    file: "formal/fstar/Parser.TriG.fst",
    roots: ["parse_trig_doc", "parse_trig_statement", "parse_graph_body", "parse_trig_graph_name"],
  },
  {
    format: "rdfxml",
    family: "RDF/XML",
    language: "fstar",
    file: "formal/fstar/Parser.RDFXML.fst",
    roots: ["parse_rdfxml_strict", "process_node_element", "process_property_element", "collect_property_attributes"],
  },
  {
    format: "jsonld",
    family: "JSON-LD expanded",
    language: "fstar",
    file: "formal/fstar/Parser.JSONLD.fst",
    roots: ["parse_jsonld", "jld_dataset_of_json", "jld_expand_top", "jld_expand_node", "jld_expand_property", "jld_value_object_to_term"],
  },
  {
    format: "ntriples",
    family: "N-Triples",
    language: "lean",
    file: "formal/lean4/L4Factoidal/Syntax/NTriples.lean",
    roots: ["parseNTriples", "readTriple11", "readSubject", "readPredicate", "readObject11"],
  },
  {
    format: "nquads",
    family: "N-Quads",
    language: "lean",
    file: "formal/lean4/L4Factoidal/Syntax/NQuads.lean",
    roots: ["parseNQuads", "parseQuadLinesAcc", "readNQuad11", "readGraphLabel"],
  },
  {
    format: "sparql",
    family: "SPARQL 1.1 Query",
    language: "lean",
    file: "formal/lean4/L4Factoidal/SPARQL/Parser.lean",
    roots: ["parseSparql", "parseSparqlWith", "pPrologue", "pSelectBody", "pAskBody", "pConstructBody"],
  },
];

function parseArgs(argv) {
  const opts = {
    out: null,
    format: "all",
    dot: false,
  };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--out") opts.out = argv[++i];
    else if (a === "--format") opts.format = argv[++i];
    else if (a === "--dot") opts.dot = true;
    else if (a === "--help" || a === "-h") {
      console.log("usage: node tools/w3c_parser_inversion_inventory.mjs [--format all|sparql|turtle|trig|rdfxml|jsonld|ntriples|nquads] [--out DIR] [--dot]");
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${a}`);
    }
  }
  return opts;
}

function lineNumberAt(text, offset) {
  let n = 1;
  for (let i = 0; i < offset; i++) if (text.charCodeAt(i) === 10) n++;
  return n;
}

function findDefs(text, language) {
  const defs = [];
  const re = language === "fstar"
    ? /^(?:let(?:\s+rec)?|and)\s+([A-Za-z_][A-Za-z0-9_']*)\b/gm
    : /^def\s+([A-Za-z_][A-Za-z0-9_']*)\b/gm;
  for (const m of text.matchAll(re)) {
    const name = m[1];
    const interesting = language === "fstar"
      ? /^(parse|scan|read|process|collect|validate|resolve|jld)_/.test(name) || /^parse[A-Z]/.test(name)
      : /^(parse|read|p|mk)[A-Z_]/.test(name);
    if (interesting) defs.push({ name, start: m.index, line: lineNumberAt(text, m.index) });
  }
  for (let i = 0; i < defs.length; i++) {
    defs[i].end = i + 1 < defs.length ? defs[i + 1].start : text.length;
  }
  return defs;
}

function uniq(xs) {
  return [...new Set(xs)].sort();
}

function stringMatches(body, re, group = 1) {
  const out = [];
  for (const m of body.matchAll(re)) out.push(m[group]);
  return uniq(out);
}

function analyzeDef(def, text, language, knownNames) {
  const body = text.slice(def.start, def.end);
  const calls = [];
  for (const name of knownNames) {
    if (name === def.name) continue;
    const callRe = new RegExp(`\\b${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "g");
    if (callRe.test(body)) calls.push(name);
  }

  const terminals = language === "fstar"
    ? [
        ...stringMatches(body, /\bTok_([A-Z0-9_]+)\b/g),
        ...stringMatches(body, /pstring(?:_ci)?\s+"([^"]+)"/g),
        ...stringMatches(body, /char_code[^=\n]*=\s*0x([0-9A-Fa-f]+)/g).map((h) => `char:0x${h}`),
      ]
    : [
        ...stringMatches(body, /\bToken\.([A-Za-z0-9_]+)/g),
        ...stringMatches(body, /\.kw\s+"([^"]+)"/g),
        ...stringMatches(body, /expect(?:Char|Tok)\s+([^)\n]+)/g),
      ];

  const errors = language === "fstar"
    ? [
        ...stringMatches(body, /ParseErr\s+"([^"]+)"/g),
        ...stringMatches(body, /ParseFail\s+"([^"]+)"/g),
      ]
    : stringMatches(body, /throw\s+\{[^}]*msg\s*:=\s*"([^"]+)"/g);

  const accepts = (body.match(/ParseOk\b|Except\.ok\b|return\b/g) || []).length;
  const rejects = (body.match(/ParseErr\b|ParseFail\b|throw\b|Except\.error\b/g) || []).length;

  return {
    name: def.name,
    line: def.line,
    calls: uniq(calls),
    terminals: uniq(terminals),
    errors: uniq(errors),
    branchSignals: { accepts, rejects },
  };
}

function reachableFrom(graph, roots) {
  const byName = new Map(graph.map((p) => [p.name, p]));
  const seen = new Set();
  const stack = roots.filter((r) => byName.has(r));
  while (stack.length) {
    const n = stack.pop();
    if (seen.has(n)) continue;
    seen.add(n);
    for (const c of byName.get(n).calls) if (!seen.has(c)) stack.push(c);
  }
  return [...seen].sort();
}

function sourceInventory(src) {
  const abs = path.join(ROOT, src.file);
  const text = fs.readFileSync(abs, "utf8");
  const defs = findDefs(text, src.language);
  const knownNames = defs.map((d) => d.name);
  const productions = defs.map((d) => analyzeDef(d, text, src.language, knownNames));
  const reachable = reachableFrom(productions, src.roots);
  const byName = new Map(productions.map((p) => [p.name, p]));
  const missingRoots = src.roots.filter((r) => !byName.has(r));
  const negativeHints = productions
    .flatMap((p) => p.errors.map((e) => ({ production: p.name, line: p.line, message: e })))
    .slice(0, 200);
  return {
    format: src.format,
    family: src.family,
    language: src.language,
    file: src.file,
    roots: src.roots,
    missingRoots,
    productionCount: productions.length,
    reachableCount: reachable.length,
    reachable,
    negativeHintCount: productions.reduce((n, p) => n + p.errors.length, 0),
    negativeHints,
    productions,
  };
}

function dotFor(inv) {
  const lines = ["digraph parser_inventory {", "  rankdir=LR;"];
  for (const source of inv.sources) {
    const prefix = `${source.format}_${source.language}`.replace(/[^A-Za-z0-9_]/g, "_");
    lines.push(`  subgraph cluster_${prefix} {`);
    lines.push(`    label="${source.family} ${source.language}";`);
    const reachable = new Set(source.reachable);
    for (const p of source.productions) {
      if (!reachable.has(p.name)) continue;
      lines.push(`    "${prefix}.${p.name}" [label="${p.name}\\n${p.line}"];`);
      for (const c of p.calls) {
        if (reachable.has(c)) lines.push(`    "${prefix}.${p.name}" -> "${prefix}.${c}";`);
      }
    }
    lines.push("  }");
  }
  lines.push("}");
  return lines.join("\n") + "\n";
}

const opts = parseArgs(process.argv);
const selected = SOURCES.filter((s) => opts.format === "all" || s.format === opts.format);
if (selected.length === 0) throw new Error(`no parser sources selected for ${opts.format}`);
const outDir = opts.out ? path.resolve(opts.out) : fs.mkdtempSync(path.join(os.tmpdir(), "factoidal-parser-inversion-"));
fs.mkdirSync(outDir, { recursive: true });

const inventory = {
  generatedBy: "tools/w3c_parser_inversion_inventory.mjs",
  generatedAt: new Date().toISOString(),
  purpose: "Parser-derived grammar inversion inventory for W3C concrete syntax fuzzing.",
  sources: selected.map(sourceInventory),
};

fs.writeFileSync(path.join(outDir, "parser-inversion-inventory.json"), JSON.stringify(inventory, null, 2));
if (opts.dot) fs.writeFileSync(path.join(outDir, "parser-inversion-inventory.dot"), dotFor(inventory));

const summary = {
  out: outDir,
  sources: inventory.sources.map((s) => ({
    format: s.format,
    language: s.language,
    file: s.file,
    productions: s.productionCount,
    reachable: s.reachableCount,
    negativeHints: s.negativeHintCount,
    missingRoots: s.missingRoots,
  })),
};
fs.writeFileSync(path.join(outDir, "summary.json"), JSON.stringify(summary, null, 2));
console.log(JSON.stringify(summary, null, 2));
