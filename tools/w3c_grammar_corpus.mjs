#!/usr/bin/env node
// Janne-style W3C concrete syntax corpus generator/runner.
//
// This generates small, named positive and negative test files for RDF-family
// concrete grammars, writes a W3C-manifest-shaped manifest.ttl, then optionally
// runs the real factoidal CLI parser/query path over every case.
//
// Scope is intentionally grammar-facing rather than graph-model-facing. The
// differential harness already renders one abstract graph into several RDF
// syntaxes; this tool instead names productions and syntax boundaries directly.

import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";

const ROOT = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");

function parseArgs(argv) {
  const opts = {
    out: null,
    run: true,
    keep: false,
    bin: process.env.FACTOIDAL_BIN || null,
    timeoutMs: 2000,
    format: "all",
  };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--out") opts.out = argv[++i];
    else if (a === "--bin") opts.bin = argv[++i];
    else if (a === "--timeout-ms") opts.timeoutMs = Number(argv[++i]);
    else if (a === "--format") opts.format = argv[++i];
    else if (a === "--no-run") opts.run = false;
    else if (a === "--keep") opts.keep = true;
    else if (a === "--help" || a === "-h") {
      console.log("usage: node tools/w3c_grammar_corpus.mjs [--out DIR] [--format all|sparql|turtle|trig|ntriples|nquads|rdfxml|jsonld] [--bin PATH] [--timeout-ms MS] [--no-run] [--keep]");
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${a}`);
    }
  }
  if (!Number.isFinite(opts.timeoutMs) || opts.timeoutMs <= 0) throw new Error("--timeout-ms must be positive");
  return opts;
}

function findBin(explicit) {
  const candidates = [
    explicit,
    path.join(ROOT, "formal/fstar/ocaml-output/factoidal"),
    path.join(ROOT, "bin/darwin-arm64/factoidal"),
    path.join(ROOT, "bin/linux-x86_64/factoidal"),
  ].filter(Boolean);
  for (const c of candidates) {
    try {
      fs.accessSync(c, fs.constants.X_OK);
      return c;
    } catch {}
  }
  throw new Error("factoidal binary not found; pass --bin PATH");
}

function caseOf(format, polarity, id, ext, title, production, text) {
  return { format, polarity, id: `${format}-${polarity}-${id}`, ext, title, production, text };
}

function rdfPrefixBlock() {
  return [
    "@prefix : <http://example.org/> .",
    "@prefix ex: <http://example.org/> .",
    "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .",
    "@prefix foaf: <http://xmlns.com/foaf/0.1/> .",
    "",
  ].join("\n");
}

function cases() {
  const c = [];

  c.push(caseOf("sparql", "positive", "prologue-and-values", "rq", "SPARQL prologue, VALUES, OPTIONAL", "Prologue, SelectQuery, GroupGraphPattern, ValuesClause", [
    "PREFIX ex: <http://example.org/>",
    "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>",
    "SELECT ?s ?age WHERE {",
    "  VALUES ?s { ex:a ex:b UNDEF }",
    "  OPTIONAL { ?s ex:age ?age . FILTER(?age = \"42\"^^xsd:integer) }",
    "} ORDER BY ?s LIMIT 5",
    "",
  ].join("\n")));
  c.push(caseOf("sparql", "positive", "graph-union-bind", "rq", "SPARQL GRAPH, UNION, BIND", "GraphGraphPattern, GroupOrUnionGraphPattern, Bind", [
    "PREFIX ex: <http://example.org/>",
    "SELECT ?s ?label WHERE {",
    "  GRAPH <urn:g> { { ?s ex:p ?o } UNION { ?s ex:q ?o } }",
    "  BIND(STR(?o) AS ?label)",
    "}",
    "",
  ].join("\n")));
  c.push(caseOf("sparql", "negative", "prefix-missing-colon", "rq", "PREFIX must use PNAME_NS", "PrefixDecl", [
    "PREFIX ex <http://example.org/>",
    "SELECT * WHERE { ?s ?p ?o }",
    "",
  ].join("\n")));
  c.push(caseOf("sparql", "negative", "iri-space", "rq", "IRIREF forbids raw space", "IRIREF", [
    "PREFIX ex: <http://example.org/>",
    "SELECT * WHERE { <http://example.org/bad iri> ?p ?o }",
    "",
  ].join("\n")));
  c.push(caseOf("sparql", "negative", "filter-missing-rhs", "rq", "FILTER expression missing right operand", "Constraint, Expression", [
    "PREFIX ex: <http://example.org/>",
    "SELECT * WHERE { ?s ?p ?o . FILTER(?s = ) }",
    "",
  ].join("\n")));

  c.push(caseOf("turtle", "positive", "collections-blank-prefix", "ttl", "Turtle empty prefix and nested collections", "PNAME_NS, collection, blankNodePropertyList", rdfPrefixBlock() + [
    "@base <http://example.org/base/> .",
    ":root ex:p [ foaf:name \"Alice\"@en ; ex:items ( ex:a ( ex:b \"lex\\\\nline\" ) \"42\"^^xsd:integer ) ] .",
    "",
  ].join("\n")));
  c.push(caseOf("turtle", "positive", "numeric-and-escaping", "ttl", "Turtle numeric literals and escapes", "numericLiteral, STRING_LITERAL_QUOTE, IRIREF", rdfPrefixBlock() + [
    "ex:s ex:int -9223372036854775808 ;",
    "     ex:dec +3.1415 ;",
    "     ex:dbl 6.02e23 ;",
    "     ex:text \"tab\\tquote\\\"backslash\\\\\" .",
    "",
  ].join("\n")));
  c.push(caseOf("turtle", "negative", "bad-iri-space", "ttl", "Turtle IRIREF forbids raw space", "IRIREF", rdfPrefixBlock() + "<http://example.org/bad iri> ex:p ex:o .\n"));
  c.push(caseOf("turtle", "negative", "unterminated-string", "ttl", "Turtle unterminated string", "STRING_LITERAL_QUOTE", rdfPrefixBlock() + "ex:s ex:p \"unterminated .\n"));
  c.push(caseOf("turtle", "negative", "prefix-missing-dot", "ttl", "Turtle @prefix directive requires dot", "prefixID", "@prefix ex: <http://example.org/>\nex:s ex:p ex:o .\n"));

  c.push(caseOf("trig", "positive", "default-and-named", "trig", "TriG default graph plus named graph", "wrappedGraph, triplesBlock", rdfPrefixBlock() + [
    "{ ex:s ex:p ex:o . }",
    "ex:g { ex:s ex:q [ ex:p \"v\" ] . }",
    "<urn:g2> { ex:a ex:p ( ex:b ex:c ) . }",
    "",
  ].join("\n")));
  c.push(caseOf("trig", "negative", "unclosed-named-graph", "trig", "TriG graph block must close", "wrappedGraph", rdfPrefixBlock() + "ex:g { ex:s ex:p ex:o .\n"));
  c.push(caseOf("trig", "negative", "literal-graph-name", "trig", "TriG graph label cannot be a literal", "labelOrSubject", rdfPrefixBlock() + "\"g\" { ex:s ex:p ex:o . }\n"));

  c.push(caseOf("ntriples", "positive", "unicode-escape-literal", "nt", "N-Triples escaped Unicode and datatype", "triple, literal, ECHAR, UCHAR", [
    "<http://example.org/s> <http://example.org/p> \"caf\\u00E9\"@fr .",
    "<http://example.org/s> <http://example.org/age> \"42\"^^<http://www.w3.org/2001/XMLSchema#integer> .",
    "",
  ].join("\n")));
  c.push(caseOf("ntriples", "negative", "relative-subject", "nt", "N-Triples requires IRIREF or blank node subject", "subject", "ex:s <http://example.org/p> <http://example.org/o> .\n"));
  c.push(caseOf("ntriples", "negative", "literal-subject", "nt", "N-Triples subject cannot be literal", "subject", "\"s\" <http://example.org/p> <http://example.org/o> .\n"));

  c.push(caseOf("nquads", "positive", "named-graph-iri-bnode", "nq", "N-Quads graph name IRI and blank node object", "quad, graphLabel", [
    "<http://example.org/s> <http://example.org/p> _:b0 <http://example.org/g> .",
    "_:b0 <http://example.org/p> \"v\" <http://example.org/g> .",
    "",
  ].join("\n")));
  c.push(caseOf("nquads", "negative", "literal-graph", "nq", "N-Quads graph label cannot be literal", "graphLabel", "<http://example.org/s> <http://example.org/p> <http://example.org/o> \"g\" .\n"));
  c.push(caseOf("nquads", "negative", "missing-dot", "nq", "N-Quads requires final dot", "quad", "<http://example.org/s> <http://example.org/p> <http://example.org/o> <http://example.org/g>\n"));

  c.push(caseOf("rdfxml", "positive", "parse-type-collection", "rdf", "RDF/XML parseType Collection", "nodeElement, propertyElt, parseTypeCollectionPropertyElt", [
    "<?xml version=\"1.0\"?>",
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:ex=\"http://example.org/\">",
    "  <rdf:Description rdf:about=\"http://example.org/s\">",
    "    <ex:items rdf:parseType=\"Collection\">",
    "      <rdf:Description rdf:about=\"http://example.org/a\"/>",
    "      <rdf:Description rdf:nodeID=\"b\"/>",
    "    </ex:items>",
    "  </rdf:Description>",
    "</rdf:RDF>",
    "",
  ].join("\n")));
  c.push(caseOf("rdfxml", "positive", "typed-node-and-datatype", "rdf", "RDF/XML typed node and datatype literal", "typedNode, propertyAttribute, literalPropertyElt", [
    "<?xml version=\"1.0\"?>",
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:ex=\"http://example.org/\">",
    "  <ex:Thing rdf:about=\"http://example.org/s\" ex:rank=\"1\">",
    "    <ex:age rdf:datatype=\"http://www.w3.org/2001/XMLSchema#integer\">42</ex:age>",
    "  </ex:Thing>",
    "</rdf:RDF>",
    "",
  ].join("\n")));
  c.push(caseOf("rdfxml", "negative", "bad-about-and-nodeid", "rdf", "RDF/XML node cannot have both about and nodeID", "idAboutAttr, nodeIdAttr", [
    "<?xml version=\"1.0\"?>",
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:ex=\"http://example.org/\">",
    "  <rdf:Description rdf:about=\"http://example.org/s\" rdf:nodeID=\"b\"><ex:p>v</ex:p></rdf:Description>",
    "</rdf:RDF>",
    "",
  ].join("\n")));
  c.push(caseOf("rdfxml", "negative", "malformed-xml", "rdf", "RDF/XML must be XML well-formed", "XML document", [
    "<?xml version=\"1.0\"?>",
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"><rdf:Description>",
    "",
  ].join("\n")));

  c.push(caseOf("jsonld", "positive", "expanded-node", "jsonld", "JSON-LD expanded node object", "expanded node object", JSON.stringify([
    {
      "@id": "http://example.org/s",
      "http://example.org/p": [{ "@id": "http://example.org/o" }],
      "http://example.org/name": [{ "@value": "Alice", "@language": "en" }],
    },
  ], null, 2) + "\n"));
  c.push(caseOf("jsonld", "negative", "bad-json", "jsonld", "JSON-LD must be JSON", "JSON text", "{ \"@id\": \"http://example.org/s\", \n"));
  c.push(caseOf("jsonld", "negative", "invalid-id-iri-space", "jsonld", "Expanded @id IRI forbids raw space", "@id IRI", JSON.stringify([
    { "@id": "http://example.org/bad iri", "http://example.org/p": [{ "@value": "v" }] },
  ], null, 2) + "\n"));

  return c;
}

function selectedCases(format) {
  const all = cases();
  if (format === "all") return all;
  return all.filter((tc) => tc.format === format);
}

function manifestEntry(tc) {
  const klass = tc.polarity === "positive" ? "mf:PositiveSyntaxTest" : "mf:NegativeSyntaxTest";
  return [
    `:${tc.id} a ${klass} ;`,
    `  mf:name ${JSON.stringify(tc.title)} ;`,
    `  mf:action <${tc.id}.${tc.ext}> ;`,
    `  fact:format ${JSON.stringify(tc.format)} ;`,
    `  fact:production ${JSON.stringify(tc.production)} .`,
    "",
  ].join("\n");
}

function writeCorpus(outDir, selected) {
  fs.mkdirSync(outDir, { recursive: true });
  for (const tc of selected) {
    fs.writeFileSync(path.join(outDir, `${tc.id}.${tc.ext}`), tc.text);
  }
  const entries = selected.map((tc) => `:${tc.id}`).join("\n    ");
  const manifest = [
    "@prefix : <#> .",
    "@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .",
    "@prefix fact: <https://factoidal.example/ns/test#> .",
    "",
    ":manifest a mf:Manifest ;",
    "  mf:name \"Generated W3C concrete grammar corpus\" ;",
    `  mf:entries ( ${entries} ) .`,
    "",
    ...selected.map(manifestEntry),
  ].join("\n");
  fs.writeFileSync(path.join(outDir, "manifest.ttl"), manifest);
}

function classify(proc) {
  const out = `${proc.stdout || ""}\n${proc.stderr || ""}`;
  if (proc.error) {
    if (proc.error.code === "ETIMEDOUT") return { kind: "timeout", out };
    return { kind: "spawn-error", out: String(proc.error) };
  }
  if (proc.signal) return { kind: "signal", out };
  if (proc.status === 0) return { kind: "accepted", out };
  return { kind: "rejected", out };
}

function runCase(bin, outDir, tc, timeoutMs) {
  const file = path.join(outDir, `${tc.id}.${tc.ext}`);
  let args;
  if (tc.format === "sparql") {
    const data = path.join(outDir, "sparql-data.ttl");
    const named = path.join(outDir, "sparql-named.ttl");
    args = ["query", "--data", data, "--named", `urn:g=${named}`, "--query", file, "-o", "json"];
  } else if (tc.format === "jsonld") {
    args = ["jsonld", "--in", file];
  } else if (tc.format === "nquads" || tc.format === "trig") {
    args = ["dump-nq", file];
  } else {
    args = ["dump", file];
  }
  const proc = spawnSync(bin, args, { encoding: "utf8", timeout: timeoutMs, maxBuffer: 1024 * 1024 });
  return classify(proc);
}

function writeSparqlData(outDir) {
  const ttl = [
    "@prefix ex: <http://example.org/> .",
    "@prefix foaf: <http://xmlns.com/foaf/0.1/> .",
    "ex:a ex:p ex:b ; ex:q ex:c ; ex:age \"42\"^^<http://www.w3.org/2001/XMLSchema#integer> ; foaf:name \"Alice\" .",
    "ex:b ex:p ex:c ; ex:q ex:a .",
    "",
  ].join("\n");
  fs.writeFileSync(path.join(outDir, "sparql-data.ttl"), ttl);
  fs.writeFileSync(path.join(outDir, "sparql-named.ttl"), ttl);
}

function runCorpus(bin, outDir, selected, timeoutMs) {
  writeSparqlData(outDir);
  const summary = {
    bin,
    out: outDir,
    total: selected.length,
    positive: { accepted: 0, rejected: 0, timeout: 0, crash: 0 },
    negative: { accepted: 0, rejected: 0, timeout: 0, crash: 0 },
    failures: [],
  };
  for (const tc of selected) {
    const r = runCase(bin, outDir, tc, timeoutMs);
    const bucket = summary[tc.polarity];
    if (r.kind === "accepted") bucket.accepted++;
    else if (r.kind === "rejected") bucket.rejected++;
    else if (r.kind === "timeout") bucket.timeout++;
    else bucket.crash++;

    const ok = tc.polarity === "positive" ? r.kind === "accepted" : r.kind === "rejected";
    if (!ok) {
      summary.failures.push({
        id: tc.id,
        format: tc.format,
        polarity: tc.polarity,
        production: tc.production,
        result: r.kind,
        output: r.out.slice(0, 1200),
      });
      fs.writeFileSync(path.join(outDir, `${tc.id}.actual.txt`), r.out || "");
    }
  }
  fs.writeFileSync(path.join(outDir, "summary.json"), JSON.stringify(summary, null, 2));
  return summary;
}

const opts = parseArgs(process.argv);
const outDir = opts.out ? path.resolve(opts.out) : fs.mkdtempSync(path.join(os.tmpdir(), "factoidal-w3c-grammar-corpus-"));
const selected = selectedCases(opts.format);
if (selected.length === 0) throw new Error(`no cases for format ${opts.format}`);
writeCorpus(outDir, selected);

let summary = { out: outDir, total: selected.length };
if (opts.run) {
  const bin = findBin(opts.bin);
  summary = runCorpus(bin, outDir, selected, opts.timeoutMs);
}
console.log(JSON.stringify(summary, null, 2));

const bad = opts.run ? summary.failures.length : 0;
if (bad || opts.keep || opts.out) {
  console.error(`corpus in ${outDir}`);
} else {
  fs.rmSync(outDir, { recursive: true, force: true });
}
process.exit(bad === 0 ? 0 : 1);
