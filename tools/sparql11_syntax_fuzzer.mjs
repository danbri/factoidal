#!/usr/bin/env node
// Lightweight SPARQL 1.1 syntax fuzzer for the real factoidal CLI parser.
//
// It intentionally avoids a separate parser oracle. Instead it generates:
//   - valid, evaluator-friendly SPARQL 1.1 query shapes that should run
//   - invalid one-edit mutations that should be rejected by the parser
//
// The useful signal is:
//   valid query rejected  -> parser/evaluator regression candidate
//   invalid query accepted -> parser permissiveness candidate
//   process exception/signal -> crash candidate

import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";

function parseArgs(argv) {
  const opts = {
    cases: 500,
    seed: 0x5eed1234,
    timeoutMs: 2000,
    keep: false,
    bin: process.env.FACTOIDAL_BIN || null,
  };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--cases") opts.cases = Number(argv[++i]);
    else if (a === "--seed") opts.seed = Number(argv[++i]);
    else if (a === "--timeout-ms") opts.timeoutMs = Number(argv[++i]);
    else if (a === "--bin") opts.bin = argv[++i];
    else if (a === "--keep") opts.keep = true;
    else if (a === "--help" || a === "-h") {
      console.log(`usage: node tools/sparql11_syntax_fuzzer.mjs [--cases N] [--seed N] [--bin PATH] [--timeout-ms MS] [--keep]`);
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${a}`);
    }
  }
  if (!Number.isFinite(opts.cases) || opts.cases <= 0) throw new Error("--cases must be positive");
  if (!Number.isFinite(opts.seed)) throw new Error("--seed must be numeric");
  return opts;
}

function findBin(root, explicit) {
  const candidates = [
    explicit,
    path.join(root, "formal/fstar/ocaml-output/factoidal"),
    path.join(root, "bin/darwin-arm64/factoidal"),
    path.join(root, "bin/linux-x86_64/factoidal"),
  ].filter(Boolean);
  for (const c of candidates) {
    try {
      fs.accessSync(c, fs.constants.X_OK);
      return c;
    } catch {}
  }
  throw new Error(`factoidal binary not found; pass --bin PATH`);
}

function mulberry32(seed) {
  let t = seed >>> 0;
  return () => {
    t += 0x6D2B79F5;
    let x = t;
    x = Math.imul(x ^ (x >>> 15), x | 1);
    x ^= x + Math.imul(x ^ (x >>> 7), x | 61);
    return ((x ^ (x >>> 14)) >>> 0) / 4294967296;
  };
}

function choice(rng, xs) {
  return xs[Math.floor(rng() * xs.length)];
}

function maybe(rng, p = 0.5) {
  return rng() < p;
}

const prefixes = [
  "PREFIX ex: <http://example.org/>",
  "PREFIX foaf: <http://xmlns.com/foaf/0.1/>",
  "PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>",
];

const vars = ["?s", "?p", "?o", "?x", "?y", "?name", "?age"];
const subjects = ["?s", "?x", "ex:a", "ex:b", "ex:c"];
const predicates = ["?p", "ex:p", "ex:q", "foaf:name", "ex:age"];
const objects = ["?o", "?y", "?name", "?age", "ex:a", "ex:b", "\"Alice\"", "\"42\"^^xsd:integer"];

function triple(rng) {
  return `${choice(rng, subjects)} ${choice(rng, predicates)} ${choice(rng, objects)} .`;
}

function bgp(rng, min = 1, max = 3) {
  const n = min + Math.floor(rng() * (max - min + 1));
  return Array.from({ length: n }, () => triple(rng)).join(" ");
}

function filter(rng) {
  return choice(rng, [
    "FILTER(?age = \"42\"^^xsd:integer)",
    "FILTER(BOUND(?s))",
    "FILTER(?name = \"Alice\")",
    "FILTER(?s != ?o)",
    "FILTER(REGEX(STR(?name), \"A\"))",
  ]);
}

function values(rng) {
  return choice(rng, [
    "VALUES ?s { ex:a ex:b }",
    "VALUES (?s ?name) { (ex:a \"Alice\") (ex:b \"Bob\") }",
    "VALUES ?age { \"42\"^^xsd:integer UNDEF }",
  ]);
}

function group(rng, depth = 0) {
  const parts = [bgp(rng, 1, 2)];
  if (maybe(rng, 0.45)) parts.push(filter(rng));
  if (maybe(rng, 0.35)) parts.push(`BIND(${choice(rng, ["STR(?name)", "?o", "\"z\""])} AS ${choice(rng, ["?z", "?label"])})`);
  if (maybe(rng, 0.25)) parts.push(values(rng));
  if (depth < 1 && maybe(rng, 0.25)) parts.push(`OPTIONAL { ${bgp(rng, 1, 2)} }`);
  if (depth < 1 && maybe(rng, 0.20)) parts.push(`{ ${bgp(rng, 1, 2)} } UNION { ${bgp(rng, 1, 2)} }`);
  if (depth < 1 && maybe(rng, 0.15)) parts.push(`GRAPH <urn:g> { ${bgp(rng, 1, 2)} }`);
  return parts.join(" ");
}

function solutionMods(rng) {
  const mods = [];
  if (maybe(rng, 0.35)) mods.push(`ORDER BY ${choice(rng, ["?s", "?name", "ASC(?name)", "DESC(?age)"])}`);
  if (maybe(rng, 0.30)) {
    const lim = 1 + Math.floor(rng() * 4);
    const off = Math.floor(rng() * 3);
    mods.push(maybe(rng) ? `LIMIT ${lim} OFFSET ${off}` : `OFFSET ${off} LIMIT ${lim}`);
  }
  return mods.join(" ");
}

function validQuery(rng) {
  const pre = prefixes.join("\n");
  const form = choice(rng, ["select", "ask", "construct"]);
  const where = `{ ${group(rng)} }`;
  let q;
  if (form === "ask") q = `ASK WHERE ${where}`;
  else if (form === "construct") q = `CONSTRUCT { ?s ?p ?o } WHERE ${where} ${solutionMods(rng)}`;
  else {
    const sel = choice(rng, ["*", "?s", "?s ?p ?o", "?name", "(COUNT(?s) AS ?c)"]);
    q = `SELECT ${maybe(rng, 0.2) ? "DISTINCT " : ""}${sel} WHERE ${where} ${solutionMods(rng)}`;
  }
  return `${pre}\n${q}`.trim();
}

function invalidQuery(rng) {
  const pre = prefixes.join("\n");
  return choice(rng, [
    `${pre}\nSELECT * WHERE { ?s ?p ?o `,
    `${pre}\nSELECT * WHERE { ? ?p ?o }`,
    `${pre}\nSELECT SELECT * WHERE { ?s ?p ?o }`,
    `${pre}\nASK WHEREX { ?s ?p ?o }`,
    `${pre}\nSELECT * WHERE { ?s ?p ?o . FILTER(?s = ) }`,
    `${pre}\nSELECT * WHERE { ?s ?p "unterminated . }`,
    `PREFIX ex <http://example.org/>\nSELECT * WHERE { ?s ?p ?o }`,
    `PREFIX ex: <http://example.org/bad iri>\nSELECT * WHERE { ?s ?p ?o }`,
    `PREFIX ex: <http://example.org/>\nSELECT * WHERE { <http://example.org/bad iri> ?p ?o }`,
  ]);
}

function classify(proc) {
  const out = `${proc.stdout || ""}\n${proc.stderr || ""}`;
  if (proc.error) {
    if (proc.error.code === "ETIMEDOUT") return { kind: "timeout", out };
    return { kind: "spawn-error", out: String(proc.error) };
  }
  if (proc.signal) return { kind: "signal", out };
  if (proc.status === 0) return { kind: "accepted", out };
  if (/SPARQL parse error|ParseErr|parse error|unexpected token|Expected/i.test(out)) {
    return { kind: "rejected", out };
  }
  return { kind: "runtime-error", out };
}

function runCase(bin, data, named, q, timeoutMs) {
  const args = [
    "query",
    "--data", data,
    "--named", `urn:g=${named}`,
    "-e", q,
    "-o", "json",
  ];
  const proc = spawnSync(bin, args, {
    encoding: "utf8",
    timeout: timeoutMs,
    maxBuffer: 1024 * 1024,
  });
  return classify(proc);
}

function writeCase(dir, prefix, i, query, result) {
  const stem = `${prefix}-${String(i).padStart(5, "0")}`;
  fs.writeFileSync(path.join(dir, `${stem}.rq`), query);
  fs.writeFileSync(path.join(dir, `${stem}.txt`), result.out || "");
}

const root = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");
const opts = parseArgs(process.argv);
const bin = findBin(root, opts.bin);
const rng = mulberry32(opts.seed);
const work = fs.mkdtempSync(path.join(os.tmpdir(), "factoidal-sparql11-fuzz-"));
const repro = path.join(work, "repro");
fs.mkdirSync(repro);

const dataPath = path.join(work, "data.ttl");
const namedPath = path.join(work, "named.ttl");
fs.writeFileSync(dataPath, `
@prefix ex: <http://example.org/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
ex:a ex:p ex:b ; foaf:name "Alice" ; ex:age "42"^^<http://www.w3.org/2001/XMLSchema#integer> .
ex:b ex:p ex:c ; foaf:name "Bob" .
ex:c ex:q ex:a .
`);
fs.writeFileSync(namedPath, fs.readFileSync(dataPath, "utf8"));

const summary = {
  seed: opts.seed,
  cases: opts.cases,
  bin,
  work,
  valid: { accepted: 0, rejected: 0, runtimeError: 0, timeout: 0, crash: 0 },
  invalid: { accepted: 0, rejected: 0, runtimeError: 0, timeout: 0, crash: 0 },
  samples: [],
};

for (let i = 0; i < opts.cases; i++) {
  const valid = validQuery(rng);
  const vr = runCase(bin, dataPath, namedPath, valid, opts.timeoutMs);
  if (vr.kind === "accepted") summary.valid.accepted++;
  else if (vr.kind === "rejected") {
    summary.valid.rejected++;
    if (summary.samples.length < 20) summary.samples.push({ kind: "valid-rejected", i, query: valid, output: vr.out.slice(0, 1000) });
    writeCase(repro, "valid-rejected", i, valid, vr);
  } else if (vr.kind === "timeout") {
    summary.valid.timeout++;
    writeCase(repro, "valid-timeout", i, valid, vr);
  } else if (vr.kind === "runtime-error") {
    summary.valid.runtimeError++;
    if (summary.samples.length < 20) summary.samples.push({ kind: "valid-runtime-error", i, query: valid, output: vr.out.slice(0, 1000) });
    writeCase(repro, "valid-runtime-error", i, valid, vr);
  } else {
    summary.valid.crash++;
    writeCase(repro, "valid-crash", i, valid, vr);
  }

  const invalid = invalidQuery(rng);
  const ir = runCase(bin, dataPath, namedPath, invalid, opts.timeoutMs);
  if (ir.kind === "accepted") {
    summary.invalid.accepted++;
    if (summary.samples.length < 20) summary.samples.push({ kind: "invalid-accepted", i, query: invalid, output: ir.out.slice(0, 1000) });
    writeCase(repro, "invalid-accepted", i, invalid, ir);
  } else if (ir.kind === "rejected") summary.invalid.rejected++;
  else if (ir.kind === "timeout") {
    summary.invalid.timeout++;
    writeCase(repro, "invalid-timeout", i, invalid, ir);
  } else if (ir.kind === "runtime-error") {
    summary.invalid.runtimeError++;
    writeCase(repro, "invalid-runtime-error", i, invalid, ir);
  } else {
    summary.invalid.crash++;
    writeCase(repro, "invalid-crash", i, invalid, ir);
  }
}

fs.writeFileSync(path.join(work, "summary.json"), JSON.stringify(summary, null, 2));
console.log(JSON.stringify(summary, null, 2));

const bad =
  summary.valid.rejected + summary.valid.runtimeError + summary.valid.timeout + summary.valid.crash +
  summary.invalid.accepted + summary.invalid.runtimeError + summary.invalid.timeout + summary.invalid.crash;

if (bad || opts.keep) {
  console.error(`repros in ${repro}`);
} else {
  fs.rmSync(work, { recursive: true, force: true });
}

process.exit(bad === 0 ? 0 : 1);
