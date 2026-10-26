#!/usr/bin/env node
// graphflow/run.mjs — execute an RDF-described transform network over
// @factoidal/core's functional API, emitting one transform certificate per
// process.
//
// A CONSUMER TOOL (Iron Rule 11): no RDF or SPARQL semantics live here. Every
// transform is an fn.* call into the extracted engine; this file only reads
// the network description (with the engine), orders the processes, moves
// values along wires, and records hashes.
//
// UNTRUSTED. This program can lie about what it did. Catching that is
// check.mjs's job, which is why check.mjs re-derives the wiring from the
// network's own canonical bytes instead of believing the certificate.
//
//   node bin/graphflow/run.mjs [network.ttl] [-o out.cert.json]

import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const require = createRequire(import.meta.url);
const HERE = dirname(fileURLToPath(import.meta.url));
const fn = require(resolve(HERE, '../../npm/factoidal/fn.js'));

const GF = 'http://factoidal.example/ns/graphflow#';

// A demo key, deliberately hard-coded and deliberately not a secret: the
// signature proves the certificate was not altered after the run, not that
// anyone in particular vouches for it. A real deployment supplies its own.
const DEMO_SK = process.env.GRAPHFLOW_SK ||
  '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60';

const sha256 = (buf) => createHash('sha256').update(buf).digest('hex');
const sha256Text = (s) => sha256(Buffer.from(s, 'utf8'));

/** Key-sorted JSON, so a JSON value has one hash and one signable form. */
function canonicalJson(value) {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return '[' + value.map(canonicalJson).join(',') + ']';
  return '{' + Object.keys(value).sort()
    .map((k) => JSON.stringify(k) + ':' + canonicalJson(value[k])).join(',') + '}';
}

// ---------------------------------------------------------------------------
// Reading the network. NOTE the guard: as of 2026-08-23 the npm entry's
// parseToDatasetJson reports a parse FAILURE as {"ok":true,"count":0}, so
// fn.parse() returns an empty dataset for malformed Turtle instead of
// throwing (the CLI gets this right and exits 1; the JS path does not).
// Ingesting a network description through that would mean a typo silently
// becomes "a network with no processes", which would then certify nothing at
// all and report success. Every parse here is floor-checked.
// ---------------------------------------------------------------------------

async function parseChecked(text, label, minTriples) {
  const ds = await fn.parse(text, { format: 'turtle' });
  if (ds.size < minTriples) {
    throw new Error(
      `${label}: parsed ${ds.size} triples, expected at least ${minTriples}. ` +
      'A malformed document parses as empty on the JS path — check the Turtle ' +
      'with `bin/<platform>/factoidal --dump-nq -d <file>`, which does report errors.');
  }
  return ds;
}

async function loadNetwork(networkPath) {
  const parts = [
    [resolve(HERE, 'vocab.ttl'), 'vocab.ttl', 20],
    [resolve(HERE, 'components.ttl'), 'components.ttl', 40],
    [networkPath, 'network', 20],
  ];
  let ds = fn.EMPTY;
  for (const [path, label, floor] of parts) {
    ds = fn.union(ds, await parseChecked(readFileSync(path, 'utf8'), label, floor));
  }
  return ds;
}

const rowsToObjects = (rows) =>
  rows.map((r) => Object.fromEntries([...r.entries()].map(([k, v]) => [k, v.value])));

async function describeNetwork(ds) {
  const q = async (sparql) =>
    rowsToObjects(await fn.query(ds, `PREFIX gf: <${GF}>\n${sparql}`));

  const network = (await q(
    'SELECT ?iri ?name ?streaming WHERE { ?iri a gf:Network ; gf:name ?name . ' +
    'OPTIONAL { ?iri gf:claimsStreaming ?streaming } }'))[0];
  if (!network) throw new Error('no gf:Network in the description');

  const processes = await q(
    'SELECT ?name ?component ?fn ?mode ?semantics WHERE { ' +
    '?net a gf:Network ; gf:process ?p . ' +
    '?p gf:name ?name ; gf:component ?component . ' +
    '?component gf:fn ?fn ; gf:mode ?mode ; gf:semantics ?semantics } ORDER BY ?name');
  if (processes.length === 0) throw new Error('the network declares no processes');

  const connections = await q(
    'SELECT ?from ?fromPort ?to ?toPort WHERE { ' +
    '?c a gf:Connection ; gf:fromProcess ?f ; gf:fromPort ?fromPort ; ' +
    'gf:toProcess ?t ; gf:toPort ?toPort . ?f gf:name ?from . ?t gf:name ?to } ' +
    'ORDER BY ?from ?to ?toPort');

  const iips = await q(
    'SELECT ?process ?port ?value WHERE { ' +
    '?i a gf:InitialPacket ; gf:targetProcess ?p ; gf:targetPort ?port ; gf:value ?value . ' +
    '?p gf:name ?process } ORDER BY ?process ?port');

  const ports = await q(
    'SELECT ?fn ?direction ?port ?kind WHERE { ' +
    '?c gf:fn ?fn . ?portIri gf:portOf ?c ; gf:direction ?direction ; ' +
    'gf:name ?port ; gf:kind ?kind } ORDER BY ?fn ?direction ?port');

  return { network, processes, connections, iips, ports };
}

// ---------------------------------------------------------------------------
// Components: the ONLY hand-written glue, and every line of it is a call into
// the extracted engine. Adding a component means adding a row here and a
// declaration in components.ttl — the second is what ends up in certificates.
// ---------------------------------------------------------------------------

const COMPONENTS = {
  parse: async (i) => ({ out: { kind: 'Dataset', value: await fn.parse(i.text.value, { format: 'turtle' }) } }),

  rhoDfClosure: async (i) => {
    const r = await fn.rhoDfClosure(i.ds.value);
    if (!r.ok) throw new Error('rhoDfClosure: engine reported ok=false');
    return { out: { kind: 'Dataset', value: r.dataset } };
  },

  validate: async (i) => {
    const r = await fn.validate(i.ds.value, i.shapes.value);
    return {
      conforms: { kind: 'Json', value: r.conforms },
      report: { kind: 'Dataset', value: r.report },
    };
  },

  canonicalize: async (i) => ({ kind: 'Text', out: { kind: 'Text', value: await fn.canonicalize(i.ds.value) } }),

  signEd25519: async (i) => ({
    out: {
      kind: 'Text',
      value: await fn.vcEd25519Sign(DEMO_SK, Buffer.from(i.text.value, 'utf8').toString('hex')),
    },
  }),
};

/** One content hash per kind. Datasets go through RDFC-1.0, so two datasets
 *  differing only in blank-node labels hash alike — which is what makes a
 *  certificate about MEANING rather than about serialisation. */
async function contentHash(v) {
  if (v.kind === 'Dataset') return fn.hash(v.value);
  if (v.kind === 'Text') return sha256Text(v.value);
  if (v.kind === 'Json') return sha256Text(canonicalJson(v.value));
  throw new Error(`no hash rule for kind ${v.kind}`);
}

function topoOrder(processes, connections) {
  const names = processes.map((p) => p.name);
  const incoming = new Map(names.map((n) => [n, 0]));
  const out = new Map(names.map((n) => [n, []]));
  for (const c of connections) {
    if (!incoming.has(c.from) || !incoming.has(c.to)) {
      throw new Error(`connection names a process not in the network: ${c.from} -> ${c.to}`);
    }
    incoming.set(c.to, incoming.get(c.to) + 1);
    out.get(c.from).push(c.to);
  }
  const ready = names.filter((n) => incoming.get(n) === 0).sort();
  const order = [];
  while (ready.length) {
    const n = ready.shift();
    order.push(n);
    for (const m of out.get(n)) {
      incoming.set(m, incoming.get(m) - 1);
      if (incoming.get(m) === 0) { ready.push(m); ready.sort(); }
    }
  }
  if (order.length !== names.length) {
    throw new Error('the network has a cycle; graphflow networks must be acyclic');
  }
  return order;
}

async function run(networkPath) {
  const ds = await loadNetwork(networkPath);
  const desc = await describeNetwork(ds);
  const byName = Object.fromEntries(desc.processes.map((p) => [p.name, p]));
  const portKind = {};
  for (const p of desc.ports) portKind[`${p.fn}|${p.direction.split('#').pop()}|${p.port}`] = p.kind.split('#').pop();

  const order = topoOrder(desc.processes, desc.connections);
  const values = {};        // "process.port" -> {kind, value}
  const transforms = [];

  for (const name of order) {
    const proc = byName[name];
    const impl = COMPONENTS[proc.fn];
    if (!impl) throw new Error(`no implementation registered for component fn "${proc.fn}"`);

    // Gather inputs: from wires first, then from initial information packets.
    const inputs = {};
    const inputProv = {};
    for (const c of desc.connections.filter((c) => c.to === name)) {
      const key = `${c.from}.${c.fromPort}`;
      if (!(key in values)) throw new Error(`input ${name}.${c.toPort} has no value from ${key}`);
      inputs[c.toPort] = values[key];
      inputProv[c.toPort] = { from: { process: c.from, port: c.fromPort } };
    }
    for (const iip of desc.iips.filter((i) => i.process === name)) {
      const kind = portKind[`${proc.fn}|In|${iip.port}`] || 'Text';
      inputs[iip.port] = { kind, value: iip.value };
      inputProv[iip.port] = { from: 'iip' };
    }

    const outputs = await impl(inputs);

    const certInputs = {};
    for (const [port, v] of Object.entries(inputs)) {
      certInputs[port] = { kind: v.kind, sha256: await contentHash(v), ...inputProv[port] };
    }
    const certOutputs = {};
    for (const [port, v] of Object.entries(outputs)) {
      if (!v || !v.kind) continue;
      values[`${name}.${port}`] = v;
      certOutputs[port] = { kind: v.kind, sha256: await contentHash(v) };
      // Small JSON answers travel inline: a certificate whose verdict is only
      // a hash makes the reader re-run the pipeline to learn the answer, and
      // the checker can re-derive an inline value's hash without the engine.
      if (v.kind === 'Json') certOutputs[port].value = v.value;
    }

    transforms.push({
      process: name,
      component: proc.component.split('#').pop(),
      fn: proc.fn,
      mode: proc.mode.split('#').pop(),
      semantics: proc.semantics,
      inputs: certInputs,
      outputs: certOutputs,
    });
    process.stderr.write(`  ran ${name.padEnd(9)} ${proc.fn.padEnd(14)} -> ` +
      Object.entries(certOutputs).map(([p, o]) => `${p}:${o.sha256.slice(0, 12)}`).join(' ') + '\n');
  }

  // The network's own bytes, canonicalised by the engine, so the checker can
  // re-derive the wiring without one.
  const networkNQuads = await fn.canonicalize(ds);

  const body = {
    format: 'graphflow-cert/0.1',
    network: {
      name: desc.network.name,
      claimsStreaming: desc.network.streaming === 'true',
      sha256: sha256Text(networkNQuads),
      nquads: networkNQuads,
    },
    engine: {
      package: '@factoidal/core',
      version: require(resolve(HERE, '../../npm/factoidal/package.json')).version,
    },
    transforms,
  };

  const pubKey = await fn.vcEd25519SecretToPublic(DEMO_SK);
  const bodyHash = sha256Text(canonicalJson(body));
  const cert = {
    ...body,
    signature: {
      suite: 'ed25519',
      publicKeyHex: pubKey,
      over: 'sha256(canonicalJson(certificate without .signature))',
      bodySha256: bodyHash,
      value: await fn.vcEd25519Sign(DEMO_SK, Buffer.from(bodyHash, 'utf8').toString('hex')),
    },
  };
  return cert;
}

const args = process.argv.slice(2);
const outIdx = args.indexOf('-o');
const outPath = outIdx >= 0 ? args[outIdx + 1] : resolve(HERE, '../../tmp/graphflow.cert.json');
const networkPath = args.find((a, i) => !a.startsWith('-') && args[i - 1] !== '-o') ||
  resolve(HERE, 'networks/validate-and-sign.ttl');

process.stderr.write(`network ${networkPath}\n`);
const cert = await run(networkPath);
writeFileSync(outPath, JSON.stringify(cert, null, 2) + '\n');
process.stderr.write(`wrote ${outPath} (${cert.transforms.length} transform certificates)\n`);
