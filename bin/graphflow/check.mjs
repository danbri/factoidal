#!/usr/bin/env node
// graphflow/check.mjs — compose per-transform certificates into a verdict
// about a whole network.
//
// TRUSTED, and deliberately small. Borrowed wholesale from the dickory
// bridge's checker discipline:
//
//   * It never runs the engine. No @factoidal/core import, no CLI, no wasm.
//     A checker that re-runs the thing it is checking has re-imported the
//     trust it exists to remove.
//   * It never reads a file it was not handed, and never touches the network.
//   * It never believes the certificate about anything it can re-derive. The
//     wiring comes from the network's own canonical N-Quads — which is why
//     the certificate embeds them — not from the runner's provenance claims.
//   * It never emits a partial pass. Exit 0 means every check passed; it
//     collects and prints ALL failures rather than stopping at the first.
//   * It prints what it does NOT establish, every time.
//
// N-Quads is line-oriented, so re-deriving the network needs a ~40-line
// tokenizer rather than an RDF engine. That is the whole reason the
// certificate carries canonical N-Quads instead of Turtle.
//
//   node bin/graphflow/check.mjs <certificate.json>

import { createHash, createPublicKey, verify as cryptoVerify } from 'node:crypto';
import { readFileSync } from 'node:fs';

const GF = 'http://factoidal.example/ns/graphflow#';
const sha256Text = (s) => createHash('sha256').update(Buffer.from(s, 'utf8')).digest('hex');

function canonicalJson(value) {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return '[' + value.map(canonicalJson).join(',') + ']';
  return '{' + Object.keys(value).sort()
    .map((k) => JSON.stringify(k) + ':' + canonicalJson(value[k])).join(',') + '}';
}

// --- a minimal N-Quads reader (no RDF engine) ------------------------------

function unescapeLiteral(s) {
  return s.replace(/\\u([0-9A-Fa-f]{4})|\\U([0-9A-Fa-f]{8})|\\(.)/g, (m, u4, u8, c) => {
    if (u4) return String.fromCodePoint(parseInt(u4, 16));
    if (u8) return String.fromCodePoint(parseInt(u8, 16));
    return { n: '\n', r: '\r', t: '\t', b: '\b', f: '\f', '"': '"', "'": "'", '\\': '\\' }[c] ?? c;
  });
}

function parseNQuads(text) {
  const triples = [];
  for (const rawLine of text.split('\n')) {
    const line = rawLine.trim();
    if (!line || line.startsWith('#')) continue;
    let i = 0;
    const term = () => {
      while (line[i] === ' ') i++;
      if (line[i] === '<') { const e = line.indexOf('>', i); const v = line.slice(i + 1, e); i = e + 1; return { type: 'iri', value: v }; }
      if (line[i] === '_') { let e = i; while (e < line.length && !' \t'.includes(line[e])) e++; const v = line.slice(i, e); i = e; return { type: 'bnode', value: v }; }
      if (line[i] === '"') {
        let e = i + 1, out = '';
        while (e < line.length) {
          if (line[e] === '\\') { out += line[e] + line[e + 1]; e += 2; continue; }
          if (line[e] === '"') break;
          out += line[e]; e++;
        }
        i = e + 1;
        let datatype = null, lang = null;
        if (line[i] === '^') { const s = line.indexOf('<', i); const en = line.indexOf('>', s); datatype = line.slice(s + 1, en); i = en + 1; }
        else if (line[i] === '@') { let e2 = i + 1; while (e2 < line.length && !' \t'.includes(line[e2])) e2++; lang = line.slice(i + 1, e2); i = e2; }
        return { type: 'literal', value: unescapeLiteral(out), datatype, lang };
      }
      return null;
    };
    const s = term(), p = term(), o = term();
    if (s && p && o) triples.push({ s, p, o });
  }
  return triples;
}

/** Rebuild the network's structure from its triples. Nothing here trusts the
 *  certificate: this is the network as the RDF says it is. */
function networkFromTriples(triples) {
  const has = (s, p, o) => triples.some((t) => t.s.value === s && t.p.value === GF + p && t.o.value === o);
  const objs = (s, p) => triples.filter((t) => t.s.value === s && t.p.value === GF + p).map((t) => t.o);
  const one = (s, p) => (objs(s, p)[0] ?? null);
  const subjectsOfType = (cls) => triples
    .filter((t) => t.p.value === 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type' && t.o.value === GF + cls)
    .map((t) => t.s.value);

  const netIri = subjectsOfType('Network')[0];
  const network = netIri ? {
    iri: netIri,
    name: one(netIri, 'name')?.value ?? null,
    claimsStreaming: (one(netIri, 'claimsStreaming')?.value ?? 'false') === 'true',
    processIris: objs(netIri, 'process').map((o) => o.value),
  } : null;

  const processes = {};
  for (const iri of subjectsOfType('Process')) {
    const name = one(iri, 'name')?.value;
    const componentIri = one(iri, 'component')?.value;
    processes[name] = {
      iri, name, componentIri,
      component: componentIri ? componentIri.split('#').pop() : null,
      fn: componentIri ? one(componentIri, 'fn')?.value : null,
      mode: componentIri ? one(componentIri, 'mode')?.value?.split('#').pop() : null,
      semantics: componentIri ? one(componentIri, 'semantics')?.value : null,
      inNetwork: network ? network.processIris.includes(iri) : false,
    };
  }

  const byIri = Object.fromEntries(Object.values(processes).map((p) => [p.iri, p.name]));
  const connections = subjectsOfType('Connection').map((iri) => ({
    from: byIri[one(iri, 'fromProcess')?.value],
    fromPort: one(iri, 'fromPort')?.value,
    to: byIri[one(iri, 'toProcess')?.value],
    toPort: one(iri, 'toPort')?.value,
  }));

  const iips = subjectsOfType('InitialPacket').map((iri) => ({
    process: byIri[one(iri, 'targetProcess')?.value],
    port: one(iri, 'targetPort')?.value,
    value: one(iri, 'value')?.value,
  }));

  // Declared input ports per component fn, so a dangling input is visible.
  const inPorts = {};
  for (const t of triples.filter((t) => t.p.value === GF + 'portOf')) {
    const portIri = t.s.value, compIri = t.o.value;
    const dir = one(portIri, 'direction')?.value;
    const fnName = one(compIri, 'fn')?.value;
    if (!fnName || !dir) continue;
    const bucket = dir.endsWith('#In') ? 'in' : 'out';
    (inPorts[fnName] ??= { in: [], out: [] })[bucket].push(one(portIri, 'name')?.value);
  }

  return { network, processes, connections, iips, ports: inPorts };
}

// --- the report ------------------------------------------------------------

class Report {
  constructor() { this.failures = []; }
  require(cond, message) { if (!cond) this.failures.push(message); return cond; }
}

function checkSignature(cert, rep) {
  const sig = cert.signature;
  if (!rep.require(sig && sig.suite === 'ed25519', 'certificate carries no ed25519 signature')) return;
  const { signature, ...body } = cert;
  const bodyHash = sha256Text(canonicalJson(body));
  rep.require(bodyHash === sig.bodySha256,
    `signed body hash ${sig.bodySha256} does not match the certificate's actual body (${bodyHash})`);
  try {
    // The raw 32-byte key wrapped as SPKI DER, so node's OpenSSL can load it.
    // Note whose crypto verifies: the signature was produced by HACL* (the
    // F*/Low*-verified library the engine ships) and is checked here by a
    // DIFFERENT implementation. Agreement across two implementations is worth
    // more than a round trip through one.
    const spki = Buffer.concat([Buffer.from('302a300506032b6570032100', 'hex'),
                                Buffer.from(sig.publicKeyHex, 'hex')]);
    const key = createPublicKey({ key: spki, format: 'der', type: 'spki' });
    const ok = cryptoVerify(null, Buffer.from(bodyHash, 'utf8'), key, Buffer.from(sig.value, 'hex'));
    rep.require(ok, 'ed25519 signature does not verify over the certificate body');
  } catch (e) {
    rep.require(false, `ed25519 signature could not be checked: ${e.message}`);
  }
}

function checkNetwork(cert, rep) {
  if (!rep.require(cert.network && typeof cert.network.nquads === 'string',
                   'certificate embeds no network description')) return null;
  const recomputed = sha256Text(cert.network.nquads);
  rep.require(recomputed === cert.network.sha256,
    `network sha256 ${cert.network.sha256} does not match the embedded bytes (${recomputed})`);
  const desc = networkFromTriples(parseNQuads(cert.network.nquads));
  rep.require(desc.network !== null, 'the embedded description contains no gf:Network');
  if (desc.network) {
    rep.require(desc.network.name === cert.network.name,
      `certificate calls the network ${JSON.stringify(cert.network.name)}, the description calls it ${JSON.stringify(desc.network.name)}`);
    rep.require(desc.network.claimsStreaming === !!cert.network.claimsStreaming,
      'the certificate and the description disagree about the streaming claim');
  }
  rep.require(Object.keys(desc.processes).length > 0,
    'the embedded description declares no processes — refusing to certify an empty network');
  return desc;
}

function checkCoverage(cert, desc, rep) {
  const certified = new Set(cert.transforms.map((t) => t.process));
  const declared = new Set(Object.values(desc.processes).filter((p) => p.inNetwork).map((p) => p.name));
  for (const name of declared) {
    rep.require(certified.has(name), `process ${name} is in the network but has no transform certificate`);
  }
  for (const name of certified) {
    rep.require(declared.has(name), `transform certificate for ${name}, which the network does not declare`);
  }
  rep.require(cert.transforms.length === new Set(cert.transforms.map((t) => t.process)).size,
    'two transform certificates for the same process');

  // What each transform CLAIMS about itself must match the description.
  for (const t of cert.transforms) {
    const p = desc.processes[t.process];
    if (!p) continue;
    rep.require(t.fn === p.fn, `${t.process}: certificate says fn ${t.fn}, the network says ${p.fn}`);
    rep.require(t.mode === p.mode, `${t.process}: certificate says mode ${t.mode}, the network says ${p.mode}`);
    rep.require(t.semantics === p.semantics,
      `${t.process}: certificate's semantics string is not the one the network declares`);
  }
}

function checkChaining(cert, desc, rep) {
  const byProcess = Object.fromEntries(cert.transforms.map((t) => [t.process, t]));

  for (const c of desc.connections) {
    const up = byProcess[c.from], down = byProcess[c.to];
    if (!rep.require(up && down, `connection ${c.from}.${c.fromPort} -> ${c.to}.${c.toPort} names an uncertified process`)) continue;
    const produced = up.outputs?.[c.fromPort];
    const consumed = down.inputs?.[c.toPort];
    if (!rep.require(produced, `${c.from} certifies no output on port ${c.fromPort}`)) continue;
    if (!rep.require(consumed, `${c.to} certifies no input on port ${c.toPort}`)) continue;
    rep.require(produced.sha256 === consumed.sha256,
      `broken chain: ${c.from}.${c.fromPort} produced ${produced.sha256.slice(0, 16)}… but ` +
      `${c.to}.${c.toPort} consumed ${consumed.sha256.slice(0, 16)}…`);
    rep.require(produced.kind === consumed.kind,
      `kind mismatch across ${c.from}.${c.fromPort} -> ${c.to}.${c.toPort}: ${produced.kind} vs ${consumed.kind}`);
    rep.require(consumed.from && consumed.from.process === c.from && consumed.from.port === c.fromPort,
      `${c.to}.${c.toPort} claims a different source than the network wires it to`);
  }

  // Initial packets anchor the chain: their hash is recomputable from the
  // network's own bytes, so the whole dataflow is pinned to the description.
  for (const iip of desc.iips) {
    const t = byProcess[iip.process];
    if (!rep.require(t, `initial packet for uncertified process ${iip.process}`)) continue;
    const consumed = t.inputs?.[iip.port];
    if (!rep.require(consumed, `${iip.process} certifies no input on port ${iip.port}`)) continue;
    const expected = sha256Text(iip.value);
    rep.require(consumed.sha256 === expected,
      `${iip.process}.${iip.port} consumed ${consumed.sha256.slice(0, 16)}… but the network's ` +
      `initial packet hashes to ${expected.slice(0, 16)}…`);
    rep.require(consumed.from === 'iip', `${iip.process}.${iip.port} does not declare its initial packet`);
  }

  // No input may be fed by nothing, and none may be fed twice.
  for (const t of cert.transforms) {
    const p = desc.processes[t.process];
    const declaredIn = desc.ports[p?.fn]?.in ?? [];
    for (const port of declaredIn) {
      const wires = desc.connections.filter((c) => c.to === t.process && c.toPort === port).length;
      const packets = desc.iips.filter((i) => i.process === t.process && i.port === port).length;
      rep.require(wires + packets === 1,
        `${t.process}.${port} is fed by ${wires + packets} sources; exactly one is required`);
    }
  }
}

/** A few claims are checkable here, with no engine, because the hashing rules
 *  pin them. Everything else in a transform is taken on the runner's word —
 *  see reportLimits(). Checking what CAN be checked is not a formality: it is
 *  the difference between a certificate that chains and one that is merely
 *  self-consistent. */
function checkDerivableTransforms(cert, rep) {
  for (const t of cert.transforms) {
    // canonicalize: hash(Dataset) is defined as sha256 of the canonical form,
    // and canonicalize emits exactly that form as Text. So its output hash
    // MUST equal its input hash — a genuine engine-free check on a real
    // transform, not just on the plumbing around it.
    if (t.fn === 'canonicalize') {
      const inHash = t.inputs?.ds?.sha256, outHash = t.outputs?.out?.sha256;
      if (inHash && outHash) {
        rep.require(inHash === outHash,
          `${t.process}: canonicalize output ${outHash.slice(0, 16)}… must equal its input's ` +
          `canonical hash ${inHash.slice(0, 16)}…, because hash(dataset) IS sha256 of the canonical form`);
      }
    }
    // Any inline value must hash to what the certificate claims for it.
    for (const [port, out] of Object.entries(t.outputs ?? {})) {
      if (!('value' in out)) continue;
      const recomputed = sha256Text(canonicalJson(out.value));
      rep.require(recomputed === out.sha256,
        `${t.process}.${port}: inline value hashes to ${recomputed.slice(0, 16)}… but the ` +
        `certificate claims ${out.sha256.slice(0, 16)}…`);
    }
  }
}

function checkStreaming(cert, desc, rep) {
  if (!cert.network?.claimsStreaming) return;
  const blocking = cert.transforms.filter((t) => t.mode === 'WholeGraph').map((t) => `${t.process} (${t.fn})`);
  rep.require(blocking.length === 0,
    `the network claims end-to-end streaming but contains whole-graph components: ${blocking.join(', ')}. ` +
    'A whole-graph transform cannot emit anything until its entire input has arrived.');
}

function reportLimits() {
  console.log('\nLIMITS — what this pass does NOT establish:');
  for (const line of [
    'that any transform computed the right answer, EXCEPT the two kinds whose',
    '  hashing rules pin them (canonicalize, and inline JSON values). Dataset',
    '  hashes come from',
    '  RDFC-1.0 canonicalisation, which this checker cannot recompute without',
    '  the engine — it checks that the hashes CHAIN, not that they are earned',
    'that the network description is the one you meant (nothing mechanical can)',
    'that the engine is correct, or that the extracted code matches its F* source',
    'that the signer is anyone in particular — the signature shows the',
    '  certificate is unaltered since the run, not that it is endorsed',
    'anything about time: there is no attestation of when the run happened',
  ]) console.log('  - ' + line);
}

const [certPath] = process.argv.slice(2);
if (!certPath) { console.error('usage: check.mjs <certificate.json>'); process.exit(2); }
const cert = JSON.parse(readFileSync(certPath, 'utf8'));

const rep = new Report();
rep.require(cert.format === 'graphflow-cert/0.1',
  `unknown certificate format ${JSON.stringify(cert.format)} (this checker implements graphflow-cert/0.1)`);
rep.require(Array.isArray(cert.transforms) && cert.transforms.length > 0,
  'certificate carries no transforms');

const desc = checkNetwork(cert, rep);
if (desc && Array.isArray(cert.transforms)) {
  checkCoverage(cert, desc, rep);
  checkChaining(cert, desc, rep);
  checkDerivableTransforms(cert, rep);
  checkStreaming(cert, desc, rep);
}
checkSignature(cert, rep);

if (rep.failures.length) {
  console.log(`REJECTED: ${certPath}`);
  for (const f of rep.failures) console.log('  ✗ ' + f);
  process.exit(1);
}

console.log(`ACCEPTED: ${certPath}`);
console.log(`  network    ${cert.network.name} (${cert.network.sha256.slice(0, 16)}…)`);
console.log(`  engine     ${cert.engine.package} ${cert.engine.version}`);
for (const t of cert.transforms) {
  const ins = Object.entries(t.inputs).map(([p, v]) => `${p}:${v.sha256.slice(0, 8)}`).join(' ') || '—';
  const outs = Object.entries(t.outputs).map(([p, v]) =>
    'value' in v ? `${p}=${JSON.stringify(v.value)}` : `${p}:${v.sha256.slice(0, 8)}`).join(' ') || '—';
  console.log(`  ${t.process.padEnd(9)} ${t.fn.padEnd(13)} ${ins}  ⟶  ${outs}`);
}
console.log(`  signature  ed25519 by ${cert.signature.publicKeyHex.slice(0, 16)}… verified with node:crypto`);
console.log(`\nCOMPOSED — ${cert.transforms.length} transform certificates chain into one network certificate:`);
console.log(`  every wire in ${cert.network.name} carries the hash its producer certified,`);
console.log('  and every initial packet hashes to the value the network description holds.');
reportLimits();
