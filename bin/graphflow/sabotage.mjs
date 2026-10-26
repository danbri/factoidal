#!/usr/bin/env node
// graphflow/sabotage.mjs — break each guard on purpose and confirm it fails.
//
// A check nobody has watched fail is not known to work. Several cases here are
// FAITHFUL adversaries: they edit the network, recompute its hash, and re-sign
// the certificate with the demo key, so every other check still passes and the
// case isolates exactly one guard. A tamper that trips five checks at once
// proves nothing about any of them.
//
//   node bin/graphflow/sabotage.mjs [case ...]

import { createHash, createPrivateKey, sign as cryptoSign } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = dirname(fileURLToPath(import.meta.url));
const CERT = resolve(HERE, '../../tmp/graphflow.cert.json');
const CHECK = resolve(HERE, 'check.mjs');
const DEMO_SK = '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60';

const sha256Text = (s) => createHash('sha256').update(Buffer.from(s, 'utf8')).digest('hex');
function canonicalJson(v) {
  if (v === null || typeof v !== 'object') return JSON.stringify(v);
  if (Array.isArray(v)) return '[' + v.map(canonicalJson).join(',') + ']';
  return '{' + Object.keys(v).sort().map((k) => JSON.stringify(k) + ':' + canonicalJson(v[k])).join(',') + '}';
}

/** Re-sign a tampered certificate with the demo key, the way an attacker who
 *  read run.mjs would. The demo key is published in this repository, so the
 *  signature is not what stops tampering — the recomputed hashes are. */
function resign(cert) {
  const { signature, ...body } = cert;
  const bodyHash = sha256Text(canonicalJson(body));
  const pkcs8 = Buffer.concat([Buffer.from('302e020100300506032b657004220420', 'hex'),
                               Buffer.from(DEMO_SK, 'hex')]);
  const key = createPrivateKey({ key: pkcs8, format: 'der', type: 'pkcs8' });
  return { ...body, signature: { ...signature, bodySha256: bodyHash,
    value: cryptoSign(null, Buffer.from(bodyHash, 'utf8'), key).toString('hex') } };
}

const load = () => JSON.parse(readFileSync(CERT, 'utf8'));

const CASES = {
  'chain-broken': () => {
    const c = load();
    // The closure's output no longer matches what validate says it consumed.
    c.transforms.find((t) => t.process === 'closure').outputs.out.sha256 = 'f'.repeat(64);
    return resign(c);
  },
  'iip-swapped': () => {
    const c = load();
    // Swap the data the network says it started from, keeping the network hash
    // honest and re-signing. Only the initial-packet anchor can catch this.
    c.network.nquads = c.network.nquads.replace('ex:Dog rdfs:subClassOf ex:Mammal', 'ex:Dog rdfs:subClassOf ex:Reptile');
    c.network.sha256 = sha256Text(c.network.nquads);
    return resign(c);
  },
  'process-added': () => {
    const c = load();
    const t = JSON.parse(JSON.stringify(c.transforms[0]));
    t.process = 'ghost';
    c.transforms.push(t);
    return resign(c);
  },
  'mode-lied': () => {
    const c = load();
    c.transforms.find((t) => t.process === 'closure').mode = 'Streamable';
    return resign(c);
  },
  'streaming-claimed': () => {
    const c = load();
    c.network.claimsStreaming = true;
    c.network.nquads = c.network.nquads.replace(
      '"false"^^<http://www.w3.org/2001/XMLSchema#boolean>',
      '"true"^^<http://www.w3.org/2001/XMLSchema#boolean>');
    c.network.sha256 = sha256Text(c.network.nquads);
    return resign(c);
  },
  'canonicalize-faked': () => {
    const c = load();
    // Move canon's output AND sign's input together, so the chain still lines
    // up and ONLY the canonicalize invariant (output hash = input's canonical
    // hash) can catch it. Tampering just one end is caught by the chain check
    // instead, which would leave this guard untested.
    c.transforms.find((t) => t.process === 'canon').outputs.out.sha256 = 'a'.repeat(64);
    c.transforms.find((t) => t.process === 'sign').inputs.text.sha256 = 'a'.repeat(64);
    return resign(c);
  },
  'inline-value-lied': () => {
    const c = load();
    // Claim the data conformed. The hash still says otherwise.
    c.transforms.find((t) => t.process === 'validate').outputs.conforms.value = true;
    return resign(c);
  },
  'signature-stale': () => {
    const c = load();
    // Alter something the network description does NOT pin — the engine
    // version — and do not re-sign. Only the signature can catch this; a field
    // the description pins would be caught by the coverage check instead.
    c.engine.version = '9.9.9';
    return c;
  },
  'empty-network': () => {
    const c = load();
    c.transforms = [];
    return resign(c);
  },
};

const names = process.argv.slice(2).length ? process.argv.slice(2) : Object.keys(CASES);
let bit = 0, missed = 0;
for (const name of names) {
  const make = CASES[name];
  if (!make) { console.log(`unknown case: ${name}`); process.exit(2); }
  const path = `/tmp/graphflow.${name}.cert.json`;
  writeFileSync(path, JSON.stringify(make(), null, 2));
  let output = '', failed = false;
  try {
    output = execFileSync(process.execPath, [CHECK, path], { encoding: 'utf8' });
  } catch (e) {
    failed = true;
    output = (e.stdout || '') + (e.stderr || '');
  }
  const reason = (output.split('\n').find((l) => l.includes('✗')) || '').trim().slice(0, 96);
  if (failed) { bit++; console.log(`  ✓ ${name.padEnd(19)} caught: ${reason || '<non-zero exit>'}`); }
  else { missed++; console.log(`  ✗ ${name.padEnd(19)} SABOTAGE WENT UNNOTICED — the checker accepted it`); }
}
console.log(`\nsabotage: ${bit} guard(s) bit, ${missed} did not`);
process.exit(missed === 0 ? 0 : 1);
