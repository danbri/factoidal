#!/usr/bin/env node
// webcrypto-differential.mjs — check the Lean JOSE verifier against an
// independent implementation of the same two algorithms.
//
// Why a differential and not more fixtures: a fixture corpus tests the
// cases somebody thought to write down. This generates fresh keys and
// fresh messages on every run with Node's WebCrypto (which is OpenSSL
// underneath), signs them there, and asks the Lean binary whether it
// accepts. Two independent implementations agreeing on 200 random
// signatures per algorithm is evidence the fixtures cannot give.
//
// Both directions are checked. A verifier that answers `true` to
// everything passes the accept half and fails the refuse half, so each
// signature is also presented with one bit flipped at a random position
// and must be refused.
//
// The binary is `lake exe l4jose-probe --jsonl`: one JSON request per
// line in, one JSON response per line out, in order.
//
//   request  {"alg":"ES256"|"RS256","key":{JWK},"msg":"<hex>","sig":"<hex>"}
//   response {"ok":true|false} | {"error":"..."}
//
// Exit codes: 0 all agreed; 1 a disagreement; 77 skipped because the
// native binary is absent (a skip is printed with its reason and is
// never silent).

import { webcrypto } from 'node:crypto';
import { spawn } from 'node:child_process';
import { existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

const subtle = webcrypto.subtle;
const getRandomValues = (a) => webcrypto.getRandomValues(a);

const here = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(here, '..', '..');
const binary = resolve(repoRoot, 'formal/lean4/.lake/build/bin/l4jose-probe');

const PER_ALG = Number(process.env.JOSE_DIFF_COUNT ?? 200);

if (!existsSync(binary)) {
  console.log(`SKIP jose webcrypto differential: ${binary} not built ` +
              `(build it with: cd formal/lean4 && lake build l4jose-probe)`);
  process.exit(77);
}

const hex = (buf) =>
  [...new Uint8Array(buf)].map((b) => b.toString(16).padStart(2, '0')).join('');

function flipOneBit(bytes) {
  const out = Uint8Array.from(bytes);
  const i = Math.floor(Math.random() * out.length);
  const bit = 1 << Math.floor(Math.random() * 8);
  out[i] ^= bit;
  return out;
}

/** Everything the JWK carries that this project does not read is dropped,
 *  so the request is exactly the members RFC 7518 requires. */
function publicJwk(jwk) {
  if (jwk.kty === 'EC') return { kty: 'EC', crv: jwk.crv, x: jwk.x, y: jwk.y };
  if (jwk.kty === 'RSA') return { kty: 'RSA', n: jwk.n, e: jwk.e };
  throw new Error(`unexpected kty ${jwk.kty}`);
}

async function buildCases() {
  const cases = [];

  // ES256: ECDSA P-256 with SHA-256, raw r || s (RFC 7518 section 3.4).
  const ec = await subtle.generateKey(
    { name: 'ECDSA', namedCurve: 'P-256' }, true, ['sign', 'verify']);
  const ecJwk = publicJwk(await subtle.exportKey('jwk', ec.publicKey));
  for (let i = 0; i < PER_ALG; i++) {
    const msg = getRandomValues(new Uint8Array(1 + Math.floor(Math.random() * 200)));
    const sig = new Uint8Array(await subtle.sign(
      { name: 'ECDSA', hash: 'SHA-256' }, ec.privateKey, msg));
    cases.push({ alg: 'ES256', key: ecJwk, msg: hex(msg), sig: hex(sig), expect: true });
    cases.push({ alg: 'ES256', key: ecJwk, msg: hex(msg),
                 sig: hex(flipOneBit(sig)), expect: false });
  }

  // RS256: RSASSA-PKCS1-v1_5 with SHA-256, 2048-bit modulus
  // (RFC 7518 section 3.3's floor).
  const rsa = await subtle.generateKey(
    { name: 'RSASSA-PKCS1-v1_5', modulusLength: 2048,
      publicExponent: new Uint8Array([1, 0, 1]), hash: 'SHA-256' },
    true, ['sign', 'verify']);
  const rsaJwk = publicJwk(await subtle.exportKey('jwk', rsa.publicKey));
  for (let i = 0; i < PER_ALG; i++) {
    const msg = getRandomValues(new Uint8Array(1 + Math.floor(Math.random() * 200)));
    const sig = new Uint8Array(await subtle.sign(
      'RSASSA-PKCS1-v1_5', rsa.privateKey, msg));
    cases.push({ alg: 'RS256', key: rsaJwk, msg: hex(msg), sig: hex(sig), expect: true });
    cases.push({ alg: 'RS256', key: rsaJwk, msg: hex(msg),
                 sig: hex(flipOneBit(sig)), expect: false });
  }

  return cases;
}

function runProbe(lines) {
  return new Promise((res, rej) => {
    const child = spawn(binary, ['--jsonl'], { stdio: ['pipe', 'pipe', 'inherit'] });
    let out = '';
    child.stdout.setEncoding('utf8');
    child.stdout.on('data', (d) => { out += d; });
    child.on('error', rej);
    child.on('close', (code) => {
      if (code !== 0) rej(new Error(`l4jose-probe --jsonl exited ${code}`));
      else res(out.split('\n').filter((l) => l.trim() !== ''));
    });
    child.stdin.end(lines.join('\n') + '\n');
  });
}

const cases = await buildCases();
const requests = cases.map((c) =>
  JSON.stringify({ alg: c.alg, key: c.key, msg: c.msg, sig: c.sig }));
const responses = await runProbe(requests);

if (responses.length !== cases.length) {
  console.error(`FAIL jose webcrypto differential: sent ${cases.length} requests, ` +
                `read ${responses.length} responses`);
  process.exit(1);
}

const tally = { ES256: { pass: 0, fail: 0 }, RS256: { pass: 0, fail: 0 } };
const failures = [];
for (let i = 0; i < cases.length; i++) {
  const c = cases[i];
  let got;
  try {
    const parsed = JSON.parse(responses[i]);
    if ('error' in parsed) { got = `error: ${parsed.error}`; }
    else { got = parsed.ok; }
  } catch {
    got = `unparseable: ${responses[i]}`;
  }
  if (got === c.expect) tally[c.alg].pass++;
  else {
    tally[c.alg].fail++;
    if (failures.length < 5) {
      failures.push(`${c.alg} case ${i}: WebCrypto says ${c.expect}, ` +
                    `Lean says ${JSON.stringify(got)}`);
    }
  }
}

for (const f of failures) console.error(`  ${f}`);

const total = (a) => tally[a].pass + tally[a].fail;
console.log(`jose-webcrypto-differential ES256: ${tally.ES256.pass} pass, ` +
            `${tally.ES256.fail} fail (out of ${total('ES256')}) ` +
            `[${PER_ALG} signatures, each also with one bit flipped]`);
console.log(`jose-webcrypto-differential RS256: ${tally.RS256.pass} pass, ` +
            `${tally.RS256.fail} fail (out of ${total('RS256')}) ` +
            `[${PER_ALG} signatures, each also with one bit flipped]`);

process.exit(tally.ES256.fail + tally.RS256.fail === 0 ? 0 : 1);
