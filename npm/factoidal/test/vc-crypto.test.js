// VC Data Integrity crypto under the JS target (js_of_ocaml + Node),
// backed by HACL*'s own official WebAssembly build (hacl-wasm) wired at
// the npm-entry layer. Mirrors bin/vc-runner/vc_runner.ml's `--crypto`
// self-test (8 native checks) and adds authoritative RFC 8032 / FIPS
// 180-4 vectors so correctness is proven, not asserted. GitHub #286.
//
// This is the off-native proof: the SAME F*-extracted VC_DataIntegrity
// pipeline that the native binary runs over vendored HACL* C runs here
// over HACL* wasm, exposed through factoidalNpmEntry.vc* .
//
// SECURITY: the negative cases (wrong key, tampered signature/proof,
// different document) MUST all report false. A verify that returns true
// without a real signature check is a security hole, not a pass.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const fs = require('node:fs');

const { initHacl } = require('../hacl-init.js');

// Load the freshly built npm-entry ABI bundle. Prefer the package-local
// copy; fall back to the build output under docs/fstar-extracted/.
function loadAbi() {
  const candidates = [
    path.join(__dirname, '..', 'factoidal-npm-entry.js'),
    path.join(__dirname, '..', '..', '..', 'docs', 'fstar-extracted',
      'factoidal-npm-entry.js'),
  ];
  for (const p of candidates) {
    if (!fs.existsSync(p)) continue;
    const mod = require(p);
    const abi = (mod && mod.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
    if (abi) return abi;
  }
  return null;
}

const J = (s) => JSON.parse(s);

// FIPS 180-4 / RFC 8032 test vectors (authoritative).
const SHA256_ABC =
  'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';
const RFC8032 = [
  { sk: '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60',
    pk: 'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a',
    msgHex: '',
    sig: 'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b' },
  { sk: '4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb',
    pk: '3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c',
    msgHex: '72',
    sig: '92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00' },
];

test('VC crypto over HACL* wasm (Node)', async (t) => {
  await initHacl();
  const abi = loadAbi();
  assert.ok(abi, 'factoidalNpmEntry ABI bundle must load (run build-ocaml.sh js)');
  for (const m of ['vcSha256Hex', 'vcEd25519SecretToPublic', 'vcEd25519Sign',
    'vcEd25519Verify', 'vcEddsaCreateFromCanonical',
    'vcEddsaVerifyFromCanonical']) {
    assert.equal(typeof abi[m], 'function', `ABI exposes ${m}`);
  }

  await t.test('SHA-256 matches FIPS 180-4 (abc)', () => {
    const r = J(abi.vcSha256Hex('abc'));
    assert.equal(r.ok, true);
    assert.equal(r.sha256, SHA256_ABC);
  });

  await t.test('Ed25519 reproduces RFC 8032 vectors (pubkey, sign, verify)', () => {
    for (const v of RFC8032) {
      const pk = J(abi.vcEd25519SecretToPublic(v.sk));
      assert.equal(pk.ok, true);
      assert.equal(pk.publicKeyHex, v.pk, 'derived pubkey == RFC 8032');

      const sig = J(abi.vcEd25519Sign(v.sk, v.msgHex));
      assert.equal(sig.ok, true);
      assert.equal(sig.signatureHex, v.sig, 'signature == RFC 8032');

      const ver = J(abi.vcEd25519Verify(v.pk, v.msgHex, v.sig));
      assert.equal(ver.ok, true);
      assert.equal(ver.valid, true, 'verify(RFC pk, msg, sig) == true');
    }
  });

  await t.test('Ed25519 verify rejects tamper / wrong key (security)', () => {
    const v = RFC8032[0];
    // Tampered signature -> false.
    const badSig = v.sig.slice(0, -2) + (v.sig.endsWith('00') ? '01' : '00');
    assert.equal(J(abi.vcEd25519Verify(v.pk, v.msgHex, badSig)).valid, false,
      'tampered signature must not verify');
    // Wrong public key -> false.
    assert.equal(J(abi.vcEd25519Verify(RFC8032[1].pk, v.msgHex, v.sig)).valid,
      false, 'wrong public key must not verify');
    // Different message -> false.
    assert.equal(J(abi.vcEd25519Verify(v.pk, '73', v.sig)).valid, false,
      'different message must not verify');
    // Malformed length -> false, never an exception-hidden true.
    assert.equal(J(abi.vcEd25519Verify('ab', v.msgHex, v.sig)).valid, false,
      'malformed public key must not verify');
  });

  await t.test('eddsa-rdfc-2022 roundtrip over canonical inputs (mirrors vc_runner)', () => {
    const sk = RFC8032[0].sk;
    const pk = J(abi.vcEd25519SecretToPublic(sk)).publicKeyHex;
    const pkWrong = J(abi.vcEd25519SecretToPublic(RFC8032[1].sk)).publicKeyHex;
    const doc =
      '<http://example.org/s> <http://example.org/p> "canonical value" .\n';
    const doc2 =
      '<http://example.org/s> <http://example.org/p> "TAMPERED value" .\n';
    const cfg =
      '_:pc <http://www.w3.org/ns/data-integrity#cryptosuite> "eddsa-rdfc-2022" .\n';

    const created = J(abi.vcEddsaCreateFromCanonical(sk, doc, cfg));
    assert.equal(created.ok, true);
    const pv = created.proofValue;
    assert.equal(typeof pv, 'string');
    assert.ok(pv.length > 0 && pv[0] === 'z', 'proofValue is multibase-z (base58btc)');

    // Correct key + document + proof -> verified true.
    assert.equal(J(abi.vcEddsaVerifyFromCanonical(pk, doc, cfg, pv)).verified,
      true, 'verify(correct key, doc, cfg, proof) == true');
    // Wrong key -> false.
    assert.equal(J(abi.vcEddsaVerifyFromCanonical(pkWrong, doc, cfg, pv)).verified,
      false, 'wrong key must not verify');
    // Different document -> false.
    assert.equal(J(abi.vcEddsaVerifyFromCanonical(pk, doc2, cfg, pv)).verified,
      false, 'tampered document must not verify');
    // Tampered proofValue -> false (flip one base58 char).
    const pvTampered = pv.slice(0, -1) + (pv.endsWith('A') ? 'B' : 'A');
    assert.equal(J(abi.vcEddsaVerifyFromCanonical(pk, doc, cfg, pvTampered)).verified,
      false, 'tampered proofValue must not verify');
  });
});
