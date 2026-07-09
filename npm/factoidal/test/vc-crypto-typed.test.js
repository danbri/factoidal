// VC Data Integrity crypto through the TYPED npm surface (index.js's
// vc* wrappers), NOT the raw ABI. This proves the two things
// test/vc-crypto.test.js (which drives the raw abi.vc* directly) does
// not:
//
//   1. The typed wrappers return parsed VALUES (hex string, boolean),
//      not the raw {ok, ...} JSON envelope.
//   2. The init story works: these wrappers AUTO-AWAIT initHacl() on
//      the first call (index.js's driver.initCrypto hook), so the test
//      NEVER calls initHacl() itself — yet sign/verify still succeed,
//      and a verify NEVER silently returns true when it should be false
//      (the #286 throw-on-uninit contract, preserved through the typed
//      layer by entryResult() throwing on {ok:false}).
//
// SECURITY: every negative case (wrong key, tampered signature/proof,
// altered message/document) MUST resolve to false, never true.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('../index.js');

// FIPS 180-4 / RFC 8032 authoritative vectors.
const SHA256_ABC =
  'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';
const V0 = {
  sk: '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60',
  pk: 'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a',
  msgHex: '',
  sig: 'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b',
};
const V1 = {
  sk: '4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb',
  pk: '3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c',
};

// The typed VC surface needs the npm-entry engine bundle. Probe it the
// same way capabilities() does, so this file no-op-skips (rather than
// hard-fails) on a checkout without the built bundle.
async function vcAvailable() {
  try {
    const caps = await factoidal.capabilities();
    return !!caps.vcCrypto;
  } catch (_) {
    return false;
  }
}

test('typed VC surface (index.js vc*): auto-init + round-trip + tamper', async (t) => {
  const skip = !(await vcAvailable());
  if (skip) {
    t.skip('npm-entry bundle with vc* exports not present (run build-ocaml.sh js + npm)');
    return;
  }

  // NB: no initHacl() call anywhere in this test — the typed wrappers
  // auto-await it on first use.

  await t.test('vcSha256Hex returns the hex digest string (FIPS 180-4 abc)', async () => {
    const digest = await factoidal.vcSha256Hex('abc');
    assert.equal(typeof digest, 'string');
    assert.equal(digest, SHA256_ABC);
  });

  await t.test('Ed25519 derive/sign/verify round-trip (RFC 8032 vector), typed values', async () => {
    const pk = await factoidal.vcEd25519SecretToPublic(V0.sk);
    assert.equal(pk, V0.pk, 'derived pubkey is the RFC 8032 value (string, not {ok,...})');

    const sig = await factoidal.vcEd25519Sign(V0.sk, V0.msgHex);
    assert.equal(sig, V0.sig, 'signature is the RFC 8032 value');

    const ok = await factoidal.vcEd25519Verify(pk, V0.msgHex, sig);
    assert.equal(ok, true, 'verify(correct) === true (boolean, not {ok,...})');
  });

  await t.test('Ed25519 verify rejects tamper / wrong key (security)', async () => {
    const badSig = V0.sig.slice(0, -2) + (V0.sig.endsWith('00') ? '01' : '00');
    assert.equal(await factoidal.vcEd25519Verify(V0.pk, V0.msgHex, badSig), false,
      'tampered signature must not verify');
    assert.equal(await factoidal.vcEd25519Verify(V1.pk, V0.msgHex, V0.sig), false,
      'wrong public key must not verify');
    assert.equal(await factoidal.vcEd25519Verify(V0.pk, '73', V0.sig), false,
      'different message must not verify');
    assert.equal(await factoidal.vcEd25519Verify('ab', V0.msgHex, V0.sig), false,
      'malformed public key must not verify (never an exception-hidden true)');
  });

  await t.test('eddsa-rdfc-2022 create + verify over canonical inputs, typed values', async () => {
    const pk = await factoidal.vcEd25519SecretToPublic(V0.sk);
    const pkWrong = await factoidal.vcEd25519SecretToPublic(V1.sk);
    const doc = '<http://example.org/s> <http://example.org/p> "canonical value" .\n';
    const doc2 = '<http://example.org/s> <http://example.org/p> "TAMPERED value" .\n';
    const cfg = '_:pc <http://www.w3.org/ns/data-integrity#cryptosuite> "eddsa-rdfc-2022" .\n';

    const pv = await factoidal.vcEddsaCreateFromCanonical(V0.sk, doc, cfg);
    assert.equal(typeof pv, 'string');
    assert.ok(pv.length > 0 && pv[0] === 'z', 'proofValue is multibase-z (base58btc)');

    assert.equal(await factoidal.vcEddsaVerifyFromCanonical(pk, doc, cfg, pv), true,
      'verify(correct key, doc, cfg, proof) === true');
    assert.equal(await factoidal.vcEddsaVerifyFromCanonical(pkWrong, doc, cfg, pv), false,
      'wrong key must not verify');
    assert.equal(await factoidal.vcEddsaVerifyFromCanonical(pk, doc2, cfg, pv), false,
      'tampered document must not verify');
    const pvTampered = pv.slice(0, -1) + (pv.endsWith('A') ? 'B' : 'A');
    assert.equal(await factoidal.vcEddsaVerifyFromCanonical(pk, doc, cfg, pvTampered), false,
      'tampered proofValue must not verify');
  });
});

test('typed VC surface: input validation throws a TypeError before any engine call', async () => {
  await assert.rejects(() => factoidal.vcSha256Hex(42), TypeError);
  await assert.rejects(() => factoidal.vcEd25519Verify('aa', 'bb', 5), TypeError);
});
