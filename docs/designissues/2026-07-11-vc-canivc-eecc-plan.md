# VC/DID development plan — canivc.com + EECC test environments

Date: 2026-07-11. Grounded against the tree at `898159c`
(`docs/test-results/latest.json`, 2026-07-11) and the canivc landing
`12cd438`. Extends the existing coverage program
([`2026-07-10-vc-did-coverage-program.md`](2026-07-10-vc-did-coverage-program.md),
epic #288) with the two new interop test environments the owner named:
**canivc.com** (Digital Bazaar community-compatibility aggregator) and the
**EECC** (European EPC Competence Center) VC/DID interop stack. Every
number is labelled pass/fail/total (anti-pattern #25); no bare ratios.

**Update 2026-07-14 (obsolescence sweep):** Tracks A1 and A4 named
below both landed and their target suites are now fully green:
`vc_di_eddsa` 31 pass, 0 fail (out of 31 — proof sets/chains +
`previousProof` chaining landed, closing the "multi-proof /
`proof.previousProof` chaining unsupported" gap called out below) and
`vc20_api` 59 pass, 0 fail (out of 59 — relatedResource digest/id
checks and the VP JSON-LD named-graph `@container: @graph` expansion
gap both closed). The root-cause narrative in §1 below is preserved as
the 2026-07-11 baseline diagnosis that motivated this plan; treat its
score numbers as historical, not current.

## 1. Current state (verified, as of 2026-07-11 — see update above for current scores)

**Scores** (`latest.json`): `vc_stage1` 117 pass, 0 fail (of 117,
structural, `VC.Credential.fst` direct); `vc_di_eddsa` 26 pass, 5 fail
(of 31, official eddsa suite via `bin/vc-api-shim`); `vc20_api` 22 pass,
37 fail (of 59, official vc-data-model-2.0 HTTP tests via the shim);
`did_key` 8 pass, 0 fail (of 8, internal vectors only).

**F\* modules**: `VC.Credential.fst` (VCDM 2.0 structural checker, 117/0),
`VC.DataIntegrity.fst` (`eddsa-rdfc-2022`, 4 crypto `assume val`s at
`:34-51`), `VC.Multibase.fst` (pure codecs, all targets), `VC.Context.fst`
(offline term resolver), `DID.Key.fst` (Ed25519-only, returns bare RDF,
not a DID Resolution Result envelope).

**Crypto** (per `crypto-policy` + `node-crypto-haclstar-vc-wasm-build`):
native = vendored HACL\* C (Ed25519 + SHA-256 only; P-256/BBS/RSA
explicitly excluded from the curated closure). Off-native = HACL\*'s
official `hacl-wasm@1.4.0` vendored and wired (Node + browser), gated by
`npm/factoidal/test/vc-crypto.test.js`. **Flag**: issue #286's checklist
still shows the wasm-wiring item unchecked though the artifacts are in the
tree — likely stale (obsolescence-sweep item), confirm before closing.

**Why the fails fail** (the actionable part):
- **`vc20_api` 37 fails — one root cause.** `bin/vc-api-shim/server.mjs`
  `handleVerify` (`:316`) does proof-shape checks + Ed25519 crypto but
  **never calls a structural validator** — every missing-`@context`,
  missing-`type`, empty-`credentialSubject`, malformed-`credentialStatus`/
  `Schema`/`termsOfUse`/`evidence`, `validUntil`<`validFrom`, non-URL-`id`
  rejection the suite expects simply never fires.
- **`vc_di_eddsa` 5 fails**: 3× `DATA_LOSS_DETECTION_ERROR` not raised
  (undefined-type / post-issuance-term documents accepted); 2× multi-proof
  / `proof.previousProof` chaining unsupported (`handleVerify` hard-rejects
  `proofs.length > 1`).

## 2. The two new environments

**canivc.com** = static aggregator over 10 published interop `index.json`
reports (vc2.0, vc-di-ecdsa, ed25519signature2020, vc-di-eddsa,
vc-di-bbs, did-key, vc-api-issuer, vc-api-verifier,
vc-bitstring-status-list, vc-jose-cose). We measurably run **3 of 10**.
Demands we don't yet meet: structural validation over HTTP; proof-set /
`previousProof` chains; a DID Resolution Result envelope; BitstringStatus­
List; ECDSA/ES256. Out of realistic near-term reach without new crypto/
serialization decisions: BBS (no HACL\* BBS), JOSE/COSE, Ed25519Signature­
2020, full VC-API exchanges.

**EECC** (github.com/european-epc-competence-center) = GS1 product-passport
VC/DID stack. **Not vendored yet** (grep-confirmed zero real hits).
Licence-gated per crypto-policy:
- `vc-verifier` (**AGPL-3.0**) — interop target only, **never vendor**;
  value is a second independent verifier reached over HTTP.
- `vc-verifier-rules`, `webuild-attestations` (**Apache-2.0**) —
  **vendorable** real-world fixtures + a rule catalogue.
- `didwebvh`, `es256-signature-2020`, `rsa-*` — reference material for
  DID-method / cryptosuite expansion, not suites to run now.

## 3. Prioritized tracks (one commit-sized deliverable each)

Order: **A2 → A1 → A3 → B1 → B2 → B3 → C**. Ranked by score-per-effort.

**Track A — canivc burndown (no new vendoring):**
- **A2 (do first — biggest jump, zero new crypto):** wire
  `VC.Credential.vc_check_from_string` into the shim's HTTP verify/issue
  path via an npm ABI export (`bin/npm-entry/entry_jsoo.ml`, following the
  `vcSha256Hex`/`vcEd25519*` pattern), called from `handleIssue`/
  `handleVerify` before the crypto step. Pure wiring — the module already
  scores 117/0; rule-#11-clean (shim gains an ABI call, no validation
  logic). Expected to close most of the 37 `vc20_api` fails. Floor:
  `vc_stage1` 117/0.
- **A1:** the 5 eddsa fails — proof-set/`previousProof` chain verification
  (new orchestration in `VC.DataIntegrity.fst`, not shim logic) +
  `DATA_LOSS_DETECTION_ERROR` (expansion coverage check, composes with A2).
- **A3:** DID Resolution Result envelope in `DID.Key.fst` (`didDocument`/
  metadata + `invalidDid`/`notFound`/… error codes) + a `GET
  /didResolvers/<did>` route — unlocks the canivc did:key conformance
  suite (community median only 25%, real headroom).

**Track B — EECC-motivated new coverage:**
- **B1:** vendor EECC `vc-verifier-rules` + `webuild-attestations`
  (Apache-2.0) into `third_party/testing/` with `PROVENANCE.md`; wire a
  runner issuing+verifying these real-world shapes. Vendor-then-wire.
- **B2:** BitstringStatusList `credentialStatus` — F\* shape checks in
  `VC.Credential.fst` + a `gzip`/`gunzip` `assume val` pair classified
  ASSUME-HOST (compression, not crypto). Unlocks the canivc
  bitstring-status-list row (community median 32.7%).
- **B3 (stretch, crypto-vendor-gated):** ECDSA `ecdsa-rdfc-201x` via
  HACL\* P-256 — extend the vendored closure to include `Hacl_P256.c`
  (record provenance), add `ecdsa_p256_sign`/`verify` `assume val`s in a
  new cryptosuite module. **Check the wasm gate**: today's vendored
  `hacl-wasm` carries Ed25519+SHA2 only, no P-256 `.wasm`; if the wasm
  route can't reach P-256, land native-only with the gap stated
  explicitly (same posture as VC.DataIntegrity's native-only footnote) —
  never hand-roll curve arithmetic (crypto-policy iron rule).

**Track C — cross-check + honesty:**
- **C1:** differential harness — issue with our shim, verify with EECC's
  public `vc-verifier` over HTTP (advisory, external availability not a
  floor; zero AGPL code in-tree).
- **C2:** per-wave dashboard + ledger upkeep and an obsolescence sweep
  (the #286 stale-checklist above is exactly this failure mode).

## 4. Dependencies / fixtures

- Fixtures already present, wire-only: **A1, A2, A3**.
- Fixtures needing vendoring: **B1** (EECC Apache-2.0 repos), **B3** (P-256
  vectors if not in HACL\* wasm).
- New `assume val`s: **B2** (gzip, ASSUME-HOST), **B3** (P-256 sign/verify,
  crypto — HACL\* only).
- A2 has no dependencies and is pure wiring against a 100%-scoring module —
  do it first.

## 5. `/goal` line (VC track)

Advance VC/DID conformance against canivc.com and the EECC interop stack:
wire `VC.Credential`'s structural checker into the vc-api-shim's HTTP
verify/issue path (official vc-data-model-2.0-test-suite currently 22
pass, 37 fail of 59, the shim doing zero structural validation of its
own); close the vc-di-eddsa gaps (26 pass, 5 fail of 31 —
proof-set/previousProof chaining + DATA_LOSS_DETECTION_ERROR); add a DID
Resolution Result envelope to unlock the canivc did:key conformance suite
(internal vectors 8 pass, 0 fail of 8, community suite unrun); then vendor
EECC's Apache-2.0 `vc-verifier-rules`/`webuild-attestations` fixtures and
implement BitstringStatusList status processing, with ECDSA/P-256 (via an
extended HACL\* closure, subject to the wasm gate) as a stretch track —
all under no-hand-rolled-crypto and shim-stays-zero-semantic-logic (rule
#11), tracked under epic #288.
