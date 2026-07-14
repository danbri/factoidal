# VC + DID coverage program: canivc evals + EECC interop as the drivers

Date: 2026-07-10. Status: PLAN. Owner directive (2026-07-10): "Add to
goal the canivc site evals and eecc github work on VC. Use these to
spawn new work towards better VC and DID coverage."

This doc turns two external reference points — the canivc.com
community dashboard (which we already integrated, task #88, commit
`12cd438`) and the European EPC Competence Center (EECC) GitHub VC/DID
stack — into a staged burndown toward broader, measured VC and DID
conformance. It supersedes the "remaining" stubs in
`.github/test-suites/vc.yaml`, `vc-di-eddsa.yaml`, `vc20-api.yaml`,
`did.yaml`.

**Update 2026-07-14 (obsolescence sweep):** both suites named in the
baseline below are now fully green — `vc_di_eddsa` 31 pass, 0 fail
(out of 31, proof sets/chains + `previousProof` landed) and
`vc20_api` 59 pass, 0 fail (out of 59, structural VC Data Model
validator now wired into the HTTP verify path + relatedResource
checks landed). The baseline below is the historical 2026-07-10
starting point for this plan, not the current score.

## Measured baseline (2026-07-10, from the canivc integration)

Run by our own VC-API shim (`bin/vc-api-shim`) against the vendored
official suites — same tests, same denominators as the published
community numbers:

- eddsa-rdfc-2022 (W3C `vc-di-eddsa-test-suite`): **26 pass, 5 fail
  (of 31)** — above the community median (41.9%), behind Grotto
  (100%), SpruceID (96.8%), Trential (93.5%). The 5 fails:
  multi-proof / previousProof chaining, DATA_LOSS_DETECTION_ERROR,
  and related proof-set cases.
- VC Data Model 2.0 issuer/verifier HTTP suite: **22 pass, 37 fail
  (of 59)** — below median (54.7%). Dominant cause: the shim does not
  route through a structural VC Data Model validator (our
  `VC.Credential.fst` scores 117/0 on fixtures but is not wired into
  the HTTP verify path).
- VC structural (vc_stage1): 117 pass, 0 fail (of 117).
- did:key runner: 8 pass, 0 fail (of 8) — but the canivc did:key
  *conformance* suite is NOT run: it needs a DID Resolution Result
  envelope + structured error codes our bare-RDF `didKeyResolve` ABI
  doesn't produce.
- Not implemented (explicit dashboard rows): BBS, ECDSA, JOSE/COSE,
  bitstring-status-list, full VC-API issuer/verifier,
  Ed25519Signature2020, eddsa-jcs-2022.

## EECC stack (researched 2026-07-10) — what it gives us

GitHub org `european-epc-competence-center`. Relevant repos and how
each informs our roadmap (LICENCE noted — it gates vendoring):

| Repo | Licence | Use to us |
|---|---|---|
| `vc-verifier` | AGPL-3.0 | Interop TARGET only (do NOT vendor AGPL). Verifies Ed25519Signature2018/2020, JsonWebSignature2020(ES256), DataIntegrityProof; cryptosuites eddsa-rdfc-2022, ecdsa-rdfc-2019, rsa-rdfc-2025, ecdsa-sd-2023; VC-JWT; status via StatusList2021 / BitstringStatusList / RevocationList2020. HTTP REST API + GS1 product-passport UI. A second independent verifier to cross-check credentials WE issue. |
| `vc-verifier-rules` | Apache-2.0 | Vendorable. Rule catalogue for verification — a source of conformance checks + fixtures. |
| `webuild-attestations` | Apache-2.0 | Vendorable. Real-world VC schemas + rulebooks (WeBuild Large-Scale Pilot). Concrete non-synthetic credential fixtures. |
| `didwebvh` | Apache-2.0 | Reference for a DID method beyond did:key — did:webvh (did:web + verifiable history). Motivates DID-method expansion. |
| `es256-signature-2020`, `ps256-signature-2020`, `rsa-multikey`, `rsa-rdfc-2025-cryptosuite` | BSD-3 | Reference implementations of cryptosuites we don't yet have — ECDSA P-256 (ES256), RSA. Test-vector sources. |
| `vc-render-method` | (HTML) | Rendering methods for VCs — ties into the MathML/rendering track for credential display. |

Licence rule: AGPL (`vc-verifier`) is an interop target reached over
HTTP or by running its published verification against our output — its
code is NEVER vendored into this repo. Apache-2.0 / BSD-3 repos may be
vendored as test vectors / reference with PROVENANCE.md per
skills/test-suites external-suite policy.

## Program — three tracks, staged, each a commit-sized wave

### Track A — canivc burndown (the measured, directly-comparable numbers)

- **A1 (eddsa 5 fails).** Diagnose each of the 5 in `VC.DataIntegrity`
  / the shim: proof-set / multiple-proof handling and previousProof
  chaining (W3C Data Integrity §proof sets & chains), plus the
  data-loss-detection case (canonicalization must round-trip all
  claims). Target: 31/31 or an enumerated honest remainder.
- **A2 (vc20-api 37 fails).** Wire `VC.Credential.vc_check_from_string`
  (the 117/0 structural validator) into the shim's /credentials/verify
  path so structural VC Data Model violations are caught over HTTP.
  Re-measure; the 37 should drop sharply. Enumerate the residue.
- **A3 (did:key conformance suite).** Add a DID Resolution Result
  envelope producer in F* (DID.Key.fst → a resolution-metadata wrapper:
  didDocument + didResolutionMetadata + didDocumentMetadata, with the
  structured error codes the suite checks: invalidDid, notFound,
  representationNotSupported). Wire a resolver route into the shim.
  Score the canivc did:key suite.

### Track B — EECC interop + new coverage the EECC stack motivates

- **B1 (interop fixtures).** Vendor `webuild-attestations` +
  `vc-verifier-rules` (Apache-2.0) test vectors with PROVENANCE.md;
  add an interop suite that issues + verifies these real-world
  credential shapes through our engine. Labelled scores.
- **B2 (bitstring-status-list).** EECC supports it and canivc scores
  it: implement BitstringStatusListEntry credentialStatus processing
  in F* (status list is a bitstring-in-a-VC; fits our existing
  bitstring + VC decode). Run the canivc vc-bitstring-status-list
  suite (currently a not-implemented row).
- **B3 (ECDSA rdfc, stretch).** HACL* has P-256; assess wiring
  ecdsa-rdfc-2019 / ecdsa-rdfc-2022 as a second cryptosuite. If the
  HACL* P-256 sign/verify is reachable through the crypto assume-val
  layer (skills/node-crypto-haclstar-vc-wasm-build), score the canivc
  ECDSA suite. If not reachable without new crypto glue, record the
  exact blocker and stop (crypto-policy: no hand-rolled curves).

### Track C — cross-check + honesty surface

- **C1.** A differential harness: credentials our shim issues, verified
  by (a) our verifier and (b) EECC's public verifier API where
  reachable — disagreements are findings. Advisory, not a floor
  (external service availability).
- **C2.** Dashboard: extend the "VC community compatibility" block with
  the new rows (did:key conformance, bitstring-status-list, EECC
  interop) and keep the not-implemented rows honest as each is closed.
  Obsolescence sweep every wave.

## Sequencing + constraints

Order: A2 (biggest measured jump, no new crypto) → A1 → A3 → B1 → B2 →
B3 → C. Each wave: one commit, immediate push, labelled scores, floors
(vc_stage1 117/0, did_key 8/0, SPARQL 631/0, RDF 1031/0), and the
rule-#11 boundary — the shim stays a consumer tool with ZERO semantic
logic; all VC/DID/crypto logic lives in F*. No AGPL code vendored. No
hand-rolled crypto (crypto-policy). Issues: open/attach a tracking
issue per track under the VC epic and tick as waves land
(issue-hygiene).

## Environment note

Written during an account-credit exhaustion (Fable 5) + repeated
container-rollback window on 2026-07-10; the build-dependent waves
(A1–B3) are queued for a stable container with credits. The did:key
envelope (A3) and the structural-validator wiring (A2) are the highest
value-per-token first strikes.
