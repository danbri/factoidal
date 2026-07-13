# Vendored: EECC VC/DID interop fixtures (Track B1)

Per
[`docs/designissues/2026-07-11-vc-canivc-eecc-plan.md`](../../../docs/designissues/2026-07-11-vc-canivc-eecc-plan.md)
§2 / Track B1. Two Apache-2.0 repos from
[european-epc-competence-center](https://github.com/european-epc-competence-center)
(EECC, the GS1 product-passport VC/DID stack), vendored for their
real-world **credential fixture data**, not their implementation code
(no logic from either repo is executed by Factoidal — see "What was
pruned" below and iron rule #7, no cobbling).

**The AGPL-3.0 `vc-verifier` repo from the same org is explicitly OUT
and was never cloned into this tree** — plan §2 names it as
"interop target only, never vendor".

## Sources

| Field | `vc-verifier-rules` | `webuild-attestations` |
|---|---|---|
| Upstream repo | `european-epc-competence-center/vc-verifier-rules` | `european-epc-competence-center/webuild-attestations` |
| Clone URL | `https://github.com/european-epc-competence-center/vc-verifier-rules.git` | `https://github.com/european-epc-competence-center/webuild-attestations.git` |
| Commit | `b165d68393485c0fd3c5285eaa32fa9c3602a264` (2026-06-22, "chore: release version 2.7.1") | `1f1096b06b40b19c3711d635a2e9bada8f8584ef` (2026-07-06, "Update README.md") |
| Retrieved | 2026-07-13, `git clone --depth 1` (plain git-protocol clone; the sandbox's GitHub release-assets/API proxy is blocked, plain clones are not) | 2026-07-13, `git clone --depth 1` |
| Licence | **Apache-2.0** — verified at `LICENSE` (full Apache 2.0 text) + `package.json`'s `"license": "Apache-2.0"` + `NOTICE` (`Copyright 2023 GS1 US`) | **Apache-2.0** — verified at `LICENCE` (British spelling; full Apache 2.0 text) + README.md's own "License" section ("This project is licensed under the Apache Licence, Version 2.0") |
| `.git` metadata | stripped after clone (plain vendored copy, not a submodule — same pattern as `third_party/contexts/` and `third_party/testing/vc-di-eddsa/`) | stripped after clone |

Both LICENSE files were read in full before vendoring, per plan
instruction to verify licences at clone time, not assume them from the
GitHub UI badge.

## What was vendored

**`vc-verifier-rules/`** — GS1's GS1-Digital-License credential chain
library (forked from `gs1us-technology/vc-verifier-rules`):
- `LICENSE`, `NOTICE`, `README.md` — repo-level docs/licence.
- `src/tests/example_chain/*.json` (4 files) — **real, DataIntegrityProof-signed
  W3C VCDM 2.0 credentials** issued by EECC's own sandbox systems
  (`did:web:id.tortugadeoro.com`, `did:web:company-wallet-dev.prod-k8s.eecc.de:...`):
  `gcp_license_credential.json` (`GS1CompanyPrefixLicenseCredential`),
  `gtin_key_credential.json` (`KeyCredential`),
  `prefix_license_credential.json` (`GS1PrefixLicenseCredential`),
  `sgtin_key_credential.json` (`KeyCredential`). Each carries a genuine
  `eddsa-rdfc-2022` `DataIntegrityProof` block (`proofValue`,
  `verificationMethod`, `cryptosuite`) and a `@context` array headed by
  `https://www.w3.org/ns/credentials/v2` — these are the crown-jewel
  fixtures: real-world VCDM 2.0 + Data Integrity shapes, not synthetic
  test vectors. This is the primary vendoring target the plan calls for.
- `src/tests/example_product_data_vc.jwt` — a `ProductDataCredential`
  example, but as a **compact JWT-VC** (JWS: `alg: Ed25519`, `kid: did:web:...`),
  a different serialization from the JSON-LD/Data-Integrity credentials
  above. Kept for reference; not fed to the structural checker (see
  "Runner scope" below — JWT-VC parsing is out of scope here).
- `src/getting-started/json-schema/*.json` (6 files) — GS1's own JSON
  Schema definitions for the GS1 key/prefix/organization/product data
  shapes referenced by the credentials' `credentialSchema` blocks.
  Reference material, not fed to the checker (JSON Schema documents
  are not credential instances).

**`webuild-attestations/`** — the WE BUILD Large-Scale-Pilot EUDI/EBW
rulebook + schema repository:
- `LICENCE`, `README.md` — repo-level docs/licence.
- `data-schemas/sd-jwt/*.json` (16 files) + `data-schemas/sd-jwt/sample-data/*.json`
  (17 files) — JSON Schema definitions and sample claim sets for
  **SD-JWT VC** attestations (`vct` claims like `eu.we-build:gln:1`).
- `data-schemas/mdoc/*.json` (2 files) + `data-schemas/mdoc/sample-data/*.json`
  (3 files) — schema + sample data for **ISO/IEC 18013-5 mdoc**
  attestations.
- `sample-data/*.json` (2 files) — two more top-level SD-JWT sample
  claim sets (`ds001-ebw-oid-sd-jwt-sample.json`,
  `ds002-pid-sd-jwt-sample.json`).

All of the above are plain JSON claim sets / schemas (SD-JWT VCs are
JWT claims prior to Selective Disclosure packing, per the sample
files' own `README.md` description) — **not** W3C VCDM JSON-LD
credentials. See "Runner scope" below for how they're classified.

Total vendored: ~544 KB across both repos (`du -sh
third_party/testing/eecc`).

## What was pruned

Both repos are npm/TypeScript projects; only fixture/schema DATA was
kept, per plan instruction ("Take the fixture/rule DATA... prune
irrelevant bulk (node_modules-ish, images, website code)"):

**`vc-verifier-rules`** — pruned: `.cursor/` (AI-assistant working
notes, not project material), `content/gs1_credential_chain.png`
(diagram image), `scripts/release.cjs`, `eslint.config.js`,
`jest.config.ts`, `nodemon.json`, `tsup.config.js`, `tsconfig.json`,
`package.json` / `package-lock.json` (npm tooling, no
`node_modules/` was ever installed — a fresh `--depth 1` clone has
none), `CHANGELOG.md`, `.npmignore`. **Also pruned: the entire
`src/lib/` rules engine** (`src/lib/engine/`, `src/lib/rules-schema/`,
`src/lib/rules-definition/`, `src/lib/gs1-verification-service.ts`,
`src/lib/types.ts`, etc.) and `src/index.ts` — this is the GS1
business-rules **implementation** (TypeScript), not data. Per iron
rule #7 (no cobbling — no hand-written reimplementation of what F\*
defines) this project does not execute vendored third-party rule
*logic*; only the credential/schema *data* it produces or consumes is
useful here. Also pruned: `src/tests/*.test.ts`,
`src/tests/mock-*.ts` (jest test harness + inline mock objects — code,
not standalone fixture files).

**`webuild-attestations`** — pruned: `rulebooks/` (23 subdirectories,
each a human-readable Markdown governance/conformance document plus
one image, `rulebooks/rb-base/issuer_obligations.jpg`) — these are
prose rulebooks, not machine-readable fixture/rule data, and match the
plan's "website code"/bulk-prune guidance. Also pruned:
`CODE_OF_CONDUCT.md`, `CONTRIBUTING.md`, `SECURITY.md`, `.aiignore`
(repo governance files).

## Runner scope (what this vendoring is used for)

`bin/eecc-runner/eecc_runner.ml` (mirrors `bin/vc-runner/vc_runner.ml`'s
pattern: an offline OCaml consumer driving F\*-extracted VC modules
directly against fixture files, no HTTP, no toolchain needed at test
time) classifies every vendored JSON file into one of three buckets:

1. **W3C VCDM JSON-LD credentials** (the 4
   `vc-verifier-rules/src/tests/example_chain/*.json` files — detected
   by the presence of both `@context` and `type` fields with
   `VerifiableCredential` in `type`) — run through
   `VC_Credential.vc_check_from_string` (the same Stage-1 structural
   checker `vc_runner` scores 117/0 with). All four are expected
   PASS: they are genuine, currently-valid GS1 credentials issued by
   EECC's own sandbox, not adversarial test vectors.

2. **Data Integrity crypto verification** — attempted via
   `VC_DataIntegrity.eddsa_rdfc_2022_verify` for the same 4 fixtures
   (they all carry a real `eddsa-rdfc-2022` `proofValue`). This is
   scored **SKIP**, not fail: each fixture's `verificationMethod` is a
   `did:web` URL (`did:web:id.tortugadeoro.com#...`,
   `did:web:company-wallet-dev.prod-k8s.eecc.de:...`) that would need
   a live HTTPS DID resolution to fetch the issuer's actual Ed25519
   public key — this project does no network I/O in a test runner
   (offline-reproducible per CLAUDE.md's testing discipline), and no
   public key material is bundled in the fixture files themselves.
   This is the "unverifiable-by-design" case the task brief names
   explicitly: the structural shape is fully checkable offline, the
   signature is not, without fabricating key material that was never
   vendored. Skipped with that reason, not guessed at and not failed.

3. **Non-JSON-LD credential formats / shape definitions** (all 40
   `webuild-attestations` files — 18 JSON Schema documents across
   `data-schemas/{sd-jwt,mdoc}/*.json` plus 22 SD-JWT/mdoc sample
   claim sets under the three `sample-data/` directories — plus
   `vc-verifier-rules`' one `.jwt` fixture and its 6 JSON Schema
   files: 47 files total) — SKIP, reason "not a W3C VCDM JSON-LD
   credential (SD-JWT / mdoc / JWT-VC / JSON-Schema document) —
   outside `VC.Credential.fst`'s structural-checker scope". Feeding
   these through the JSON-LD checker would produce a spurious FAIL
   (no `@context`, no `type: VerifiableCredential` — because they are
   a different credential format entirely, not because they are
   malformed VCDM credentials), which would misreport a format
   mismatch as a structural defect. Honest skip, per the task brief's
   instruction, not a fail.

See `.github/test-suites/eecc-interop.yaml` for the wired suite and
`bin/eecc-runner/eecc_runner.ml`'s header comment for the full
classification logic.

## Updating

Re-run the same `git clone --depth 1` against both clone URLs above,
diff against this vendored copy, re-verify both LICENSE files did not
change licence terms, and update the commit/date table above.
