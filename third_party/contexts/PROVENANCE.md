# Vendored JSON-LD contexts — provenance

Offline copies of the JSON-LD `@context` documents that
Factoidal's verified checkers resolve without network access.

## `credentials-v2.jsonld` — W3C VCDM 2.0 base context

- **Term IRI:** `https://www.w3.org/ns/credentials/v2`
- **Retrieved:** 2026-07-09 (`curl -H 'Accept: application/ld+json'`)
- **SHA-256:** `59955ced6697d61e03f2b2556febe5308ab16842846f5b586d7f1f7adec92734`
- **Bytes:** 10131

This is the base context every Verifiable Credential / Verifiable
Presentation document MUST list first (VC Data Model 2.0, W3C
Recommendation 2025-05-15, §4.1). Its top-level `@context` object
carries `"@protected": true`, so every term it defines
(`VerifiableCredential`, `VerifiablePresentation`,
`EnvelopedVerifiableCredential`, `credentialSubject`, `issuer`, …) is a
protected term: a later inline context may not redefine it with a
different mapping. The context declares no document-level `@vocab`.

`VC.Context.fst` reads this file's parsed `json_val` (supplied by the
consumer — the native `vc_runner` parses it once at startup and passes
it in; the F\* side does no I/O) to build the base term → (IRI,
protected?) map used for VCDM `type`-value resolution and
redefinition-of-protected detection. Keeping the term data in the
vendored file rather than hardcoded in F\* means the map tracks the
real W3C context byte-for-byte.

### Licence

The W3C context document at `https://www.w3.org/ns/credentials/v2` is
published by the W3C. W3C normative deliverables and their companion
artifacts (including the served context documents) are made available
under the **W3C Document Licence** and the **W3C Software and Document
Notice and Licence** (https://www.w3.org/copyright/software-license-2023/
and https://www.w3.org/copyright/document-license-2023/). This vendored
copy is byte-identical to the upstream document; it is reproduced here
unmodified solely to let the offline verified checker resolve the base
context without a network fetch. No warranty; see the W3C licences for
terms.

## `credentials-examples-v2.jsonld` — VCDM examples vocabulary context

- **Term IRI:** `https://www.w3.org/ns/credentials/examples/v2`
- **Retrieved:** 2026-07-10 (`curl -sSL -H 'Accept: application/ld+json'`)
- **SHA-256:** `57393fbc69d6efb9b9b5dc9cb6b9880b0944360abfe2eaf459c9e58cf2279d7c`
- **Bytes:** 84

A single `@vocab` mapping to `https://www.w3.org/ns/credentials/examples#`
used by many W3C VC test-suite fixtures for informal properties like
`alumniOf`. Used by `bin/vc-api-shim/server.mjs`'s local context
registry (task #88) alongside `credentials-v2.jsonld` so JSON-LD
documents from the vendored test suites can be parsed offline (see
"Licence" above — same W3C terms).

## `security-data-integrity-v2.jsonld` — Data Integrity security context

- **Term IRI:** `https://w3id.org/security/data-integrity/v2` (redirects
  to the W3C-published context)
- **Retrieved:** 2026-07-10 (`curl -sSL -H 'Accept: application/ld+json'`)
- **SHA-256:** `67f21e6e33a6c14e5ccfd2fc7865f7474fb71a04af7e94136cb399dfac8ae8f4`
- **Bytes:** 2609

Defines `DataIntegrityProof`, `proof`, `cryptosuite`, `proofValue`,
`verificationMethod`, `proofPurpose` etc. for documents that reference
this context explicitly rather than relying on the (also-sufficient)
scoped definitions bundled inside `credentials-v2.jsonld`. Same licence
terms as above.

## `security-multikey-v1.jsonld` — Multikey verification-method context

- **Term IRI:** `https://w3id.org/security/multikey/v1` (redirects to
  the W3C-published context)
- **Retrieved:** 2026-07-10 (`curl -sSL -H 'Accept: application/ld+json'`)
- **SHA-256:** `ba2c182de2d92f7e47184bcca8fcf0beaee6d3986c527bf664c195bbc7c58597`
- **Bytes:** 1010

Defines the `Multikey` verification-method type and
`publicKeyMultibase` — referenced by did:key DID Documents and some VC
test fixtures. Same licence terms as above.

## `credentials-v1.jsonld` — VCDM 1.1 base context

- **Term IRI:** `https://www.w3.org/2018/credentials/v1`
- **Retrieved:** 2026-07-10 (`curl -sSL -H 'Accept: application/ld+json'`)
- **SHA-256:** `ab4ddd9a531758807a79a5b450510d61ae8d147eab966cc9a200c07095b0cdcc`
- **Bytes:** 7687

The VC Data Model 1.1 base context — `data-integrity-test-suite-assertion`'s
default fixture (`validVc.json`, vendored inside
`third_party/testing/vc-di-eddsa/node_modules/`) uses this context, not
the v2 one, so the shim's local context registry needs both. Unlike
`credentials-v2.jsonld`, `proof` and `credentialSubject` are top-level
(unscoped) terms here. Same licence terms as above.

## `credentials-v2-20240720-8d0ee107.jsonld` — VCDM 2.0 base context, 2024-07-20 revision

- **Term IRI:** `https://www.w3.org/ns/credentials/v2` (historical revision)
- **Source:** `w3c/vc-data-model` git commit
  `8d0ee1072f16284a1a0613d78bd7c20c915bad09` (2024-07-20,
  "Remove `@vocab` definition from v2 context."), file
  `contexts/credentials/v2` — retrieved 2026-07-14 via
  `git show 8d0ee107:contexts/credentials/v2` from a clone of
  https://github.com/w3c/vc-data-model.
- **SHA-256:** `24a18c90e9856d526111f29376e302d970b2bd10182e33959995b0207d7043b9`
- **Bytes:** 10139

An earlier published revision of the SAME resource as
`credentials-v2.jsonld` above (the served document changed between
2024-07 and the 2025-05-15 Recommendation). Vendored for
`bin/vc-api-shim/server.mjs`'s relatedResource digest registry: VCDM
2.0 §5.3 requires a declared `digestSRI`/`digestMultibase` to match
"the digest computed for the retrieved resource", and the shim
verifies offline against the digests of every vendored revision of a
known resource. Real-world credentials citing this resource carry
digests of whichever revision was live when they were issued — the
W3C vc-data-model-2.0-test-suite's own `relatedResource` fixture
digests are of exactly this revision (its `digestMultibase`
`uJKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7k` is the base64url of
this file's SHA-256 above — the file content is self-authenticating
against the digests that reference it). NOT used by the JSON-LD
context registry (parsing always uses the current
`credentials-v2.jsonld`). Same licence terms as above.
