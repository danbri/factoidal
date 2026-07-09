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
