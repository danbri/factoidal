# Verifiable Credentials program plan

Scoping doc for W3C Verifiable Credentials (VC) support, modeled on
the stage structure in
[`2026-07-05-rml-program-plan.md`](2026-07-05-rml-program-plan.md).
VC is a **securing** problem, not a construction or validation
problem: given an RDF-shaped credential document, canonicalize it,
hash it, sign the hash, and attach the signature as a `proof` block;
verification runs the same pipeline and checks the signature. The
closest precedent in this codebase is RDFC-1.0 (`RDF.Canonical.fst`,
86/86 W3C tests) plus JSON-LD's `toRdf` pipeline (a JSON document in,
a canonical form out) — not SHACL/ShEx (schema validation) or RML
(mapping-driven construction). The one genuinely new ingredient is
public-key cryptography (Ed25519/ECDSA sign+verify), which this
program does **not** implement — see the crypto-vendoring section
below.

## Vendored suite: verdict

`.gitmodules` already declares two relevant gitlinks, both currently
**uninitialized** (`git submodule status` shows a leading `-`):

- `third_party/testing/vc` → `w3c/vc-data-model-2.0-test-suite`
- `third_party/testing/did` → `w3c/did-test-suite`

Both were scratch-cloned (shallow, disposable, nothing committed) to
inventory before deciding whether to initialize them as-is.

**`vc-data-model-2.0-test-suite` is a live-endpoint interop harness
for most of its content, but carries a static-fixture subset worth
vendoring on its own terms.** The suite's `package.json` runs
`mocha tests/` against a `@digitalbazaar/mocha-w3c-interop-reporter`;
every test file (`tests/4.08-credential-subject.js` and ~20 siblings)
calls `endpoints.issue(...)`/`endpoints.verify(...)` through
`TestEndpoints`, which is configured (via `w3c/vc-test-suite-
implementations`) to hit a named implementation's HTTP endpoints
(`POST /credentials/issue`, `/verify`, `/derive`) — there is no
"run offline" mode as shipped. **However**, every one of those test
files loads its input from `tests/input/*.json`: **120 static VC/VP
documents**, named with an explicit `-ok`/`-fail` suffix encoding the
expected verdict (65 `-ok`, 49 `-fail`, plus a handful in
`tests/input/names-and-descriptions/` following the same convention).
These are structural-conformance fixtures (`credential-no-subject-
fail.json`, `credential-subject-multiple-ok.json`, `presentation-
holder-ok.json`, …) that exercise VCDM 2.0's normative MUST/MUST NOT
statements about document *shape*, entirely independent of signing.
**Recommendation: vendor the submodule for the fixture files, but do
not attempt to run the upstream mocha suite** — write a bespoke
non-HTTP runner (`bin/vc-runner`, see Module plan) that loads each
`tests/input/*.json` file, runs our own extracted structural
validator against it, and checks the result against the filename's
`-ok`/`-fail` suffix. This is the same "reuse the fixture, skip the
upstream harness" move the RML plan made for `kg-construct/rml-test-
cases`, but for a different reason — there it was a wrong repo,
here it is a repo whose fixtures are reusable but whose harness
assumes a live server we do not have (and building one is a distinct,
larger, later-staged goal — see Stage 8).

**`did-test-suite` is out of scope for this program.** VC's Data
Integrity cryptosuites resolve a `did:key` verification method by
**local multibase decoding only** (no network resolution — see the
Fit section); the DID test suite exercises full DID *method*
resolution (`did:web`, `did:key` edge cases, DID document structure)
which is a distinct, network-facing program. Leave the submodule
gitlink in place, uninitialized, until a DID-method program is
scoped separately.

## Spec landscape and standardization state

The VC 2.0 family reached **W3C Recommendation on 2025-05-15** (press
release: "W3C publishes Verifiable Credentials 2.0 as a W3C
Standard"). This is a materially different starting point from the
RML and ShEx programs (Community Group reports, no Recommendation
track) — VC 2.0 is a finished, stable Rec family, not a moving draft.

| Spec | Status | Scope |
|---|---|---|
| VC Data Model 2.0 (`vc-data-model`) | REC 2025-05-15 | Credential/Presentation JSON-LD document shape: `@context`, `type`, `credentialSubject`, `issuer`, `validFrom`/`validUntil`, `credentialStatus`, `credentialSchema`, `termsOfUse`, `evidence`, `refreshService` |
| VC Data Integrity (`vc-data-integrity`) | REC (current draft at 1.1) | The `proof` mechanism: `DataIntegrityProof` type, the transform→hash→proof-serialization pipeline, `verificationMethod`/`proofPurpose`/`created`/`challenge`/`domain` |
| EdDSA cryptosuites (`vc-di-eddsa`) | REC (current draft 1.1) | `eddsa-rdfc-2022` (RDFC-1.0 canonicalization + SHA-256 + Ed25519) and `eddsa-jcs-2022` (JCS canonicalization + SHA-256 + Ed25519) |
| ECDSA cryptosuites (`vc-di-ecdsa`) | REC (current draft 1.1) | `ecdsa-rdfc-2019` and `ecdsa-jcs-2019` (P-256 primary; P-384 variant), plus `ecdsa-sd-2023` (selective disclosure — not scoped here) |
| Bitstring Status List (`vc-bitstring-status-list`) | REC 2025-05-15 | Revocation/suspension via a compressed bitstring published at a URL, referenced from `credentialStatus` |
| VC-JOSE-COSE (`vc-jose-cose`) | REC (part of the 2025-05-15 family) | An alternative **securing mechanism**: wraps a credential as a JWT (JOSE) or CBOR/COSE object instead of attaching a Data Integrity `proof`. Argued out of scope below. |

Two more specs are due as Recommendations in September 2026 (Render
Method, Confidence Method per the WG charter) — neither affects the
core securing pipeline this plan targets; revisit if a fixture need
appears.

**VC-JOSE-COSE is a different securing mechanism, not a superset.**
Where Data Integrity canonicalizes the *RDF dataset* and signs a hash
of the canonical form, JOSE/COSE securing signs a JSON or CBOR
*serialization* directly (no RDF canonicalization step at all in the
JOSE case — some COSE profiles do use canonicalization, but the
mainstream JWT-VC path does not). Building it would mean adding a
JWT/JWS parser and a CBOR/COSE parser, neither of which this project
has any other use for and neither of which touches RDF semantics.
Recommendation: **explicit non-goal** unless a concrete interop
requirement shows up (see Open decision 2).

## Test suites

Every cryptosuite-conformance suite in the W3C VC ecosystem is a live
HTTP interop harness, confirmed by inspecting three shallow clones
(scratch, not committed):

| Suite | Repo | Shape |
|---|---|---|
| VCDM 2.0 structural conformance | `w3c/vc-data-model-2.0-test-suite` | Mocha + `TestEndpoints` HTTP calls; **120 static `-ok`/`-fail` input fixtures reusable without the harness** (see above) |
| EdDSA cryptosuite interop | `w3c/vc-di-eddsa-test-suite` | Mocha suites `05-di-rdfc-create.js`, `15-di-rdfc-verify.js`, `30-rdfc-interop.js`, `60-jcs-interop.js`, `70-data-model.js`, `80-algorithms.js` — every one drives a configured implementation's issue/verify endpoints via `w3c/vc-test-suite-implementations`; no offline fixture directory found |
| ECDSA cryptosuite interop | `w3c/vc-di-ecdsa-test-suite` | Same shape as EdDSA's suite (not separately cloned; same harness family, same authors) |
| Bitstring Status List interop | `w3c/vc-bitstring-status-list-test-suite` | Same harness family (not cloned; deferred per Open decision 3) |

**No official W3C repo ships pure fixture-in/fixture-out cryptosuite
test vectors** (input document → expected canonical N-Quads → hash →
signature bytes) the way `rdf-canon`'s manifest does for RDFC-1.0
itself. The cryptosuite specs' own "Test Vectors" appendices (e.g.
`vc-di-eddsa`'s §3, rendered at `w3c.github.io/vc-di-eddsa/`)
describe the pipeline procedurally with key material shown, but the
rendered spec does not appear to carry fully-populated worked
examples (final canonical N-Quads text, hash bytes, proof-value
string) inline — re-check the raw spec source directly (not just the
rendered HTML) before Stage 4 in case the appendix is more complete
than this pass found.

An independent, **unofficial** single-maintainer repo,
`Wind4Greg/EdDSA-Test-Vectors`, exists and is genuinely useful in
shape (`input/specExample.json`, `input/keyPair.json`,
`input/multiKeyPairs.json`, `input/v1/unsecured.json`,
`input/v2/unsecured.json`) but is a **generator** (`JCSDataIntegrity
Create.js`, `ECDSAP256Create.js`, …) that produces vectors on demand
using the maintainer's own JS libraries, not a frozen, versioned set
of expected outputs. **Recommendation: do not vendor it as a
submodule** (unofficial, single-maintainer, generator-shaped, not a
stable pinned artifact) — treat it only as a scratch reference for
hand-deriving a handful of our own fixture files once the signing
pipeline exists, the same posture the RML plan took toward its own
scratch clones.

**Net effect: this program's early stages are gated on our own
fixtures, not a vendored suite.** Stage 1 (structural validation)
gets real W3C coverage for free via the 120 `tests/input/*.json`
fixtures. Stages 4+ (actual signing/verification) either (a) hand-
derive a small number of fixtures from the spec's worked examples
once confirmed complete, or (b) build the minimal VC-API HTTP
surface needed to point the official interop harness at us (Stage
8/9 — a materially bigger lift, staged late).

## Fit: what's reusable, what's new

**Reusable without change:**

- **RDFC-1.0** (`RDF.Canonical.fst`, 86/86 W3C tests) is exactly the
  canonicalization step every `-rdfc-` cryptosuite needs. Its
  `hash_algorithm` dispatch (`HA_SHA256` / `HA_SHA384`, lines 47-58)
  already covers both hash widths the ECDSA suites need (SHA-256 for
  P-256, SHA-384 for P-384) — `apply_hash` is the single call site a
  Data Integrity transform-and-hash pipeline would invoke.
- **JSON-LD `toRdf`** (404 pass, 52 fail, 11 skip of 467 per
  `docs/claude-rules/current-state.md`, rising) turns a credential's
  `@context`-bearing JSON-LD document into the RDF dataset RDFC-1.0
  canonicalizes. A credential **is** a JSON-LD document by
  construction (VCDM 2.0 §4.1 requires `@context` as the first
  property) — no new expansion logic needed, only enough passing
  coverage of the specific context shapes credentials use (the
  `https://www.w3.org/ns/credentials/v2` context and whatever
  extension contexts a fixture pulls in).
- **`Parser.JSONLD`'s `jcanon_*` family** (RFC 8785 JCS subset:
  `jcanon_number`, `jcanon_string`, `jcanon_sort_fields`, lines
  270-337) is exactly the canonicalization the `-jcs-` cryptosuite
  variants need in place of RDFC-1.0 — JCS canonicalizes the JSON
  serialization directly, skipping RDF entirely. Confirm the
  existing subset covers full credential documents (nested objects,
  arrays, all the JSON value kinds VCDM produces) before relying on
  it for Stage 7.
- **`XSD.Datatypes`'s `dateTime` ordering** (moved from
  `SHACL.Validation.fst`, `both_datetimes`/`dt_parse_ms`) is directly
  usable for VCDM's `validFrom`/`validUntil` ordering check (§4.9
  Validity Period — MUST NOT have `validUntil` before `validFrom`).

**Not reusable — needs a new small module:**

- **Multibase/multikey encoding.** No base58btc or base64url-nopad
  codec exists anywhere in the tree (`grep -ri "base58\|multibase\|
  multikey"` across `formal/fstar/*.fst` returns nothing). Verification
  methods are published as multibase strings (`z6Mk...` = `z` prefix +
  base58btc + multicodec-tagged key bytes) and proof values are
  multibase-encoded signatures. This is pure byte encoding — no
  crypto — and belongs in F* per rule #11 (arbitrary-precision
  base-58 division is ordinary arithmetic on `nat`, not a
  crypto primitive).
- **Credential/presentation structural validation** — the checks the
  120 `tests/input/*.json` fixtures exercise (required-property
  presence, `type` array membership, `credentialSubject` non-empty,
  `validFrom`/`validUntil` ordering, `credentialStatus`/
  `credentialSchema`/`termsOfUse` object shape) — is new: a decoder
  over the already-parsed JSON-LD expanded form (reusing
  `JSONLD.Expand`'s output, not re-parsing raw JSON), the mirror image
  of `SHACL.Validation.fst`'s "read typed constraints out of an
  already-decoded graph" pattern.
- **Data Integrity's transform→hash→proof-serialization pipeline** —
  the orchestration that calls RDFC-1.0 (or JCS), calls the hash
  dispatch, calls the crypto seam (below), and assembles/parses the
  `proof` JSON block (`type: DataIntegrityProof`, `cryptosuite`,
  `verificationMethod`, `proofPurpose`, `proofValue`) is new
  orchestration logic living entirely in F*.

## Crypto: no hand-rolled primitives, HACL* is the sanctioned path

**Hard constraint, not a design choice: this repo does not hand-roll
signature, hash, or curve arithmetic, in F* or in OCaml.** The
project's existing SHA-256/SHA-384 realisation is instructive here,
and worth stating precisely because it is easy to misremember:
`RDF.Canonical.fst`'s `hash_sha256`/`hash_sha384` and `SPARQL11.
Algebra.fst`'s `hash_md5`/`hash_sha1`/`hash_sha256`/`hash_sha384`/
`hash_sha512` are `assume val`s realised by
`formal/fstar/ocaml-output/fstar_pure_hashes.ml` — a **hand-written,
pure-OCaml** MD5/SHA implementation, not Digestif. The module's own
banner explains why: it replaces an earlier `Digest`/`Digestif.
SHA384`-backed realisation that **crashed under `wasm_of_ocaml`**
(pulling in C dependencies the WASM target can't link); the pure-OCaml
version runs unmodified on native, `js_of_ocaml`, and `wasm_of_ocaml`.
This is a real precedent to carry forward, but it cuts the other way
from "hashing already goes through a C library" — today's hash path
is deliberately **not** C-backed, specifically because C-backed
crypto broke a extraction target. Any HACL* integration route needs
to answer the same question before Stage 3: does it work under
`wasm_of_ocaml`, or does VC support quietly become native-only?

Ed25519/ECDSA sign+verify is categorically different from hashing —
it is public-key cryptography, and this project does not implement
public-key cryptography from scratch. **HACL\*** (the Project Everest
verified library, written in F\*/Low\*, compiled via KaRaMeL to C) is
the sanctioned source: it is literally the code Mozilla ships in
Firefox's NSS (Curve25519 and ChaCha20-Poly1305 landed in NSS from
HACL\*), and `docs/designissues/2026-05-07-io-verification-and-third-
party.md` already designates it as the project's chosen crypto
vendor for SHA-256 (that doc's Mode A/Mode B split). Ed25519 and
ECDSA P-256 are both in HACL\*'s scope (confirmed: `hacl-star` opam
package, latest 0.7.x, ships `Hacl_star.Hacl.Ed25519` and `Hacl_star.
Hacl.P256` modules) — this is an extension of an already-chosen
vendor, not a new one.

Evaluate in this order, cheapest/most-aligned first:

1. **`hacl-star` opam bindings (Mode A, matching the SHA-256 plan).**
   Not currently installed (`opam list | grep hacl` returns nothing
   on this switch). Action before Stage 3: `opam install hacl-star`
   on the project's OCaml 4.14.1 switch and confirm it builds; then
   confirm it links under `js_of_ocaml`/`wasm_of_ocaml` specifically
   (per the paragraph above — this is the step that failed for
   Digestif and must not be assumed to pass silently here). Upstream
   note: "new releases of the OCaml API are no longer made in the
   main `hacl-star` repository, but are instead available from
   `cryspen/hacl-packages`" — check whether the opam package still
   resolves to a maintained artifact or needs re-pointing at
   Cryspen's packaging.
2. **Vendored HACL\* extracted C via hand-written stubs**, following
   the existing `parquet_zstd_stubs.c` precedent (`formal/fstar/
   experimental_ocaml_glue/parquet_zstd_stubs.c` plus its
   `ocaml-output/parquet_zstd_stubs_jsoo.c` and `.o` companions for
   the jsoo/wasm targets) — the project already has a working
   pattern for "vendor a C library, write ASSUME-CRYPTO-shaped
   OCaml/C stubs for each extraction target separately." Fall back to
   this if option 1's opam package doesn't build or doesn't cross the
   wasm boundary.
3. **Direct NSS FFI, last resort.** Calling into a system NSS install
   is the least-aligned route (unversioned system dependency, least
   verified-crypto framing, no story for `wasm_of_ocaml` or KaRaMeL C
   at all) — only reachable if both HACL\* routes fail outright.

Whichever route wins, the F\*-side seam is two `assume val`s per
curve (`ed25519_sign`/`ed25519_verify`,
`ecdsa_p256_sign`/`ecdsa_p256_verify`), classified ASSUME-CRYPTO per
`skills/ocaml-boundary/SKILL.md`'s taxonomy — acceptable, the same
tier as the existing hash assume-vals, and strictly a realisation of
upstream HACL\*'s proof, not a new proof obligation for this repo.

## Module plan

- **`formal/fstar/VC.Multibase.fst`** — base58btc encode/decode
  (Bitcoin alphabet, arbitrary-precision big-endian byte-string ↔
  `nat` conversion, pure F\*) and base64url-nopad encode/decode;
  multicodec varint prefix handling for `Ed25519PublicKey`
  (`0xed01`) and `P256PublicKey` (`0x1200`) tags used by `did:key`/
  Multikey verification methods. No crypto — pure byte encoding, with
  a roundtrip lemma (`decode (encode bs) == Some bs`) the same shape
  as any other serializer in this codebase.
- **`formal/fstar/VC.Credential.fst`** — structural decoder + checks
  over an already-expanded JSON-LD credential/presentation
  (`JSONLD.Expand`'s output): required `@context`/`type`/
  `credentialSubject`/`issuer` presence, `validFrom`/`validUntil`
  ordering (reusing `XSD.Datatypes`'s dateTime comparison),
  `credentialStatus`/`credentialSchema`/`termsOfUse` object-shape
  checks. Scored directly against the 120 vendored `tests/input/
  *.json` fixtures — no crypto dependency, can land before the
  crypto-vendoring decision above is even resolved.
- **`formal/fstar/VC.DataIntegrity.fst`** — the transform→hash→proof
  pipeline: given a credential + cryptosuite name, dispatch to
  RDFC-1.0 (`-rdfc-` suites) or JCS (`-jcs-` suites) for
  canonicalization, dispatch `apply_hash` for SHA-256/384, call the
  `assume val` sign/verify seam, and serialize/parse the `proof` JSON
  block (`DataIntegrityProof` type, `cryptosuite`, `verificationMethod`
  multibase-decoded via `VC.Multibase`, `created`, `proofPurpose`,
  `proofValue` multibase-encoded signature bytes).
- **`bin/vc-runner/vc_runner.ml`** — consumer wiring only (rule #11):
  two modes. Structural mode (Stage 1) loads `tests/input/*.json`,
  calls extracted `VC.Credential`, compares against the filename's
  `-ok`/`-fail` suffix. Crypto mode (Stage 8+) either replays
  hand-derived fixtures against extracted `VC.DataIntegrity`, or (
  stretch, Stage 9) stands up the minimal VC-API HTTP surface
  (`/credentials/issue`, `/verify`) so the official `vc-di-*-test-
  suite` harnesses can target us directly.

## Staged plan

| Stage | Deliverable | Predicted coverage | Gate |
|---|---|---|---|
| 1 | Initialize `third_party/testing/vc` submodule; `VC.Credential.fst` skeleton (required-property + type-membership checks only) | **DONE (2026-07-05).** Measured: 80 pass, 34 fail, 6 skip (out of 120 `tests/input/*.json` fixtures). All 34 fails are on `-fail`-suffixed fixtures (zero false-fails on `-ok` fixtures) and land entirely inside the documented Stage 2 deferral list — issuer presence/shape, `credentialStatus`/`credentialSchema`/`termsOfUse`/`evidence`/`refreshService` inner-shape checks, `validFrom`/`validUntil` ordering, top-level `id` format/cardinality, `holder` shape, `name`/`description` extra-property rejection, and context-driven type redefinition (needs real JSON-LD term resolution, out of scope for Stage 1). The 6 skips are fixtures with neither a `-ok` nor `-fail` filename suffix (3 `-fail-or-inject`, 3 unsuffixed `presentation-self-asserted-vc-*` identity cross-checks) — never folded into the pass/fail denominator. See `formal/fstar/VC.Credential.fst`'s header comment for the exact rule set and `bin/vc-runner/vc_runner.ml` for the runner. | none |
| 2 | `VC.Credential.fst` complete: `validFrom`/`validUntil` ordering, `credentialStatus`/`credentialSchema`/`termsOfUse` shape checks | Majority of the 120 fixtures | Stage 1 |
| 3 | Crypto-vendoring decision executed: `opam install hacl-star` (or fallback route), confirm native + `js_of_ocaml` + `wasm_of_ocaml` all link | No test coverage yet — infrastructure gate | own item, blocks Stage 5 |
| 4 | `VC.Multibase.fst`: base58btc/base64url codecs + multicodec tag handling + roundtrip lemma | Unit-tested in isolation (no W3C fixture targets this directly) | none (independent of Stage 3) |
| 5 | `VC.DataIntegrity.fst` — `eddsa-rdfc-2022` create+verify (reuses RDFC-1.0 + SHA-256 + HACL\* Ed25519 seam) | Hand-derived fixtures from the spec's worked examples (re-check completeness first — see Test suites section) | Stages 3, 4 |
| 6 | `ecdsa-rdfc-2019` (P-256, SHA-256; P-384 variant if HACL\* P-384 confirmed available) | Same hand-derived-fixture approach as Stage 5 | Stage 5 |
| 7 | `-jcs-` variants (`eddsa-jcs-2022`, `ecdsa-jcs-2019`) reusing `jcanon_*` in place of RDFC-1.0 | Same fixture approach | Stage 5 |
| 8 | `bin/vc-runner` wiring, structural + crypto modes | Score structural mode against all 120 fixtures, crypto mode against hand-derived vectors, labelled separately | Stages 2, 5 |
| 9 (indefinite) | Minimal VC-API HTTP surface (`/credentials/issue`, `/verify`) so `vc-di-eddsa-test-suite`/`vc-di-ecdsa-test-suite` can run against us directly | Full official-suite score, if built | Stage 8 |
| 10 (indefinite) | Bitstring Status List (`vc-bitstring-status-list`) | Gzip-compressed bitstring encode/decode + base64url; gzip is a new ASSUME-HOST call-out (same taxonomy tier as regex — see Open decision 3) | Stage 2 |
| 11 (out of scope, revisit only on demand) | VC-JOSE-COSE enveloped proofs | Needs a JWT/JOSE parser and a CBOR/COSE parser, neither otherwise useful to this project | own program, not scheduled |

## Open decisions

1. **Crypto binding route** (this is the only open question about
   *how*, not *whether*, to get Ed25519/ECDSA — hand-rolling is
   ruled out per the section above). Evaluate `hacl-star` opam
   bindings first; fall back to vendored HACL\* C stubs
   (`parquet_zstd_stubs.c` precedent) if the opam package doesn't
   build on OCaml 4.14.1 or doesn't cross the `wasm_of_ocaml`
   boundary; NSS FFI only if both fail. Resolve before Stage 3.
2. **VC-JOSE-COSE scope.** Recommend explicit non-goal (different
   securing mechanism, needs JWT/CBOR parsing this project has no
   other use for) unless a concrete interop requirement names it.
3. **Bitstring Status List's gzip dependency.** The bitstring itself
   is GZIP-compressed per spec before base64url encoding. Writing a
   pure-F\* DEFLATE/GZIP codec is a large, disproportionate
   undertaking for one status-list feature; the pragmatic path is an
   `assume val gzip_compress`/`gunzip_decompress` pair, classified
   ASSUME-HOST (host-engine call-out) the same way `regex_match` is —
   compression semantics are not RDF/VC semantics. Confirm this
   framing before Stage 10 rather than reaching for a "just do it in
   OCaml" shortcut (anti-pattern risk, per `ocaml-boundary`).
4. **Whether to build the minimal VC-API HTTP server at all**
   (Stage 9). It is the only way to get a score against the *official*
   `vc-di-eddsa-test-suite`/`vc-di-ecdsa-test-suite` harnesses, but it
   is a nontrivial HTTP consumer for a benefit (upstream-badge parity)
   distinct from correctness, which the hand-derived-fixture path
   (Stages 5-7) already establishes more cheaply. Recommend deferring
   until Stages 1-8 land and the owner explicitly wants the official
   interop badge.
5. **`did:key` scope inside `VC.DataIntegrity`.** Verification-method
   resolution for `did:key` is pure local multibase decoding (no
   network I/O) and belongs inside this program (folded into
   `VC.Multibase`/`VC.DataIntegrity`, not a separate module). Full DID
   *method* resolution (`did:web` and friends, requiring network
   fetch) is explicitly out of scope here — the already-declared
   `third_party/testing/did` submodule stays uninitialized pending a
   separate DID-method program; do not let `did:web` support creep
   into this plan's Stage 5/6.
6. **Re-verify the cryptosuite specs' Test Vectors appendices before
   Stage 5.** This pass read the rendered `w3c.github.io/vc-di-eddsa/`
   HTML through a summarizing fetch and could not confirm whether the
   "Test Vectors" section's worked examples are fully populated
   (final canonical N-Quads, hash, proof bytes) or only procedural.
   If they are complete, they're a better fixture source than
   hand-deriving from scratch — check the raw spec source (not just
   the rendered page) first.
