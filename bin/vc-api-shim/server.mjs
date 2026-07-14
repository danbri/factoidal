#!/usr/bin/env node
'use strict';

// bin/vc-api-shim/server.mjs — VC-API HTTP shim over Factoidal's npm
// engine bundle (task #88, canivc.com community-compatibility
// integration; docs/designissues/2026-07-10-canivc-community-compat.md).
//
// This is a CONSUMER TOOL (iron rule #11: "Consumer tools ... are not
// part of the verified library and belong in bin/<consumer>/"). It
// adapts HTTP <-> the npm bundle's public API ONLY:
//   - JSON-LD parse + RDFC-1.0 canonicalize:  npm/factoidal `parse`,
//     `canonicalize` (fn.* / index.js's public surface, the SAME
//     surface exercised by npm/factoidal/test/vc-crypto*.test.js).
//   - eddsa-rdfc-2022 create/verify:          `vcEddsaCreateFromCanonical`,
//     `vcEddsaVerifyFromCanonical`, `vcEd25519SecretToPublic`.
//   - did:key resolution:                     `didKeyResolve`.
//   - VC Data Model 2.0 structural conformance: `vcCheckCredential`
//     (Track A2, docs/designissues/2026-07-11-vc-canivc-eecc-plan.md),
//     called from handleIssue/handleVerify/handleVerifyPresentation
//     before any crypto step. The SAME export handles both VCs and VPs
//     — VC.Credential.vc_check_from_string already dispatches on the
//     document's `type` internally (see VC.Credential.fst's
//     vc_check_document), so no separate npm ABI export was needed for
//     Verifiable Presentation verification (Track A3).
//   - Verifiable Presentation verification: POST /presentations/verify
//     (handleVerifyPresentation), sharing verifySecuredDocument with
//     handleVerify — structural check first, then the same
//     eddsa-rdfc-2022 Data Integrity proof verification over the VP's
//     own top-level proof (a presentation's embedded
//     `verifiableCredential` entries are structurally checked by
//     VC.Credential.fst but their own proofs are NOT independently
//     re-verified by this route — documented gap, not silently
//     assumed).
// It contains ZERO VC/RDF semantic logic: it never judges credential
// well-formedness itself, never rewrites a verdict, and never
// special-cases a test's input. A structural `valid`/`reason` outcome
// is exactly what `vcCheckCredential` (VC.Credential.vc_check_from_
// string, F*-verified) returned; a `verified` outcome is exactly what
// `vcEddsaVerifyFromCanonical` returned; a parse/canonicalize failure
// propagates as an honest error, not a fabricated pass or fail.
//
// The ONE piece of hand-written codec logic here is base58btc +
// Ed25519-multicodec (0xed 0x01) encode/decode for did:key identifiers
// (base58btcEncode/Decode, didKeyFromPublicKeyHex,
// publicKeyHexFromVerificationMethod below). This is wire-format
// transcoding — the same algorithm VC.Multibase.fst implements — not
// verification/correctness logic. It exists because the npm ABI
// exposes did:key *resolution* (didKeyResolve, F*-verified) but not
// did:key *construction* from a raw public key (no ABI export for the
// forward direction; see the design doc's WP2 section). All actual
// correctness — canonicalization, hashing, signing, verifying — routes
// through the engine.
//
// JSON-LD context handling: the npm bundle's JSON-LD loader has NO
// remote-context fetch wired (JSONLD.Loader.fst is an assume-val I/O
// seam with no documentLoader registered for this npm-entry consumer —
// see bin/npm-entry/entry_jsoo.ml). This shim ships a small local
// registry of vendored context documents (third_party/contexts/) and
// inlines them into `@context` before calling `parse`. A document
// whose context isn't in the registry fails to parse — an honest,
// documented gap, not a silent skip.
//
// Usage:
//   node bin/vc-api-shim/server.mjs --port 40443
//   node bin/vc-api-shim/server.mjs --port 40443 --seed-file path.json

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const REPO_ROOT = path.resolve(__dirname, '..', '..');

// npm/factoidal/index.js is CommonJS; bridge it into this ESM entry
// point with createRequire rather than forking a second copy of the
// wrapper (this shim's only engine dependency is that one file's
// public API).
const require = createRequire(import.meta.url);
const engine = require(path.join(REPO_ROOT, 'npm', 'factoidal', 'index.js'));

// ---------------------------------------------------------------------
// Local JSON-LD context registry (see header comment).
// ---------------------------------------------------------------------

const CONTEXTS_DIR = path.join(REPO_ROOT, 'third_party', 'contexts');
const CONTEXT_REGISTRY = new Map([
  ['https://www.w3.org/ns/credentials/v2', 'credentials-v2.jsonld'],
  ['https://www.w3.org/ns/credentials/examples/v2', 'credentials-examples-v2.jsonld'],
  ['https://w3id.org/security/data-integrity/v2', 'security-data-integrity-v2.jsonld'],
  ['https://w3id.org/security/multikey/v1', 'security-multikey-v1.jsonld'],
  ['https://www.w3.org/2018/credentials/v1', 'credentials-v1.jsonld'],
]);
const CONTEXT_CACHE = new Map();

function loadContext(iri) {
  if (CONTEXT_CACHE.has(iri)) return CONTEXT_CACHE.get(iri);
  const fname = CONTEXT_REGISTRY.get(iri);
  if (!fname) return undefined;
  const text = fs.readFileSync(path.join(CONTEXTS_DIR, fname), 'utf8');
  const doc = JSON.parse(text)['@context'];
  CONTEXT_CACHE.set(iri, doc);
  return doc;
}

// Replace any `@context` entry we have a local copy of with the parsed
// object, in place of the remote IRI string. Entries we don't
// recognise are passed through unchanged (and will fail to parse
// downstream if the document actually needs them — no guessing).
//
// Also unwraps the remote-context-DOCUMENT form: an entry that is an
// object `{"@context": X}` (the shape a dereferenced remote context
// file has, which digitalbazaar tooling embeds verbatim — e.g. the
// data-integrity-test-suite-assertion previousProof fixtures) is
// replaced by X itself. Same plumbing category as the IRI inlining
// above: both convert an indirection encoding into the equivalent
// inline context definition BEFORE the F* JSON-LD processor sees it;
// the strict F* context processor itself stays unchanged (an inline
// "@context" key inside a context definition is not valid JSON-LD 1.1,
// and the W3C JSON-LD negative tests depend on it staying rejected).
//
// Walks the WHOLE document tree, not just the top level: the VCDM v2
// context defines `verifiableCredential` (and other terms) with BOTH
// `"@container": "@graph"` AND a scoped `"@context": null` (see
// third_party/contexts/credentials-v2.jsonld) — the null scoped
// context means the JSON-LD processor resets the active context when
// it descends into an embedded credential, so that credential's OWN
// inline `@context` is what actually gets consulted, not the
// enclosing document's. Before this fix, only `doc['@context']` was
// rewritten, so a VP's embedded `verifiableCredential` array entries
// (each carrying their own `"@context":
// ["https://www.w3.org/ns/credentials/v2"]`) kept the bare remote
// IRI string. Since this bundle has no remote-context loader wired
// (module banner above), that unresolved nested reference made the
// F* JSON-LD processor treat the credential's own context as
// unresolvable, and the entire `@graph`-wrapped named-graph subtree
// it names was silently dropped from the RDF dataset (confirmed:
// canonicalizing such a VP produced only the top-level `type`
// triple) — not an error, and not a JSON-LD Expand/toRdf bug: the
// SAME `@container:@graph` + `@context:null` combination, with an
// INLINE object context instead of a remote string reference, is
// exercised and passes in the W3C toRdf suite (pr43). Recursing here
// fixes vc20-api's three VP-with-embedded-credential fails
// ("multiple @context URLs in a VP", "valid VP with
// verifiableCredential", "valid VP with holder") by giving the
// processor the same context content the real signer used when it
// computed the proof.
function inlineContexts(docIn) {
  const doc = JSON.parse(JSON.stringify(docIn));
  const rewrite = (ctx) => {
    if (typeof ctx === 'string') {
      const local = loadContext(ctx);
      return local !== undefined ? local : ctx;
    }
    if (Array.isArray(ctx)) return ctx.map(rewrite);
    if (ctx !== null && typeof ctx === 'object' && '@context' in ctx && Object.keys(ctx).length === 1) {
      return rewrite(ctx['@context']);
    }
    return ctx;
  };
  // `walk` only ever calls `rewrite` on a "@context" key's VALUE, never
  // recursing into it afterward — a context definition's own internal
  // structure (e.g. a term's scoped "@context": null) is JSON-LD
  // machinery, not a nested document subtree, and must stay untouched.
  const walk = (node) => {
    if (Array.isArray(node)) return node.map(walk);
    if (node !== null && typeof node === 'object') {
      const out = {};
      for (const [k, v] of Object.entries(node)) {
        out[k] = k === '@context' ? rewrite(v) : walk(v);
      }
      return out;
    }
    return node;
  };
  return walk(doc);
}

async function canonicalizeJsonld(doc) {
  const ds = await engine.parse(JSON.stringify(inlineContexts(doc)), { format: 'jsonld' });
  return engine.canonicalize(ds);
}

// ---------------------------------------------------------------------
// VC Data Model 2.0 structural conformance (Track A2,
// docs/designissues/2026-07-11-vc-canivc-eecc-plan.md). ALL judgment
// comes from the F*-extracted VC.Credential.vc_check_from_string via
// the npm ABI's vcCheckCredential export (rule #11: this shim never
// re-implements a structural check, it only maps the verdict to an
// HTTP rejection). `V2_CONTEXT_TEXT` is the vendored VCDM v2 base
// context document's raw text (the SAME file bin/vc-runner/vc_runner.ml
// reads as `v2ctx` for the offline vc_stage1 suite), read once at
// startup and passed through unmodified on every call.
// ---------------------------------------------------------------------

const V2_CONTEXT_TEXT = fs.readFileSync(
  path.join(CONTEXTS_DIR, 'credentials-v2.jsonld'), 'utf8');

// ---------------------------------------------------------------------
// relatedResource digest registry (VCDM 2.0 §5.3, Track A4). The
// F*-verified check (VC.Credential.vc_check_related_resource_digests_
// from_string, via the npm ABI's vcCheckRelatedResourceDigests) owns
// ALL the judgment — how a declared digestSRI/digestMultibase value
// decodes, what "matches" means, and the offline policy (unknown
// resource ids and uncovered algorithms pass; a KNOWN resource whose
// digest matches no known revision is the spec's mismatch error). This
// shim only supplies the registry the engine cannot build itself (no
// I/O in F*): for each resource id, the sha256 + sha384 digests of
// EVERY vendored revision of that resource's content bytes, computed
// here from the real files at startup — never hardcoded digest
// constants. Hashing a static vendored file is a host-crypto primitive
// call (same category as the base58 codec above, per the crypto-policy
// skill); the engine has no sha384 primitive, so both hashes use
// node:crypto for symmetry. Multiple revisions per id because the
// served document changes over time and a credential's digest refers
// to whichever revision was live when it was issued (see
// third_party/contexts/PROVENANCE.md's 20240720 entry).
// ---------------------------------------------------------------------

const RELATED_RESOURCE_FILES = new Map([
  ['https://www.w3.org/ns/credentials/v2', [
    'credentials-v2.jsonld',                  // current (2025-05-15 REC era)
    'credentials-v2-20240720-8d0ee107.jsonld', // 2024-07-20 revision
  ]],
]);

const RELATED_RESOURCE_REGISTRY_JSON = JSON.stringify(
  [...RELATED_RESOURCE_FILES].map(([id, files]) => ({
    id,
    digestsHex: files.flatMap((f) => {
      const bytes = fs.readFileSync(path.join(CONTEXTS_DIR, f));
      return [
        crypto.createHash('sha256').update(bytes).digest('hex'),
        crypto.createHash('sha384').update(bytes).digest('hex'),
      ];
    }),
  })));

// VC.Credential.fst's structural checker is VCDM 2.0-specific: its
// @context sentinel requires the v2 base context IRI first (VCDM 2.0
// §4.1). A document whose FIRST @context entry is the legacy VC 1.1
// base context (https://www.w3.org/2018/credentials/v1) is explicitly
// NOT claiming VCDM 2.0 conformance — it is out of scope for a
// VCDM-2.0-specific gate, the same way a SPARQL 1.0 query being
// rejected by a SPARQL 1.1-only validator would be a mapping error,
// not a defect in the validator. This matters because the (separate,
// upstream) Data Integrity eddsa-rdfc-2022 conformance suite
// (third_party/testing/vc-di-eddsa, a DIFFERENT W3C test suite from
// vc-data-model-2.0-test-suite) deliberately exercises proof mechanics
// against exactly such a legacy-context fixture (its vendored
// data-integrity-test-suite-assertion/validVc.json) — Data Integrity
// proofs are not scoped to a VCDM version. Skipping the VCDM 2.0
// structural gate for that one explicit, unambiguous case and letting
// the (unrelated) crypto layer handle the document as it did before
// this gate existed is a mapping decision on THIS shim's part (rule
// #11: no semantic logic added — it is an all-or-nothing bypass of the
// F*-verified check, not a partial reimplementation of it), not a
// change to VC.Credential.fst. No vc-data-model-2.0-test-suite fixture
// uses the v1 context (grep-confirmed against third_party/testing/vc/
// tests/input/*.json), so this carve-out cannot mask a real vc20_api
// violation.
const VC1_LEGACY_CONTEXT = 'https://www.w3.org/2018/credentials/v1';

function firstContextEntry(ctx) {
  if (typeof ctx === 'string') return ctx;
  if (Array.isArray(ctx) && ctx.length > 0) return ctx[0];
  return undefined;
}

// Returns {valid: true} | {valid: false, reason: string}.
async function checkStructural(doc) {
  if (firstContextEntry(doc && doc['@context']) === VC1_LEGACY_CONTEXT) {
    // Data Integrity proof mechanics are not scoped to a VCDM version
    // (see this branch's original comment above) — the FULL
    // vcCheckCredential gate below is VCDM-2.0-specific and does not
    // apply here, but two invariants of the Data Integrity / VC Data
    // Model spec DO apply regardless of @context vintage (Track A1,
    // docs/designissues/2026-07-11-vc-canivc-eecc-plan.md):
    //   1. credentialSubject presence/shape (vcCheckCredentialSubject
    //      — the SAME rule vcCheckCredential enforces for v2 documents,
    //      just without the v2-only @context gate around it).
    //   2. DATA_LOSS_DETECTION_ERROR (vcCheckNoDataLoss): an undefined
    //      type/credentialSubject term that a lenient JSON-LD processor
    //      would silently drop MUST be rejected, not signed/verified
    //      over. Needs the REAL (inlined) context object, not a remote
    //      IRI string — this engine build has no remote-context loader.
    const subj = await engine.vcCheckCredentialSubject(JSON.stringify(doc));
    if (!subj.valid) return subj;
    return engine.vcCheckNoDataLoss(JSON.stringify(inlineContexts(doc)));
  }
  const structural = await engine.vcCheckCredential(V2_CONTEXT_TEXT, JSON.stringify(doc));
  if (!structural.valid) return structural;
  // relatedResource digest verification (VCDM 2.0 §5.3) — a separate
  // F*-verified gate because vc_check_document's signature carries no
  // digest registry (see the registry builder's comment above).
  return engine.vcCheckRelatedResourceDigests(
    RELATED_RESOURCE_REGISTRY_JSON, JSON.stringify(doc));
}

// The Data Integrity vocabulary (DataIntegrityProof, cryptosuite,
// verificationMethod, proofPurpose, created, proofValue) is only
// SCOPED inside credentials-v2.jsonld's "VerifiableCredential" term —
// it is not defined at all by the older VC 1.1 base context
// (credentials-v1.jsonld). A proof options document canonicalized
// under a v1-only context would silently DROP those properties
// (JSON-LD's "undefined term" rule is drop-not-error), producing a
// truncated, non-interoperable signature input. Every proofOptions
// document therefore gets the security/data-integrity/v2 context
// appended if not already present — this is what real eddsa-rdfc-2022
// implementations do (a proof block commonly carries its own explicit
// @context distinct from the securing document's), not a
// test-specific special case: it applies unconditionally, to every
// credential context vintage, and only supplies vocabulary — it never
// changes which properties are read from the input.
const DATA_INTEGRITY_CONTEXT = 'https://w3id.org/security/data-integrity/v2';
const VC_V2_CONTEXT = 'https://www.w3.org/ns/credentials/v2';
function proofContextFor(credentialContext) {
  const base = Array.isArray(credentialContext)
    ? credentialContext.slice()
    : (credentialContext ? [credentialContext] : []);
  // credentials-v2.jsonld already carries a scoped DataIntegrityProof
  // definition (verified by hand: parsing v2 alone resolves
  // cryptosuite/verificationMethod/proofPurpose correctly). Appending
  // security-data-integrity-v2.jsonld ON TOP of v2 redefines those
  // same protected terms and the engine rejects the document
  // ("invalid or unsupported JSON-LD") — confirmed by direct testing,
  // not a guess. Only append when v2 (or the DI context itself) isn't
  // already present.
  if (!base.includes(VC_V2_CONTEXT) && !base.includes(DATA_INTEGRITY_CONTEXT)) {
    base.push(DATA_INTEGRITY_CONTEXT);
  }
  return base;
}

// ---------------------------------------------------------------------
// base58btc + Ed25519-multicodec (0xed 0x01) codec — wire format only.
// Mirrors VC.Multibase.fst's ed25519_multicodec_prefix /
// multibase_encode_base58btc (formal/fstar/VC.Multibase.fst:188-197);
// re-implemented here only because the npm ABI does not expose a
// did:key *construction* function (only didKeyResolve, the reverse).
// ---------------------------------------------------------------------

const B58_ALPHABET = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';

function base58btcEncode(bytes) {
  let n = 0n;
  for (const b of bytes) n = (n << 8n) | BigInt(b);
  let out = '';
  while (n > 0n) {
    out = B58_ALPHABET[Number(n % 58n)] + out;
    n /= 58n;
  }
  for (const b of bytes) {
    if (b === 0) out = '1' + out; else break;
  }
  return out;
}

function base58btcDecode(str) {
  let n = 0n;
  for (const ch of str) {
    const idx = B58_ALPHABET.indexOf(ch);
    if (idx < 0) throw new Error(`base58btcDecode: invalid character ${ch}`);
    n = n * 58n + BigInt(idx);
  }
  let hex = n.toString(16);
  if (hex.length % 2) hex = '0' + hex;
  const bytes = Buffer.from(hex, 'hex');
  let leadingZeros = 0;
  for (const ch of str) { if (ch === '1') leadingZeros++; else break; }
  return Buffer.concat([Buffer.alloc(leadingZeros), bytes]);
}

const ED25519_MULTICODEC_PREFIX = Buffer.from([0xed, 0x01]);

function didKeyFromPublicKeyHex(pkHex) {
  const pk = Buffer.from(pkHex, 'hex');
  const tagged = Buffer.concat([ED25519_MULTICODEC_PREFIX, pk]);
  const mb = 'z' + base58btcEncode(tagged);
  return `did:key:${mb}`;
}

// "did:key:z6Mk...#z6Mk..." or "did:key:z6Mk..." -> 32-byte pubkey hex,
// or null if not a well-formed Ed25519 did:key (never throws; an
// unresolvable verificationMethod must produce verified:false, not a
// crashed request).
function publicKeyHexFromVerificationMethod(vm) {
  if (typeof vm !== 'string' || !vm.startsWith('did:key:')) return null;
  const rest = vm.slice('did:key:'.length);
  const mb = rest.split('#')[0];
  if (!mb.startsWith('z')) return null;
  try {
    const tagged = base58btcDecode(mb.slice(1));
    if (tagged.length !== 34) return null;
    if (tagged[0] !== 0xed || tagged[1] !== 0x01) return null;
    return tagged.subarray(2).toString('hex');
  } catch {
    return null;
  }
}

// ---------------------------------------------------------------------
// Issuer identity — TEST KEY ONLY, deterministic from a fixed seed
// fixture (bin/vc-api-shim/test-issuer-seed.json). Not for production
// use; documented in that fixture's own header.
// ---------------------------------------------------------------------

function loadIssuerIdentity(seedFile) {
  const fixture = JSON.parse(fs.readFileSync(seedFile, 'utf8'));
  return { secretKeyHex: fixture.secretKeyHex, seed: fixture.seed };
}

async function buildIssuer(seedFile) {
  const { secretKeyHex, seed } = loadIssuerIdentity(seedFile);
  const publicKeyHex = await engine.vcEd25519SecretToPublic(secretKeyHex);
  const did = didKeyFromPublicKeyHex(publicKeyHex);
  const verificationMethod = `${did}#${did.slice('did:key:'.length)}`;
  return { secretKeyHex, publicKeyHex, did, verificationMethod, seed };
}

// ---------------------------------------------------------------------
// HTTP plumbing.
// ---------------------------------------------------------------------

function readJsonBody(req) {
  return new Promise((resolve, reject) => {
    let data = '';
    req.on('data', (chunk) => { data += chunk; });
    req.on('end', () => {
      if (!data) return resolve({});
      try { resolve(JSON.parse(data)); } catch (e) { reject(e); }
    });
    req.on('error', reject);
  });
}

function sendJson(res, status, obj) {
  const body = JSON.stringify(obj, null, 2);
  res.writeHead(status, {
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': Buffer.byteLength(body),
  });
  res.end(body);
}

// POST /credentials/issue  { credential, options? } -> { verifiableCredential }
async function handleIssue(issuer, body) {
  const credential = body && body.credential;
  if (!credential || typeof credential !== 'object') {
    return [400, { errors: [{ message: 'request body must have a "credential" object' }] }];
  }
  // Structural conformance (VC.Credential.fst, via vcCheckCredential) —
  // BEFORE any crypto/canonicalization step. Rejects the same shapes
  // the offline vc_stage1 suite's tests/input/*-fail.json fixtures do:
  // missing/malformed @context, missing type, empty credentialSubject,
  // malformed credentialStatus/credentialSchema/termsOfUse/evidence/
  // refreshService, non-URL ids, validUntil before validFrom, etc.
  const structural = await checkStructural(credential);
  if (!structural.valid) {
    return [400, { errors: [{ message: `structural validation failed: ${structural.reason}` }] }];
  }
  const unsecured = { ...credential };
  delete unsecured.proof;

  const proofPurpose = (body.options && body.options.proofPurpose) || 'assertionMethod';
  const proofOptions = {
    '@context': proofContextFor(credential['@context']),
    type: 'DataIntegrityProof',
    cryptosuite: 'eddsa-rdfc-2022',
    created: new Date().toISOString(),
    verificationMethod: issuer.verificationMethod,
    proofPurpose,
  };

  let docNquads, cfgNquads;
  try {
    docNquads = await canonicalizeJsonld(unsecured);
    cfgNquads = await canonicalizeJsonld(proofOptions);
  } catch (e) {
    return [400, { errors: [{ message: `canonicalization failed: ${e.message}` }] }];
  }

  let proofValue;
  try {
    proofValue = await engine.vcEddsaCreateFromCanonical(issuer.secretKeyHex, docNquads, cfgNquads);
  } catch (e) {
    return [500, { errors: [{ message: `proof creation failed: ${e.message}` }] }];
  }

  // The returned document's top-level @context must ALSO carry the
  // Data Integrity vocabulary: a consumer expanding proof.type using
  // the DOCUMENT's own top-level context (not proof's nested one) —
  // exactly what the eddsa-rdfc-2022 test suite's own assertions do —
  // needs DataIntegrityProof/cryptosuite resolvable from there too.
  const verifiableCredential = {
    ...credential,
    '@context': proofContextFor(credential['@context']),
    proof: { ...proofOptions, proofValue },
  };
  // Response shape: the VC-API spec's documented envelope is
  // {"verifiableCredential": {...}}. The two vendored test harnesses
  // disagree on this in practice: eddsa-rdfc-2022's HTTP client
  // (vc-test-suite-implementations' makeHttpsRequest) unwraps
  // data.verifiableCredential when present; vc-data-model-2.0's own
  // local TestEndpoints.js, when talking to a plain http:// (not
  // https://) endpoint — the documented local-testing mode — returns
  // the raw response body with NO unwrapping, so it needs the
  // credential's fields at the top level. Exposing both (spread +
  // the wrapper key) satisfies both real consumers with the same
  // data, not two different answers.
  return [201, { ...verifiableCredential, verifiableCredential }];
}

// Verify ONE proof entry from a (possibly multi-proof) proof set or
// proof chain. For a plain SET member (no previousProof) the document
// hash input is the UNSECURED document's canonical N-Quads, the same
// for every such proof (`docNquads`, canonicalized once by the
// caller). For a CHAIN member (previousProof present) the VC Data
// Integrity spec's "Verify Proof Sets and Chains" algorithm instead
// hashes the unsecured document WITH the matching previous proof
// object(s) re-attached as its `proof` property (full objects,
// proofValue included — mirroring "Add Proof Set/Chain", which signs
// chained proofs over exactly that shape), so a chained proof's
// document hash is per-proof, not shared. That is what cryptographic-
// ally binds the chain order: tamper with an earlier proof and every
// later proof that names it stops verifying. A dangling previousProof
// (no proof in `allProofs` with that id) is the spec's "does not exist
// in allProofs" error, reported per-proof here (the caller also
// cross-checks the topology for its error envelope). Never throws — a
// resolution/canonicalization/crypto failure comes back as
// `{ok: false, reason}` so the caller can evaluate every proof in a
// set even when one individually fails.
async function verifyOneProof(doc, unsecured, docNquads, allProofs, proof) {
  if (proof.cryptosuite !== 'eddsa-rdfc-2022') {
    return { ok: false, reason: `unsupported cryptosuite "${proof.cryptosuite}" (this shim only implements eddsa-rdfc-2022)` };
  }
  if (typeof proof.proofValue !== 'string') {
    return { ok: false, reason: 'proof has no proofValue' };
  }
  // The Data Integrity spec requires type, verificationMethod, and
  // proofPurpose on every proof (2.1 Proofs) — a request-shape check,
  // not a cryptographic judgment. A VerifiablePresentation's proof
  // commonly carries proofPurpose "authentication" plus "challenge"/
  // "domain" (AuthenticationProofPurpose) rather than "assertionMethod"
  // — this check only requires the three fields be present strings, it
  // never constrains their value, so both shapes pass unchanged.
  for (const field of ['type', 'verificationMethod', 'proofPurpose']) {
    if (typeof proof[field] !== 'string' || proof[field] === '') {
      return { ok: false, reason: `proof is missing required field "${field}"` };
    }
  }
  // Respect an explicit proof-level @context if the document carries
  // one (common from other implementations); otherwise fall back to
  // the document's own context plus the Data Integrity vocabulary
  // (see proofContextFor's comment above). Any extra proof fields
  // (challenge, domain, id, previousProof, ...) ride along via the
  // `...proof` spread, so they canonicalize as part of this proof's
  // own config exactly as the signer included them.
  const proofOptions = {
    '@context': proof['@context'] || proofContextFor(doc['@context']),
    ...proof,
  };
  delete proofOptions.proofValue;

  // Chain member: re-attach the referenced previous proof object(s) to
  // the unsecured document and canonicalize THAT as this proof's
  // document-hash input (see header comment). Set member: use the
  // caller's shared unsecured-document N-Quads unchanged.
  let effectiveDocNquads = docNquads;
  if (proof.previousProof !== undefined) {
    const refs = Array.isArray(proof.previousProof) ? proof.previousProof : [proof.previousProof];
    const matching = [];
    for (const ref of refs) {
      const m = allProofs.find((p) => p && typeof p.id === 'string' && p.id === ref);
      if (!m) {
        return { ok: false, reason: `proof.previousProof "${ref}" does not match the id of any proof in this document` };
      }
      matching.push(m);
    }
    try {
      effectiveDocNquads = await canonicalizeJsonld({ ...unsecured, proof: matching });
    } catch (e) {
      return { ok: false, reason: `canonicalization failed (chained document): ${e.message}` };
    }
  }

  let cfgNquads;
  try {
    cfgNquads = await canonicalizeJsonld(proofOptions);
  } catch (e) {
    return { ok: false, reason: `canonicalization failed: ${e.message}` };
  }

  const pkHex = publicKeyHexFromVerificationMethod(proof.verificationMethod);
  if (!pkHex) {
    return { ok: false, reason: `could not resolve verificationMethod "${proof.verificationMethod}" (only did:key Ed25519 is supported by this shim)` };
  }

  try {
    const verified = await engine.vcEddsaVerifyFromCanonical(pkHex, effectiveDocNquads, cfgNquads, proof.proofValue);
    return verified ? { ok: true } : { ok: false, reason: 'signature did not verify' };
  } catch (e) {
    return { ok: false, reason: `verify failed: ${e.message}` };
  }
}

// Shared structural + Data Integrity proof verification for any secured
// VCDM 2.0 document — a VerifiableCredential (POST /credentials/verify)
// or a VerifiablePresentation (POST /presentations/verify). The two
// routes differ only in their request/response envelope field name
// ("verifiableCredential" vs "verifiablePresentation"); the checks
// themselves are identical because VC.Credential.vc_check_from_string
// already dispatches VC-shaped vs VP-shaped documents internally (its
// @context/type checks apply to both; credentialSubject is checked only
// when "VerifiableCredential" is in `type`, the embedded
// `verifiableCredential` list only when "VerifiablePresentation" is) —
// see VC.Credential.fst's vc_check_document. Reusing one function here
// keeps that symmetry on the shim side too (rule #11: no per-route
// semantic logic, both routes map the SAME F*-verified verdict).
//
// Proof sets / chains (Track A1, docs/designissues/2026-07-11-vc-
// canivc-eecc-plan.md): `doc.proof` MAY be an unordered set of
// objects (VC Data Integrity §2.1 "Proofs"). EVERY proof is verified
// independently by verifyOneProof above — set members against the
// shared unsecured-document hash, chain members (previousProof
// present) against the unsecured document with their referenced
// previous proof(s) re-attached (see verifyOneProof's header comment
// for the spec algorithm). Every `proof.previousProof` reference (a
// single string or an unordered list of strings) MUST name a proof.id
// present in this SAME set — VC Data Integrity §"Verify Proof Sets and
// Chains": "If a proof with id equal to previousProof does not exist
// in allProofs, an error MUST be raised". "Each value identifies
// another data integrity proof, all of which MUST also verify for the
// current proof to be considered verified" is covered by requiring
// EVERY proof's own signature to verify, and the chain ordering is
// cryptographically bound because a chained proof's document hash
// embeds the referenced proofs in full — corrupt an earlier proof and
// both its own verifyOneProof call AND every later proof that names it
// fail; no separate recursive "verify the referent first" walk is
// needed.
async function verifySecuredDocument(doc) {
  // Structural conformance (VC.Credential.fst, via vcCheckCredential) —
  // BEFORE any crypto/canonicalization step. A structurally invalid
  // document is rejected regardless of whether its proof would
  // otherwise verify.
  const structural = await checkStructural(doc);
  if (!structural.valid) {
    return [400, { verified: false, errors: [{ message: `structural validation failed: ${structural.reason}` }] }];
  }
  const proofs = Array.isArray(doc.proof) ? doc.proof : (doc.proof ? [doc.proof] : []);
  if (proofs.length === 0) {
    return [400, { verified: false, errors: [{ message: 'document has no proof' }] }];
  }

  const unsecured = { ...doc };
  delete unsecured.proof;

  let docNquads;
  try {
    docNquads = await canonicalizeJsonld(unsecured);
  } catch (e) {
    return [400, { verified: false, errors: [{ message: `canonicalization failed: ${e.message}` }] }];
  }

  const perProof = [];
  for (const proof of proofs) {
    perProof.push(await verifyOneProof(doc, unsecured, docNquads, proofs, proof));
  }

  // previousProof topology: every reference must resolve to an id
  // actually present in this proof set (proofs without an "id" simply
  // cannot be referenced — a dangling reference to one is exactly the
  // "does not exist in allProofs" failure the spec names).
  const proofIds = new Set(proofs.map((p) => p && p.id).filter((id) => typeof id === 'string'));
  const chainErrors = [];
  for (const proof of proofs) {
    if (proof.previousProof === undefined) continue;
    const refs = Array.isArray(proof.previousProof) ? proof.previousProof : [proof.previousProof];
    for (const ref of refs) {
      if (typeof ref !== 'string' || !proofIds.has(ref)) {
        chainErrors.push(`proof.previousProof "${ref}" does not match the id of any proof in this document`);
      }
    }
  }

  const results = proofs.map((proof, i) => ({ proof, verified: perProof[i].ok }));
  const verified = perProof.every((r) => r.ok) && chainErrors.length === 0;
  if (!verified) {
    const errors = perProof
      .filter((r) => !r.ok)
      .map((r) => ({ message: r.reason }))
      .concat(chainErrors.map((message) => ({ message })));
    // A verified:false crypto/topology outcome (correctly-shaped
    // proof(s), wrong signature/key/tampered document/dangling
    // previousProof) is still reported as an error response (400) —
    // this suite's own assertions (data-integrity-test-suite-
    // assertion's verificationFail) require a non-2xx status + error
    // body for every non-passing verification, not a
    // 200-with-verified:false envelope.
    return [400, { verified: false, results, errors }];
  }
  return [200, { verified: true, results }];
}

// POST /credentials/verify  { verifiableCredential } -> { verified, ... }
async function handleVerify(body) {
  const vc = body && body.verifiableCredential;
  if (!vc || typeof vc !== 'object') {
    return [400, { verified: false, errors: [{ message: 'request body must have a "verifiableCredential" object' }] }];
  }
  return verifySecuredDocument(vc);
}

// POST /presentations/verify  { verifiablePresentation, options? } -> { verified, ... }
// Same structural-then-crypto pipeline as handleVerify (see
// verifySecuredDocument's header comment) — this route exists because
// the vc-data-model-2.0-test-suite's own VP-shaped negative tests
// (Basic Conformance, Contexts, Types, Algorithms) need a real
// `vpVerifiers` endpoint to POST to; without one, the suite's
// TestEndpoints.verifyVp resolves to `null` and every `assert.rejects`
// against it fails "missing expected rejection" regardless of the VP's
// actual shape (docs/test-results/by-suite/vc20-api.json's `remaining`
// entry, before this route existed).
async function handleVerifyPresentation(body) {
  const vp = body && body.verifiablePresentation;
  if (!vp || typeof vp !== 'object') {
    return [400, { verified: false, errors: [{ message: 'request body must have a "verifiablePresentation" object' }] }];
  }
  return verifySecuredDocument(vp);
}

async function main() {
  const args = process.argv.slice(2);
  let port = 40443;
  let seedFile = path.join(__dirname, 'test-issuer-seed.json');
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--port') port = Number(args[++i]);
    else if (args[i] === '--seed-file') seedFile = args[++i];
  }

  const issuer = await buildIssuer(seedFile);

  const server = http.createServer(async (req, res) => {
    try {
      if (req.method === 'GET' && req.url === '/') {
        return sendJson(res, 200, { name: 'factoidal-vc-api-shim', issuer: issuer.did });
      }
      if (req.method === 'POST' && req.url === '/credentials/issue') {
        const body = await readJsonBody(req);
        const [status, out] = await handleIssue(issuer, body);
        return sendJson(res, status, out);
      }
      if (req.method === 'POST' && req.url === '/credentials/verify') {
        const body = await readJsonBody(req);
        const [status, out] = await handleVerify(body);
        return sendJson(res, status, out);
      }
      if (req.method === 'POST' && req.url === '/presentations/verify') {
        const body = await readJsonBody(req);
        const [status, out] = await handleVerifyPresentation(body);
        return sendJson(res, status, out);
      }
      return sendJson(res, 404, { errors: [{ message: `no route for ${req.method} ${req.url}` }] });
    } catch (e) {
      return sendJson(res, 500, { errors: [{ message: e.message || String(e) }] });
    }
  });

  server.listen(port, () => {
    // Deterministic startup log line (grepped by tests/vc-api-shim/run.sh
    // and the suite run.sh scripts to know the shim is ready).
    console.log(`vc-api-shim listening on http://localhost:${port} issuer=${issuer.did}`);
  });

  process.on('SIGTERM', () => server.close(() => process.exit(0)));
  process.on('SIGINT', () => server.close(() => process.exit(0)));
}

main().catch((e) => {
  console.error('vc-api-shim: fatal:', e);
  process.exit(1);
});
