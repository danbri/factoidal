---
title: "Verifiable Credentials and CSVW"
description: "VC Data Model structural validation plus eddsa-rdfc-2022 Data Integrity signatures — real Ed25519 + SHA-256 via vendored HACL* (no hand-rolled crypto) — and CSVW csv2rdf converting a real municipal-data fixture live in the browser."
layout: hub.njk
series: docs-hub
series_order: 13
vocab: schema.org
status: published
tests: tests/hub/post13_test.mjs
---

The last three posts covered rules ([RIF](./10-rules-rif-core.md)),
syntax ([post 11](./11-one-graph-five-syntaxes.md)), and the whole npm
surface ([post 12](./12-the-api-tour.md)). This post closes the series
on the two newest capabilities this project has added: **Verifiable
Credentials** — structural validation *and* `eddsa-rdfc-2022` Data
Integrity signatures — and **CSVW** (CSV on the Web) csv2rdf
conversion. The point of this post is to say exactly how far each one
goes today, and to draw the line honestly between the pipeline steps
that run live in your browser and the signature step that runs
natively.

## Verifiable Credentials: structural validation

A Verifiable Credential is a JSON(-LD) document — an issuer's claim
about a subject, structured so it can later be cryptographically
signed and checked. `VC.Credential.fst` checks the **structural**
rules the VC Data Model 2.0 spec lays out: `@context` presence,
`type` membership, `credentialSubject` non-emptiness, issuer/
credentialStatus/credentialSchema/termsOfUse/evidence/refreshService/
proof inner shapes, `validFrom`/`validUntil` well-formedness and
ordering, holder shape, and closed language-map validation on names
and descriptions.

Measured against the vendored W3C `vc-data-model-2.0-test-suite`
fixtures: **109 pass, 5 fail, 6 skip (of 120)** — see
[the test-results dashboard]({{ '/test-results/' | url }}) for the
current run. The 5 fails are diagnosed, not swept under a skip: 4 are
a single JSON-LD type-redefinition cluster that needs a
context-processing module (a later stage, not yet built); 1 is a
suite artifact — the fixture pair in question has one file whose
`validFrom`/`validUntil` fields are literal placeholder strings
(`'PAST DATE'`/`'FUTURE DATE'`) that the upstream test suite's own
JavaScript substitutes at run time, so the two raw fixtures are
structurally identical and any offline check that catches the
`-fail` case would also wrongly fail its `-ok` sibling. 109 of 114
plain-verdict fixtures is the measured ceiling for a structural
validator with no live substitution step.

**Structural validation has no browser export.** `npm/factoidal`'s
browser entry (`browser.js`) exports no VC structural-validation
function — no `vcValidate`, nothing VC-shaped — so that particular
check runs in the native/Node runner, not live on this page. Below is
one of the vendored test fixtures the validator checks, shown
statically (not executed):

```json
{
  "@context": [
    "https://www.w3.org/2018/credentials/v1"
  ],
  "type": ["VerifiableCredential"],
  "credentialSubject": {
    "id": "did:key:z6MkhTNL7i2etLerDK8Acz5t528giE5KA4p75T6ka1E1D74r"
  }
}
```

A minimal but valid credential: a `@context`, a `type` that includes
`VerifiableCredential`, and a non-empty `credentialSubject`. That's
enough to pass every structural check `VC.Credential.fst` runs today
— issuer, status, schema, and the rest are optional fields this
fixture simply omits.

## Data Integrity: eddsa-rdfc-2022 signatures, via HACL\*

Structural validation is everything you can check *before* a signature
enters the picture. The signature layer is now here too.
`VC.DataIntegrity.fst` implements the `eddsa-rdfc-2022` cryptosuite end
to end — the same pipeline the W3C Data Integrity spec defines:

1. **Canonicalize** the unsecured credential (and, separately, the
   proof-options block) to a stable byte sequence with RDFC-1.0, so two
   isomorphic graphs sign to the same thing regardless of blank-node
   labelling or triple order.
2. **Hash** each canonical form with SHA-256.
3. **Sign** the combined digest with Ed25519, producing a 64-byte
   signature.
4. **Encode** the signature as a multibase-`z` (base58btc) `proofValue`
   and wrap it in a `DataIntegrityProof` block.
5. **Verify** by recomputing the digest and checking the signature
   against the issuer's public key.

**No cryptography is hand-rolled.** Ed25519 and SHA-256 both come from
[HACL\*](https://github.com/danbri/factoidal/blob/claude/main/third_party/hacl/PROVENANCE.md)
— the F\*/Low\*-verified crypto library Mozilla ships inside NSS —
vendored as C (cryspen/hacl-packages, Apache-2.0) and called through a
thin `assume val` seam, exactly as the project's crypto-sourcing policy
requires
([`skills/crypto-policy/SKILL.md`](https://github.com/danbri/factoidal/blob/claude/main/skills/crypto-policy/SKILL.md)).
The F\* pipeline around them — canonicalize, assemble the hash input,
multibase-encode the signature, serialize the proof block — is verified
in F\*; those two primitive call-outs are the only crypto that isn't
ours to prove.

### Steps 1–2 run live in your browser

The first two steps are pure transforms with no secret key, so they run
live here on the same credential dataset the native runner signs below.
Step 1 is RDFC-1.0 canonicalization — `Factoidal.canonicalize`, the raw
ABI export [post 08](./08-canonical-graphs-rdfc10.md) introduced:

```observable-js
// The unsecured credential, as an RDF dataset -- the exact one the
// native vc_runner signs further down. The blank node _:b0 makes
// canonicalization do real work rather than a no-op.
const credential = `<urn:credential:1> <https://www.w3.org/2018/credentials#issuer> <urn:issuer:acme> .
<urn:credential:1> <http://schema.org/credentialSubject> _:b0 .
_:b0 <http://schema.org/name> "Alice" .
`;

const canonical = await Factoidal.canonicalize(credential, { format: "nquads" });
return { canonical, lines: canonical.trim().split("\n").length };
```

The blank node `_:b0` comes out as `_:c14n0` — RDFC-1.0's canonical
label — so the same credential serialized with any other blank-node
name produces byte-identical output. Step 2 is SHA-256 of those
canonical bytes. This cell uses Web Crypto's `crypto.subtle.digest`,
the browser's own SHA-256, which computes bit-for-bit the same digest
the native pipeline gets from HACL\*:

```observable-js
const credential = `<urn:credential:1> <https://www.w3.org/2018/credentials#issuer> <urn:issuer:acme> .
<urn:credential:1> <http://schema.org/credentialSubject> _:b0 .
_:b0 <http://schema.org/name> "Alice" .
`;

async function sha256Hex(text) {
  const bytes = new TextEncoder().encode(text);
  const digest = await crypto.subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(digest)].map((b) => b.toString(16).padStart(2, "0")).join("");
}

const canonical = await Factoidal.canonicalize(credential, { format: "nquads" });
const sha256 = await sha256Hex(canonical);
return { sha256, hashLength: sha256.length };
```

That 32-byte digest (64 hex characters) is the input the signature
covers. Everything up to this line runs in the browser; the step that
needs a secret key — Ed25519 sign, and its verify — does not.

### Steps 3–5 run natively: the real roundtrip

Ed25519 sign and verify go through the vendored HACL\* C, which does
**not** link under `wasm_of_ocaml` today, so there is no live
browser/wasm cell for the signature itself — that gap is tracked in
[#286](https://github.com/danbri/factoidal/issues/286). The honest form
for a native-only step is its actual transcript. Here is
`./bin/linux-x86_64/vc_runner --crypto`, run against the vendored
HACL\* build, verbatim:

```text
=== VC Data Integrity eddsa-rdfc-2022 roundtrip (crypto mode) ===

  [PASS] Ed25519 keypair derived (HACL* secret_to_public)
  [PASS] create produced a multibase-z proofValue
  [PASS] multibase-z proofValue decodes back to signature hex
  [PASS] verify with correct key + document + proof = true
  [PASS] verify with WRONG public key = false
  [PASS] verify against a DIFFERENT document = false
  [PASS] verify with a TAMPERED proofValue = false
  [PASS] DataIntegrityProof block serializes with proofValue

========================================
vc-dataintegrity-eddsa-rdfc-2022: 8 pass, 0 fail (out of 8)
========================================
```

Read the negative cases, because they are the point of a signature.
**Verify returns `false`** when the public key is wrong (someone else's
key can't validate this issuer's proof), when the document differs by a
single triple (the runner changes `"Alice"` to `"Mallory"`, the digest
moves, and the signature no longer matches), and when the `proofValue`
itself is tampered (swap two characters of its base58 body and the
decoded signature is garbage). Only the correct key, against the exact
signed document, with an untouched proof, returns `true`. That trio —
wrong key, wrong document, tampered proof, all rejected — is what a
Data Integrity proof buys you.

Because Ed25519 is native-only, this roundtrip is not one of the live
browser cells above; it is pinned instead by the `vc_runner --crypto`
self-test itself, whose real output is the transcript above (8 pass, 0
fail). That self-test derives a keypair, signs the credential dataset,
verifies it, runs each negative case, and confirms the
`DataIntegrityProof` block serializes with its `proofValue`.

## CSVW: CSV on the Web, converted live

CSVW turns an ordinary CSV file plus a JSON metadata document into
RDF. The metadata document (`tableSchema.columns`) names each column,
its datatype, and how to build a subject IRI per row; `csv2rdf`
combines the two into triples. Below is the W3C CSVW spec's own
canonical example — a small municipal tree-maintenance table — run
live through `Factoidal.csvwToRdf(csvText, metadataJson, options)`
(`npm/factoidal/browser.js`'s raw CSVW export):

```csv
GID,On Street,Species,Trim Cycle,Inventory Date
1,ADDISON AV,Celtis australis,Large Tree Routine Prune,10/18/2010
2,EMERSON ST,Liquidambar styraciflua,Large Tree Routine Prune,6/2/2010
```

```json
{
  "@context": ["http://www.w3.org/ns/csvw", {"@language": "en"}],
  "url": "tree-ops.csv",
  "tableSchema": {
    "columns": [
      {"name": "GID", "titles": ["GID"], "datatype": "string", "required": true},
      {"name": "on_street", "titles": "On Street", "datatype": "string"},
      {"name": "species", "titles": "Species", "datatype": "string"},
      {"name": "trim_cycle", "titles": "Trim Cycle", "datatype": "string"},
      {"name": "inventory_date", "titles": "Inventory Date",
       "datatype": {"base": "date", "format": "M/d/yyyy"}}
    ],
    "primaryKey": "GID",
    "aboutUrl": "#gid-{GID}"
  }
}
```

**Standard mode** — the default — emits the row data plus CSVW's own
provenance triples (`csvw:TableGroup`/`csvw:Table`/`csvw:Row`,
recording which row each subject came from):

```observable-js
const csvText = `GID,On Street,Species,Trim Cycle,Inventory Date
1,ADDISON AV,Celtis australis,Large Tree Routine Prune,10/18/2010
2,EMERSON ST,Liquidambar styraciflua,Large Tree Routine Prune,6/2/2010
`;

const metadataJson = JSON.stringify({
  "@context": ["http://www.w3.org/ns/csvw", { "@language": "en" }],
  "url": "tree-ops.csv",
  "tableSchema": {
    "columns": [
      { "name": "GID", "titles": ["GID"], "datatype": "string", "required": true },
      { "name": "on_street", "titles": "On Street", "datatype": "string" },
      { "name": "species", "titles": "Species", "datatype": "string" },
      { "name": "trim_cycle", "titles": "Trim Cycle", "datatype": "string" },
      { "name": "inventory_date", "titles": "Inventory Date",
        "datatype": { "base": "date", "format": "M/d/yyyy" } }
    ],
    "primaryKey": "GID",
    "aboutUrl": "#gid-{GID}"
  }
});

try {
  const result = await Factoidal.csvwToRdf(csvText, metadataJson, { base: "http://example.org/" });
  const lines = result.nquads.trim().split("\n");
  return {
    available: true,
    totalQuads: lines.length,
    dataQuads: lines.filter((l) => l.includes("#GID") || l.includes("#on_street") ||
      l.includes("#species") || l.includes("#trim_cycle") || l.includes("#inventory_date")).length,
    firstRow: lines.filter((l) => l.includes("gid-1")),
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

24 quads total: 10 data triples (5 columns × 2 rows) plus 14
provenance triples describing the table and its rows. **Minimal
mode** drops the provenance layer and emits only the row data:

```observable-js
const csvText = `GID,On Street,Species,Trim Cycle,Inventory Date
1,ADDISON AV,Celtis australis,Large Tree Routine Prune,10/18/2010
2,EMERSON ST,Liquidambar styraciflua,Large Tree Routine Prune,6/2/2010
`;

const metadataJson = JSON.stringify({
  "@context": ["http://www.w3.org/ns/csvw", { "@language": "en" }],
  "url": "tree-ops.csv",
  "tableSchema": {
    "columns": [
      { "name": "GID", "titles": ["GID"], "datatype": "string", "required": true },
      { "name": "on_street", "titles": "On Street", "datatype": "string" },
      { "name": "species", "titles": "Species", "datatype": "string" },
      { "name": "trim_cycle", "titles": "Trim Cycle", "datatype": "string" },
      { "name": "inventory_date", "titles": "Inventory Date",
        "datatype": { "base": "date", "format": "M/d/yyyy" } }
    ],
    "primaryKey": "GID",
    "aboutUrl": "#gid-{GID}"
  }
});

try {
  const result = await Factoidal.csvwToRdf(csvText, metadataJson, { base: "http://example.org/", mode: "minimal" });
  const lines = result.nquads.trim().split("\n");
  return { available: true, totalQuads: lines.length, lines };
} catch (err) {
  return { available: false, note: err.message };
}
```

10 quads — exactly the row data, no `csvw:Row`/`csvw:Table` bookkeeping.
Both modes are real conversion output from the same F\*-extracted
`CSVW.Conversion.fst`, not two different tools.

### How far csv2rdf goes today

This example converts cleanly, but it's a simple table — no list-valued
cells, no multi-table joins. Measured against the full vendored W3C
CSVW test suite (`manifest-rdf.jsonld`, 270 entries, compared via
RDFC-1.0 canonicalization the same way this project's other W3C
runners compare): **19 pass (of 270)**. The fail buckets are named,
not hidden behind one number:

- **58 `NegativeRdfTest`** — fixtures that should be *rejected*; there
  is no CSVW validation layer yet (a later stage).
- **~105 format-facet fixtures** — the `datatype.format` facet (like
  this post's own `M/d/yyyy` date format, which happens to work) isn't
  implemented broadly enough to cover the suite's harder cases (a
  later stage).
- **13 separator/list-valued-cell fixtures** — CSVW's `separator`
  facet (one cell, multiple values) isn't decoded yet.
- **The remainder** span multi-level `aboutUrl`/`propertyUrl`/
  `valueUrl` inheritance the suite's harder fixtures stress beyond this
  pass's one-level approximation, plus assorted per-fixture edge cases.

Metadata decoding — parsing a CSVW metadata document at all, separate
from doing the conversion — is much further along: **286 of 293**
vendored metadata documents decode to a valid table or table group (a
further 1 decodes to a valid-but-empty table group, itself not a
decoder failure; the remaining fixtures are either deliberately
malformed negative tests the decoder correctly rejects, or schemas
referenced by external URL, out of scope for an offline decoder). Both
figures are measured by `bin/csvw-runner`, not estimated — see
[the test-results dashboard]({{ '/test-results/' | url }}).

## What's next

This is the last post in the current wave of the series — the [hub
index](../) lists everything published so far, and the series plan
names what's still ahead: SPARQL Update and the HTTP protocol, JSON-LD,
RML, the functional dataset API, and the performance story.

Every live cell above is pinned in
[`tests/hub/post13_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post13_test.mjs),
executed against the real npm-entry ABI the same way the in-browser
`Factoidal` binding is.
