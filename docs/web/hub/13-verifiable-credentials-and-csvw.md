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
goes, and to draw the line between the pipeline steps that run live in
your browser and those this page still demonstrates natively. (The
signature primitives themselves now run everywhere -- browser and Node
included -- via HACL*'s WebAssembly build; the npm `vc*` functions
expose them.)

## Verifiable Credentials: structural validation

A Verifiable Credential is a JSON(-LD) document — an issuer's claim
about a subject, structured so it can later be cryptographically
signed and checked. `VC.Credential.fst` checks the **structural**
rules the VC Data Model 2.0 spec lays out: `@context` presence,
`type` membership, `credentialSubject` non-emptiness, issuer/
credentialStatus/credentialSchema/termsOfUse/evidence/refreshService/
proof inner shapes, `validFrom`/`validUntil` well-formedness and
ordering, holder shape, and closed language-map validation on names
and descriptions. `VC.Context.fst` adds an offline JSON-LD `type`-value
resolution pass over the document's own `@context` array — catching a
protected-term redefinition, a type term mapped to a non-URL, and an
unmapped type term whose `@vocab` fallback was nullified — reading the
vendored W3C VCDM v2 base context so no network fetch is needed.

Measured against the vendored W3C `vc-data-model-2.0-test-suite`
fixtures: **113 pass, 1 fail, 6 skip (of 120)** — see
[the test-results dashboard]({{ '/test-results/' | url }}) for the
current run. The 1 fail is diagnosed, not swept under a skip: it is a
suite artifact — the fixture pair in question has one file whose
`validFrom`/`validUntil` fields are literal placeholder strings
(`'PAST DATE'`/`'FUTURE DATE'`) that the upstream test suite's own
JavaScript substitutes at run time, so the two raw fixtures are
structurally identical and any offline check that catches the
`-fail` case would also wrongly fail its `-ok` sibling. 113 of 114
plain-verdict fixtures is the measured ceiling for an offline
checker with no live substitution step.

**The structural validator has no browser export.** `npm/factoidal`'s
browser entry (`browser.js`) exports no VC Data Model
structural-validation function — no `vcValidate` — so that particular
check runs in the native/Node runner, not live on this page. (The
eddsa-rdfc-2022 *crypto* primitives are a separate matter: they are now
exposed as the `vc*` functions on both the Node and browser entries —
see the Data Integrity section below.) Below is one of the vendored
test fixtures the validator checks, shown statically (not executed):

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
Step 1 is RDFC-1.0 canonicalization — `fn.canonicalize`, the same
typed wrapper [post 08](./08-canonical-graphs-rdfc10.md) introduced.
The unsecured credential — the exact RDF dataset the native
`vc_runner` signs further down, with a blank node `_:b0` so
canonicalization does real work rather than a no-op — is used by both
cells below, so it's declared once as a shared named cell:

```observable-js
credential = `<urn:credential:1> <https://www.w3.org/2018/credentials#issuer> <urn:issuer:acme> .
<urn:credential:1> <http://schema.org/credentialSubject> _:b0 .
_:b0 <http://schema.org/name> "Alice" .
`
```

```observable-js
const canonical = await fn.canonicalize(credential, { format: "nquads" });
return { canonical, lines: canonical.trim().split("\n").length };
```

The blank node `_:b0` comes out as `_:c14n0` — RDFC-1.0's canonical
label — so the same credential serialized with any other blank-node
name produces byte-identical output. Step 2 is SHA-256 of those
canonical bytes. This cell uses Web Crypto's `crypto.subtle.digest`,
the browser's own SHA-256, which computes bit-for-bit the same digest
the native pipeline gets from HACL\*:

```observable-js
async function sha256Hex(text) {
  const bytes = new TextEncoder().encode(text);
  const digest = await crypto.subtle.digest("SHA-256", bytes);
  return [...new Uint8Array(digest)].map((b) => b.toString(16).padStart(2, "0")).join("");
}

const canonical = await fn.canonicalize(credential, { format: "nquads" });
const sha256 = await sha256Hex(canonical);
return { sha256, hashLength: sha256.length };
```

That 32-byte digest (64 hex characters) is the input the signature
covers. Everything up to this line runs in the browser; the step that
needs a secret key — Ed25519 sign, and its verify — does not.

### Steps 3–5: the real roundtrip

The transcript below is `./bin/linux-x86_64/vc_runner --crypto`, run
against the vendored HACL\* **C** build, verbatim. The same
F\*-extracted eddsa-rdfc-2022 pipeline now also runs *off*-native — in
Node and the browser — over HACL\*'s own official **WebAssembly** build,
exposed as the `vc*` functions on `npm/factoidal`
([#286](https://github.com/danbri/factoidal/issues/286) landed). It is
not wired as a live cell on this page (the browser `vc*` path needs an
explicit HACL\* wasm init step this demo does not set up), so the
authoritative signed roundtrip here stays the native transcript:

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

This roundtrip is shown as the native transcript rather than a live
browser cell (the in-page cells don't wire the HACL\* wasm init the
`vc*` path needs); it is pinned instead by the `vc_runner --crypto`
self-test itself, whose real output is the transcript above (8 pass, 0
fail). That self-test derives a keypair, signs the credential dataset,
verifies it, runs each negative case, and confirms the
`DataIntegrityProof` block serializes with its `proofValue`.

## CSVW: CSV on the Web, converted live

CSVW turns an ordinary CSV file plus a JSON metadata document into
RDF. The metadata document (`tableSchema.columns`) names each column,
its datatype, and how to build a subject IRI per row; `csv2rdf`
combines the two into triples. Two features carry the weight and both
run live below: **datatype coercion** — a column's declared `datatype`
becomes the RDF literal's `^^` type — and **URI templates** — RFC 6570
templates in `aboutUrl`/`propertyUrl` turn a cell value into a subject
or predicate IRI. Below is a small municipal-facilities table run
live through `Factoidal.csvwToRdf(csvText, metadataJson, options)`
(`npm/factoidal/browser.js`'s raw CSVW export):

{% raw %}

```csv
code,name,latitude,longitude,population
BRS,Bristol City Hall,51.4545,-2.5879,459300
BTH,Bath Guildhall,51.3811,-2.359,94782
```

```json
{
  "@context": "http://www.w3.org/ns/csvw",
  "url": "sites.csv",
  "tableSchema": {
    "columns": [
      {"name": "code", "titles": "code", "datatype": "string", "suppressOutput": true},
      {"name": "name", "titles": "name", "datatype": "string", "propertyUrl": "http://schema.org/name"},
      {"name": "latitude", "titles": "latitude", "datatype": "number", "propertyUrl": "http://schema.org/latitude"},
      {"name": "longitude", "titles": "longitude", "datatype": "number", "propertyUrl": "http://schema.org/longitude"},
      {"name": "population", "titles": "population", "datatype": "integer", "propertyUrl": "http://schema.org/population"}
    ],
    "aboutUrl": "http://example.org/sites{#code}",
    "primaryKey": "code"
  }
}
```

Three things the metadata asks for, each visible in the output:
`aboutUrl` is a fragment template `{#code}` (RFC 6570 fragment
expansion), so each row's subject is `…/sites#BRS`, `…/sites#BTH` —
the `code` column feeds the template but `suppressOutput` keeps it
from also emitting a plain triple. `datatype: "number"` is a CSVW
built-in that maps to `xsd:double`; `datatype: "integer"` maps to
`xsd:integer`. **Standard mode** — the default — emits the row data
plus CSVW's own provenance triples (`csvw:TableGroup`/`csvw:Table`/
`csvw:Row`, recording which row each subject came from). The CSV text
and its metadata document are shared by both modes below, so each is
declared once as a named cell:

```observable-js
csvText = `code,name,latitude,longitude,population
BRS,Bristol City Hall,51.4545,-2.5879,459300
BTH,Bath Guildhall,51.3811,-2.359,94782
`
```

```observable-js
metadataJson = JSON.stringify({
  "@context": "http://www.w3.org/ns/csvw",
  "url": "sites.csv",
  "tableSchema": {
    "columns": [
      { "name": "code", "titles": "code", "datatype": "string", "suppressOutput": true },
      { "name": "name", "titles": "name", "datatype": "string", "propertyUrl": "http://schema.org/name" },
      { "name": "latitude", "titles": "latitude", "datatype": "number", "propertyUrl": "http://schema.org/latitude" },
      { "name": "longitude", "titles": "longitude", "datatype": "number", "propertyUrl": "http://schema.org/longitude" },
      { "name": "population", "titles": "population", "datatype": "integer", "propertyUrl": "http://schema.org/population" }
    ],
    "aboutUrl": "http://example.org/sites{#code}",
    "primaryKey": "code"
  }
})
```

```observable-js
try {
  const result = await Factoidal.csvwToRdf(csvText, metadataJson, { base: "http://example.org/" });
  const lines = result.nquads.trim().split("\n");
  const data = lines.filter((l) => l.includes("schema.org"));
  return {
    available: true,
    totalQuads: lines.length,
    dataQuads: data.length,
    provenanceQuads: lines.filter((l) => l.includes("ns/csvw#")).length,
    sampleTypedTriples: data.filter((l) => l.includes("#BRS")),
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

22 quads total: 8 data triples (4 emitted columns × 2 rows — `code` is
suppressed) plus 14 provenance triples describing the table and its
rows. The `sampleTypedTriples` for the first row show the coercion at
work: `<…/sites#BRS> <http://schema.org/latitude> "51.4545"^^…double`,
`…population> "459300"^^…integer`. **Minimal mode** drops the
provenance layer and emits only the typed row data:

```observable-js
try {
  const result = await Factoidal.csvwToRdf(csvText, metadataJson, { base: "http://example.org/", mode: "minimal" });
  const lines = result.nquads.trim().split("\n");
  return {
    available: true,
    totalQuads: lines.length,
    hasDoubleTyping: lines.some((l) => l.includes("XMLSchema#double")),
    hasIntegerTyping: lines.some((l) => l.includes("XMLSchema#integer")),
    templatedSubjects: [...new Set(lines.map((l) => l.split(" ")[0]))],
    lines,
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

{% endraw %}

8 quads — exactly the typed row data, no `csvw:Row`/`csvw:Table`
bookkeeping; `templatedSubjects` is the two fragment-template IRIs
`<…/sites#BRS>` and `<…/sites#BTH>`. Both modes are real conversion
output from the same F\*-extracted `CSVW.Conversion.fst`, not two
different tools.

### How far csv2rdf goes today

This example converts cleanly, and most of the vendored W3C CSVW test
suite (`manifest-rdf.jsonld`, compared via RDFC-1.0 canonicalization
the same way this project's other W3C runners compare) now converts
with it — the datatype layer covers the built-in datatype aliases
(`number`→`xsd:double`, `binary`→`xsd:base64Binary`,
`datetime`→`xsd:dateTime`, `any`→`xsd:anyAtomicType`) with an
invalid-lexical-form fallback to a plain string, the UAX-35 `format`
facets (custom date/time patterns like `M/d/yyyy`, number patterns
like `#,##0.##` with groupChar/decimalChar/percent/per-mille, `Y|N`
booleans, duration lexical checking) via the F\*-verified
`CSVW.Formats` engine, length/value constraints, the
`separator`/list-valued-cell facet, RFC 6570 fragment URI templates,
and common-property emission. For the live score see
[the test-results dashboard]({{ '/test-results/' | url }}). The fail
buckets that remain are named, not hidden behind one number:

- **Metadata discovery** — fixtures that locate their metadata via
  Link headers, directory metadata, or `/.well-known/csvm`
  (protocol-level discovery, parked).
- **Metadata normalization warnings** — inconsistent array/object
  values, properties on the wrong description level, `@base`/`@type`
  edge cases in the `@context`.
- **Schema compatibility + validation** — `rowTitles`, title-language
  intersection checks, required/null interaction, foreign-key
  NegativeRdf fixtures, inherited-property propagation combinatorics,
  and the regex-valued duration `format` facet.

Metadata decoding — parsing a CSVW metadata document at all, separate
from doing the conversion — is further along: **286 of 293** vendored
metadata documents decode to a valid table or table group (a further 1
decodes to a valid-but-empty table group, itself not a decoder
failure; the remaining fixtures are either deliberately malformed
negative tests the decoder correctly rejects, or schemas referenced by
external URL, out of scope for an offline decoder). Both figures are
measured by `bin/csvw-runner`, not estimated — see
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
