---
title: "Verifiable Credentials and CSVW"
description: "The two newest arrivals: honest VC Data Model structural validation with no crypto yet, and CSVW csv2rdf converting a real municipal-data fixture live in the browser."
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
Credentials** structural validation and **CSVW** (CSV on the Web)
csv2rdf conversion. Both are recent and both are honestly
mid-development — the point of this post is to say exactly how far
each one goes today, not further.

## Verifiable Credentials: structural validation, no crypto yet

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

**There is no cryptography here, deliberately.** VC Data Integrity
proofs (`eddsa-rdfc-2022` and similar) need real signature
verification, and this project's crypto-sourcing policy is explicit
about how that has to arrive: never hand-rolled, adopted from HACL\*
(the F\*/Low\*-verified library Mozilla ships inside NSS) in a fixed
order, gated on wasm compatibility — see
[`skills/crypto-policy/SKILL.md`](https://github.com/danbri/factoidal/blob/claude/main/skills/crypto-policy/SKILL.md)
for the full policy. Structural validation (this post) is everything
that can be checked *before* a signature enters the picture; signing
and verifying is a later, separate stage.

**VC has no browser cell in this post.** `npm/factoidal`'s browser
entry (`browser.js`) exports no VC function at all — no `vcValidate`,
nothing VC-shaped — so unlike every other post in this series there is
nothing to run live here. Below is one of the vendored test fixtures
this project's own validator checks, shown statically (not executed):

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
