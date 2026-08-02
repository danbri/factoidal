# third_party/vocabularies — real published vocabularies, vendored for benchmarking

Four widely-deployed RDFS/OWL vocabularies, cached so that
[`tools/bench-closure.sh`](../../tools/bench-closure.sh) measures
entailment closure on real schemas without a network round trip.

Nothing here is hand-written or modified. Each file is the upstream
byte stream, recorded below with the URL it came from, the retrieval
date and its SHA-256. Provenance style follows
[`../qudt/PROVENANCE.md`](../qudt/PROVENANCE.md) and
[`../jsonld-context-cache/README.md`](../jsonld-context-cache/README.md).

## Why these files exist

Synthetic shapes give the scaling **exponent**; only real vocabularies
answer whether the engine is **usable**. The closure benchmark reports,
for each of these, input triples, output triples, expansion ratio, wall
time, CPU time, and whether the run completes at all inside a stated
cap. A cap trip is recorded as a result, not hidden.

## Files and retrieval

Retrieved 2026-07-31, all over HTTPS through the sandbox proxy.

| File | Retrieved from | SHA-256 | Bytes | Triples (`factoidal count`) |
|---|---|---|---|---|
| `skos.rdf` | `http://www.w3.org/2009/08/skos-reference/skos.rdf` (redirects to `https://www.w3.org/…`) | `e79633b8d0564816cee8a99f5c9acf9a0e6fc7257c7209acd684ecad53a89dd6` | 28,966 | 254 |
| `foaf.rdf` | `http://xmlns.com/foaf/spec/index.rdf` (redirects to `https://xmlns.com/…`) | `3d859b5d92a2c3d041545d014fa826f682ca06d056af8c7b31e32d930abf2bc5` | 44,209 | 635 |
| `dublin_core_terms.ttl` | `https://www.dublincore.org/specifications/dublin-core/dcmi-terms/dublin_core_terms.ttl` | `13df401072dd7015bf9d75162f3e41c8138075304b7b9cc1aa1e9c16db976797` | 47,834 | 700 |
| `schemaorg-30.0-current-https.ttl` | `https://schema.org/version/30.0/schemaorg-current-https.ttl` | `320938f0945d717fc317f822c707f10944e7a7a0097018665a3b95dcf475b39d` | 1,104,341 | 17,949 |

### Version pins

* **SKOS** — the namespace document for the 18 August 2009
  Recommendation. SKOS is a finished Recommendation; the URL is already
  a dated one and there is no later revision to drift to.
* **FOAF** — `xmlns.com/foaf/spec/index.rdf` is FOAF's own published
  specification RDF. FOAF has no versioned distribution URLs, so the
  SHA-256 above is the pin: if upstream edits the file, the hash moves
  and the change is visible in a diff of this table.
* **DCMI Metadata Terms** — the DCMI Turtle distribution. Same
  situation as FOAF: hash-pinned rather than URL-pinned.
* **schema.org** — pinned to release **30.0**. `…/version/latest/…` was
  fetched first and was byte-identical to `…/version/30.0/…` on
  2026-07-31 (same SHA-256), so no content was lost by pinning. Do not
  re-vendor from `latest`; bump the pin deliberately, as with QUDT.

## Licences

| File | Licence |
|---|---|
| `skos.rdf` | [W3C Software and Document Notice and License](https://www.w3.org/copyright/software-license-2023/) — W3C Recommendation material. |
| `foaf.rdf` | Creative Commons Attribution 1.0 (stated in the document itself: `<http://creativecommons.org/licenses/by/1.0/>`). |
| `dublin_core_terms.ttl` | Creative Commons Attribution 4.0, DCMI. |
| `schemaorg-30.0-current-https.ttl` | Creative Commons Attribution-ShareAlike 3.0 (schema.org's stated terms). |

## The large vocabulary: why QUDT and not the Gene Ontology

The closure benchmark's largest real input is
[`../qudt/QUDT-all-in-one-OWL.ttl`](../qudt/) — 130,404 triples,
already vendored for the QUDT programme, so it costs this benchmark
zero additional bytes.

The Gene Ontology was considered and **not** vendored. A HEAD request to
`http://purl.obolibrary.org/obo/go.owl` on 2026-07-31 reported
`content-length: 129,874,498` — 130 MB of RDF/XML. That is roughly ten
times the whole rest of `third_party/` for one benchmark row, on a
disk-constrained build host, and QUDT already supplies a real
six-figure-triple vocabulary. If a larger input is ever wanted, fetch GO
at run time rather than committing it.
