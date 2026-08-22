# Lean 4 vs F\*: feature parity, measured

Owner question, 2026-08-22: "How close is our L4 version to working
feature parity with the F\* codebase?"

Everything below is MEASURED in this session unless the row says
otherwise. F\* numbers come from `docs/test-results/latest.json`; Lean
numbers come from building `l4w3c` and the probes and running them
against the same W3C manifests on disk.

## Headline

**The Lean tree is at or near parity on the RDF + SPARQL + JSON-LD
core, and absent on the periphery and the storage/serving layers.**
The single most useful number: on the full SPARQL 1.1 manifest the
Lean engine scores **601 pass, 0 fail, 30 unsupported (out of 631)**
against F\*'s 631 pass, 0 fail — and **all 30 unsupported are
entailment-regime tests** (OWL-Direct, OWL-RDF-Based, RIF), not core
SPARQL. Zero failures on either side.

## At parity (measured this session)

| Suite | F\* | Lean 4 |
|---|---|---|
| SPARQL 1.1, non-entailment-regime | 631 pass, 0 fail (of 631) | 601 pass, 0 fail (of 601 attempted) |
| rdf-turtle | in rdf 1030 of 1031 | 313 pass, 0 fail (of 313) |
| rdf-trig | in rdf | 356 pass, 0 fail (of 356) |
| rdf-n-triples | in rdf | 70 pass, 0 fail (of 70) |
| rdf-n-quads | in rdf | 87 pass, 0 fail (of 87) |
| rdf-mt (RDF semantics) | in rdf | 39 pass, 0 fail (of 39) |
| JSON-LD toRdf | 467 pass, 0 fail (of 467) | 467 pass, 0 fail (of 467) |
| SHACL core / SPARQL | 98 / 22 | 98 / 22 (from PORT_NOTES, not re-run here) |

## Close, with known gaps (measured)

| Area | F\* | Lean 4 | Gap |
|---|---|---|---|
| RDF/XML | in rdf suite | 130 pass, 2 fail (of 132, eval-isomorphic) | 2 tests |
| OWL 2 profile QL | 87 pass, 0 fail | 76 pass, 11 fail (of 87) | 11 tests |
| SPARQL entailment regimes | supported | 30 unsupported | see below |

## Absent from the Lean tree

Present in F\*, no Lean counterpart: ShEx (1,182 tests), RML (76+),
RIF Core (46 of 50), CSVW (270), GeoSPARQL (37), XSLT/XPath/MathML/
JSON Schema/Schematron, the XML conformance corpus (1,447 of 2,585),
the VC/DID stack beyond the Lean `VC/` modules, the COTTAS/HDT storage
layer, and the HTTP serving layer (`SPARQL.HTTP.*`, admin, static
files, backend info).

That last one matters for the new framing — a linked information
system with the Web at its heart. The Lean tree HAS `SPARQL/Protocol`,
`GraphStore` and `ServiceDescription` modules, so the protocol
SEMANTICS are ported; what is absent is the server that speaks them.

## The 30 unsupported, characterised

All are SPARQL queries under an entailment regime the Lean engine does
not yet answer: OWL-Direct (about 20, including the `paper-sparqldl-*`
and `simple 1..8` families and the qualified-cardinality parent/child
queries), OWL-RDF-Based (about 6), and RIF (4). None is a core SPARQL
feature.

This is the same target the Lean OWL tableau ladder is walking toward
(https://github.com/danbri/factoidal/issues/466): three rungs landed —
base clash calculus, ∃-witness, role box — with the ≤-rule witness
merge and qualified cardinality still to come. When the tableau can
decide these concept forms, the regime tests become answerable rather
than unsupported. **That is the shortest path from 601 to 631**, and
it is already in progress.

## Honest reading

- Parity on the CORE is real, not aspirational: identical pass counts,
  zero failures, on the same manifest files.
- Parity on BREADTH is not close. F\* carries roughly 9 spec families
  the Lean tree has never touched.
- The Lean tree is not a serving system: no storage backend, no HTTP
  server. It computes; it does not yet host.
- Performance is a separate axis and is measured separately: the Lean
  evaluator is quadratic on joins
  (`docs/designissues/2026-08-22-indexing-and-join-processing.md`).
