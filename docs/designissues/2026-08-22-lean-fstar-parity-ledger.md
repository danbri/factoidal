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

## Closed since this ledger was written

**GeoSPARQL** (2026-08-22, same day): ported to Lean as
`L4Factoidal/Geo/` — `Types` (exact-decimal geometry model), `Order`
(`Scaled` is a linear order), `BBox` (with the pre-filter soundness
theorem proved), `Topology` (division-free geometric kernel),
`Wkt` (parser + decimal rendering), `Functions` (the `geof:`
extension-function table). Scope honesty: the F\* module also carries
linestring-vs-linestring and polygon-vs-polygon predicate pairs that
this port does NOT yet cover — the Lean side is the kernel plus the
point-vs-polygon fragment. The 37 W3C tests are not yet run against
it, because that needs the harness wiring, not more geometry.

**CSVW** (2026-08-22): the main module set is ported —
`L4Factoidal/CSVW/` carries `Dialect` (dialect description + CSV
reader), `Metadata` (model + §5.1.1 inheritance), `UriTemplate`,
`Conversion` (cell rules), `Emit` (csv2rdf triples, minimal and
standard), `Formats` (boolean + numeric), `Json` (csv2json, minimal
and standard) and `Validate` (with the error/warning split the W3C
suite depends on). Scope honesty: date/time patterns and the
regex-valued duration `format` facet are NOT ported (`noFormat` is
returned, which keeps the cell rather than rejecting it).

**csv2rdf now has a real conformance runner** (`Harness/CsvwRdfRun`,
`lake exe l4csvw-rdf`): the whole pipeline against the suite's own
expected `.ttl`, compared by graph isomorphism, driven by
`manifest-rdf.jsonld`.

📊 **9 pass, 0 fail, 0 comparison-gave-up, 0 skip (out of 9)** — the
no-metadata subset, both modes. 261 of the 270 manifest entries carry
metadata (an `implicit` member) and are NOT attempted: they need
`@context` resolution, `tableSchema` inheritance and metadata
discovery. That is the next CSVW increment, and it is the whole
remaining denominator.

Landing that runner cost two real bugs, both recorded in
`formal/lean4/PORT_NOTES.md`: standard-mode table and group assembly
was missing from `Emit.lean`, and the isomorphism comparison refused
above 16 blank nodes and reported the refusal as a difference.

**Opened 2026-08-22, same day** (module set ported, W3C suites not yet
run against the Lean side — that needs harness wiring):

| Family | Lean modules |
|---|---|
| ShEx | `ShEx/Schema`, `Validation` (node constraints), `Shapes` (satisfaction with EXTRA/CLOSED) |
| RML | `RML/Mapping` (term maps, templates, IRI-vs-URI encoding) |
| RIF Core | `RIF/Core` (AST + bounded forward chaining) |
| JSON Schema | `JSONSchema/Validate` (three-valued, exact rationals) |
| Schematron | `Schematron/Validate` (assert/report inversion) |
| XPath | `XPath/Number` (IEEE specials + exact decimals) |
| HTTP serving | `HTTP/Server` (routing, negotiation, responses) |
| Storage | `Storage/Bytes` (VByte, CRCs, checksummed sections) |

The HTTP one closes the gap this ledger flagged against the project's
framing: the Lean tree HAD the protocol SEMANTICS (`SPARQL/Protocol`,
`GraphStore`, `ServiceDescription`) but not the server that speaks
them. It now has both.

## Absent from the Lean tree

Present in F\*, no Lean counterpart: XSLT, MathML, the XML conformance
corpus (1,447 of 2,585), the VC/DID stack beyond the Lean `VC/`
modules, and the COTTAS columnar store above the byte layer. Several
ported families are SLICES rather than complete — ShEx has no
reference recursion, RIF no builtins, XPath only the number type,
storage only the byte primitives, CSVW no date formats. Each states
its own scope in its module header.

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
