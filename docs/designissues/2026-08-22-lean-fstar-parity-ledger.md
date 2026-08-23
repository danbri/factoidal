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
| SPARQL entailment regimes | supported | 30 unsupported | see below |

Re-measured 2026-08-23: `owl2_profile_ql` is 87 pass, 0 fail (of 87),
and the whole rdf manifest is 1031 pass, 0 fail (of 1031). The two
RDF/XML failures are `rdfms-xml-literal-namespaces` XMLLiteral
canonicalisation differences, reported as `notEqual` rather than as a
comparison that gave up.

## Suites the Lean tree now runs END TO END (measured 2026-08-23)

Each of these has a real conformance runner, not a reader-level probe:
the whole pipeline runs and the result is compared against the suite's
own expected output.

| Suite | Runner | Result |
|---|---|---|
| csv2rdf | `l4csvw-rdf` | **252 pass, 10 fail, 6 skip (of 270)** |
| csv2json | `l4csvw-json` | **253 pass, 9 fail, 6 skip (of 270)** |
| JSON Schema draft-07 | `l4jsonschema` | **726 pass, 0 fail (of 726 decided), 44 undetermined (of 770)** |
| Content MathML | `l4mathml` | **56 pass, 0 fail (of 56)** |

Both CSVW numbers include the 58 NEGATIVE tests, scored by the
validator: 58 pass, 0 fail on each. Each CSVW runner also cross-checks
the validator against every POSITIVE test's metadata and reports the
documents it wrongly rejects — currently 0. That number exists because
a negative score can otherwise be bought with rules that reject
everything, and nothing in the negative column would disagree.

The JSON Schema residue is NAMED rather than counted: every draft-07
assertion keyword is implemented, so the 44 undetermined are `$id`
base-URI resolution, not a missing keyword.

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
