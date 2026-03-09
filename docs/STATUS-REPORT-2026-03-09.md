# Factoidal Status Report — 2026-03-09

## Live Test Results (freshly run)

### SPARQL 1.1: 291 pass, 114 fail, 205 skip, 21 unsupported

| Suite | Pass | Fail | Skip | Unsup | Notes |
|-------|------|------|------|-------|-------|
| syntax-query | 94 | 0 | 0 | 0 | **PERFECT** |
| bind | 10 | 0 | 0 | 0 | **PERFECT** |
| bindings | 10 | 0 | 0 | 1 | Near-perfect (1 Turtle result unsupported) |
| grouping | 6 | 0 | 0 | 0 | **PERFECT** |
| syntax-fed | 3 | 0 | 0 | 0 | **PERFECT** |
| construct | 2 | 0 | 0 | 5 | 5 need Turtle result format |
| delete-insert | 8 | 0 | 9 | 0 | 9 skipped (UPDATE) |
| property-path | 31 | 2 | 0 | 0 | 94% pass |
| negation | 11 | 1 | 0 | 0 | 92% pass |
| exists | 5 | 1 | 0 | 0 | 83% pass |
| subquery | 9 | 3 | 0 | 2 | 75% pass |
| aggregates | 30 | 14 | 0 | 3 | 64% — numeric type issues |
| functions | 42 | 33 | 0 | 0 | 56% — many value-representation failures |
| entailment | 27 | 43 | 0 | 0 | 39% — OWL/DL + RDFS inference gaps |
| cast | 0 | 6 | 0 | 0 | 0% — type casting broken |
| project-expression | 3 | 4 | 0 | 0 | 43% |
| service | 0 | 7 | 0 | 0 | 0% — needs federation |
| protocol | 0 | 0 | 34 | 0 | Skipped (HTTP protocol) |
| *UPDATE suites* | 0 | 0 | 205 | 0 | Skipped (not in F* spec) |
| csv-tsv-res | 0 | 0 | 0 | 6 | Not yet wired |
| json-res | 0 | 0 | 0 | 4 | Not yet wired |

### RDF 1.1: 672 pass, 359 fail, 0 skip, 0 unsupported

| Suite | Pass | Fail | Total | Rate |
|-------|------|------|-------|------|
| rdf-mt | 33 | 6 | 39 | **85%** |
| rdf-n-triples | 41 | 29 | 70 | 59% |
| rdf-n-quads | 53 | 34 | 87 | 61% |
| rdf-turtle | 217 | 96 | 313 | 69% |
| rdf-trig | 237 | 119 | 356 | 67% |
| rdf-xml | 91 | 75 | 166 | 55% |

### Combined: 963 pass, 473 fail

---

## What Works Well (Proven Strengths)

### F* Core (fully verified, 0 admits in RDF graph spec)
- **RDF graph types and operations** — 1,052 lines, fully proven
- **SPARQL 1.1 algebra and evaluator** — 3,065 lines (2 admits, 11 accounted assume vals)
- **RDFS closure** — subPropertyOf, domain, range, subClassOf, container membership
- **Datatype value equivalence** — xsd:integer and xsd:decimal normalization
- **Language tag case-insensitivity** — lang_tag_eq in F*
- **Plain literal / xsd:string equivalence** — literal_value_eq in F*

### F* Parsers (8 complete, all extracted, no assume vals)
- Parser.Combinators (352 lines) — combinator foundation
- Parser.NTriples (544 lines)
- Parser.Turtle (1,232 lines)
- Parser.NQuads (298 lines)
- Parser.TriG (382 lines)
- Parser.XML (592 lines) — non-validating
- Parser.RDFXML (795 lines)
- Parser.SRX (275 lines) — SPARQL Results XML
- Parser.CSVResults (646 lines)
- **Total: 5,116 lines of verified parser code**

### SPARQL Query Understanding
- Syntax parsing: 94/94 (100%)
- Basic graph patterns, OPTIONAL, UNION, FILTER, BIND, VALUES
- Subqueries, EXISTS/NOT EXISTS, property paths
- Aggregates (COUNT, GROUP_CONCAT, MIN, MAX, SAMPLE — partial)
- CONSTRUCT (2 of 7)

---

## What's Broken / Neglected

### 1. SPARQL Value Representation (33 failures in `functions`)

The row counts match but values differ. Root cause: F* evaluator doesn't
properly handle output types for many built-in functions:

- **CEIL/FLOOR/ROUND** — numeric type promotion issues
- **SUBSTR, UCASE, LCASE** — language tag / datatype propagation
- **STRBEFORE/STRAFTER** — datatype preservation
- **ENCODE_FOR_URI** — likely encoding differences
- **SHA1/SHA256/SHA384/SHA512** — hash function stubs produce wrong output
- **SECONDS/TIMEZONE** — datetime component extraction
- **IRI()/URI()** — base IRI resolution
- **IF/COALESCE** — type handling
- **REPLACE** — regex replacement differences
- **plus-1-corrected** — numeric addition type rules
- **CONCAT** — language tag / datatype merging

### 2. SPARQL Entailment (43 failures)

Three distinct categories:
- **OWL-DL entailment (23 failures)**: `sparqldl-*`, `paper-sparqldl-*` — need
  OWL class expression evaluation (someValuesFrom, minCardinality, etc.). These
  require an OWL reasoner, which is out of scope for now.
- **Simple entailment (8 failures)**: `simple 1-8` — blank node as existential
  variable matching. The F* graph doesn't treat blank nodes as wildcards during
  entailment checking.
- **RDFS entailment (12 failures)**: `RDFS inference test *` — the SPARQL
  entailment regime expects RDFS closure to be applied to query data, but the
  evaluator doesn't call `rdfs_closure` during SPARQL query evaluation.

### 3. SPARQL Cast Suite (6/6 failing)

All `xsd:boolean/integer/float/double/decimal/string` cast tests fail. The F*
evaluator lacks proper CAST/datatype conversion functions. Row counts match (31
each) so the query logic works — just the conversion results are wrong.

### 4. SPARQL Aggregates (14 failures)

- **SUM/AVG** — numeric type promotion during aggregation
- **GROUP BY with functions** — GROUP BY on computed expressions
- **DISTINCT aggregates** — some DISTINCT variants broken
- **GROUP_CONCAT** — separator handling edge case

### 5. RDF Parser Negative Tests (~40% of parser failures)

The F*-extracted parsers are too lenient — they accept malformed input that
should be rejected. This accounts for most parser suite failures:
- N-Triples: 29 failures (many "should reject but parsed OK")
- N-Quads: 34 failures (similar pattern)
- Turtle: 96 failures (mix of negative tests + eval mismatches)
- TriG: 119 failures (similar to Turtle)
- RDF/XML: 75 failures (mix)

### 6. RDF Model Theory — 6 Remaining Failures

| Test | Issue |
|------|-------|
| datatypes-semantic-equivalence-within-type-1 | Value-space entailment for integers not wired into simple_entails |
| datatypes-semantic-equivalence-within-type-2 | Same — decimal equivalence |
| datatypes-semantic-equivalence-between-datatypes | Cross-type numeric equivalence (integer/decimal) |
| datatypes-test009 | False positive — should NOT entail but does |
| tex-01-language-tag-case-1 | Language tag normalization not applied during entailment |
| tex-01-language-tag-case-2 | Same |

Root cause: `simple_entails` in w3c_runner.ml uses syntactic triple matching.
The F* spec has `datatype_value_eq` and `lang_tag_eq` but these aren't used
in the entailment check.

### 7. Not Yet Implemented

| Feature | Impact |
|---------|--------|
| SPARQL UPDATE | 205 tests skipped (add, delete, clear, copy, drop, move) |
| SPARQL Federation (SERVICE) | 7 failures |
| JSON result format | 4 unsupported |
| CSV/TSV result format comparison | 6 unsupported |
| Turtle result format | ~10 unsupported (CONSTRUCT results) |
| OWL-DL reasoning | 23 entailment failures |
| SPARQL Protocol | 34 skipped (HTTP) |
| SPARQL11.Parser.fst | 16 assume vals remaining |

---

## Architecture Summary

```
F* Specifications (9,801 lines total)
├── RDF.Graph.Executable.fst    1,052 lines  0 admit  0 assume val
├── SPARQL11.Algebra.fst        3,065 lines  2 admit  11 assume val
├── SPARQL11.Parser.fst           568 lines  0 admit  16 assume val (in dev)
├── Parser.Combinators.fst        352 lines  proven
├── Parser.NTriples.fst           544 lines  proven
├── Parser.Turtle.fst           1,232 lines  proven
├── Parser.NQuads.fst             298 lines  proven
├── Parser.TriG.fst               382 lines  proven
├── Parser.XML.fst                592 lines  proven
├── Parser.RDFXML.fst             795 lines  proven
├── Parser.SRX.fst                275 lines  proven
└── Parser.CSVResults.fst         646 lines  proven
```

---

## Priority Actions (by impact)

### Quick wins (could fix 50+ tests)
1. **Wire `datatype_value_eq` and `lang_tag_eq` into entailment checking** — fixes 4-6 rdf-mt tests
2. **Fix parser strictness** — reject malformed input in negative tests — fixes ~50 parser tests
3. **Fix SPARQL function return types** — many functions return correct values with wrong datatypes

### Medium effort (could fix 30+ tests)
4. **Implement simple entailment** (blank node matching) — fixes 8 entailment tests
5. **Wire RDFS closure into SPARQL entailment regime** — fixes 12 RDFS entailment tests
6. **Fix numeric type promotion in aggregates** — fixes ~10 aggregate tests
7. **Fix SHA hash stubs** — fixes 8 hash function tests

### Large effort
8. **Implement SPARQL CAST functions** — fixes 6 cast tests
9. **Implement SPARQL UPDATE in F*** — would address 205 skipped tests
10. **Complete SPARQL11.Parser.fst** — replace hand-written SPARQL parser
