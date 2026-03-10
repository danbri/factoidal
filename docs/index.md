---
title: Factoidal
layout: base.njk
---

# Factoidal

A formally verified RDF/SPARQL implementation. The **F\* specifications are the product**. Executable code is obtained by extraction, not hand-written.

## W3C Conformance (as of 2026-03-10)

### SPARQL 1.1

<p class="score">303 / 408 applicable tests passing (74%)</p>

Tested against the [W3C rdf-tests](https://github.com/w3c/rdf-tests) SPARQL 1.1 suites (631 total; 205 UPDATE/protocol skipped, 18 unsupported format).

| Suite | Pass/Total | | Suite | Pass/Total |
|-------|-----------|---|-------|-----------|
| syntax-query | 94/94 | | aggregates | 38/47 |
| functions | 71/75 | | property-path | 31/33 |
| bind | 9/10 | | negation | 11/12 |
| project-expression | 7/7 | | subquery | 9/14 |
| grouping | 6/6 | | entailment | 26/70 |

### RDF 1.1

<p class="score">644 / 1031 parser tests passing (62%)</p>

| Suite | Pass/Total | | Suite | Pass/Total |
|-------|-----------|---|-------|-----------|
| Turtle | 203/313 | | TriG | 223/356 |
| RDF/XML | 91/166 | | N-Quads | 53/87 |
| N-Triples | 41/70 | | rdf-mt | 33/39 |

## Architecture

```
F* formal spec  (the product)
    |
    v
fstar.exe --codegen OCaml  (extraction)
    |
    v
OCaml binaries  (thin I/O glue)
    |-- factoidal: SPARQL query + RDF parsing CLI
    |-- w3c_runner: W3C conformance test runner
    v
W3C SPARQL 1.1 + RDF 1.1 conformance results
```

## Reports

- [Detailed test results]({{ '/test-results/' | url }})
- [W3C SPARQL 1.1 Test Report (2026-03-08)]({{ '/w3c-sparql11-test-report-2026-03-08/' | url }})
- [Work Log]({{ '/worklog/' | url }})

## Source

- [github.com/danbri/factoidal](https://github.com/danbri/factoidal)
- [F\* specifications](https://github.com/danbri/factoidal/tree/master/formal/fstar) — RDF.Graph.Executable.fst (638 lines), SPARQL11.Algebra.fst (3658 lines)
