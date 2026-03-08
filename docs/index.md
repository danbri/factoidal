---
title: Factoidal
layout: base.njk
---

# Factoidal

A formally verified RDF/SPARQL implementation. The **F\* specifications are the product**. Executable code is obtained by extraction, not hand-written.

## W3C SPARQL 1.1 Conformance

<p class="score">198 / 426 tests passing (46.5%)</p>

First conformance run: 2026-03-08. Full results against the
[W3C rdf-tests](https://github.com/w3c/rdf-tests) SPARQL 1.1 suites.

| Category | Result |
|----------|--------|
| Pass | 198 |
| Fail | 209 |
| Skip (UPDATE/protocol) | 205 |
| Unsupported format | 19 |

### Strongest suites

| Suite | Pass | Total | Rate |
|-------|------|-------|------|
| syntax-query | 75 | 94 | 80% |
| functions | 52 | 75 | 69% |
| bind | 7 | 10 | 70% |
| project-expression | 6 | 7 | 86% |
| grouping | 4 | 6 | 67% |

## Architecture

```
F* formal spec  (the product)
    |
    v
fstar.exe --codegen OCaml  (extraction)
    |
    v
OCaml test runner  (unverified I/O glue)
    |-- reads W3C manifest .ttl files
    |-- parses .rq / .srx / .ttl
    |-- calls extracted evaluator
    |-- compares actual vs expected
    v
W3C conformance results
```

## Reports

- [W3C SPARQL 1.1 Test Report (2026-03-08)]({{ '/w3c-sparql11-test-report-2026-03-08/' | url }})
- [Work Log]({{ '/worklog/' | url }})

## Source

- [github.com/danbri/factoidal](https://github.com/danbri/factoidal)
- [F\* specifications](https://github.com/danbri/factoidal/tree/main/formal/fstar) — RDF.Graph.Executable.fst (610 lines), SPARQL11.Algebra.fst (2760 lines)
