---
title: Work Log
layout: base.njk
---

# Factoidal Work Log

Development log for the formally verified RDF/SPARQL implementation.
Entries are datetime-stamped (UTC).

---

## 2026-03-08T16:00Z — RDF 1.1 W3C Tests Added

Added W3C RDF 1.1 conformance tests (N-Triples + Turtle) to the test runner.

**New CLI options:**
- `./w3c_runner --rdf` — run all RDF 1.1 suites
- `./w3c_runner --rdf rdf-turtle` — run specific RDF suite
- `./w3c_runner --all` — run both SPARQL 1.1 and RDF 1.1 suites
- `./w3c_runner --list` — now lists both SPARQL and RDF suites

**RDF 1.1 results: 338 pass, 45 fail (88.3%)**

| Suite | Pass | Fail | Rate |
|-------|------|------|------|
| rdf-n-triples | 61 | 9 | 87.1% |
| rdf-turtle | 277 | 36 | 88.5% |

Test types supported:
- `TestNTriplesPositiveSyntax` / `TestNTriplesNegativeSyntax`
- `TestTurtlePositiveSyntax` / `TestTurtleNegativeSyntax`
- `TestTurtleEval` (parse Turtle, compare triples to expected N-Triples)
- `TestTurtleNegativeEval`

Failure categories:
- 22× parser too permissive (accepts invalid syntax — bad numeric escapes, bad
  URIs, bad lang tags, bad struct)
- 8× Unicode PN_CHARS_BASE handling (extended Unicode in prefix/local names)
- 4× IRI resolution edge cases (RFC 3986)
- 4× negative eval tests (parser doesn't detect semantic errors)
- 2× parser too strict (turtle-syntax-prefix-02, turtle-syntax-number-11)

SPARQL results unchanged at 198 pass, 209 fail.

---

## 2026-03-08T14:00Z — Phase 1 Complete: W3C Test Infrastructure

**Milestone:** First real W3C SPARQL 1.1 conformance run against F\*-extracted code.

Built the complete OCaml test infrastructure:
- N-Triples, Turtle, and SPARQL Results XML parsers
- Full SPARQL 1.1 query parser (60+ built-in functions, property paths, subqueries)
- W3C manifest reader and CLI test runner

**Results: 198 pass, 209 fail, 205 skip, 19 unsupported** out of 631 tests.
46.5% pass rate on evaluable tests. The 205 skips are UPDATE/protocol tests
(out of scope for a query evaluator).

Strongest areas: syntax parsing (75/94), string/numeric functions (52/75),
BIND expressions (7/10). Weakest: property paths (3/33), aggregates (9/47),
EXISTS (1/6).

The failures map cleanly to known gaps in the F\* spec — this is exactly what
the test infrastructure was built to reveal.

**Full analysis:** [W3C SPARQL 1.1 Test Report](w3c-sparql11-test-report-2026-03-08.md)

**Next steps (Phase 2):**
1. Wire hash function stubs (10 easy wins)
2. Wire eval_exists_fwd (13 more passes)
3. Fix GROUP BY / aggregation in F\* spec (30 failures)
4. Implement property path evaluation in F\* (28 failures)
