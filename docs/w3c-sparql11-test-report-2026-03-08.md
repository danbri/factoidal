---
title: W3C SPARQL 1.1 Test Report
layout: base.njk
---

# W3C SPARQL 1.1 Conformance Test Report

**Date:** 2026-03-08
**Runner:** `formal/fstar/ocaml-output/w3c_runner`
**Test data:** `tests/w3c/sparql/sparql11/` (W3C rdf-tests submodule)
**Evaluator:** F\*-extracted `eval_select_query` (SPARQL11.Algebra.fst → OCaml)

## Summary

| Metric | Count |
|--------|-------|
| **Pass** | 198 |
| **Fail** | 209 |
| **Skip** | 205 |
| **Unsupported** | 19 |
| **Total** | 631 |

**Pass rate (excluding skips):** 198 / 426 = **46.5%**

Skipped tests are primarily UPDATE operations (INSERT/DELETE/LOAD/CLEAR/DROP)
and protocol tests, which are out of scope for a query evaluator. The
unsupported category covers result formats we don't parse yet (.srj, .csv,
Turtle result sets).

## Per-Suite Results

| Suite | Pass | Fail | Skip | Unsup | Notes |
|-------|------|------|------|-------|-------|
| syntax-query | 75 | 19 | 0 | 0 | Parser handles most SPARQL 1.1 syntax |
| functions | 52 | 23 | 0 | 0 | Strong on string/numeric builtins |
| entailment | 24 | 46 | 0 | 0 | Simple entailment works; RDFS/OWL doesn't |
| aggregates | 9 | 35 | 0 | 3 | GROUP BY not collapsing rows |
| bind | 7 | 3 | 0 | 0 | Core BIND works |
| project-expression | 6 | 1 | 0 | 0 | Nearly complete |
| grouping | 4 | 2 | 0 | 0 | Basic grouping works |
| negation | 4 | 8 | 0 | 0 | Blocked on EXISTS wiring |
| property-path | 3 | 30 | 0 | 0 | Path eval is a stub |
| syntax-fed | 3 | 0 | 0 | 0 | Federation syntax parses |
| bindings | 2 | 8 | 0 | 1 | VALUES join not applied |
| exists | 1 | 5 | 0 | 0 | Blocked on EXISTS wiring |
| delete-insert | 8 | 0 | 9 | 0 | Passing tests are syntax-only |
| construct | 0 | 4 | 0 | 3 | CONSTRUCT not fully wired |
| subquery | 0 | 12 | 0 | 2 | Turtle parse errors + eval issues |
| cast | 0 | 6 | 0 | 0 | Parser doesn't handle cast syntax |
| service | 0 | 7 | 0 | 0 | No federation endpoint |
| csv-tsv-res | 0 | 0 | 0 | 6 | Result format not supported |
| json-res | 0 | 0 | 0 | 4 | Result format not supported |

(UPDATE suites — add, basic-update, clear, copy, delete, delete-data,
delete-where, drop, http-rdf-update, move, protocol, syntax-update-\*,
update-silent — all skipped: 205 tests total.)

## Failure Analysis

The 209 failures break down into clear categories. Most trace back to a small
number of root causes in the F\* spec or the OCaml test infrastructure.

### 1. Aggregate / GROUP BY (30 failures)

The F\*-extracted evaluator does not collapse rows by GROUP BY before applying
aggregate functions. Queries return the raw solution sequence instead of grouped
results.

**Impact:** All COUNT/SUM/AVG/MIN/MAX tests with GROUP BY fail. GROUP_CONCAT
works in some cases because it already operates on the full sequence.

**Root cause:** `eval_group_aggregate` in SPARQL11.Algebra.fst — needs the
grouping pass that partitions solutions before aggregation.

### 2. SPARQL Parser Gaps (30 failures)

The hand-written SPARQL parser doesn't handle:
- **Datatype constructor calls** (6 tests): `xsd:integer("1")` syntax
- **Complex HAVING** expressions
- **Some built-in function forms** (RAND, IF error propagation, COALESCE edge
  cases)
- **Collection syntax in property paths**

### 3. Property Paths (28 failures)

`eval_property_path` in the F\* spec is a stub returning `[]` for most path
types (sequence, `+`, `*`, negated property set). Only simple predicate paths
evaluate correctly.

**Root cause:** The F\* spec acknowledges this — property path evaluation
requires transitive closure, which needs careful specification.

### 4. Negative Syntax (24 failures)

The parser accepts 24 queries that should be rejected. These are validation
gaps, not evaluation bugs:
- Invalid aggregate placement (COUNT 8–12)
- BIND variable scoping violations
- Invalid prefix names
- Invalid GROUP BY forms

### 5. EXISTS / NOT EXISTS (13 failures)

`eval_exists_fwd` is declared as `assume val` in F\* but not wired to the real
`eval_exists` function in `ocaml-patches.sh`. All EXISTS/NOT EXISTS filters
evaluate to false, returning empty results.

**Fix:** Wire the `assume val` to the concrete implementation — a pure OCaml
patch, no F\* changes needed.

### 6. Entailment / Inference (30 failures)

Tests requiring RDFS subclass/subproperty reasoning, OWL DL entailment, or RIF
rules. The evaluator implements simple entailment only. **These are expected
failures** — adding inference is a Phase 3+ concern.

### 7. Hash Functions (10 failures)

MD5, SHA-1, SHA-256, SHA-384, SHA-512 are `assume val` in F\* with no OCaml
stubs. Each has 2 tests (plain + Unicode).

**Fix:** Add OCaml `Digest` stubs in `ocaml-patches.sh` — a quick win.

### 8. VALUES / Bindings (8 failures)

Post-query VALUES clauses are not being applied as a join/filter. The evaluator
returns the full unfiltered solution sequence.

### 9. Subquery Issues (12 failures)

- 5 failures: Turtle parser can't handle test data files (newlines in IRIs)
- 5 failures: subquery evaluation returns empty results
- 2 failures: SPARQL parse errors

### 10. Other (24 failures)

SERVICE (7, expected — no endpoint), CONSTRUCT (4), BIND edge cases (5),
function evaluation issues (8: STRDT, STRLANG, ABS, UUID).

## Priority Roadmap

Ranked by test count impact and implementation difficulty:

| Priority | Category | Failures | Fix Location | Difficulty |
|----------|----------|----------|--------------|------------|
| **1** | Hash stubs | 10 | ocaml-patches.sh | Easy |
| **2** | EXISTS wiring | 13 | ocaml-patches.sh | Easy |
| **3** | Aggregate/GROUP BY | 30 | SPARQL11.Algebra.fst | Medium |
| **4** | Property paths | 28 | SPARQL11.Algebra.fst | Hard |
| **5** | Parser gaps | 30 | sparql_parser.ml | Medium |
| **6** | VALUES join | 8 | SPARQL11.Algebra.fst | Medium |
| **7** | Negative syntax | 24 | sparql_parser.ml | Medium |
| **8** | Subquery eval | 12 | Multiple | Medium |
| — | Entailment | 30 | Out of scope | — |
| — | SERVICE | 7 | Out of scope | — |

Items 1–2 are pure OCaml patches that can be applied immediately. Items 3–4
require F\* spec changes, re-extraction, and re-testing.

## Appendix: Example Tests

### A. Passing: BIND with arithmetic (bind01)

```sparql
PREFIX : <http://example.org/>
SELECT ?z
{ ?s ?p ?o . BIND(?o+10 AS ?z) }
```

The evaluator correctly evaluates arithmetic in BIND expressions, computes
`?o + 10` for each solution, and binds the result to `?z`. This exercises
pattern matching, expression evaluation, and solution extension — core
functionality that the F\* spec handles well.

### B. Passing: GROUP_CONCAT with SEPARATOR

```sparql
PREFIX : <http://example.org/>
SELECT (GROUP_CONCAT(?o ; SEPARATOR=", ") AS ?concat)
WHERE { ?s ?p ?o } GROUP BY ?s
```

GROUP_CONCAT is one of the few aggregates that works because it concatenates
all values in the group. The separator handling is correctly implemented in
the F\* spec.

### C. Failing: COUNT with GROUP BY (agg01)

```sparql
PREFIX : <http://www.example.org>
SELECT (COUNT(?O) AS ?C)
WHERE { ?S ?P ?O }
```

**Expected:** 1 row with the count of all `?O` bindings.
**Got:** 5 rows (one per solution mapping, no aggregation applied).

The evaluator returns the raw solution sequence. The GROUP BY / aggregation
pass that should collapse all rows into a single group and compute COUNT is
not implemented in the F\* spec's `eval_group_aggregate`.

### D. Failing: Simple property path (pp01)

```sparql
PREFIX ex: <http://www.example.org/schema#>
PREFIX in: <http://www.example.org/instance#>
SELECT * WHERE { in:a ex:p1/ex:p2/ex:p3 ?x }
```

**Expected:** 1 row matching the path `ex:p1 → ex:p2 → ex:p3`.
**Got:** 0 rows.

The path expression `ex:p1/ex:p2/ex:p3` (a sequence path) requires the
evaluator to chain three predicate lookups. The current F\* stub returns `[]`
for all non-trivial property paths.

### E. Failing: EXISTS filter (exists01)

```sparql
PREFIX ex: <http://www.example.org/>
SELECT * WHERE {
  ?s ?p ?o
  FILTER EXISTS { ?s ?p ex:o }
}
```

**Expected:** 3 rows where the subject has a triple with object `ex:o`.
**Got:** 0 rows.

The `eval_exists_fwd` assume val is not wired to the concrete `eval_exists`
function, so all EXISTS filters evaluate to false. This is a wiring fix in
`ocaml-patches.sh`, not a spec gap.

### F. Failing: MD5 hash (md5-01)

```sparql
PREFIX : <http://example.org/>
SELECT (MD5(?l) AS ?hash) WHERE { :s1 :str ?l }
```

**Expected:** 1 row with the MD5 hash of the string value.
**Got:** Runtime error — "Not yet implemented: SPARQL11.Algebra.hash_md5".

The F\* spec declares `assume val hash_md5 : string -> string` but the OCaml
extraction produces a `failwith` placeholder. Adding a `Digest.to_hex
(Digest.string s)` stub in `ocaml-patches.sh` will fix all 10 hash tests.

### G. Passing: Syntax parsing (75 of 94)

The SPARQL parser correctly handles the vast majority of SPARQL 1.1 syntax:
SELECT/ASK/CONSTRUCT, PREFIX/BASE, OPTIONAL, UNION, MINUS, FILTER, BIND,
VALUES, GROUP BY, HAVING, ORDER BY, LIMIT/OFFSET, DISTINCT, property path
syntax, subqueries, 60+ built-in functions. The 19 syntax failures are
mostly edge cases (invalid prefix names accepted, scope violations not caught).
