---
title: Work Log
layout: base.njk
---

# Factoidal Work Log

Development log for the formally verified RDF/SPARQL implementation.
Entries are datetime-stamped (UTC).

---

## 2026-03-08T19:00Z — Property Paths: F* Spec + Parser Wiring

Implemented property path evaluation end-to-end. Three categories of fixes:

**1. F* spec changes (SPARQL11.Algebra.fst):**
- `PP_Sequence` / `PP_Alternative`: removed incorrect `dedup_path` — SPARQL
  property paths use bag semantics for these operators (duplicates from different
  paths are preserved). Set semantics only applies to `PP_ZeroOrMore`/`PP_OneOrMore`.
- `PP_NegatedSet`: split into `negated_direct_iris` and `negated_inverse_iris`.
  Direct-only sets (`!(:p)`) produce only forward matches; inverse-only sets
  (`!(^:p)`) produce only reverse matches; mixed sets (`!(:p|^:q)`) produce both.
  Previously lumped both directions into one excluded list.

**2. SPARQL parser fix (sparql_parser.ml):**
- `parse_property_list_not_empty` was discarding parsed property paths and
  substituting a dummy triple `urn:sparql:path:placeholder`. Now returns
  `(triple_pattern list * group_graph_pattern list)` and emits proper
  `GP_PropertyPath` nodes that reach the F*-extracted evaluator.
- `PP_NegatedSet` parsing: changed inner call from `parse_path_primary` to
  `parse_path_elt_or_inverse` so `^a` and `^:p` are recognized inside `!(...)`.

**3. F* extraction pipeline:** Re-extracted, patched, compiled — all changes
flow through `fstar.exe --codegen OCaml` → `ocaml-patches.sh` → compile.

**SPARQL results: 266 pass, 141 fail** (was 243/164) — **+23 net passes**

| Suite | Before | After | Delta |
|-------|--------|-------|-------|
| property-path | 3 | 26 | +23 |
| bind | 10 | 10 | 0 |

Remaining property-path failures (7): named graph support (3), zero-length
paths on empty graphs (4 — spec requires returning the bound node even when
the graph is empty).

**RDF results unchanged:** 338 pass, 45 fail.

**Cumulative from session start:** 198→266 pass (+68), 209→141 fail (-68).

---

## 2026-03-08T18:00Z — GROUP BY / Aggregation in F* Spec

Implemented GROUP BY / aggregation pipeline in `SPARQL11.Algebra.fst` (upstream
F* spec, not OCaml patches). The commented-out spec at lines 2046–2085 is now
concrete code.

**F* changes (SPARQL11.Algebra.fst):**
- `eval_expr_in_group`: evaluates expressions in group context, dispatching
  `E_Aggregate` to `eval_aggregate` and other expressions against the group's
  representative solution
- `eval_select_item_group`: handles SI_Var and SI_Expr in group context
- `aggregate_group` / `aggregate_groups`: produce one solution per group
- `select_has_aggregates`: detects whether aggregation is needed
- `eval_select_query` updated: when GROUP BY is present OR SELECT has aggregates,
  the full grouping → aggregation → HAVING pipeline runs

Also fixed `ocaml-patches.sh` to properly wire `eval_exists_fwd` assume val stub
after re-extraction (the body was still `failwith` even though the forward ref
was declared).

**SPARQL results: 243 pass, 164 fail** (was 216/191) — **+27 net passes**

| Suite | Before | After | Delta |
|-------|--------|-------|-------|
| aggregates | 9 | 31 | +22 |
| bind | 7 | 10 | +3 |
| entailment | 24 | 27 | +3 |
| exists | 4 | 4 | 0 |
| negation | 9 | 9 | 0 |
| functions | 62 | 61 | -1 |

The 1 function regression is likely an edge case where the aggregation detection
triggers on a non-aggregate query. Remaining aggregate failures: 5 are negative
syntax tests (parser accepts invalid), 2 are SPARQL parse errors, 3 are
GROUP BY edge cases (key equality, HAVING).

**RDF results unchanged:** 338 pass, 45 fail.

**Cumulative from session start:** 198→243 pass (+45), 209→164 fail (-45).

---

## 2026-03-08T17:00Z — Hash Stubs + EXISTS Wiring

Wired three categories of `assume val` stubs in `ocaml-patches.sh`:

1. **Hash functions** (MD5, SHA-1, SHA-256, SHA-384, SHA-512): OCaml `Digest`
   stubs. MD5 produces correct results; SHA variants use Digest as placeholder
   (OCaml stdlib only has MD5 — a proper crypto lib needed for SHA correctness).

2. **eval_exists_fwd**: Forward-ref pattern (like eval_expr_ebv/fwd) wires the
   `assume val` to the concrete `eval_exists` function. EXISTS/NOT EXISTS filters
   now evaluate correctly.

3. **GP_Filter patch**: Extraction lost the special E_Exists/E_NotExists dispatch
   in GP_Filter. Patched to match on E_Exists/E_NotExists and call eval_exists
   via the forward ref, falling back to filter_solutions_fwd for other exprs.

**SPARQL results: 216 pass, 191 fail** (was 198/209) — **+18 passes**

| Category | Before | After | Delta |
|----------|--------|-------|-------|
| functions | 52 | 62 | +10 |
| negation | 4 | 9 | +5 |
| exists | 1 | 4 | +3 |

**RDF results unchanged:** 338 pass, 45 fail.

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
