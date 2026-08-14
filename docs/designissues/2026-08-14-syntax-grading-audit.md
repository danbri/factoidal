# 2026-08-14 — W3C runner grading audit (issue #429)

Scope: every place `bin/w3c-runner/w3c_runner.ml` grades a positive-syntax,
negative-syntax, or eval test, across Turtle, TriG, N-Triples, N-Quads,
RDF/XML, and SPARQL syntax (query + update, 1.1 and 1.2). "Real" = the check
can fail for the reason it claims to check. "Vacuous" = the check almost
always passes regardless of correctness (issue #429's finding).

## RDF 1.1 suite (`run_rdf_test`, lines ~2644-2836)

| Test type | Entry point used | Result used? | Verdict |
|---|---|---|---|
| TestNTriplesPositiveSyntax | `parse_ntriples_fstar` (LENIENT — `Parser_NTriples.parse_ntriples`, never raises, skips bad lines) | `ignore`d | **VACUOUS** — issue #429 core bug |
| TestNTriplesNegativeSyntax | `parse_ntriples_strict` (returns `None` on error) | inspected (`None`→Pass) | real |
| TestTurtlePositiveSyntax | `parse_turtle_fstar` (LENIENT — `parse_turtle_with_base`) | `ignore`d | **VACUOUS** — the exact case named in #429 |
| TestTurtleNegativeSyntax | `parse_turtle_strict` | inspected | real |
| TestTurtleEval | `parse_turtle_fstar` (LENIENT) then `graphs_equal_strict` vs expected `.nt` | inspected | real comparison, but the LENIENT parse of the input is a blind spot: a strict-only rejection bug (CLI would refuse the file) can't surface here if lenient still emits the right triples |
| TestTurtleNegativeEval | `parse_turtle_strict` | inspected | real |
| TestNQuadsPositiveSyntax | `parse_nquads_fstar` (LENIENT) | `ignore`d | **VACUOUS** |
| TestNQuadsNegativeSyntax | `parse_nquads_strict` | inspected | real |
| TestTrigPositiveSyntax | `parse_trig_fstar` (LENIENT — `parse_trig_with_base_lenient`) | `ignore`d | **VACUOUS** |
| TestTrigNegativeSyntax | `parse_trig_strict` | inspected | real |
| TestTrigEval | `parse_trig_fstar` (LENIENT) then compare vs expected `.nq` | inspected | real comparison, same lenient-input blind spot as TurtleEval |
| TestTrigNegativeEval | `parse_trig_strict` | inspected | real |
| TestXMLEval | `parse_rdfxml_fstar` (only entry point with a base; no strict-with-base variant exists) then compare vs expected `.nt` | inspected | real (no lenient/strict split exists for this entry point, so no blind spot) |
| TestXMLNegativeSyntax | `Parser_RDFXML.parse_rdfxml_strict` | inspected | real |

There is no standalone `TestXMLPositiveSyntax` type in the rdf-xml manifest —
every positive RDF/XML test ships a result file and runs as `TestXMLEval`, so
RDF/XML was never exposed to the vacuous-`ignore` pattern.

## RDF 1.2 suite (`run_rdf12_test`, lines ~3105-3355)

| Test type | Entry point used | Verdict |
|---|---|---|
| TestNTriplesPositiveSyntax | `parse_ntriples_strict_12` | real (already fixed under epic #305 before this audit) |
| TestNTriplesNegativeSyntax | `parse_ntriples_strict_12` | real |
| TestNQuadsPositiveSyntax | `parse_nquads_strict_12` | real |
| TestNQuadsNegativeSyntax | `parse_nquads_strict_12` | real |
| TestTurtlePositiveSyntax | `parse_turtle_strict_12` | real |
| TestTurtleNegativeSyntax | `parse_turtle_strict_12` | real |
| TestTurtleEval | `parse_turtle_12` (LENIENT — `parse_turtle_with_base_12`) then compare | real comparison, same lenient-input blind spot as 1.1 TurtleEval |
| TestTrigPositiveSyntax | `parse_trig_strict_12` | real |
| TestTrigNegativeSyntax | `parse_trig_strict_12` | real |
| TestTrigEval | `parse_trig_lenient_12` then compare | same blind spot |
| TestNTriplesPositiveC14N / TestNQuadsPositiveC14N | strict parse required (`None`→Fail), byte-compare canonical output | real |
| PositiveEntailmentTest / NegativeEntailmentTest (1.2) | `parse_turtle_12` (LENIENT) on both action+result, then entailment function | real entailment check, same lenient-input blind spot |
| TestXMLEval | `parse_rdfxml_fstar` then compare | real |
| TestXMLNegativeSyntax | `parse_rdfxml_strict` | real |

**Finding**: the RDF 1.2 suite's *positive-syntax* tests were already fixed
(strict entry points) before this audit — apparently landed under epic #305.
The bug in #429 is specific to the **RDF 1.1** positive-syntax tests. The
1.2 Eval/Entailment tests share the milder "lenient input parse, but the
output IS compared" blind spot with the 1.1 Eval tests.

## SPARQL syntax tests (`run_test`, lines ~2200-2235; `run_sparql12_test`, ~3366-3386)

| Test type | Entry point used | Verdict |
|---|---|---|
| PositiveSyntaxTest(11) | `parse_sparql_query` (single entry point, no lenient variant — raises `Sparql_parse_error` on any grammar violation) | real — `ignore` here is harmless because the ONLY way to reach `Pass` is a successful parse; there is no separate lenient SPARQL query parser to diverge from |
| NegativeSyntaxTest(11) | same `parse_sparql_query`, exception required to Pass | real |
| PositiveUpdateSyntaxTest(11, and bare 1.2 form) | `parse_sparql_update` (single entry point) | real |
| NegativeUpdateSyntaxTest(11, and bare 1.2 form) | `parse_sparql_update` | real |

SPARQL has no strict/lenient split at all — one query parser, one update
parser, each either returns an AST or raises. So `ignore (parse_sparql_query
...); Pass` is NOT the #429 pattern: failure to parse always raises before
reaching `Pass`, and the CLI uses the identical entry point. No fix needed
here.

## Fix applied

Only the RDF 1.1 positive-syntax arms in `run_rdf_test` were vacuous. Fixed
by switching TestNTriplesPositiveSyntax / TestTurtlePositiveSyntax /
TestNQuadsPositiveSyntax / TestTrigPositiveSyntax to their strict entry
points (`parse_ntriples_strict`, `parse_turtle_strict`, `parse_nquads_strict`,
`parse_trig_strict`), requiring `Some` to Pass — matching what
`factoidal dump`/`validate` actually run. See commit history on this branch
for the diff and the resulting score change.

Eval-test lenient-input blind spot (Turtle/TriG/NTriples-1.2 Eval,
PositiveEntailmentTest 1.2) is noted above but left as a separate, smaller
finding — tracked as a follow-up rather than folded into this landing, since
the primary correctness signal (graph/entailment comparison) is already
real there; only strict-vs-lenient *parser divergence on well-formed input*
would slip through, which is a narrower class of bug than #429's "never
checked at all".
