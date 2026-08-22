# Lean 4 W3C harness — design (issue #466, ladder rung 3)

Owner steer (2026-08-22, verbatim): "we should prioritise syntax work
that allows us to run current unit tests. Then look into ways of
creating more unit tests that truly exercise an implementation."

The "current unit tests" are the W3C files under
`third_party/testing/w3c/` (rdf11: rdf-turtle, rdf-n-triples,
rdf-n-quads, rdf-trig, rdf-xml, rdf-mt; sparql11: ~60 sub-suites) and
the rdf-canon suite. Iron rule #6 applies unchanged to the Lean tree:
read the real manifests and files from disk, never synthetic
"inspired by" tests. The F\* tree's runner (`bin/w3c-runner/
w3c_runner.ml`, hand-written OCaml) is the reference for what a test
entry means; the Lean harness is a native Lean executable doing the
same job with the Lean engine.

## What a manifest entry needs

| Need | Source of truth in the F\* runner | Lean component (status) |
|---|---|---|
| Manifest parsing (`manifest.ttl`: `mf:entries` list, `mf:action` bnode with `qt:query`/`qt:data`/`qt:graphData`/`qt:serviceData`, `mf:result`, `rdf:type` = test type, `rdft:approval`) | `w3c_runner.ml` ~440–640 | **Turtle parser (wave 2)** — the gating item; RDF collections (`( )`) for `mf:entries` are mandatory |
| Data files | `.ttl` / `.nt` / `.nq` / `.trig` / `.rdf` | N-Triples/N-Quads (wave 1, in flight); Turtle + TriG (wave 2); RDF/XML (after the XML port, in flight) |
| Query files `.rq` / `.ru` | `SPARQL11.Parser.fst` (4.5k lines) | **SPARQL parser port (wave 2, the largest single rung)** — tokenizer + grammar → the Lean `GraphPattern`/`Expr` AST, which must first grow GRAPH/VALUES/BIND/sub-SELECT/property paths + solution modifiers (projection, ORDER BY, DISTINCT, LIMIT/OFFSET) and query forms |
| Expected results `.srx` / `.srj` / `.csv` / `.tsv` / `.ttl` (CONSTRUCT) | `Parser.SRX/JSONResults/CSVResults` | SRX via the XML port; SRJ via the JSON port; CSV/TSV small |
| Comparison | `RDF.GraphIsomorphism.fst`: `graphs_isomorphic_outcome`, `datasets_isomorphic_outcome`, `solutions_isomorphic_outcome ordered` (bnode-iso over binding rows, order-sensitive when ORDER BY) | Isomorphism port (wave 1, in flight) + a solutions-isomorphism port |
| Test-type dispatch | `test_type` string: `PositiveSyntaxTest11`, `NegativeSyntaxTest11`, `QueryEvaluationTest`, `UpdateEvaluationTest`, `TestTurtleEval`, `TestTurtlePositiveSyntax`, `TestNTriplesNegativeSyntax`, … | harness `Main.lean` match |

## Architecture

`formal/lean4/Harness/` (a `lean_exe` target `l4w3c`), separate from
the library so the library stays spec-only:

- `Manifest.lean` — Turtle → the small `TestCase` record the F\*
  runner uses (name, type, action files, result file, approval).
- `Run.lean` — per test-type execution: parse → evaluate → compare,
  producing `pass | fail reason | skip reason | unsupported feature`.
  The `unsupported` bucket is explicit and counted (the F\* runner's
  `HARNESS-DIAG` discipline: a test that the Lean tree cannot attempt
  yet is reported as such, never silently passed or dropped).
- `Main.lean` — `l4w3c <suite-dir>...` printing the same score-line
  grammar as `w3c_runner` ("N pass, M fail, K skip, U unsupported
  (out of T)") so the two trees' numbers are directly comparable and
  the dashboard can ingest them later.

Scores are NEVER quoted for the Lean tree until this executable
produces them from the real files (factoidal-lean-basics skill rule).

## Order of unlocking (what becomes runnable when)

1. Turtle (+ collections, bnode property lists, numeric/boolean sugar,
   `@prefix`/`PREFIX`, relative IRI resolution against the manifest
   base) → the rdf-turtle, rdf-n-triples, rdf-n-quads suites run
   (syntax positive/negative + eval via isomorphism). ~600 tests.
2. TriG → rdf-trig (~300). RDF/XML → rdf-xml (~180) after the XML
   port.
3. SPARQL query parser + the wider algebra → sparql11 query suites
   (hundreds); Update parser + `apply_update` port → update suites.
4. rdf-canon (RDFC-1.0) after N-Quads + SHA-256.
5. rdf-mt (entailment) after the RDFS closure port; the regime
   theorem program can then be re-run natively.

## "Tests that truly exercise an implementation" (owner's second ask)

Beyond W3C conformance, three mechanisms fit Lean specifically:
- **Differential guards**: the same fixture run through the F\* native
  binary (`bin/<platform>/factoidal`) and the Lean harness, compared
  by isomorphism — catches divergence in both directions. Cheap once
  the harness exists.
- **Sabotage tests** (already practised): mutate a clause, assert a
  named guard/theorem fails. Codify as a script over a list of
  (file, pattern, expected-failing-guard) triples.
- **Property-based generators**: Lean has no QuickCheck in core; a
  small generator for random graphs/patterns with a fixed seed, run
  as `#guard`s over invariants (e.g. `evalBgp_mono` instances,
  isomorphism reflexivity, parse∘serialise) is ~100 lines and
  exercises paths the hand-written fixtures miss.
