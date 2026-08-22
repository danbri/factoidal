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

**Status 2026-08-22 (branch `lean4/differential`):** the first and
third mechanisms are built and measured — `lake exe l4diff` and
`lake exe l4prop`, see the section "Tests that truly exercise an
implementation — measured" at the end of this document. The sabotage
script (second mechanism) is still practised by hand; that section
records the two sabotages run against the new probes.

## Status 2026-08-22

The runner exists and has been run. `lake exe l4w3c` is a native Lean
executable in `formal/lean4/Harness/` (`Common.lean`, `Manifest.lean`,
`Run.lean`, `Main.lean`, `HarnessTests.lean`; `lean_exe l4w3c` in
`lakefile.toml`, in `defaultTargets`). It reads the real
`manifest.ttl` files off disk with `L4Factoidal.Syntax.Turtle`, walks
`mf:entries` as an RDF collection, dispatches on the `rdf:type` local
name, and prints the score-line grammar `bin/w3c-runner/w3c_runner.ml`
prints.

What became runnable: the four rdf11 syntax suites and rdf-canon —
items 1, 2 (the TriG half) and 4 of the "Order of unlocking" list
above. Every SPARQL type (item 3) is reached, typed, counted and
reported `unsupported <type>`; it is not silently dropped and it stays
in its denominator.

**Update 2026-08-22, later the same day:** RDF/XML (item 2's other
half) is wired: two `Run.lean` clauses (`TestXMLEval`,
`TestXMLNegativeSyntax`) over `Syntax/RdfXml.lean`. Measured, verbatim:

```
rdf-xml: 166 pass, 0 fail, 0 skip, 0 unsupported (out of 166)
```

and the six-manifest total is now
`TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported (out of 1078)`
(rdf-trig rose to 356 of 356 when graph names became
`Subject`-typed — the two blank-node-graph-name fails below are
closed). The rdf-xml denominator, 166, matches the F\* runner's.

### Measured score lines, verbatim

`lake exe l4w3c --quiet` over the five manifests, exactly as printed:

```
rdf-turtle: 313 pass, 0 fail, 0 skip, 0 unsupported (out of 313)
HARNESS-DIAG rdf-turtle: no_manifest=0 zero_tests=0 budget_exceeded=0
rdf-n-triples: 70 pass, 0 fail, 0 skip, 0 unsupported (out of 70)
HARNESS-DIAG rdf-n-triples: no_manifest=0 zero_tests=0 budget_exceeded=0
rdf-n-quads: 87 pass, 0 fail, 0 skip, 0 unsupported (out of 87)
HARNESS-DIAG rdf-n-quads: no_manifest=0 zero_tests=0 budget_exceeded=0
rdf-trig: 356 pass, 0 fail, 0 skip, 0 unsupported (out of 356)
HARNESS-DIAG rdf-trig: no_manifest=0 zero_tests=0 budget_exceeded=0
rdf-canon: 86 pass, 0 fail, 0 skip, 0 unsupported (out of 86)
HARNESS-DIAG rdf-canon: no_manifest=0 zero_tests=0 budget_exceeded=0
TOTAL: 912 pass, 0 fail, 0 skip, 0 unsupported (out of 912)
HARNESS-DIAG TOTAL: no_manifest=0 zero_tests=0 budget_exceeded=0
```

The two `rdf-trig` failures this document first recorded
(`anonymous_blank_node_graph`, `labeled_blank_node_graph`) were fixed
on 2026-08-22 by giving `RDF.NamedGraph.name` the type `Subject` — see
"The two failures" below, which now records the repair. The lines this
run first printed were:

```
FAIL anonymous_blank_node_graph: not isomorphic to the expected dataset (got 1 quads, expected 1)
FAIL labeled_blank_node_graph: not isomorphic to the expected dataset (got 1 quads, expected 1)
rdf-trig: 354 pass, 2 fail, 0 skip, 0 unsupported (out of 356)
TOTAL: 910 pass, 2 fail, 0 skip, 0 unsupported (out of 912)
```

Exit code 1 when a manifest with failures is run, 0 otherwise
(checked both ways).

### Side by side with the F\* tree

F\* numbers from [`docs/test-results/latest.json`](../test-results/latest.json),
commit `c3c0c37`, same five manifests:

| Suite | Lean (`l4w3c`) | F\* (`w3c_runner`) |
|---|---|---|
| rdf-turtle | 313 pass, 0 fail, 0 skip, 0 unsupported (out of 313) | 313 pass, 0 fail, 0 skip, 0 unsupported (out of 313) |
| rdf-n-triples | 70 pass, 0 fail, 0 skip, 0 unsupported (out of 70) | 70 pass, 0 fail, 0 skip, 0 unsupported (out of 70) |
| rdf-n-quads | 87 pass, 0 fail, 0 skip, 0 unsupported (out of 87) | 87 pass, 0 fail, 0 skip, 0 unsupported (out of 87) |
| rdf-trig | 356 pass, 0 fail, 0 skip, 0 unsupported (out of 356) | 356 pass, 0 fail, 0 skip, 0 unsupported (out of 356) |
| rdf-canon | 86 pass, 0 fail, 0 skip, 0 unsupported (out of 86) | 86 pass, 0 fail, 0 skip, 0 unsupported (out of 86) |

**Every denominator agrees.** That is the check that matters for a new
manifest walk: a harness that quietly drops entries scores well on a
smaller population, and only the denominator shows it. The totals were
also cross-checked against the manifest files directly — the
`rdft:Test*` type counts sum to 313 / 70 / 87 / 356, and the rdf-canon
`mf:entries` collection has 86 members.

### The two failures — engine, not harness — FIXED 2026-08-22

**Both are green now** (`rdf-trig` 356 pass, 0 fail, out of 356;
TOTAL 912 pass, 0 fail, out of 912). The fix is
`RDF.NamedGraph.name : Subject` on branch
`lean4/namedgraph-subject`, described at the end of this section. The
diagnosis below is kept because it is what the harness was for: it
found an engine gap, in the data model, that no test in the tree had
reached.

Both were `TestTrigEval` entries with a blank-node GRAPH NAME
(`anonymous_blank_node_graph` writes `[] {...}`,
`labeled_blank_node_graph` writes `_:g {...}`; both fixtures' `.nq`
files write `_:b1`). The gap is in the DATASET MODEL, and it was
already written down in `formal/lean4/PORT_NOTES.md` before this
runner existed:

- `L4Factoidal/RDF/Graph.lean:81` types `NamedGraph.name` as `Iri`
  (a `String`), so `Syntax.NQuads.graphLabelToIri` carries a
  blank-node graph name as the sentinel string `"_:" ++ label`.
- `L4Factoidal/RDF/Isomorphism.lean:435` `Dataset.namesMatchB`
  compares graph names by raw string equality, and
  `Dataset.isoSearchStep:483` returns `none` on a name mismatch
  BEFORE any blank-node bijection search runs. `_:g` and `_:b1` are
  different strings, so datasets that are isomorphic under RDF 1.1
  Concepts §4/§3.6 are reported unequal.

Cross-check that isolates it to the isomorphism path: running the same
two fixture pairs through this tree's own RDFC-1.0 canonicalizer
produces identical output on both sides
(`<http://a.example/s> <http://a.example/p> <http://a.example/o> _:c14n0 .`),
so `RDF/Canonical.lean` handles blank-node graph labels correctly
already. The parsers are not at fault either — the quad counts match.

The harness does NOT work around this. Switching TriG eval to a
canonicalization comparison would turn both failures green, but the
F\* runner's `datasets_equal_strict` calls
`datasets_isomorphic_outcome`, not the canonicalizer (its comment says
otherwise; the code is the authority), so a canonicalization
comparison would make the two trees' numbers incomparable and would
hide a real gap. The fix belongs in `RDF/Graph.lean` +
`RDF/Isomorphism.lean`: `NamedGraph.name` wants to be a `Subject` (or
an `Iri`/`BNodeId` sum), and `Dataset.checkMapping` wants to apply the
candidate blank-node mapping to graph names before comparing them.

#### What the fix changed (2026-08-22)

Exactly that, plus the sweep it forces:

- `RDF/Graph.lean` — `NamedGraph.name : Subject`;
  `Dataset.lookupNamed` keys on `Subject`; new
  `Dataset.lookupNamedIri` for the `GRAPH <iri>` / `FROM NAMED` call
  sites; `Dataset.renameBnodes` / `Dataset.prefixBnodes` moved here and
  extended to rename blank-node graph NAMES (RDF 1.1 Concepts §3.4
  scoping covers the name slot); `NamedGraph` and `Dataset` derive
  `DecidableEq`.
- `RDF/Isomorphism.lean` — `Dataset.bnodes` includes graph-name blank
  nodes; `Dataset.namesMatchB` takes the candidate mapping and applies
  it to a name before lookup; a new mapping-free `Dataset.namesPrune`
  (IRI names must correspond; blank-node-named graph counts must agree
  — both invariant under any renaming) replaces the raw-string
  pre-filter in `Dataset.isoSearchStep`.
- `RDF/Canonical.lean` — `QQuad` is `Option Subject × Triple`. Every
  `"_:"` sentinel test (`isBnodeGraphLabel`, `bnodeOfGraphLabel`) is
  gone; the graph slot reuses `canonSubject` and `relabelSubject`.
- `RDF/CanonicalTheorems.lean` — the §4.5 relabelling lemmas
  (`quadMentionsBnode_rename`, `renderForHfdq_rename`,
  `hfdqRenders_rename`, `hashFirstDegreeQuads_rename`) LOST their
  `isBnodeGraphLabel gi = false` hypotheses and now hold for every
  dataset, blank-node graph names included.
- `SPARQL/Algebra.lean` / `Query.lean` — `GRAPH <iri>` goes through
  `lookupNamedIri`; `GRAPH ?g` binds `?g` to `name.toTerm`, so it can
  now bind a blank node; `FROM NAMED` builds `Subject.iri`.

`Dataset.isomorphic?_sound` and `Dataset.isomorphic?_refl` stayed
proved with no `sorry`, on `[propext, Classical.choice, Quot.sound]`.
`Dataset.isomorphic?_refl` keeps its `namesNoDup` hypothesis: it is
still needed, and for the same reason — `lookupNamed` returns the FIRST
graph carrying a name, so a `Dataset` value listing two graphs under
one name is not equal to itself under name matching, whether the
duplicated name is an IRI or a blank node.

### A counting correction this rung produced

`test-38.ttl` — a UTF-16 surrogate pair written as two `\u` escapes —
was recorded as one of the Turtle port's known misses. It is NOT one
of the rdf-turtle manifest's 313 entries. The directory-walking probe
(`Harness/TurtleProbe.lean`) reached it by file name; the
manifest-driven runner does not, and neither does the F\* runner. The
probe and the runner count different populations, which is exactly why
a probe number was never a conformance number.

### Design points that survived contact, and one that did not

Held: the `unsupported` bucket (explicit, named, inside the
denominator); the `HARNESS-DIAG` line (a missing manifest prints
`0 pass ... (out of 0)` with `no_manifest=1`, so an empty run cannot
read as green — verified against a nonexistent path); scores quoted
only from this executable.

Changed: the base IRI. This document's table assumed the suites'
documented base `http://www.w3.org/2013/TurtleTests/<file>`. The
vendored corpus has since moved and its manifests declare
`mf:assumedTestBase <https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/>`,
with fixtures regenerated against it. The harness READS the triple
(as `w3c_runner`'s `extract_assumed_test_base` does) instead of
hardcoding either value; a hardcoded 2013 base fails the
IRI-resolution entries.

### Next rungs, unchanged

RDF/XML landed (166 of 166, see the update above) with exactly the
predicted change: two `Run.lean` clauses. SPARQL needs the
query-string parser first; `TestCase` already carries `qt:query`,
`qt:data` and `qt:graphData` for that day.

## Status 2026-08-22 (later): the sparql11 QUERY suites run

Branch `lean4/sparql-harness`. `lake exe l4w3c
../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl` now
follows `mf:include` (one score line per sub-manifest plus `TOTAL`)
and runs four SPARQL test types: `QueryEvaluationTest`,
`CSVResultFormatTest`, `PositiveSyntaxTest11`, `NegativeSyntaxTest11`.
UPDATE, Protocol, Graph Store and Service Description types stay
`unsupported <type>` (named, counted); an evaluation test that names
an `sd:entailmentRegime` is `unsupported entailment regime <R>` (the
Lean tree has the rdfs-core closure only).

What changed, by file:

- `Harness/Manifest.lean` — `mf:include` (`manifestIncludes` /
  `parseManifestIncludes`), `sd:entailmentRegime` (one IRI or a
  collection), `qt:serviceData`.
- `Harness/Compare.lean` (new) — the comparison rules of
  `run_query_eval_test`: multiset of rows under ONE blank-node
  bijection, pinned to row position when the query has ORDER BY;
  `Term.eqb` for values; CSV-lenient comparison for `.csv` expected
  files; a budgeted search whose give-up is `budgetExceeded`, never a
  pass; the `rs:ResultSet` Turtle decoder (with `rs:index`).
- `Harness/Run.lean` — fixture loading by extension (`.ttl` / `.nt` /
  `.nq` / `.trig` / `.rdf`), `qt:graphData` as IRI-named graphs,
  `qt:serviceData` into `EvalEnv.services`, expected files by
  extension (`.srx` / `.srj` / `.tsv` / `.csv` / `.ttl`), SELECT / ASK
  / CONSTRUCT dispatch; syntax tests parse with the query file's own
  `file:` IRI as BASE.
- `Harness/Common.lean` — `HARNESS-DIAG` gains `rows_compared` and
  `triples_compared`: the measurement check. A suite at 100% with
  both at 0 compared nothing.
- Library: `SPARQL/Query.lean` gains `QueryPattern.rewriteBnodes`
  (port of `rewrite_query_bnodes_pattern`: WHERE-clause blank nodes
  are non-distinguished variables) applied inside `evalSelect` /
  `evalAsk` / `evalConstruct` as the F\* `eval_select_query` does, and
  `stripSyntheticBnodeVars` at the `SELECT *` projection (before
  DISTINCT, F\* site). The old doc comment called the rewrite "a
  parser-level concern"; the F\* source applies it in evaluation, and
  without it `[ :p ?x ]` in a WHERE clause matched only a data blank
  node with the same generated label. `SPARQL/Exists.lean` (new)
  supplies `EvalEnv.existsHook` (§18.6 `substitute` then evaluate).

### Measured score lines, verbatim

`lake exe l4w3c ../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`,
score lines only (the `HARNESS-DIAG` line follows each one in the
real output):

```
add: 0 pass, 0 fail, 0 skip, 8 unsupported (out of 8)
aggregates: 42 pass, 5 fail, 0 skip, 0 unsupported (out of 47)
basic-update: 0 pass, 0 fail, 0 skip, 13 unsupported (out of 13)
bind: 10 pass, 0 fail, 0 skip, 0 unsupported (out of 10)
bindings: 11 pass, 0 fail, 0 skip, 0 unsupported (out of 11)
cast: 0 pass, 6 fail, 0 skip, 0 unsupported (out of 6)
clear: 0 pass, 0 fail, 0 skip, 4 unsupported (out of 4)
construct: 7 pass, 0 fail, 0 skip, 0 unsupported (out of 7)
copy: 0 pass, 0 fail, 0 skip, 6 unsupported (out of 6)
csv-tsv-res: 5 pass, 1 fail, 0 skip, 0 unsupported (out of 6)
delete-data: 0 pass, 0 fail, 0 skip, 6 unsupported (out of 6)
delete-insert: 8 pass, 0 fail, 0 skip, 9 unsupported (out of 17)
delete-where: 0 pass, 0 fail, 0 skip, 6 unsupported (out of 6)
delete: 0 pass, 0 fail, 0 skip, 19 unsupported (out of 19)
drop: 0 pass, 0 fail, 0 skip, 4 unsupported (out of 4)
entailment: 0 pass, 0 fail, 0 skip, 70 unsupported (out of 70)
exists: 4 pass, 2 fail, 0 skip, 0 unsupported (out of 6)
functions: 43 pass, 32 fail, 0 skip, 0 unsupported (out of 75)
grouping: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
json-res: 4 pass, 0 fail, 0 skip, 0 unsupported (out of 4)
move: 0 pass, 0 fail, 0 skip, 6 unsupported (out of 6)
negation: 12 pass, 0 fail, 0 skip, 0 unsupported (out of 12)
project-expression: 7 pass, 0 fail, 0 skip, 0 unsupported (out of 7)
property-path: 33 pass, 0 fail, 0 skip, 0 unsupported (out of 33)
service: 6 pass, 1 fail, 0 skip, 0 unsupported (out of 7)
subquery: 14 pass, 0 fail, 0 skip, 0 unsupported (out of 14)
syntax-query: 94 pass, 0 fail, 0 skip, 0 unsupported (out of 94)
syntax-update-1: 0 pass, 0 fail, 0 skip, 54 unsupported (out of 54)
syntax-update-2: 0 pass, 0 fail, 0 skip, 1 unsupported (out of 1)
update-silent: 0 pass, 0 fail, 0 skip, 13 unsupported (out of 13)
syntax-fed: 3 pass, 0 fail, 0 skip, 0 unsupported (out of 3)
service-description: 0 pass, 0 fail, 0 skip, 3 unsupported (out of 3)
protocol: 0 pass, 0 fail, 0 skip, 34 unsupported (out of 34)
http-rdf-update: 0 pass, 0 fail, 0 skip, 19 unsupported (out of 19)
TOTAL: 309 pass, 47 fail, 0 skip, 275 unsupported (out of 631)
HARNESS-DIAG TOTAL: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=1715 triples_compared=88
```

The denominator, 631, is the sum of the typed entries in the 34
included manifests (3 + 19 + 48 + 13 + 66 + 42 + 34 + 309 + 3 + 94)
and equals the F\* runner's `sparql` total in
[`docs/test-results/latest.json`](../test-results/latest.json):
`631 pass, 0 fail, 0 skip, 0 unsupported (out of 631)` — the bar.

Measurement check per suite at 100%: `bind` rows_compared=60,
`bindings` 50, `construct` triples_compared=64, `grouping` 18,
`json-res` 26, `negation` 84, `project-expression` 24,
`property-path` 149, `subquery` rows 74 + triples 24. `syntax-query`
(94) and `syntax-fed` (3) compare nothing by design — they are
accept/reject tests. Caveat: `delete-insert`'s 8 passes are
`mf:NegativeSyntaxTest11` entries whose action is an UPDATE request;
the QUERY parser rejects them, which is the expected verdict — the
F\* runner scores them the same way, but the pass says nothing about
UPDATE syntax.

The `unsupported` bucket, by reason: `UpdateEvaluationTest` 94,
`PositiveUpdateSyntaxTest11` 42, `NegativeUpdateSyntaxTest11` 13,
`ProtocolTest` 34, `GraphStoreProtocolTest` 19,
`ServiceDescriptionTest` 3, entailment regimes 70 (OWL-Direct 18 on
its own; the rest name combinations of OWL-Direct / OWL-RDF-Based /
RDFS / RDF / D; RIF 4).

### Sabotage

1. `compareSelectRows` forced to `.equal`: `lake build` FAILS at
   `Harness/HarnessTests.lean:272–278` (the bijection and
   strict-equality `#guard`s) — the build never reaches the runner.
2. The runner's call site forced to `.equal` (guards untouched):
   `TOTAL: 354 pass, 2 fail` — 45 named tests FLIP from fail to pass
   (`cast` 0 → 6 of 6, `functions` 43 → 73 of 75, `aggregates`
   42 → 47 of 47, `csv-tsv-res` 5 → 6, `exists` 4 → 6, `service`
   6 → 7). The two that stay failed are ASK tests (`RAND()`, `UUID()
   per binding`), which the SELECT path does not touch. Restored;
   the numbers above are from the restored build.

The six RDF suites after the change:
`TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported (out of 1078)`.

### The 47 failures, by cause

All 47 are EVALUATOR findings (the harness reproduces the F\* rules;
the F\* tree passes every one of these). Grouped:

| Cause | Tests | Where |
|---|---|---|
| §17.5 XSD constructor functions (`xsd:integer(?v)` …) are not evaluated: the IRI goes to `EvalEnv.ext` and errors | 8: `cast` ×6, `GROUP BY with a function`, `Protect from error in AVG` | `SPARQL/Expr.lean` functionCall dispatch (banner: "every unrecognised functionCall IRI") |
| Hash builtins scoped out | 10: `MD5()`, `SHA1()`, `SHA256()`, `SHA384()`, `SHA512()` ×2 each | `Expr.lean:1361` |
| REGEX / REPLACE scoped out (no regex engine) | 5: `REPLACE()` ×4, `SERVICE test 5` (its FILTER is a `regex`) | `Expr.lean:1331` |
| Fresh-value builtins unimplemented (`BNODE()`, `BNODE(str)`, `RAND()`, `UUID()` ×2, `STRUUID()`) | 6 | `Expr.lean` banner (§17.6 family) |
| `TIMEZONE()` / `TZ()` scoped out | 2 | `Expr.lean:1393` |
| Numeric lexical form: value-equal, lexically different (`2E-1` vs `2.0E-1`, `1.05E3` vs `1050`, `2.1E3` vs `2100`, data `"1.0E6"` vs TSV `1.0e6`). The F\* runner tolerates these through `numeric_literal_equal`; this harness compares with `Term.eqb` per the brief | 4: `MIN with GROUP BY`, `AVG DISTINCT with GROUP BY`, `SUM DISTINCT with GROUP BY`, `tsv03` | aggregate result serialisation in `SPARQL/Query.lean` / `Expr.lean` (double formatting) |
| `STRBEFORE` / `STRAFTER` argument checks: a non-string first argument (`:s7 :str 7`) and incompatible language tags must be errors (§17.4.3.1) | 4 | `Expr.lean:1305`, `:1315` |
| `STRDT` on a language-tagged or typed literal must be an error | 2: `STRDT()`, `STRDT() TypeErrors` | `Expr.lean:1240` |
| EXISTS hook limits: active graph inside `GRAPH`, and an EXISTS nested in an EXISTS body (lowered with `emptyEnv` at parse time). FIXED 2026-08-22 (branch `lean4/sparql-exists`): `Expr.existsPat` carries a `QueryPattern`, conditions receive the active graph; `exists: 6 pass, 0 fail (out of 6)`, `TOTAL: 311 pass, 45 fail, 0 skip, 275 unsupported (out of 631)` | 2: `Exists within graph pattern`, `Nested positive exists` | `SPARQL/Exists.lean` header (design record); `PORT_NOTES.md` EXISTS stage |
| `CONCAT` argument compatibility (non-string / mixed-language arguments must error) | 1: `CONCAT() 2` | `Expr.lean:1325` |
| `IF(1/0, …)`: an error in the condition must propagate, not read as false | 1 | `Expr.lean:1267` |
| `IRI("rel")` needs the query BASE (`EvalEnv` carries none; F\* passes `q.q_base`) | 1 | `Expr.lean:1231` |
| `SECONDS()` returns `"01"` where `"1"` (canonical decimal) is expected | 1 | `Expr.lean:1389` |

None of these was changed in this branch (the brief: list, do not
fix). Each group is a separate issue candidate.
## Status 2026-08-22 — the OWL 2 corpus runs (`l4owl-probe`, branch `lean4/owl-corpus`)

`Harness/OwlProbe.lean` was a census ("0 of 931 runnable: no RDF/XML
mapping"). With `Syntax/RdfXml.lean` landed the same day, it now parses
every case's RDF/XML premise and conclusion, merges `owl:imports` from
the catalog wrapper nodes, runs `OWL.RL.step` under fuel 100 and a
per-closure wall-clock cap (checked between driving triples, so one
slow round cannot escape it), and judges the four test types exactly as
`bin/owl-runner/owl_runner.ml` does — one unit per (case, test type),
`ProfileIdentificationTest` tallied only, relaxed blank-node match on
conclusions, functional-syntax-only cases `unsupported` and in the
denominator, a parse failure a FAIL with the parser's message.

Verbatim (per-closure cap 20 000 ms; the three profile catalogs and
type-inconsistency run in 82 / 70 / 57 / 1570 ms, the two large type
catalogs in 326 s and 397 s):

```
profile-RL.rdf: 102 pass, 19 fail, 0 skip, 5 unsupported (out of 126)
HARNESS-DIAG-OWL profile-RL.rdf: cases=91 units=126 triples_parsed=1227 closure_rounds=428 clashes=10 cap_hits=0 parse_failures=0 wall_ms=82
profile-EL.rdf: 95 pass, 21 fail, 1 skip, 4 unsupported (out of 121)
HARNESS-DIAG-OWL profile-EL.rdf: cases=87 units=121 triples_parsed=1098 closure_rounds=409 clashes=4 cap_hits=0 parse_failures=0 wall_ms=70
profile-QL.rdf: 76 pass, 11 fail, 0 skip, 0 unsupported (out of 87)
HARNESS-DIAG-OWL profile-QL.rdf: cases=65 units=87 triples_parsed=872 closure_rounds=303 clashes=5 cap_hits=0 parse_failures=0 wall_ms=57
type-positive-entailment.rdf: 291 pass, 115 fail, 0 skip, 6 unsupported (out of 412)
HARNESS-DIAG-OWL type-positive-entailment.rdf: cases=206 units=412 triples_parsed=28902 closure_rounds=1544 clashes=0 cap_hits=10 parse_failures=0 wall_ms=326261
type-inconsistency.rdf: 29 pass, 84 fail, 1 skip, 14 unsupported (out of 128)
HARNESS-DIAG-OWL type-inconsistency.rdf: cases=128 units=128 triples_parsed=5258 closure_rounds=425 clashes=29 cap_hits=0 parse_failures=0 wall_ms=1570
type-consistency.rdf: 453 pass, 118 fail, 0 skip, 12 unsupported (out of 583)
HARNESS-DIAG-OWL type-consistency.rdf: cases=354 units=583 triples_parsed=41248 closure_rounds=2111 clashes=0 cap_hits=12 parse_failures=1 wall_ms=396557
```

Sum over the six catalogs: 1046 pass, 368 fail, 2 skip, 41 unsupported
(out of 1457 units over 931 cases). The per-type denominators agree
with the F\* runner's where it publishes them (profile-RL PE 30 of 30;
profile-QL 87; profile-EL 121 less one functional-syntax skip = 120;
type-inconsistency 128 less one RDF-BASED-only skip = 127).

F\* side, each with its manifest and regime: `owl_rl_positive_entailment`
30 pass, 0 fail (out of 30) = profile-RL.rdf PE line, RL regime (Lean:
11 pass, 18 fail, 1 unsupported); `owl2_profile_ql` 87 pass, 0 fail
(out of 87) = profile-QL.rdf (Lean 76 of 87); `owl2_profile_el` 119
pass, 1 fail (out of 120) = profile-EL.rdf (Lean 95 of 121);
`owl2_dl_inconsistency` 126 pass, 1 fail (out of 127) =
type-inconsistency.rdf under `--regime dl`, i.e. RL closure + tableau
refuter (Lean, RL closure only: 29 of 128). No F\* line exists for
type-positive-entailment.rdf or type-consistency.rdf.

Every FAIL is named in the run log and grouped by cause. On the RL
profile catalogs all are rows the port scoped out by name (the F\*
`[ext]` differentFrom-synthesis, comprehension-witness, hasSelf, chain
and equivalentClass-annotation rules; the `with_reflexivity` wrapper
that types every subject `owl:Thing`; Table 7 dt-diff and the datatype
map; the eq-diff2/3 and prp-adp clash rows). On the type catalogs the
bulk are OWL DL entailments that need the tableau. Full list with rule
names: `formal/lean4/PORT_NOTES.md`, "Measured against the real
corpus, second entry". One parser finding: `FS2RDF-literals-ar` carries
an XMLLiteral as element content under `rdf:datatype`, which §7.2.16
forbids; `Parser.RDFXML.fst` accepts it by a documented non-spec
extension the Lean parser deliberately does not copy. `RdfXml.lean`
was not edited; the rdf11 gates still read 1078 of 1078 (`l4w3c`) and
132 / 41 / 130 of 132 (`l4rdfxml-probe`).

Sabotage check: removing cax-sco from `conclusionsList` takes
profile-RL from 102 pass to 98 pass (WebOnt-imports-011 PE and
WebOnt-description-logic-101/103/104 Inconsistency flip to FAIL);
restored.

### Update 2026-08-22 (evening): sparql11 query suites at full pass

After the EXISTS restructure, the builtins/casts/hashes stage and the
pure regex engine (`L4Factoidal/Regex/`) were wired into `Expr.lean`,
`lake exe l4w3c ../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`
prints, verbatim:

```
TOTAL: 356 pass, 0 fail, 0 skip, 275 unsupported (out of 631)
```

Every query-type entry (QueryEvaluationTest, CSVResultFormatTest,
PositiveSyntaxTest11, NegativeSyntaxTest11) passes; the 275 are the
UPDATE, Protocol, Graph Store, Service Description and entailment-regime
types, still named and counted. The F\* runner's line for the same
631 is 631 pass, 0 fail. The six RDF suites stay at 1078 of 1078.

## Status 2026-08-22 — SPARQL 1.1 Update (branch `lean4/sparql-update`)

The three UPDATE test types run. `SPARQL/Update.lean` is the port of
`SPARQL11.Algebra.fst` Parts 6b and 19b–19e (AST, INSERT DATA, DELETE
DATA, DELETE WHERE, DELETE/INSERT with WITH / USING / USING NAMED,
CREATE / CLEAR / DROP / COPY / MOVE / ADD, LOAD SILENT);
`SPARQL/UpdateParser.lean` is grammar [29]–[52] over the existing
tokenizer, reusing the query parser's triples-block, group-graph-
pattern and prologue productions; `Harness/Manifest.lean` reads the
`ut:` vocabulary (`ut:request`, `ut:data`, `ut:graphData` with
`ut:graph` + `rdfs:label`, on the action and on `mf:result`);
`Harness/Run.lean` gained `runUpdateEvaluation` / `runUpdateSyntaxTest`
in one block. Two semantic choices differ from the F\* and are
recorded in `PORT_NOTES.md` (this stage's "Decisions"): the semantics
returns `Except UpdateError Dataset` and raises the §3.2 errors that
`SILENT` suppresses (the F\* ignores `SILENT`), and fresh blank-node
labels are longer than every label in the store rather than salted by
triple count.

Verbatim, `lake exe l4w3c ../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`:

```
add: 8 pass, 0 fail, 0 skip, 0 unsupported (out of 8)
basic-update: 13 pass, 0 fail, 0 skip, 0 unsupported (out of 13)
clear: 4 pass, 0 fail, 0 skip, 0 unsupported (out of 4)
copy: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
delete-data: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
delete-insert: 17 pass, 0 fail, 0 skip, 0 unsupported (out of 17)
delete-where: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
delete: 19 pass, 0 fail, 0 skip, 0 unsupported (out of 19)
drop: 4 pass, 0 fail, 0 skip, 0 unsupported (out of 4)
move: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
syntax-update-1: 54 pass, 0 fail, 0 skip, 0 unsupported (out of 54)
syntax-update-2: 1 pass, 0 fail, 0 skip, 0 unsupported (out of 1)
update-silent: 13 pass, 0 fail, 0 skip, 0 unsupported (out of 13)
TOTAL: 505 pass, 0 fail, 0 skip, 126 unsupported (out of 631)
```

From the baseline `TOTAL: 356 pass, 0 fail, 0 skip, 275 unsupported
(out of 631)` the 149 UPDATE entries (94 UpdateEvaluationTest, 42
PositiveUpdateSyntaxTest11, 13 NegativeUpdateSyntaxTest11) all moved to
pass; no FAIL, no SKIP (the suites hold no non-SILENT LOAD, which
would skip with "non-silent LOAD not yet implemented (no HTTP fetch)"
as in the F\* runner). The 126 still `unsupported` are the Protocol,
Graph Store, Service Description and entailment-regime types. The
query-type entries are unchanged at 356 pass, 0 fail. The six RDF
suites: `TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported (out of
1078)`.

Comparison note: the expected and actual stores are compared by
`Dataset.isomorphicOutcome` after dropping empty named-graph slots on
both sides — the F\* runner canonicalises to N-Quads, which has no
representation for an empty graph, while the Lean isomorphism matches
graph names; without the drop, `CLEAR GRAPH` / `CREATE GRAPH` tests
would fail here and pass there on an artefact of the comparison.

Sabotage check (2026-08-22): with the DELETE and INSERT steps of
`applyModify` swapped (insert first, then delete), `lake build` fails
at `UpdateTests.lean:110` (`DELETE { :s :p :o } INSERT { :s :p :o }
WHERE {}` must leave the triple in place). The W3C run, however, is
UNCHANGED at 505 pass, 0 fail: the only combined DELETE/INSERT
operation in the suites is `delete-insert-01`
(`DELETE { ?a foaf:knows ?b } INSERT { ?b foaf:knows ?a }`), and its
data `delete-insert-pre-01.ttl` holds no symmetric `foaf:knows` pair,
so both orders give the same store; `delete-insert-01b` / `01c`
sequence the two operations explicitly. The §3.1.3 ordering is pinned
by the guard, not by the corpus — a gap in the W3C suite worth
knowing. Restored (file checked out from the branch), build green
again.
## Status 2026-08-22 — entailment regimes run (branch `lean4/entailment`)

The rdf-mt suite and the RDFS / RDF / D entries of the sparql11
`entailment` suite now run in the Lean harness. The engine side is
`formal/lean4/L4Factoidal/RDFS/FullClosure.lean` (RDF 1.1 Semantics
§8.1 rdfD2, §9.2 rdfs1–13, §8.2 / §9.3 axiomatic triples; derivation
relation `DerivesFull` plus the `fullClosure` fixpoint on top of the
rdfs-core step), `RDF/Datatypes.lean` (the datatype map: lexical
spaces, D-value equality, value-space membership; `rdf:XMLLiteral`
decided by the XML parser) and `RDF/Entailment.lean` (simple
entailment by instance — specification `SimpleEntails`, §5.2 — with a
witness-then-certificate decision procedure, the four regimes, and the
two D-inconsistency shapes). Harness: `Harness/Manifest.lean` reads
`mf:entailmentRegime`, `mf:recognizedDatatypes` and `mf:result false`;
`Harness/Run.lean` gains `runEntailmentTest` (one contiguous block for
`PositiveEntailmentTest` / `NegativeEntailmentTest`) and applies
`Regime.closure` to the fixtures of a sparql11 entailment entry.

### Measured score lines, verbatim

```
rdf-mt: 39 pass, 0 fail, 0 skip, 0 unsupported (out of 39)
HARNESS-DIAG rdf-mt: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=0 triples_compared=133
entailment: 40 pass, 0 fail, 0 skip, 30 unsupported (out of 70)
HARNESS-DIAG entailment: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=133 triples_compared=0
TOTAL: 396 pass, 0 fail, 0 skip, 235 unsupported (out of 631)        (sparql11/manifest-all.ttl)
TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported (out of 1078)        (rdf-n-triples, rdf-n-quads, rdf-turtle, rdf-trig, rdf-xml, rdf-canon)
```

Denominators match the F\* runner's (rdf-mt 39; entailment 70; 631).
F\* side: rdf-mt 38 pass, 0 fail, 1 unsupported (out of 39) — the
unsupported entry is `rdfs-entailment-test001`, rdf:XMLLiteral
well-formedness, which this tree decides; sparql11 entailment 70 pass,
0 fail (out of 70), the difference being the OWL-RL / OWL-Direct / RIF
regimes.

### The 30 unsupported, by regime

- `OWL-Direct` only (18): paper-sparqldl-Q2, paper-sparqldl-Q3,
  parent3, parent4, parent5, parent6, parent7, parent8, parent9,
  parent10, simple1–simple8.
- `OWL-Direct/OWL-RDF-Based` (8): lang, plainLit, paper-sparqldl-Q1,
  paper-sparqldl-Q4, sparqldl-10, sparqldl-11, sparqldl-12, sparqldl-13.
- `RIF` (4): rif01, rif03, rif04, rif06.

Every entry whose regime list names RDFS, RDF or D (alone or beside
OWL names) runs under the strongest of those three and passes. No
FAIL in either suite.

### Sabotage

rdfs9 removed from the rdfs-core step: the sparql11 entailment suite
drops to 37 pass, 3 fail (rdfs04, rdfs05, rdfs09) and `lake build`
fails at `ClosureTheorems.stepConclusions_sound`; rdf-mt does NOT move
(39 pass) — the suite has no entry exercising rdfs9, which is now
recorded in `PORT_NOTES.md` and pinned by a guard. rdfs7 removed:
rdf-mt drops to 37 pass, 2 fail (`rdfms-seq-representation-test003`,
`rdfs-subPropertyOf-semantics-test001`). Both restored, all gates
green.

### Theorems landed

`Derives.toFull` (rdfs-core ⊆ full RDFS), `DerivesFull.mono` /
`.cut`, eight per-row soundness lemmas, `fullClosure_extensive`,
`fullClosure_sound`, `rdfClosure_extensive`, `rdfClosure_sound`,
`fullClosure_saturated_or_underfueled`, `simpleEntails_sound`,
`SimpleEntails.refl`. Axiom audit: propext, Classical.choice,
Quot.sound. Completeness at saturation for the eight new rows is the
named open obligation.

## Status 2026-08-22 (night): the three protocol-shaped types run (branch `lean4/protocol`)

`ProtocolTest`, `GraphStoreProtocolTest` and `ServiceDescriptionTest`
are scored. No HTTP server is started — the W3C entries describe each
test as an HTTP exchange in Markdown inside `rdfs:comment`, and both
trees decode that text: the F\* runner through the extracted
`SPARQL.Protocol` / `SPARQL.GraphStore` / `SPARQL.ServiceDescription`
modules, the Lean harness through their ports
(`formal/lean4/L4Factoidal/SPARQL/Protocol.lean`, `GraphStore.lean`,
`ServiceDescription.lean`) driven by `Harness/ProtocolRun.lean`, which
reproduces `run_protocol_test`, `run_gsp_test` and
`run_service_description_test` clause for clause (manifest-shape glue
included: the `$GRAPHSTORE$` placeholder collapse, the entry-name
seeding with its `gsp_seeded` counter, the `mismatched payload` name
dispatch). Stage entry with the module correspondence, decisions and
findings: `formal/lean4/PORT_NOTES.md`, "Stage: SPARQL 1.1 Protocol,
Graph Store HTTP Protocol, Service Description".

Harness changes: `Manifest.lean` captures `rdfs:comment`; `Run.lean`
takes the per-manifest Graph Store (`IO.Ref`, created in `Main.lean`,
reset at `PUT - Initial state`) and adds the three arms as one block;
`HARNESS-DIAG` prints `gsp_seeded=N` (the F\* runner's `gsp_seed`).

### Measured score lines, verbatim

`lake exe l4w3c ../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`:

```
protocol: 34 pass, 0 fail, 0 skip, 0 unsupported (out of 34)
HARNESS-DIAG protocol: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=0 triples_compared=0 gsp_seeded=0
http-rdf-update: 19 pass, 0 fail, 0 skip, 0 unsupported (out of 19)
HARNESS-DIAG http-rdf-update: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=0 triples_compared=0 gsp_seeded=1
service-description: 3 pass, 0 fail, 0 skip, 0 unsupported (out of 3)
HARNESS-DIAG service-description: no_manifest=0 zero_tests=0 budget_exceeded=0 rows_compared=0 triples_compared=0 gsp_seeded=0
TOTAL: 601 pass, 0 fail, 0 skip, 30 unsupported (out of 631)
```

(Measured after merging `claude/main` with the SPARQL 1.1 Update
stage into the branch; before that merge the update-shaped protocol
entries were `unsupported` and the line read `protocol: 26 pass,
0 fail, 0 skip, 8 unsupported (out of 34)`.) The query types stay at
356 pass, 0 fail; the 30 unsupported are the OWL-Direct /
OWL-RDF-Based / RIF entailment-regime tests (after merging the
entailment stage from `claude/main` too; rdf-mt 39 pass, 0 fail (out
of 39)); the six RDF suites at
`TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported (out of 1078)`.
The F\* runner's lines for the same three suites
(`docs/test-results/latest.json`): protocol 34 pass, 0 fail (out of
34); http-rdf-update 19 pass, 0 fail (out of 19), `gsp_seed` 1;
service-description 3 pass, 0 fail (out of 3).

### FAIL / unsupported, by cause

No FAIL. No unsupported in the three suites. The update-shaped
entries (`update_dataset_*`, `update_post_form`, `update_post_direct`,
`update_base_uri`, `bad_update_syntax`) go through
`parseSparqlUpdate` / `applyUpdateIn` from the Update stage; only the
first request block of an UPDATE-then-ASK entry is decoded, as in the
F\* runner.

### Theorems (axioms: propext, Classical.choice, Quot.sound)

`percentDecode_percentEncode_ascii` / `urlDecode_percentEncode_ascii`
(decoding inverts encoding on every ASCII string: RFC 3986 reserved +
unreserved sets and `%`), `decodeRequest_get_no_query` (a GET without
`query=` is a 400-class verdict), `decodeTarget_malformed_graph` (a
GSP `graph=` that is not an IRI is 400). 134 `#guard`s in
`SPARQL/ProtocolTests.lean`, one per decoding rule, over the W3C
request shapes.

### Sabotage

1. `+` → space removed from percent-decoding: `lake build` fails at
   `ProtocolTests.lean:31` and `:56`. With those two guards disabled
   NO W3C protocol test flips: the manifest writes every space as
   `%20`, and its only `+` characters are in response media types.
   The guards are the only detector for that rule.
2. The §2.1.6 charset rule forced to accept everything:
   `bad_query_non_utf8` and `bad_update_non_utf8` flip to FAIL
   (`Expected 4xx but decode_request accepted (POST /sparql/; …)`).
   Before the Update merge the second landed in `unsupported` — a
   decoder regression on an update-shaped entry was invisible until
   the Update parser existed. Restored; the numbers above are from
   the restored build.

### Findings against the F\* (not fixed here)

- `formal/fstar/SPARQL.Protocol.fst:146–167` (`url_decode_chars`):
  `%XX` becomes codepoint XX, so `%C3%A9` decodes to `Ã©`, not `é`.
- `formal/fstar/SPARQL.Protocol.fst:509–533` (`chars_contains_word`):
  a prefix match not bounded by whitespace returns `false` instead of
  continuing the scan, so `INSERT { <withdraw> … } USING <g> …` is not
  seen to carry `USING` and the §2.2.4 conflict is missed.
- `CLAUDE.md` says "SPARQL Protocol reaching 53 pass, 0 fail";
  `latest.json` has 56 pass, 0 fail across the three suites.

## Status 2026-08-22 — "Tests that truly exercise an implementation" — measured (branch `lean4/differential`)

Two executables, both in `formal/lean4/lakefile.toml`'s default
targets, both run from the repository root:

- `formal/lean4/.lake/build/bin/l4diff [--fstar BIN] [--gen N] [--seed S] [manifest.ttl ...]`
  (`Harness/Differential.lean`) — the DIFFERENTIAL harness. Every
  `QueryEvaluationTest` / `CSVResultFormatTest` of the manifests given,
  plus `N` generated (graph, query) pairs, run through
  `bin/darwin-arm64/factoidal` (`-o json` for SELECT/ASK, `-o ntriples`
  for CONSTRUCT, via `IO.Process` under a `perl alarm` cap) AND through
  `parseSparql` + `evalSelect` / `evalAsk` / `evalConstruct` (the path
  `Harness/Run.lean` takes), compared with `Harness/Compare.lean`'s
  `compareSelectRows` (solution multisets under a blank-node bijection)
  and `Graph.isomorphicOutcome`. Per-suite outcomes: agree / disagree /
  tie-order / fstar-error / lean-error / skipped (named), with the
  rows-or-triples-compared measurement on every line. Exit 1 on any
  disagreement or error.
- `formal/lean4/.lake/build/bin/l4prop [--cases N] [--seed S]`
  (`Harness/PropProbe.lean`) — the PROPERTY probe over
  `L4Factoidal/Testing/Gen.lean` (pure, seeded: splitmix64 over `Nat`;
  graphs over a bounded vocabulary with plain, language-tagged and
  typed numeric literals; BGPs; a query grammar of BGP / OPTIONAL /
  FILTER-comparison-and-BOUND / UNION / MINUS with DISTINCT / ORDER BY /
  LIMIT, rendered as SPARQL text AND as the algebra AST) and
  `L4Factoidal/Testing/Props.lean` (18 invariants, each `Case → Option
  String`). Every failure prints the seed, the graph as N-Triples and
  the query; exit 1 on any failure. `L4Factoidal/Testing/GenTests.lean`
  pins determinism (same seed → same case; the exact rendering of two
  seeds; the splitmix64 reference output for seed 0) and the
  invariants on three fixed seeds, as build-time `#guard`s.

### Measured, verbatim

`l4diff --gen 500 --seed 0 third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`
(every per-suite line with at least one case; the other 19 suites are
all `skipped` — syntax, update, protocol types):

```
DIFF aggregates: 42 agree, 0 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 5 skipped (out of 47); rows_or_triples_compared=176
DIFF bind: 10 agree, 0 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 10); rows_or_triples_compared=60
DIFF bindings: 10 agree, 0 disagree, 0 tie-order, 1 fstar-error, 0 lean-error, 0 skipped (out of 11); rows_or_triples_compared=44
DIFF cast: 3 agree, 3 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 6); rows_or_triples_compared=372
DIFF construct: 3 agree, 0 disagree, 0 tie-order, 2 fstar-error, 0 lean-error, 2 skipped (out of 7); rows_or_triples_compared=16
DIFF csv-tsv-res: 6 agree, 0 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 6); rows_or_triples_compared=76
DIFF exists: 5 agree, 0 disagree, 0 tie-order, 1 fstar-error, 0 lean-error, 0 skipped (out of 6); rows_or_triples_compared=14
DIFF functions: 65 agree, 10 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 75); rows_or_triples_compared=569
DIFF grouping: 4 agree, 0 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 2 skipped (out of 6); rows_or_triples_compared=18
DIFF json-res: 4 agree, 0 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 4); rows_or_triples_compared=26
DIFF negation: 12 agree, 0 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 12); rows_or_triples_compared=84
DIFF project-expression: 7 agree, 0 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 7); rows_or_triples_compared=24
DIFF property-path: 31 agree, 0 disagree, 0 tie-order, 2 fstar-error, 0 lean-error, 0 skipped (out of 33); rows_or_triples_compared=137
DIFF service: 0 agree, 1 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 6 skipped (out of 7); rows_or_triples_compared=2
DIFF subquery: 13 agree, 1 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 14); rows_or_triples_compared=99
DIFF sparql11 (all): 215 agree, 15 disagree, 0 tie-order, 6 fstar-error, 0 lean-error, 395 skipped (out of 631); rows_or_triples_compared=1717
DIFF generated (500 cases from seed 0): 497 agree, 3 disagree, 0 tie-order, 0 fstar-error, 0 lean-error, 0 skipped (out of 500); rows_or_triples_compared=461
DIFF TOTAL: 712 agree, 18 disagree, 0 tie-order, 6 fstar-error, 0 lean-error, 395 skipped (out of 1131); rows_or_triples_compared=2178
```

The 395 skipped: 319 entries whose type is not a query evaluation
test (syntax, update, protocol), 70 entailment-regime entries (the
CLI is not driven with `--entail`), 6 SERVICE tests that need
`qt:serviceData` (the CLI has no such form). Nothing is skipped
silently: every skip line names its reason.

`l4prop --cases 500 --seed 0` (and again with `--seed 1000`: 500
cases, 0 failures, 495 BGP rows):

```
PROP bgp_mono: 500 pass, 0 fail (out of 500)
PROP join_comm: 500 pass, 0 fail (out of 500)
PROP union_append: 500 pass, 0 fail (out of 500)
PROP minus_subset: 500 pass, 0 fail (out of 500)
PROP filter_subset: 500 pass, 0 fail (out of 500)
PROP distinct_idem: 500 pass, 0 fail (out of 500)
PROP orderby_perm: 500 pass, 0 fail (out of 500)
PROP ntriples_roundtrip: 500 pass, 0 fail (out of 500)
PROP turtle_roundtrip: 500 pass, 0 fail (out of 500)
PROP srx_roundtrip: 500 pass, 0 fail (out of 500)
PROP srj_roundtrip: 500 pass, 0 fail (out of 500)
PROP csv_roundtrip: 500 pass, 0 fail (out of 500)
PROP tsv_roundtrip: 500 pass, 0 fail (out of 500)
PROP rdfc_relabel: 500 pass, 0 fail (out of 500)
PROP iso_reflexive: 500 pass, 0 fail (out of 500)
PROP iso_relabel: 500 pass, 0 fail (out of 500)
PROP query_parses: 500 pass, 0 fail (out of 500)
PROP distinct_no_dup: 500 pass, 0 fail (out of 500)
PROP TOTAL: 500 cases, 0 failures; measurement: 3229 triples generated, 514 BGP rows evaluated
```

### Findings, with attribution (none "fixed" in the comparator)

Each disagreement was attributed by reading the specification and,
for the W3C entries, the expected-result file. "F\* CLI" means
`bin/darwin-arm64/factoidal` as driven here; where the F\* W3C runner
(`bin/darwin-arm64/w3c_runner`) scores the same test as a pass, the
reason is stated.

1. **Lean bug, FIXED in this landing — CONSTRUCT sliced the UNORDERED
   solution sequence** (generated seeds 169 and 324: `CONSTRUCT …
   ORDER BY … LIMIT n`). `evalConstruct` applied `sliceSolutions`
   without `sortSolutions`; §18.2.4 builds OrderBy then Slice for every
   query form. Fixed in `SPARQL/Query.lean`, pinned by a `#guard` in
   `SPARQL/QueryTests.lean` (`DESC(?label) LIMIT 1` drives the template
   with bob). The two seeds STILL disagree after the fix because —
2. **F\* bug — `eval_construct_query` also slices the unordered
   sequence.** Repro (seed 169): the same query as `SELECT * … ORDER BY
   ?x ?y ?z LIMIT 1` returns the row `?x=_:b2 ?y=_:b1`, but the
   CONSTRUCT output is EMPTY; seed 324: the SELECT `LIMIT 3` returns
   `s2, s1, s1` rows, the CONSTRUCT emits a triple for the `_:b1` row
   instead of one `s1` row. The same omission in both trees; they
   disagreed only because their unordered evaluation orders differ.
3. **F\* bug — ASK with a repeated variable in one triple pattern**
   (generated seed 115): `ASK { ?x <q> ?x }` answers `true` on a graph
   with no such triple, while `SELECT * { ?x <q> ?x }` on the same
   graph returns no row. Same answer through both CLI evaluation
   paths (`--entail none` forces `SPARQL11_Algebra.eval_ask_query`).
   Lean: `false`. §16.3: ASK is true iff the pattern has a solution.
4. **F\* evaluator: SELECT expressions that must be ERRORS (unbound)
   are bound** — `functions`: `STRDT()` (`STRDT("bar"@en, xsd:string)`
   → `"bar"`; expected unbound), `STRDT() TypeErrors`, `CONCAT() 2`
   (`CONCAT(7, 7)` → `"77"^^xsd:integer`), `IF() error propogation`
   (`IF(1/0, …)` → `true`; expected unbound), `STRBEFORE()` /
   `STRAFTER()` (on `"DEF"^^xsd:string`), `STRBEFORE() datatyping` /
   `STRAFTER() datatyping` (`STRBEFORE("abc", "b"@cy)` → `"a"`; §17.4.3
   argument compatibility says error), `REPLACE()` (on an integer);
   `cast`: `xsd:boolean` / `xsd:integer` / `xsd:decimal` (extra or
   differing cast results, e.g. `xsd:decimal("+33.3300")` → Lean
   `"33.33"`, F\* no binding; `xsd:integer("1.5")` → F\* `1`). Lean's
   rows match the W3C `.srx` files (the Lean harness scores all of
   these as PASS). **Why the F\* W3C runner reports them as PASS:**
   `bin/w3c-runner/w3c_runner.ml:741–752` `binding_row_matches_with`
   checks that every EXPECTED binding is present in the actual row and
   ignores EXTRA actual bindings, so a row that should have an unbound
   variable passes when the engine binds it. The Lean comparator
   (`Harness/Compare.lean` `domainsEqual`) requires equal domains.
   This is a comparator leniency in the F\* runner hiding evaluator
   bugs; 13 of the 15 W3C disagreements are of this kind.
5. **F\* CLI — `SERVICE SILENT <unreachable>` yields no solutions**
   (`service` test 7: expected 2 rows with `?o2` unbound, F\* 0 rows,
   Lean 2 rows; SPARQL 1.1 Federated Query §2.3 — SILENT makes the
   failed SERVICE a single empty solution). The F\* runner passes the
   test through its own SERVICE handling; not chased further here.
6. **F\* CLI — `GRAPH ?g { ?x ?p ?g }` does not constrain the inner
   `?g` to the graph name** (`subquery` sq02: expected 1 row, F\* 2,
   Lean 1; also reproduced WITHOUT the sub-select). §18.6: the graph
   name binding must be compatible with the inner solution. The F\*
   runner passes sq02; its named-graph loading differs from the CLI's
   `-n IRI=FILE` and was not chased.
7. **F\* CLI — `UUID()` returns the same value for two BINDs in one
   query** (`functions` uuid02, ASK `FILTER(?u1 != ?u2)`: F\* false,
   Lean true, expected true). Both CLI paths.
8. **F\* CLI — CONSTRUCT with an RDF collection in the template emits
   an invalid blank-node label**: `_:tpl_0__:bnode_13 <…> <…> .` in
   `-o ntriples` output (`construct` "CONSTRUCT list"; counted as
   `fstar-error` because the output is not N-Triples). The template's
   list blank node keeps its `_:` prefix inside the label the
   per-solution freshening builds.
9. **F\* CLI has no query BASE** (5 `fstar-error`s: `bindings`
   "VALUES inside GRAPH …" `<empty.ttl>`, `construct`where04 `FROM
   <data.ttl>`, `exists`02 `graph <exists02.ttl>`, `property-path`
   pp34/pp35 `<ng-01.ttl>`): `factoidal_cli.ml` calls `parse_sparql
   query_text` with no base, and `-b` rebases only the data files
   (tried: it did not reach the parser and it broke one exists test
   by moving the data base). Harness-visible CLI limitation, not an
   engine finding; the W3C runners of both trees pass the query's
   file IRI as base.
10. **Spec ambiguity, recorded, not decided — zero-column CSV/TSV.**
    A `SELECT` result with NO variables serialises to an empty header
    line; `parseCsv` / `parseTsv` reject it as "empty input (no header
    line)". RFC 4180 reads an empty line as one empty field; the
    CSV/TSV format §2 says the header lists the variable names. The
    CSV and TSV round-trip properties are therefore stated for results
    with at least one variable (`Case.hasVars`).
11. **Comparator observation (kept as is):** `compareSelectRows`'s
    numeric leniency (`numericLiteralEqual`: same numeric datatype,
    equal value) means a lexical-form-only difference such as `"1E0"`
    vs `"1.0E0"^^xsd:double` counts as agreement. The W3C expected
    files need this; it is named here so nobody reads "agree" as
    "byte-identical".

### Sabotage

Two sabotages, each applied to the restored tree, with ONLY the two
probe executables rebuilt (`lake build l4prop l4diff`) so the library's
own `#guard`s and theorems could not stop the build first; then the
full `lake build` was run to see whether the library catches it too;
then `git checkout --` and a green rebuild (261 jobs).

1. **`insertOrdered` drops a row that ties with the one it is
   inserted next to** (`SPARQL/Query.lean`):
   - `l4prop`: exit 1, `PROP orderby_perm: 497 pass, 3 fail (out of
     500)`, the other 17 invariants unchanged; first repro printed:
     seed 207, the ORDER BY output missing two tied rows.
   - `l4diff`: `sparql11 (all): 214 agree, 16 disagree` (one more than
     the baseline 15) — the generated 500 stayed at 3 because generated
     ORDER BY covers all three variables, so ties are between identical
     rows only.
   - full `lake build`: FAILS — `QueryTheorems.lean:283` (the
     `sortSolutions_perm` proof no longer type-checks) and
     `QueryTests.lean:379` (a `#guard`).
2. **`tryBindTerm` ignores an existing binding of a repeated
   variable** (`SPARQL/Algebra.lean`: `?x <q> ?x`, or `?s :p ?o . ?t
   :q ?o`, match regardless of what `?x` / `?o` already holds — the
   class of bug finding 3 above is in the F\* tree):
   - `l4prop`: exit 0, 0 failures — NOT caught. The algebra laws are
     relative (monotonicity, commutativity, subset) and a uniformly
     wrong matcher satisfies them; the round trips and canonicalisation
     do not touch matching. Recorded as a limit of property testing
     without an oracle.
   - `l4diff`: exit 1, `generated (500 cases from seed 0): 403 agree,
     97 disagree` (baseline 3) and `sparql11 (all): 214 agree, 16
     disagree` (baseline 15; the W3C queries rarely repeat a variable
     in a predicate or object position).
   - full `lake build`: **PASSES** — none of the library's 966 `#guard`s
     and no theorem constrains a repeated variable in the object or
     predicate position. Two `#guard`s were added to
     `L4Factoidal/Tests.lean` after this run (`?x :name ?x` and
     `?s :name ?n . ?s :age ?n` both yield no row on the fixture), so
     the library build now catches this class as well.

Both sabotages were restored; the numbers in "Measured, verbatim"
above are from the restored build.
