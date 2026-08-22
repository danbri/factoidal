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
| EXISTS hook limits: active graph inside `GRAPH`, and an EXISTS nested in an EXISTS body (lowered with `emptyEnv` at parse time) | 2: `Exists within graph pattern`, `Nested positive exists` | `SPARQL/Exists.lean` header; `Parser.lean:79` AST-gap note |
| `CONCAT` argument compatibility (non-string / mixed-language arguments must error) | 1: `CONCAT() 2` | `Expr.lean:1325` |
| `IF(1/0, …)`: an error in the condition must propagate, not read as false | 1 | `Expr.lean:1267` |
| `IRI("rel")` needs the query BASE (`EvalEnv` carries none; F\* passes `q.q_base`) | 1 | `Expr.lean:1231` |
| `SECONDS()` returns `"01"` where `"1"` (canonical decimal) is expected | 1 | `Expr.lean:1389` |

None of these was changed in this branch (the brief: list, do not
fix). Each group is a separate issue candidate.
