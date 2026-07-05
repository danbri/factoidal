# Project scope — what factoidal does and does not cover

Companion to `CLAUDE.md`. Lists features that are explicitly **not planned**
so future agents (and humans) don't burn cycles attempting them.

## In scope

- RDF 1.1 abstract syntax + all core serialisations (N-Triples, Turtle,
  N-Quads, TriG, RDF/XML, JSON-LD).
- SPARQL 1.1 Query, Update, Protocol, federated `SERVICE`.
- SPARQL 1.1 result formats (XML/SRX, JSON, CSV, TSV).
- RDF model theory / RDFS entailment (forward-chaining closure in F\*).
- OWL 2 RL entailment (rule-based subset, F\* closure rules).
- OWL DL via `OWL.QueryRewrite` rewriter for queryable fragments
  (`someValuesFrom`, `allValuesFrom`, `unionOf`, `intersectionOf`,
  cardinality CEs) — best-effort, not full DL classification.
- RIF Core — the frame/BGP-shaped rule-body subset exercised by the
  4 vendored W3C RIF test cases plus the applicable subset of the
  full vendored Core dialect corpus (see below), verified in
  `RIF.Core.Syntax.fst` / `RIF.Core.Translation.fst` /
  `RIF.Core.Eval.fst` + `Parser.RIFXML.fst`, driven end-to-end by
  `bin/rif-runner/rif_runner.ml`.

## Out of scope — not planned

### RIF Core (Rule Interchange Format) — supported subset only

RIF Core is a full production-rule language; factoidal implements only
the fragment the 4 vendored W3C RIF test cases exercise: `Forall` /
`Frame` / `And` / `Implies` rule bodies translated to SPARQL BGPs
(`RIF.Core.Translation.fst`), forward-chaining fixpoint saturation
(`RIF.Core.Eval.fst`), and single `<Import>` companion-graph
resolution (with OWL-Direct closure applied first when the import's
own `<profile>` declares it — see `bin/rif-runner/rif_runner.ml`'s
`apply_import_closure`). General RIF-BLD (built-ins, list terms,
`External` function calls) and RIF-PRD (production rules, actions,
retraction) are **not implemented** and not planned.

**Concretely:** the 4 RIF tests under
`third_party/testing/w3c/sparql/sparql11/entailment/` (manifest IRIs
`:rif01 :rif03 :rif04 :rif06`, all tagged `sd:entailmentRegime ent:RIF`)
now PASS, measured via `bin/rif-runner/rif_runner.ml` (4 pass, 0 fail
out of 4, 2026-07-04):

- `:rif01` — RIF Logical Entailment (referencing RIF XML).
- `:rif03` — RIF Core WG tests: Frames.
- `:rif04` — RIF Core WG tests: Modeling Brain Anatomy (the imported
  ontology needs OWL-Direct closure — `owl_rl_closure_with_reflexivity`
  + `Tableau.tableau_materialise` — before the rule body's
  `rdf:type MaterialAnatomicalEntity` check matches individuals the
  ontology only asserts via `rdf:type Gyrus` + `rdfs:subClassOf`).
- `:rif06` — RIF Core WG tests: RDF Combination Blank Node.

Any RIF document whose rule bodies or imports fall outside the
frame/BGP + single-`<Import>` shape above is out of scope; a runner
encountering one should report an honest FAIL/SKIP with a diagnosis,
not force a PASS.

**Full Core dialect corpus (2026-07-05):** `bin/rif-runner/rif_runner.ml`
also walks the complete official W3C RIF Core dialect test
distribution vendored at `third_party/testing/rif-core-suite/`
(46 tests — see that directory's `README.md` for source/license/
inventory, and `bin/rif-runner/README.md` for the full pipeline,
score, and skip-bucket table). Measured: **7 pass, 3 fail, 36 skip
(out of 46)**; combined with the 4 tests above, **11 pass, 3 fail,
36 skip (out of 50)**. The skips are almost entirely RIF-BLD
built-ins (`External`, 16 tests) and the genuine RIF Core constructs
this project does not implement (`Equal`, `Exists`, `List` — 4
tests combined) plus the syntax-safeness/import-rejection test
categories (12 tests, no dialect-conformance validator exists). The
3 FAILs are diagnosed, not swept under a SKIP: 2 are real
construct/semantics gaps (`rdf:PlainLiteral` language-tag decoding
in `Parser.RIFXML.fst`'s `const_from_type`; OWL-Direct semantics has
no ontology-annotation-triple exclusion step before RIF rule bodies
evaluate against an imported graph) and 1 is a data defect in the
official `Core_v1.22.zip` distribution itself (a malformed
`xsd:string` datatype IRI in `RDF_Combination_Constant_Equivalence_4`'s
vendored import files, present since the test was authored in 2010).
None of the 3 are fixed here — all three need F\* edits, out of
scope for the PR that added the corpus walker; see
`bin/rif-runner/README.md` for the per-test detail.

### Full OWL DL tableau classifier

The `Tableau.fst` module sketches stages (a)–(e) but a complete
DL tableau (skolemisation, disjunction blocking, complementOf
contrapositive, fresh-individual witnesses) is not the project goal.
Specific DL-only entailment tests (`paper-sparqldl-Q3`, the OWL 2 RL
fp/ifp-differentFrom contrapositive cases) are tracked in #58 and the
OWL-RL triage doc but are not in the current critical path.
`WebOnt-I5.26-010` is tracked separately below (comprehension
entailment, not a tableau gap).

### OWL 1 Full comprehension-principle entailments — WebOnt-I5.5-005, WebOnt-I5.26-010

These are the 2 permanent failures in the `profile-RL.rdf` /
`profile-EL.rdf` / `profile-QL.rdf` PositiveEntailmentTest catalogs
(27 pass, 2 fail of 29 RDF/XML tests, as of 2026-07-05; see
`bin/owl-runner/owl_runner.ml`). Re-derived and confirmed 2026-07-05
against the catalog's own `test:description` text (both tests carry
`test:species FULL` and `test:species DL` alongside `RL`/`EL`/`QL`
profile tags — the W3C catalog cross-lists them for profile
identification even though the entailment itself is an OWL 1 Full
phenomenon):

- **WebOnt-I5.5-005.** Premise: `Class(a)` (bare class declaration,
  nothing else). Conclusion: `_:b owl:unionOf (a)` — an anonymous
  class equal to `ObjectUnionOf(a)` exists. Catalog description,
  verbatim: *"This test exhibits the effect of the comprehension
  principles in OWL Full. The conclusion ontology only contains a
  class declaration, ObjectUnionOf class expression does not appear
  in an axiom."*
- **WebOnt-I5.26-010.** Premise: `ObjectProperty(p)` (bare property
  declaration, nothing else). Conclusion:
  `_:n owl:onProperty p ; owl:minCardinality 1 ; rdf:type
  owl:Restriction` — the restriction `p minCardinality 1` exists as a
  class expression. Catalog description, verbatim: *"This is
  trivially true given that first:p is an individualvaluedPropertyID"*
  — "trivially true" refers to OWL Full's comprehension guarantee
  that every describable class/property expression denotes something,
  not to any RDF-level derivation.

**Why neither is a missing RL rule or a matcher bug.** Both premises
assert nothing about any individual, and neither premise graph
contains a `unionOf`/`Restriction`/`onProperty`/`minCardinality`
triple naming a bnode the conclusion could structurally match — the
conclusion asserts the *bare existence* of a class expression node
with no premise-side antecedent to hang a Horn rule off of. OWL 1
Full's comprehension conditions (informally: "for every describable
class expression, some resource denotes it") guaranteed these
entailments; OWL 2's RDF-Based Semantics demoted comprehension to an
*informative, non-normative* appendix, and OWL 2 RL's PR1 completeness
theorem was never proved over bnode-only conclusions in the first
place (RL is a Horn/Datalog fragment: every rule has a premise-side
antecedent pattern, and comprehension entailments have none). No sound
Horn rule over `{Class(a)}` or `{ObjectProperty(p)}` alone produces
these triples — anything that did would have to fire on literally
every named class/property in every graph, unconditionally, since
there is nothing else in the premise to gate on.

**A "fix" would be a triple generator, not a semantic rule**: for
every named class C, unconditionally emit a singleton-`unionOf`
scaffold (`_:x owl:unionOf (C)` + the `rdf:List` triples, 4 triples);
for every named object property P, unconditionally emit a
`minCardinality 1` restriction scaffold (`_:y owl:onProperty P ;
owl:minCardinality 1 ; rdf:type owl:Restriction`, 3 triples). This is
not the `owl_rule_named_equivClass_to_sameAs`-style narrow rewrite
(CLAUDE.md "Known sound-but-narrow rewrites") because it has no guard
condition to narrow — the trigger is "class exists" / "property
exists" with no other premise fact required, so it manufactures the
same junk triples on **every** graph unconditionally, growing every
closure regardless of whether the query at hand cares about
comprehension at all (the opposite of the #262 closure-size
direction, and unlike the sound-but-narrow rewrite it has no sibling
NegativeEntailmentTest keeping it in check — nothing would ever make
these two scaffolds NOT fire).

**Disposition: intentionally not implemented, permanent scope
exclusion.** Do not attempt an anchor/scaffold hack to pass these two
— re-verify this reasoning (does the premise gain a real antecedent
fact in a future catalog revision? does OWL 2 RL gain a comprehension
rule in a future profile revision?) before revisiting, but as of the
OWL 2 RL/RDF specification these are out of scope. If a future OWL 1
Full compatibility mode is ever built as its own opt-in regime
(distinct from OWL 2 RL/Direct), the generator shape above is the
starting point and must itself be documented as a comprehension-mode
rewrite, gated so it never leaks into the OWL 2 RL/Direct closures
scored by the floors in `skills/test-suites/SKILL.md`.

### Non-monotonic / negation-as-failure inference

Tests requiring NaF (e.g. WebOnt fixed-point complementOf) are
monotonically unreachable by OWL-RL closure and out of scope for any
Datalog-style closure loop. Tracked in #58.

### XSD facet semantics beyond datatype subClass hierarchy

The XSD numeric subClass hierarchy (`xsd:byte ⊑ xsd:short ⊑ xsd:int ⊑
xsd:integer` etc.) is in scope as built-in axioms.
Facet-level reasoning (e.g. `xsd:nonNegativeInteger ∩
xsd:nonPositiveInteger ⊑ xsd:short`) is not.

## Update protocol

When a scope decision changes (in either direction), update this file
**in the same commit** that introduces the new feature or removes the
last code path supporting the dropped one. Do not let the doc drift.
