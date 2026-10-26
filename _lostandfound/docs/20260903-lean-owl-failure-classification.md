# Lean OWL probe: classification of the 316 default-regime failures

Measured 2026-09-03. `l4owl-probe` is `formal/lean4/Harness/OwlProbe.lean`,
built at `formal/lean4/.lake/build/bin/l4owl-probe`. All commands ran from
the repository root, because the probe resolves catalog paths relative to
the working directory (run from `formal/lean4/` it prints "manifest not
found" style diagnostics while still returning an exit code).

No verdict was changed to produce this document. No manifest, catalog, or
`.lean` file was edited. This is a measurement and classification report
only.

## Commands and totals

Six catalogs (`profile-RL.rdf profile-QL.rdf profile-EL.rdf
type-positive-entailment.rdf type-inconsistency.rdf type-consistency.rdf`)
are the probe's own default set (`OwlProbe.catalogs`) and are the scope of
the CAUSE table below, because this is the set the task's 316-failure
figure was measured against.

```
cd <repo root>
./formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
```
TOTAL: 1131 pass, 316 fail, 2 skip, 8 unsupported (out of 1457)

```
./formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl
```
TOTAL: 1208 pass, 239 fail, 2 skip, 8 unsupported (out of 1457)

This 1208/239 figure differs from the value named as "previously measured"
in `Harness/OwlProbe.lean`'s `--refute-budget` table (1177 pass, 270 fail).
Re-running the identical command today gives 1208/239, not 1177/270. The
difference is 31 tests. No `.lean` file that the closure or refuter touches
changed in this worktree before the run (`lake build` succeeded with no
Lean edits). The most likely explanation is that the "previously measured"
figure predates a landed improvement and was not updated; this document
does not chase that further because it is out of scope for a failure
classification of the CURRENT default-regime total, but it should be
corrected in `Harness/OwlProbe.lean`'s own comment in a future landing.

## Per-catalog breakdown

All ten catalog files named in the task. The middle six are the probe's
default set; the last four needed an explicit catalog list
(`l4owl-probe --dir third_party/testing/owl <files...>`). Catalog-level
scores are identical whether a catalog is scored alone or alongside others
(verified: the six-catalog run and a ten-catalog run agree to the digit on
every shared catalog), because each catalog is judged independently.

| Catalog | Default: N pass, M fail, skip, unsupported (out of T) | `--dl`: N pass, M fail, skip, unsupported (out of T) |
| --- | --- | --- |
| profile-RL.rdf | 117 pass, 9 fail, 0 skip, 0 unsupported (out of 126) | 118 pass, 8 fail, 0 skip, 0 unsupported (out of 126) |
| profile-QL.rdf | 82 pass, 5 fail, 0 skip, 0 unsupported (out of 87) | 83 pass, 4 fail, 0 skip, 0 unsupported (out of 87) |
| profile-EL.rdf | 102 pass, 18 fail, 1 skip, 0 unsupported (out of 121) | 110 pass, 10 fail, 1 skip, 0 unsupported (out of 121) |
| syntax-dl.rdf | 282 pass, 137 fail, 1 skip, 4 unsupported (out of 424) | 339 pass, 80 fail, 1 skip, 4 unsupported (out of 424) |
| semantics-direct.rdf | 514 pass, 191 fail, 1 skip, 4 unsupported (out of 710) | 578 pass, 127 fail, 1 skip, 4 unsupported (out of 710) |
| type-consistency.rdf | 485 pass, 94 fail, 0 skip, 4 unsupported (out of 583) | 485 pass, 94 fail, 0 skip, 4 unsupported (out of 583) |
| type-inconsistency.rdf | 30 pass, 97 fail, 1 skip, 0 unsupported (out of 128) | 94 pass, 33 fail, 1 skip, 0 unsupported (out of 128) |
| type-positive-entailment.rdf | 315 pass, 93 fail, 0 skip, 4 unsupported (out of 412) | 318 pass, 90 fail, 0 skip, 4 unsupported (out of 412) |
| type-negative-entailment.rdf | 46 pass, 0 fail, 0 skip, 0 unsupported (out of 46) | 46 pass, 0 fail, 0 skip, 0 unsupported (out of 46) |
| RL-RDF-rules-tests.rdf | 0 pass, 0 fail, 0 skip, 0 unsupported (out of 0) | 0 pass, 0 fail, 0 skip, 0 unsupported (out of 0) |

Sum of the six default-set rows: 1131 pass, 316 fail (out of 1457) — matches
the task's stated baseline exactly.

`RL-RDF-rules-tests.rdf` has zero `test:TestCase` elements. This is not a
probe defect: the file (24 lines) is a query export stub — an
`owl:Ontology` header, one `owl:AnnotationProperty` declaration, and an
HTML comment recording the wiki query that was supposed to populate it
("Test case export for query ... [[Category:RL RDF rules test]] ..."). The
export produced no rows. `type-negative-entailment.rdf` is fully passing in
both regimes (46/46): its verdict condition is an absence check, and the
RL closure already omits everything these 23 cases require to stay absent.

## CAUSE table (the 316 default-regime failures, 315 `closure-gap` + 1 `parser`)

Method: every `FAIL <case> [<type>]: <reason>` line from the six-catalog
default run was extracted (`FAIL-GROUP` already groups by the probe's own
coarse tag — `closure-gap` for 315 of 316, `parser` for 1). Each of the 190
distinct failing case identifiers was then classified against evidence:
its own `test:description` text and premise/conclusion RDF/XML read from
the catalog files, the specific missing/unexpected triple printed in the
`FAIL` reason line, and the documented NOT-ported lists in
`RLClosure.lean`'s and `RLRules.lean`'s own header comments (which name
most of these gaps already, by W3C row id). Counts are (case, test-type)
units, matching the probe's own denominator; a case appearing in more than
one catalog or under more than one test type is counted once per unit.

| # | Cluster | Units | Example test ids | Missing capability |
| - | --- | --- | --- | --- |
| 1 | Full DL / tableau completeness | 108 | WebOnt-description-logic-008, WebOnt-description-logic-909, Consistent-but-all-unsat, New-Feature-BottomObjectProperty-001, WebOnt-I5.24-002 | The RL/RDF rule set is sound but incomplete for OWL DL; these premises need the tableau refuter (`--dl`), and a documented budget ceiling on the refuter still leaves about a quarter of this cluster undecided even then. |
| 2 | OWL Full / RDF-Based meta-axioms and comprehension | 54 | WebOnt-Class-001, WebOnt-Thing-003, WebOnt-unionOf-002, WebOnt-AnnotationProperty-002, WebOnt-I5.5-005 | Fixed RDF-Based-Semantics meta axioms (e.g. `rdfs:Class rdf:type owl:Class`) and OWL-Full-style class-expression comprehension are in the engine's documented `[mode]`/comprehension-witness gap, not ported. |
| 3 | Built-in vocabulary axiom triples missing | 26 | rdfbased-sem-prop-comment-type, rdfbased-sem-prop-label-type, WebOnt-I5.5-001, WebOnt-I5.5-002, WebOnt-imports-010 | `RLClosure.lean`'s `axiomTriples` has only `owl:Thing`/`owl:Nothing` typing and the XSD datatype axioms; it is missing the fixed triples typing `rdfs:comment`/`rdfs:label`/`rdfs:seeAlso`/`rdfs:isDefinedBy`/`owl:deprecated`/`owl:versionInfo`/`owl:backwardCompatibleWith`/`owl:incompatibleWith`/`owl:priorVersion` as `owl:AnnotationProperty`, `rdf:first`/`rdf:rest` as `owl:FunctionalProperty`, and `owl:imports` domain/range. |
| 4 | Datatype value-space reasoning (Table 7) | 25 | Plus and Minus Zero are Distinct, Datatype-Float-Discrete-001, Inconsistent Byte Filler, string-integer-clash, Contradicting-dateTime-restrictions | Table 7's `dt-type1`/`dt-type2`/`dt-eq`/`dt-diff`/`dt-not-type` rows quantify over a datatype's value space; this port (like the F* engine) fixes no datatype map, so none of these rows fire. |
| 5 | Restriction/cardinality existential-witness comprehension | 20 | bnode2somevaluesfrom, somevaluesfrom2bnode, WebOnt-Restriction-001, WebOnt-Restriction-006, WebOnt-disjointWith-010 | The comprehension-witness `[ext]` layer that mints a blank node or individual (`svf2_existential_witness`, `minc1_bridge`) to WITNESS a `someValuesFrom`/`minCardinality` restriction is not ported — minting a fresh node under a proved-terminating naming scheme was named and deferred. |
| 6 | `owl:AllDifferent`/`owl:AllDisjointProperties` over a member list | 19 | WebOnt-AllDifferent-001, WebOnt-distinctMembers-001, New-Feature-DisjointObjectProperties-002, New-Feature-DisjointDataProperties-002, rdfbased-sem-ndis-alldisjointproperties-fw | `eq-diff2`, `eq-diff3`, `prp-adp`, `cax-adp` — the LIST-walking clash/derivation rows for `owl:AllDifferent`/`owl:AllDisjointProperties` — are named as not-ported (same shape as the ported `cax-adc` for `owl:AllDisjointClasses`, omitted only for size). |
| 7 | Qualified-cardinality deriving rows and the `owl:cardinality` shorthand | 15 | New-Feature-DataQCR-001, New-Feature-ObjectQCR-001, WebOnt-cardinality-001, WebOnt-cardinality-004, rdfbased-sem-restrict-maxqcr-inst-obj-one | `cls-maxqc3`/`cls-maxqc4` (the qualified-cardinality DERIVING rows — their two CLASH siblings `cls-maxqc1`/`cls-maxqc2` are ported) are not ported, and there is no rule desugaring `owl:cardinality` into the `owl:minCardinality`+`owl:maxCardinality` pair it is shorthand for. |
| 8 | Functional/InverseFunctional property edge cases | 12 | WebOnt-FunctionalProperty-003, WebOnt-InverseFunctionalProperty-003, functionality-clash | Two distinct sub-gaps: `inverseOfDomRngFlipFor` flips domain/range across `owl:inverseOf` but nothing flips the FUNCTIONAL/INVERSE-FUNCTIONAL property CHARACTERISTIC itself across an `owl:inverseOf` pair; and `prp-fp`/`prp-ifp` clash detection needs datatype VALUE equality on literals (`"1"^^xsd:int` vs `"1"^^xsd:integer`), which `OwlProbe.lean`'s own header names as not ported. |
| 9 | Restriction-comparison schema rows (Table 8) | 10 | rdfbased-sem-restrict-allvalues-cmp-class, rdfbased-sem-restrict-allvalues-cmp-prop, rdfbased-sem-restrict-hasvalue-cmp-prop, rdfbased-sem-restrict-somevalues-cmp-prop | `scm-op`, `scm-dp`, `scm-hv`, `scm-svf1`, `scm-svf2`, `scm-avf1`, `scm-avf2` — the five-premise restriction-comparison rows — have no `owl_rule_*` in the F* engine's own ledger either, so this is a gap shared by both trees, not a Lean-behind-F* one. |
| 10 | `owl:hasKey` edge cases | 8 | New-Feature-Keys-001, New-Feature-Keys-002, New-Feature-Keys-006 | `prp-key` (`prpKeyFor`) is ported and fires on the basic shape; these three still fail (missing `owl:sameAs` merges), which needs a closer read of the premise than this pass had time for — flagged as an open question rather than asserted with certainty. |
| 11 | `owl:hasSelf` | 7 | New-Feature-SelfRestriction-001, New-Feature-SelfRestriction-002, Footnote-not-about-self | `cls-hasself1`/`cls-hasself2-synth` (the self-restriction forward and synthesis rows) are named as not ported in the comprehension-witness `[ext]` list. |
| 12 | Direct-Semantics annotation exclusion filter | 5 | WebOnt-I4.6-005-Direct | See "Believed wrongly scored" below — this is a harness/filter defect candidate, not a reasoning gap. |
| 13 | Property-chain deriving direction | 4 | New-Feature-ObjectPropertyChain-BJP-002 | The ported `chainToTrans` derives transitivity FROM a self-chain axiom; this test needs the reverse — synthesizing a fresh RDF LIST node (`_:owlfs_chain0 rdf:first p`) to WITNESS that a `TransitiveProperty` entails an equivalent `owl:propertyChainAxiom`. Skolem-LIST witnesses are explicitly out of scope of the current port (`RLClosure.lean` line 33: "any witness needing a skolem LIST rather than a single skolem node"). |
| 14 | `owl:disjointUnionOf` | 2 | New-Feature-DisjointUnion-001 | No row anywhere in `RLClosure.lean`/`ClassExpr.lean`/`Vocabulary.lean` references `owl:disjointUnionOf`; the construct is not read at all. |
| — | RDF/XML parse failure | 1 | FS2RDF-literals-ar | See "Believed wrongly scored" — checked and found CORRECT, not a defect. |

108+54+26+25+20+19+15+12+10+8+7+5+4+2+1 = 316.

Clusters 5 and 7 both trace to the same undated `[ext]` comprehension-witness
family in `RLRules.lean` (`svf2_existential_witness`, `minc1_bridge`,
`cls_maxqc_comp`); they are kept separate because their SYMPTOM differs
(existential witness for `someValuesFrom`/`minCardinality` vs. a derived
`sameAs`/type fact for qualified cardinality), and a fixer would likely
land them as separate commits.

## Cost to close, per cluster

All Lean paths are under `formal/lean4/L4Factoidal/OWL/`; all F* paths
under `formal/fstar/`.

1. **Full DL / tableau completeness.** Lean already has the tableau:
   `Tableau.lean`, `Refute.lean`, `CountingOracle.lean`, invoked via
   `--dl --refute-budget N` (default 64). `Harness/OwlProbe.lean`'s own
   measurement table says raising the budget past 64 closes nothing more
   on `type-inconsistency.rdf` ("the remaining 35 need rules, not
   budget"). F* has the same architecture (`Tableau.fst`,
   `Tableau.Refute.fst`, `Tableau.CountingOracle.fst`) and scores higher
   on this catalog (126/127 vs. Lean's 94/128 under `--dl`), and
   `OwlProbe.lean` documents that its own `--dl` class-expression
   materialisation is ONE pass, not iterated to a fixpoint — closing this
   gap most likely means either adding tableau completion rules (not a
   budget change) or iterating the materialisation pass to a fixpoint,
   matching whatever the F* runner's DL regime actually does in
   `bin/owl-runner/owl_runner.ml`.
2. **Meta-axioms/comprehension.** `RLRules.lean` lines 69–77 name the gap
   exactly: `svf2_existential_witness`, `minc1_bridge`, `cls_hasself1/2`,
   `cls_svf_thing_*`, and the `[mode]` rules. F* already has all of these
   (`OWL.Closure.fsti`: `owl_rule_svf2_existential_witness` at line 1445,
   `owl_rule_minc1_bridge` at line 1508, `owl_rule_cls_hasself1`/
   `owl_rule_cls_hasself2_synth` at lines 1818/1844) — this is a
   Lean-behind-F* gap with a concrete F* source to port from.
3. **Built-in vocabulary axiom triples.** Trivial by comparison: F*'s
   `OWL.Closure.fsti` lines 4931–5002 define exactly this list
   (`owl_builtin_vocabulary_axioms`). Port it into `RLClosure.lean`'s
   `axiomTriples` (currently lines 233–235).
4. **Datatype value-space reasoning.** Neither tree fixes a datatype map
   for Table 7 (confirmed: no `owl_rule_dt_*` in `OWL.Closure.fsti`).
   Closing this needs `L4Factoidal/RDF/Datatypes.lean`'s existing XSD
   numeric tower extended with an equality/distinctness/type-membership
   oracle and Table 7 instantiated against it, in both trees.
5. **Existential-witness comprehension.** Same F* source as cluster 2
   (`owl_rule_svf2_existential_witness`, `owl_rule_minc1_bridge`).
6. **AllDifferent/AllDisjointProperties.** `RLRules.lean` line 57–59 names
   `eq-diff2`, `eq-diff3`, `prp-adp`, `cax-adp` as omitted "only for
   size", same LIST-walking shape as the ported `cax-adc`
   (`RLClosure.lean` lines ~798–806, `caxAdcAt`/`caxAdcToComplementFor`).
   F* has this (`OWL.Closure.fsti` lines 5045–5137,
   `owl_AllDisjointProperties_iri`, "cax-adp-expand").
7. **Qualified-cardinality deriving rows.** `RLRules.lean` line 60–63
   names `cls-maxqc3`/`cls-maxqc4` as not ported (their clash siblings
   are). F* has `owl_rule_cls_maxqc34` (`OWL.Closure.fsti` line 4193).
   The `owl:cardinality` shorthand rule has no F* counterpart found by
   this pass (not confirmed absent from F*, only not found by grep).
8. **Functional/InverseFunctional edge cases.** The domain/range flip
   pattern already exists (`inverseOfDomRngFlipFor`, `RLClosure.lean`
   lines 392–421) as a template for a characteristic-flip row. The
   datatype-value-equality half needs the same Table-7 datatype map as
   cluster 4.
9. **Restriction-comparison schema rows.** Not in F* either — this is new
   work in both trees, not a port. `RLRules.lean` line 64–68 records that
   the F* engine ledger in `OWL.RL.Spec.fst` lists no `owl_rule_*` for
   `scm-op`/`scm-dp`/`scm-hv`/`scm-svf1`/`scm-svf2`/`scm-avf1`/`scm-avf2`.
10. **`owl:hasKey` edge cases.** `prpKeyFor` (`RLClosure.lean` lines
    433–441) and `sharesKeyValuesB`. Needs a case-by-case read of
    New-Feature-Keys-001/002/006 against the premise RDF/XML before a fix
    can be scoped; not attempted in this pass.
11. **`owl:hasSelf`.** `RLRules.lean` line 70–74 names `cls_hasself1/2` as
    not ported. F* has `owl_rule_cls_hasself1`/`owl_rule_cls_hasself2_synth`
    (`OWL.Closure.fsti` lines 1818–1876).
12. **Direct-Semantics annotation filter.** `L4Factoidal/OWL/
    DirectMappingFilter.lean` (its own header, lines 23–32) states the
    scope limit explicitly: it does not special-case built-in OWL 2
    annotation properties (`rdfs:label`, `rdfs:comment`,
    `owl:versionInfo`) that need no declaration, "No corpus test
    exercises those." Cluster 12 below is evidence that claim no longer
    holds.
13. **Property-chain deriving direction.** No F* row found for this
    direction either (only `owl_rule_prp_spo2`, the forward chain-to-
    property direction, was found in this pass's greps). Needs a skolem
    LIST naming scheme, the same class of problem `RLClosure.lean` line
    33 names as deferred project-wide.
14. **`owl:disjointUnionOf`.** No existing row in either tree found by
    this pass. `owl:disjointUnionOf(C, C1, ..., Cn)` unfolds to
    `C owl:equivalentClass (C1 unionOf ... unionOf Cn)` plus
    `AllDisjointClasses(C1, ..., Cn)`; likely composable from the already-
    ported `cls-uni`/`cax-adc` machinery once the class-expression reader
    recognises the predicate.

## Believed wrongly scored

**WebOnt-I4.6-005-Direct** (5 units — profile-RL, profile-QL, profile-EL,
type-positive-entailment, type-consistency). The test's own description:
"Under the direct semantics, test WebOnt-I4.6-005 must be treated as a
positive entailment test because the direct semantics ignore annotations
in the conclusion ontology." The conclusion ontology is:

```
<owl:Class rdf:ID="C2">
  <rdfs:comment>An example class.</rdfs:comment>
</owl:Class>
```

`OwlProbe.lean`'s `excludeAnnotationTriples` (ported from
`L4Factoidal/OWL/DirectMappingFilter.lean`) is supposed to drop the
`rdfs:comment` triple from the conclusion before checking it under Direct
Semantics, per the test's own description. It only drops a triple whose
predicate is declared `owl:AnnotationProperty`/`owl:OntologyProperty`
INSIDE THE SAME GRAPH being filtered. This tiny conclusion graph never
declares `rdfs:comment` that way — it is a built-in annotation property
that needs no local declaration. So the filter does not drop it, the probe
then checks `C2 rdfs:comment "An example class."` against the RL closure,
does not find it (correctly — the premise's `owl:equivalentClass` relation
between C1 and C2 does not transfer C1's own annotation to C2 under
RDF-Based Semantics either), and reports FAIL. `DirectMappingFilter.lean`'s
own header (lines 27–32) states the scope limit as deliberate: "It does
NOT special-case the built-in OWL 2 annotation properties that need no
declaration ... No corpus test exercises those, and adding them
speculatively is anti-pattern #4." This test is exactly such a corpus
case; the "no corpus test exercises those" premise is false for this
catalog. This looks like a genuine harness-filter gap rather than a
reasoning gap in the closure — no verdict was changed to record this.

**FS2RDF-literals-ar** (the 1 `parser` failure). Checked and found
CORRECT, not a defect: the premise embeds an `rdf:XMLLiteral` value using
`rdf:datatype="...XMLLiteral"` on a property element that also has
XML ELEMENT content (a nested `<rdf:RDF>...</rdf:RDF>` tree), rather than
`rdf:parseType="Literal"`. RDF/XML Syntax §7.2.16's production rules do
not allow `rdf:datatype` combined with element content on a property
element; that combination is reserved for `rdf:parseType="Literal"`. The
Lean RDF/XML parser's rejection is a correct, spec-conformant read of a
non-conformant construct in the catalog's own test data, not a parser
defect.

## Gate

`cd formal/lean4 && lake build` exits 0 (936 jobs, no edits made to any
`.lean` file in this session). No `--list-failures` flag was added: the
existing `FAIL <case> [<type>]: <reason>` lines already print a full
per-test verdict and reason for every failing case, which is what this
classification needed; adding an unused reporting flag was judged not
worth the diff. Because no `.lean` source changed, the pass/fail/skip/
unsupported totals are unchanged by construction — no before/after
comparison was needed.
