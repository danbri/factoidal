# The 289 OWL 2 RL failures, re-classified from scratch

Date: 2026-09-04. Supersedes the bucket COUNTS of
[`2026-09-03-owl-failure-split.md`](2026-09-03-owl-failure-split.md),
which classified the RL gap when it stood at 319 fail. Since that
document the annotation-property axiomatic triples (`d980a444d`), the
rest of Table 6.5 (`cc4049738`), `scm-op`/`scm-dp` (`cb1883e0f`), the
`cax-adc` cell narrowing (`a32c3275a`) and the corrected conclusion
matcher (`f2988f1e6`) all landed, and several units were reclassified by
hand and never re-measured. The earlier document stays as the record of
the fix landings and their predicted-against-realised deltas.

Tracked in <https://github.com/danbri/factoidal/issues/651>.

## The measurement

Binary `formal/lean4/.lake/build/bin/l4owl-probe`, built at commit
`58a5dc236`. Corpus `third_party/testing/owl`, six catalogs. Closure
fuel 100, per-closure cap 30000 ms, corrected conclusion matcher (one
blank-node mapping over the whole conclusion graph).

    RL closure only:  1158 pass, 289 fail, 2 skip, 8 unsupported (out of 1457)
    cases=931 units=1457 triples_parsed=79078 closure_rounds=5572
    clashes=53 cap_hits=0 parse_failures=1

This reproduces the issue-651 baseline exactly, `cap_hits=0`, so no
figure below carries cap noise.

## The method

Every FAIL line the probe prints carries a cause tag and, for a
positive-entailment failure, the FIRST conclusion triple the matcher
could not place. The 289 are classified on THAT triple — its predicate,
and for `rdf:type` its object — never on which constructs the case
happens to mention. The earlier document measured both methods against
realised landings: the construct-occurrence marker predicted 24 units
and delivered 7; the first-missing-triple method predicted 18 and
delivered 18, and predicted 2 and delivered 2.

Classifier: [`tools/owl-rl-failure-split.py`](../../tools/owl-rl-failure-split.py),
a pure function of the probe run given on its command line. Reproduce with

    formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl > run.txt
    python3 tools/owl-rl-failure-split.py run.txt

Predicate sets used:

- **structure**: `owl:unionOf`, `owl:intersectionOf`, `owl:complementOf`,
  `owl:oneOf`, `owl:someValuesFrom`, `owl:allValuesFrom`, `owl:hasValue`,
  `owl:hasSelf`, `owl:onProperty`, `owl:onClass`, `owl:onDataRange`,
  `owl:onDatatype`, the five cardinality predicates, `owl:withRestrictions`,
  `owl:datatypeComplementOf`, `owl:members`, `owl:distinctMembers`,
  `owl:propertyChainAxiom`, `owl:disjointUnionOf`, `rdf:first`,
  `rdf:rest`; plus `rdf:type` of `owl:Restriction`, `owl:AllDifferent`,
  `owl:AllDisjointClasses`, `owl:AllDisjointProperties`, `owl:DataRange`,
  `rdf:List`, `owl:NegativePropertyAssertion`; plus `rdf:type` of a
  BLANK NODE class.
- **annotation**: `rdfs:comment`, `rdfs:label`, `rdfs:seeAlso`,
  `rdfs:isDefinedBy`, `owl:versionInfo`.
- **schema**: `rdfs:subClassOf`, `rdfs:subPropertyOf`, `rdfs:domain`,
  `rdfs:range`, `owl:equivalentClass`, `owl:equivalentProperty`,
  `owl:disjointWith`, `owl:inverseOf`, `owl:propertyDisjointWith`; plus
  `rdf:type` of a vocabulary class (`owl:FunctionalProperty`,
  `owl:InverseFunctionalProperty`, `owl:TransitiveProperty`,
  `owl:SymmetricProperty`, `owl:ObjectProperty`, `owl:DatatypeProperty`,
  `owl:Class`, `rdfs:Class`, `rdf:Property`, `rdfs:Datatype`, …).
- **assertional**: everything else — `owl:sameAs`, `owl:differentFrom`,
  `rdf:type` of an ontology's own class, an ontology's own property.

## The counts

| Bucket | What the first missing thing is | RL units | Cases |
|---|---|---|---|
| **B3** | a premise asserted inconsistent produced no clash | 107 | 92 |
| **B1** | the conclusion restates class-expression or axiom STRUCTURE | 73 | 31 |
| **B7** | a schema-level (TBox) triple is not derived | 54 | 27 |
| **B5** | an assertional triple is not derived | 47 | 23 |
| **B2** | an annotation does not travel across `owl:equivalentClass` | 5 | 1 |
| **B6** | no single blank-node mapping serves every conclusion triple | 2 | 1 |
| **C** | not about the engine (an RDF/XML parse failure) | 1 | 1 |
| **B4** | a consistent premise produced a clash, or a cap trip | 0 | 0 |
| | **total** | **289** | |

After the `inv-fp` landing recorded below the same tool reports B7 at
50 and every other bucket unchanged, which is the whole of the delta.

B7 is new in this split. The 2026-09-03 document had no schema bucket:
its B5 mixed assertional and schema-level conclusions, and its counts
put 107 in B5. Separating them is what makes the residue readable —
B5 is now almost entirely tableau work, and B7 is where the remaining
rule rows are.

### What changed against the 2026-09-03 counts

| | 2026-09-03 (at 319) | today (at 289) |
|---|---|---|
| A — construct absent | 41 | retired as a category |
| B5 | 107 | 47 (B5) + 54 (B7) |
| B3 | 106 | 107 |
| B1 | 56 | 73 |
| B2 | 5 | 5 |
| C | 4 | 1 |

Category **A** is retired deliberately. It was decided by a
construct-occurrence marker, and that marker over-predicted twice by a
factor of two or more (24 predicted, 7 realised). A construct with no
rule row shows up in this split under the bucket of the triple it fails
to produce, which is where the work order belongs.

B1 grew from 56 to 73 while the total FELL from 319 to 289. Three
causes, all accounted: the corrected conclusion matcher moved 2 units
into failure and they are B1-shaped; the landings closed B5/B7 units
and not B1 units, so B1's SHARE rose; and 18 units the 2026-09-03
document had already hand-moved from B5 to B1 in prose are counted in
B1 here for the first time.

## What the method cannot see

Stated beside the result, per anti-pattern 28.

1. **Only the FIRST missing conclusion triple is classified.** A
   conclusion missing five triples for five reasons lands in the bucket
   of the first. The matcher searches a single blank-node mapping, so
   "first" is the first triple of the conclusion graph in document
   order, not the first cause in any logical order.
2. **A predicate is not a cause.** `rdfs:subClassOf` puts a unit in B7
   whether the gap is a missing Table 9 row or a class-expression
   subsumption no closure decides. The five
   `rdfbased-sem-restrict-*-cmp-*` cases inside B7 are the first kind;
   `WebOnt-I5.2-002` is the second. The bucket is a work order, not a
   verdict, and the correction is the MEASURED delta after a fix.
3. **B3 is one string.** "No clash row fired" carries no information
   about WHICH inconsistency was missed, so B3's 107 are not ranked at
   all *by this classifier*. They are ranked below, in
   [B3 ranked, by the clash that should fire](#b3-ranked-by-the-clash-that-should-fire),
   by reading each case's PREMISE off the catalog rather than by
   changing the probe.
4. **The classifier cannot distinguish an absent rule row from a
   present row whose premise was never derived.** `New-Feature-Keys-001`
   is in B5 with a missing `owl:sameAs`; prp-key IS implemented and does
   not fire. Only reading the premise separates those.
5. **Zero units are attributable to a cap trip in this run**
   (`cap_hits=0`), so unlike the 2026-09-03 run no bucket is hiding a
   truncated closure. That was checked, not assumed.
6. **No OWL catalog entry is commented out upstream** — re-checked on
   this corpus. There is no withdrawn-test category.

## Where each bucket's work belongs

- **B3 (107)** — the tableau refuter. Under `--dl` the same corpus
  leaves far fewer inconsistency failures, and 78 of the 92 B3 cases are
  `WebOnt-description-logic-*` or datatype-restriction cases that no RL
  clash row decides. Not `RLClosure.lean` work.
- **B1 (73)** — one design decision, not 31 fixes. See
  [`2026-09-04-owl-b1-class-expression-structure.md`](2026-09-04-owl-b1-class-expression-structure.md).
  An RL closure cannot mint `owl:unionOf` / `owl:Restriction`
  scaffolding, and the `--dl` regime answers these by refutation.
  Largest single RL win available, and the largest open question.
- **B7 (54)** — mixed. 10 units are the five written-and-unlanded
  `scm-svf*`/`scm-avf*`/`scm-hv` rows. 4 units
  (`WebOnt-FunctionalProperty-003`, `WebOnt-InverseFunctionalProperty-003`)
  are one schema row: `P owl:inverseOf Q` with `P` functional gives `Q`
  inverse-functional — NOT a Profiles Table 9 row, so it needs a
  semantic-conditions transcription and its own soundness proof. The
  other 40 are class-expression subsumption and extensional-semantics
  cases that belong to the refuter.
- **B5 (47)** — mostly the refuter. The rule-row residue is
  `owl:AllDifferent` ⊢ pairwise `owl:differentFrom` (6 units) and
  `ICEXT(I(owl:Thing)) = IR` (6 units). The 10 `description-logic-2xx`
  units and the 12 existential-witness units are B3 work in a
  positive-entailment costume.
- **B2 (5)** — one case, `WebOnt-I4.6-005-Direct`.
- **B6 (2)** — one case, `WebOnt-I5.26-009`. The conclusion is
  satisfiable triple by triple and not under one mapping. Correct
  behaviour under RDF 1.1 Semantics; it needs a real entailment, not a
  matcher change.
- **C (1)** — `FS2RDF-literals-ar`, `rdf:datatype` on a property element
  with element content (RDF/XML §7.2.16). An RDF/XML parser gap.

## The identifiers, per bucket

Each line is a case with its unit count. A case scores one unit per
(catalog, test type) pair, so most appear twice.

#### C — 1 units, 1 cases

- `FS2RDF-literals-ar [ConsistencyTest]` — 1

#### B1 — 73 units, 31 cases

- `New-Feature-DataQCR-001 [PositiveEntailmentTest]` — 2
- `New-Feature-DisjointDataProperties-002 [PositiveEntailmentTest]` — 4
- `New-Feature-DisjointObjectProperties-002 [PositiveEntailmentTest]` — 4
- `New-Feature-ObjectPropertyChain-BJP-002 [PositiveEntailmentTest]` — 4
- `New-Feature-ObjectQCR-001 [PositiveEntailmentTest]` — 2
- `New-Feature-SelfRestriction-002 [PositiveEntailmentTest]` — 3
- `WebOnt-Class-006 [PositiveEntailmentTest]` — 2
- `WebOnt-FunctionalProperty-005 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.2-004 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.2-006 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.24-002 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.24-003 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.5-005 [PositiveEntailmentTest]` — 5
- `WebOnt-Nothing-002 [PositiveEntailmentTest]` — 2
- `WebOnt-Restriction-005-direct [PositiveEntailmentTest]` — 2
- `WebOnt-Restriction-006 [PositiveEntailmentTest]` — 2
- `WebOnt-cardinality-001 [PositiveEntailmentTest]` — 2
- `WebOnt-cardinality-002 [PositiveEntailmentTest]` — 2
- `WebOnt-cardinality-003 [PositiveEntailmentTest]` — 2
- `WebOnt-cardinality-004 [PositiveEntailmentTest]` — 2
- `WebOnt-cardinality-006 [PositiveEntailmentTest]` — 2
- `WebOnt-complementOf-001 [PositiveEntailmentTest]` — 2
- `WebOnt-description-logic-901 [PositiveEntailmentTest]` — 2
- `WebOnt-description-logic-903 [PositiveEntailmentTest]` — 2
- `WebOnt-equivalentClass-006 [PositiveEntailmentTest]` — 2
- `WebOnt-equivalentClass-007 [PositiveEntailmentTest]` — 2
- `WebOnt-extra-credit-003 [PositiveEntailmentTest]` — 2
- `WebOnt-extra-credit-004 [PositiveEntailmentTest]` — 2
- `WebOnt-unionOf-003 [PositiveEntailmentTest]` — 2
- `WebOnt-unionOf-004 [PositiveEntailmentTest]` — 2
- `bnode2somevaluesfrom [PositiveEntailmentTest]` — 3

#### B2 — 5 units, 1 cases

- `WebOnt-I4.6-005-Direct [PositiveEntailmentTest]` — 5

#### B3 — 107 units, 93 cases

- `Contradicting datatype Restrictions [InconsistencyTest]` — 1
- `Contradicting-dateTime-restrictions [InconsistencyTest]` — 1
- `Datatype-Float-Discrete-001 [InconsistencyTest]` — 1
- `Different types in Datatype Restrictions and Complement [InconsistencyTest]` — 1
- `Inconsistent Byte Filler [InconsistencyTest]` — 1
- `Inconsistent Data Complement with the Restrictions [InconsistencyTest]` — 1
- `Inconsistent Disjoint Dataproperties [InconsistencyTest]` — 1
- `Inconsistent String Pattern with Disjoint Dataproperties [InconsistencyTest]` — 1
- `Minus Infinity is not in owl:real [InconsistencyTest]` — 1
- `New-Feature-BottomDataProperty-001 [InconsistencyTest]` — 2
- `New-Feature-BottomObjectProperty-001 [InconsistencyTest]` — 2
- `New-Feature-Keys-002 [InconsistencyTest]` — 2
- `New-Feature-Keys-006 [InconsistencyTest]` — 3
- `New-Feature-Rational-002 [InconsistencyTest]` — 1
- `New-Feature-TopObjectProperty-001 [InconsistencyTest]` — 1
- `Plus and Minus Zero are Distinct [InconsistencyTest]` — 3
- `WebOnt-I5.5-003 [InconsistencyTest]` — 1
- `WebOnt-I5.5-004 [InconsistencyTest]` — 1
- `WebOnt-I5.8-001 [InconsistencyTest]` — 1
- `WebOnt-I5.8-003 [InconsistencyTest]` — 1
- `WebOnt-Restriction-001 [InconsistencyTest]` — 2
- `WebOnt-Restriction-002 [InconsistencyTest]` — 2
- `WebOnt-Thing-003 [InconsistencyTest]` — 3
- `WebOnt-description-logic-001 [InconsistencyTest]` — 1
- `WebOnt-description-logic-002 [InconsistencyTest]` — 1
- `WebOnt-description-logic-003 [InconsistencyTest]` — 1
- `WebOnt-description-logic-004 [InconsistencyTest]` — 1
- `WebOnt-description-logic-007 [InconsistencyTest]` — 1
- `WebOnt-description-logic-008 [InconsistencyTest]` — 1
- `WebOnt-description-logic-010 [InconsistencyTest]` — 1
- `WebOnt-description-logic-011 [InconsistencyTest]` — 1
- `WebOnt-description-logic-012 [InconsistencyTest]` — 1
- `WebOnt-description-logic-013 [InconsistencyTest]` — 1
- `WebOnt-description-logic-014 [InconsistencyTest]` — 1
- `WebOnt-description-logic-015 [InconsistencyTest]` — 1
- `WebOnt-description-logic-017 [InconsistencyTest]` — 1
- `WebOnt-description-logic-019 [InconsistencyTest]` — 1
- `WebOnt-description-logic-022 [InconsistencyTest]` — 1
- `WebOnt-description-logic-023 [InconsistencyTest]` — 1
- `WebOnt-description-logic-026 [InconsistencyTest]` — 1
- `WebOnt-description-logic-027 [InconsistencyTest]` — 1
- `WebOnt-description-logic-029 [InconsistencyTest]` — 1
- `WebOnt-description-logic-030 [InconsistencyTest]` — 1
- `WebOnt-description-logic-032 [InconsistencyTest]` — 1
- `WebOnt-description-logic-033 [InconsistencyTest]` — 1
- `WebOnt-description-logic-035 [InconsistencyTest]` — 1
- `WebOnt-description-logic-040 [InconsistencyTest]` — 1
- `WebOnt-description-logic-102 [InconsistencyTest]` — 1
- `WebOnt-description-logic-105 [InconsistencyTest]` — 1
- `WebOnt-description-logic-106 [InconsistencyTest]` — 1
- `WebOnt-description-logic-107 [InconsistencyTest]` — 1
- `WebOnt-description-logic-108 [InconsistencyTest]` — 1
- `WebOnt-description-logic-109 [InconsistencyTest]` — 1
- `WebOnt-description-logic-110 [InconsistencyTest]` — 1
- `WebOnt-description-logic-111 [InconsistencyTest]` — 1
- `WebOnt-description-logic-502 [InconsistencyTest]` — 1
- `WebOnt-description-logic-504 [InconsistencyTest]` — 1
- `WebOnt-description-logic-601 [InconsistencyTest]` — 1
- `WebOnt-description-logic-602 [InconsistencyTest]` — 1
- `WebOnt-description-logic-603 [InconsistencyTest]` — 1
- `WebOnt-description-logic-604 [InconsistencyTest]` — 1
- `WebOnt-description-logic-608 [InconsistencyTest]` — 1
- `WebOnt-description-logic-610 [InconsistencyTest]` — 1
- `WebOnt-description-logic-611 [InconsistencyTest]` — 1
- `WebOnt-description-logic-612 [InconsistencyTest]` — 1
- `WebOnt-description-logic-613 [InconsistencyTest]` — 1
- `WebOnt-description-logic-614 [InconsistencyTest]` — 1
- `WebOnt-description-logic-615 [InconsistencyTest]` — 1
- `WebOnt-description-logic-617 [InconsistencyTest]` — 1
- `WebOnt-description-logic-623 [InconsistencyTest]` — 1
- `WebOnt-description-logic-626 [InconsistencyTest]` — 1
- `WebOnt-description-logic-627 [InconsistencyTest]` — 1
- `WebOnt-description-logic-629 [InconsistencyTest]` — 1
- `WebOnt-description-logic-630 [InconsistencyTest]` — 1
- `WebOnt-description-logic-632 [InconsistencyTest]` — 1
- `WebOnt-description-logic-633 [InconsistencyTest]` — 1
- `WebOnt-description-logic-641 [InconsistencyTest]` — 1
- `WebOnt-description-logic-642 [InconsistencyTest]` — 1
- `WebOnt-description-logic-643 [InconsistencyTest]` — 1
- `WebOnt-description-logic-644 [InconsistencyTest]` — 1
- `WebOnt-description-logic-646 [InconsistencyTest]` — 1
- `WebOnt-description-logic-650 [InconsistencyTest]` — 1
- `WebOnt-description-logic-909 [InconsistencyTest]` — 1
- `WebOnt-description-logic-910 [InconsistencyTest]` — 1
- `WebOnt-disjointWith-010 [InconsistencyTest]` — 1
- `WebOnt-maxCardinality-001 [InconsistencyTest]` — 1
- `WebOnt-miscellaneous-203 [InconsistencyTest]` — 1
- `WebOnt-miscellaneous-204 [InconsistencyTest]` — 1
- `datatype-restriction-min-max-inconsistency [InconsistencyTest]` — 1
- `functionality-clash [InconsistencyTest]` — 2
- `inconsistent_datatypes [InconsistencyTest]` — 1
- `one=two [InconsistencyTest]` — 1
- `string-integer-clash [InconsistencyTest]` — 3

#### B4 — 0 units, 0 cases


#### B5 — 47 units, 22 cases

- `New-Feature-DisjointUnion-001 [PositiveEntailmentTest]` — 2
- `New-Feature-Keys-001 [PositiveEntailmentTest]` — 3
- `WebOnt-AllDifferent-001 [PositiveEntailmentTest]` — 2
- `WebOnt-AnnotationProperty-002 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.8-004 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.8-010 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.8-017 [PositiveEntailmentTest]` — 2
- `WebOnt-description-logic-201 [PositiveEntailmentTest]` — 2
- `WebOnt-description-logic-202 [PositiveEntailmentTest]` — 2
- `WebOnt-description-logic-205 [PositiveEntailmentTest]` — 2
- `WebOnt-description-logic-206 [PositiveEntailmentTest]` — 2
- `WebOnt-description-logic-208 [PositiveEntailmentTest]` — 2
- `WebOnt-differentFrom-002 [PositiveEntailmentTest]` — 2
- `WebOnt-distinctMembers-001 [PositiveEntailmentTest]` — 2
- `WebOnt-extra-credit-002 [PositiveEntailmentTest]` — 2
- `WebOnt-oneOf-003 [PositiveEntailmentTest]` — 2
- `WebOnt-oneOf-004 [PositiveEntailmentTest]` — 2
- `WebOnt-someValuesFrom-001 [PositiveEntailmentTest]` — 2
- `WebOnt-someValuesFrom-003 [PositiveEntailmentTest]` — 3
- `WebOnt-unionOf-002 [PositiveEntailmentTest]` — 2
- `rdfbased-sem-restrict-maxqcr-inst-obj-one [PositiveEntailmentTest]` — 2
- `somevaluesfrom2bnode [PositiveEntailmentTest]` — 3

#### B6 — 2 units, 1 cases

- `WebOnt-I5.26-009 [PositiveEntailmentTest]` — 2

#### B7 — 54 units, 27 cases

- `Consistent-but-all-unsat [PositiveEntailmentTest]` — 2
- `WebOnt-Class-001 [PositiveEntailmentTest]` — 2
- `WebOnt-Class-003 [PositiveEntailmentTest]` — 2
- `WebOnt-Class-005-direct [PositiveEntailmentTest]` — 2
- `WebOnt-FunctionalProperty-003 [PositiveEntailmentTest]` — 2
- `WebOnt-FunctionalProperty-004 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.2-002 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.21-002 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.24-004 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.3-014 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.3-015 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.5-001 [PositiveEntailmentTest]` — 2
- `WebOnt-I5.5-002 [PositiveEntailmentTest]` — 2
- `WebOnt-InverseFunctionalProperty-003 [PositiveEntailmentTest]` — 2
- `WebOnt-InverseFunctionalProperty-004 [PositiveEntailmentTest]` — 2
- `WebOnt-SymmetricProperty-002 [PositiveEntailmentTest]` — 2
- `WebOnt-SymmetricProperty-003 [PositiveEntailmentTest]` — 2
- `WebOnt-TransitiveProperty-002 [PositiveEntailmentTest]` — 2
- `WebOnt-equivalentClass-004 [PositiveEntailmentTest]` — 2
- `WebOnt-equivalentProperty-004 [PositiveEntailmentTest]` — 2
- `WebOnt-equivalentProperty-005 [PositiveEntailmentTest]` — 2
- `WebOnt-imports-010 [PositiveEntailmentTest]` — 2
- `rdfbased-sem-restrict-allvalues-cmp-class [PositiveEntailmentTest]` — 2
- `rdfbased-sem-restrict-allvalues-cmp-prop [PositiveEntailmentTest]` — 2
- `rdfbased-sem-restrict-hasvalue-cmp-prop [PositiveEntailmentTest]` — 2
- `rdfbased-sem-restrict-somevalues-cmp-class [PositiveEntailmentTest]` — 2
- `rdfbased-sem-restrict-somevalues-cmp-prop [PositiveEntailmentTest]` — 2

## Fix landings measured against this split

### `inv-fp` — the property characteristic travels across `owl:inverseOf`

| Rows added | RL before → after | `--dl` before → after |
|---|---|---|
| invFpIfp, invIfpFp, invFpIfpRev, invIfpFpRev | 1158 pass, 289 fail → 1162 pass, 285 fail (out of 1457) | 1296 pass, 151 fail → 1300 pass, 147 fail (out of 1457) |

Bucket B7. **Predicted 4 RL units, realised 4 RL units and 4 `--dl`
units**, and the four are the same two cases scored in two catalogs
each: `WebOnt-FunctionalProperty-003` and
`WebOnt-InverseFunctionalProperty-003`, both
`PositiveEntailmentTest`. No test regressed in either regime — the RL
failing sets differ by exactly those four lines and nothing else.
`cap_hits` 0, `clashes` 53, `closure_rounds` 5572 in RL, all unchanged.
NegativeEntailmentTest 38 pass, 0 fail (out of 38) and ConsistencyTest
1 fail in both regimes, unchanged.

**These four rows are NOT a table transcription, and the file says so.**
OWL 2 RL/RDF Table 9 has no row for the characteristic travelling
across `owl:inverseOf`. The rows are a consequence of three published
conditions of the OWL 2 RDF-Based Semantics (2nd Edition):
`CondInverseOf` (Table 5.13 — IEXT(q) is the transposition of IEXT(p))
and the Table 5.14 conditions for `owl:FunctionalProperty` and
`owl:InverseFunctionalProperty`. Table 5.14 states each characteristic
as an `iff`; `OWL/Semantics.lean`'s `CondFunctional` carries only the
half that READS a membership, so the half that CONCLUDES one is stated
in `RLSemantics.lean` under its table name (`T514FunctionalIntro`,
`T514InverseFunctionalIntro`) and taken as a HYPOTHESIS of the
derivation rather than added to any bundle. The derivation is
`rlCondInvFpIfp_of_semantics` and its three companions. Anyone reading
these rows as table rows should read that derivation first.

Four rows, not two: the closure has no `owl:inverseOf` symmetry row,
so reading the declaration from its object is a separate rule. Only
the two forward rows are exercised by the corpus.

**Cost gates.** Peak resident on the `type-positive-entailment`
catalog under `--dl`, `/usr/bin/time -l`: 138 MB, 277 s wall, 356 pass,
52 fail (out of 412). The whole `--dl` corpus: 242 MB peak, 734 s. The
2026-09-03 split records 141 MB for the same catalog before any of
this, so peak memory does not move — unlike the five `scm-svf*` rows,
which took it to 7.47 GB. `RLSemantics` elaborated in 58 s in the full
rebuild that carries these rows. That is an absolute figure, not a
delta: no before-figure was taken on this machine, which was running
two other agents throughout, so the wall-clock numbers here are not
comparable with the 2026-09-03 document's.

Touch points, for the next row that lands the same way: a `Derives`
constructor and its two `mono` arms in `RLRules.lean`; an
`RlCond` definition, a bundle field, a `tripleIrisNonReserved` arm and
a `TripleHolds` arm in `RLSemantics.lean`; a bundle field in
`RLHerbrand.lean`; the executable row and its `conclusionsList` entry
in `RLClosure.lean`; the indexed row, its `ofGraph` theorem and its
list entry in `RLClosureIndexed.lean`; a soundness theorem, a
`conclusionsFrom_sound` bullet, ONE MORE `rfl` in that proof's `rcases`
pattern, and a T4 arm in `RLTheorems.lean`; and a `RlRowId`
constructor, a `rlRowRule` row, a `cond_*` theorem and a bundle field
in `Unified/OwlRlSchema.lean`. The `rcases` pattern is the one that
fails with an error pointing at a line far from the edit.

## Judgement: should RL get a refutation fallback like `--dl`?

Yes, and it should be a separate REGIME rather than a change to the RL
closure. Reasons:

1. B1 (73) plus the refuter-shaped parts of B3, B5 and B7 is most of
   the 289. No quantity of Profiles Table rows reaches them; an RL
   closure derives triples, and these conclusions are not triples any
   sound closure over the premise can derive.
2. The OWL 2 conformance definition for a positive entailment test is
   model-theoretic. A reasoner that answers by refuting premise plus
   negated conclusion is conforming; it is not a shortcut around the
   test.
3. Putting the fallback INSIDE the RL closure would be unsound in the
   other direction: the RL profile's guarantee is that its closure is a
   sound and (for RL-restricted ontologies) complete consequence
   operator. Refutation is a different decision procedure with a
   different completeness claim, and mixing them makes neither claim
   statable.

So the shape to build is a third regime flag, not a wider RL rule set —
and the RL score line should keep reporting the closure alone, because
that number is what the profile's completeness claim is about.

## The landing: `--rl-refute`, a third regime with two score lines

Date: 2026-09-04. Implements the judgement above. `Harness/OwlProbe.lean`
only; no rule row, no closure change, no `Refute.lean` change.

### What was built

`OwlProbe.Regime` replaces the single `dl : Bool` with two independent
capabilities — `materialise` (one class-expression pass between two
closures) and `refuter` (the tableau may decide a unit the closure did
not). Three regimes are named from them:

| Flag | `materialise` | `refuter` |
|---|---|---|
| (default) | false | false |
| `--rl-refute` | false | **true** |
| `--dl` | true | true |

Every judge now returns a `Verdict` carrying TWO outcomes: the verdict
under the regime, and the verdict the CLOSURE ALONE reached on the same
unit. They are equal wherever the refuter is off. `runCatalog` scores
both, so a run with the refuter on prints two labelled score lines per
catalog and per test type, plus `TOTAL [closure alone]` and
`TOTAL [closure or refutation]`.

### The measurement

Binary built at this commit, corpus `third_party/testing/owl`, six
catalogs, closure fuel 100, per-closure cap 30000 ms, refuter budget 64,
single-blank-node-mapping conclusion matching.

| Regime | Score |
|---|---|
| default (RL closure only) | 1162 pass, 285 fail, 2 skip, 8 unsupported (out of 1457) |
| `--rl-refute` **[closure alone]** | 1162 pass, 285 fail, 2 skip, 8 unsupported (out of 1457) |
| `--rl-refute` **[closure or refutation]** | 1307 pass, 140 fail, 2 skip, 8 unsupported (out of 1457) |
| `--dl` | 1316 pass, 131 fail, 2 skip, 8 unsupported (out of 1457) |

`--dl` now also prints a closure line of its own, 1176 pass, 271 fail
(out of 1457): the class-expression materialisation pass closes 14 of
the 285 by CONTAINMENT, before any refutation.

The `--rl-refute` closure line reproduces the default regime EXACTLY,
and its 285 FAIL lines are byte-identical to the default regime's. That
equality is the check that the closure's answer was not touched: the
same closure ran, and the refuter was added beside it and never inside
it. `--dl` did not move.

`refuter_passes=145`, `refuter_flips_to_fail=0`, `cap_hits=0`.

### Which of the 285 the refuter closed, by bucket

Classifier `tools/owl-rl-failure-split.py` on both runs.

| Bucket | Closure alone | With refutation | Closed |
|---|---|---|---|
| B3 — a premise asserted inconsistent produced no clash | 107 | 15 | **92** |
| B1 — the conclusion restates class-expression structure | 73 | 42 | **31** |
| B5 — an assertional triple is not derived | 47 | 37 | **10** |
| B7 — a schema-level triple is not derived | 50 | 40 | **10** |
| B6 — no single blank-node mapping serves the conclusion | 2 | 0 | **2** |
| B2 — an annotation does not travel | 5 | 5 | 0 |
| C — an RDF/XML parse failure | 1 | 1 | 0 |
| **total** | **285** | **140** | **145** |

B3 is where refutation belongs and the number says so: 92 of 107
inconsistencies no RL clash row decides are decided by the tableau. The
92 come from `judgeInconsistency`; the other 53 are the
positive-entailment fallback.

### The refuter's reach, stated as a limit and not hidden in a fail count

Of the 177 positive-entailment units the closure failed:

- **53** were decided by refutation (`PE-BY-REFUTATION`, all with
  `premise_alone_refuted=false`, so none is a vacuous pass);
- **70 produced NO negation goal at all** — `OWL.NegationGoals`
  does not negate that conclusion shape, so the refuter never got to
  ask the question. This is the single largest limit on the regime and
  it is now a counted diagnostic (`pe_no_negation_goal`) and a printed
  line per unit (`PE-REFUTER-WITHHELD ... noGoals`), not a silent part
  of the 140;
- **54** were answered with a countermodel: the refuter looked and said
  the entailment does not hold on the RL closure it was given;
- **0** exhausted the tableau budget, so no part of the residue is
  budget noise.

The 70 concentrate in `WebOnt-I5.5-005` and `WebOnt-I4.6-005-Direct`
(5 units each), the two `New-Feature-Disjoint*Properties-002` cases
(4 each), and about thirty cases at 2 units each. Extending
`negationGoals` to those shapes is the next work order for this regime,
and it is a `NegationGoals` change, not a closure change.

### Which number to publish

**Publish the closure-alone number, 1162 pass, 285 fail (out of 1457),
as OWL 2 RL conformance.** The OWL 2 RL profile's guarantee is about a
CLOSURE: it is a sound consequence operator and complete for the
RL-restricted fragment. A tableau refutation of
`premise union not-conclusion` is a different decision procedure with a
different completeness claim, so a number that mixes them supports
neither claim. The 1307 is publishable, and conforming under the
model-theoretic definition of the OWL 2 conformance tests, as an
**engine** figure with its regime named — never as an RL-profile figure.

The probe enforces the distinction in its OUTPUT, not only here: a run
with the refuter on prints the explanation of the two lines in its
header, prints both lines at every catalog and at TOTAL, and prints
`DECIDED-BY-REFUTER <unit>` for each of the 145 units the two verdicts
disagree on.

### Soundness gates, before and after

| Gate | Value |
|---|---|
| ConsistencyTest, `--rl-refute` | 761 pass, 1 fail (out of 762) — unchanged |
| NegativeEntailmentTest, `--rl-refute` | 38 pass, 0 fail (out of 38) |
| `refuter_flips_to_fail` | 0 — the refuter fabricated no contradiction on any premise asserted consistent |
| `cap_hits` | 0 |
| RDF 1.1 | 1031 pass, 0 fail (out of 1031) |
| SPARQL 1.1 | 631 pass, 0 fail (out of 631) |

`judgeConsistency` under `--rl-refute` runs the refuter on the RL
closure of every consistent premise — 762 units — and refuted none of
them. That is the gate that would have caught a refuter fabricating a
clash, and it is why the consistency line is run in this regime rather
than assumed from `--dl`.

### Cost, and whether CI can afford it

`/usr/bin/time -l`, whole corpus, this machine, with other work running:

| Regime | Wall | Peak resident |
|---|---|---|
| default | 28 s | 239 MB |
| `--rl-refute` | 546 s | 213 MB |
| `--dl` | 585 s | 241 MB |

Affordable in CI beside the other two: 546 s of one core and 213 MB.
It is nineteen times the default regime's wall clock and that is the
refuter, not the closure — the closure half is the same 28 s of work.
Peak memory is BELOW the default regime's, because no materialisation
pass runs.

## B3 ranked, by the clash that should fire

Measured 2026-09-04 at commit `cecee9476`, RL regime, from the same
probe run the counts above come from. B3 there is **106 units across 92
cases** — one unit less than the table, because the five `scm` rows
(`9ce7191ab`) closed `WebOnt-description-logic-002`.

"No clash row fired" says nothing about WHICH inconsistency was missed,
which is why item 3 of *What the method cannot see* recorded B3 as
unranked. The rank below reads each case's PREMISE off the catalog and
asks one question: could a Horn closure decide this inconsistency at
all? An OWL 2 RL clash row is a table row from Profiles §4.3 — all
premises positive, no case split, no invented individual. A premise
whose only proof of inconsistency needs a witness or a case split is
not RL closure work whatever row is added.

Reproduce with `tools/owl-b3-premise-rank.py`.

| Tier | Group | Units | Cases |
|---|---|---|---|
| A | prp-fp then literal distinctness (`dt-diff` + `eq-diff1`) | 7 | 4 |
| A | prp-key then eq-diff1 | 5 | 2 |
| A | dt-not-type (Table 8) | 4 | 2 |
| A | `ICEXT(I(owl:Thing)) = IR` then cls-nothing2 | 3 | 1 |
| — | `rdf:nil` has no `rdf:rest` — no Profiles row | 2 | 2 |
| B | an existential witness is required | 81 | 77 |
| B | a disjunction must be case-split | 3 | 3 |
| B | max-cardinality N>0 — counting distinct fillers | 1 | 1 |
| | **total** | **106** | **92** |

**Tier A is 19 units of 106.** Everything else is the refuter's, and
the earlier reading that `--rl-refute` closes 92 of the 107 is
consistent with that: refutation searches, and 85 of these need search.

### What the tiers mean

**Tier B, 85 units.** 77 cases carry `ObjectSomeValuesFrom`,
`DataSomeValuesFrom`, `owl:someValuesFrom`, `owl:minCardinality` or an
exact cardinality. The inconsistency is only visible at an individual
the premise does not name, and a Horn closure never mints one. The 68
`WebOnt-description-logic-*` cases are the OilEd satisfiability suite
and are all of this kind or the disjunctive kind: `inconsistent001`
equates a class with a `owl:unionOf` of `owl:intersectionOf` pairs, and
deciding it needs the case split. Adding a clash row for any of these
would be adding a search to the closure.

**Tier A, 19 units.** Four groups, each a real Profiles §4.3 row or a
short composition of two:

1. **prp-fp then literal distinctness — 7 units, 4 cases.** A
   functional property with two fillers whose data values differ.
   `functionality-clash` has `"18"^^xsd:integer` and `"19"^^xsd:integer`;
   `Plus and Minus Zero are Distinct` has `"+0.0"^^xsd:float` and
   `"-0.0"^^xsd:float`, two values of the float space by XSD 1.1
   §3.3.5; `WebOnt-miscellaneous-203`/`204` compare two
   `rdf:XMLLiteral` fillers.
   `New-Feature-Keys-006`, counted under prp-key below, is also this
   shape — it declares `FunctionalDataProperty(:hasName)` with the
   fillers `"Peter"` and `"Kichwa-Tembo"`.
2. **prp-key then eq-diff1 — 5 units, 2 cases.** `New-Feature-Keys-002`
   needs prp-key to give `owl:sameAs` between two individuals declared
   `DifferentIndividuals`. prp-key IS implemented, so the gap is in a
   premise it does not derive, not in the row.
3. **dt-not-type — 4 units, 2 cases.** The one Profiles §4.3
   no-consequent row the engine does not implement, and its reach in B3
   is two cases. `string-integer-clash` is the clean shape: a data
   property with `xsd:integer` range and an `xsd:string` filler.
   `Contradicting-dateTime-restrictions` needs the row over a
   `DatatypeRestriction`, using the facet interval.
4. **`ICEXT(I(owl:Thing)) = IR` — 3 units, 1 case.**
   `WebOnt-Thing-003` asserts `owl:Thing owl:equivalentClass
   owl:Nothing` and names no individual. It is the same missing fact
   the six B5 units named in *Where each bucket's work belongs* need.

The two `rdf:nil`/`rdf:rest` units (`WebOnt-I5.5-003`, `-004`) are an
RDF-based-semantics fact — `rdf:nil` is not a list cell — with no row
in any Profiles table. Listed apart so nobody looks for one.

### What this ranking cannot see

Stated beside the result, per anti-pattern 28.

1. **It reads the premise, not the closure.** A case in Tier A is one
   where a Horn row COULD decide the inconsistency. Whether the row
   fires also depends on the closure deriving its other premises, which
   this method does not check — `New-Feature-Keys-002` is exactly that
   case. The correction is the measured delta after a landing.
2. **The tier gate is syntactic.** A premise mentioning
   `owl:someValuesFrom` is put in Tier B even if some other part of it
   is separately inconsistent by a Horn row. That direction is safe for
   a work order (it under-promises), and it is why the prp-fp landing
   below closed a case the table counts under prp-key.
3. **`fsPremiseOntology` is preferred over `rdfXmlPremiseOntology`**
   when a case carries both, so the construct names read are Functional
   Syntax where available. A case whose two serialisations differ in
   constructs would be classified on the Functional one.

### Landing 1 against this ranking — `prp-fp` over literal fillers

Profiles §4.3 Table 5 `prp-fp`, composed with Table 8 `dt-diff` and
`eq-diff1`. Tier A group 1.

| | RL |
|---|---|
| before | 1173 pass, 274 fail, 2 skip, 8 unsupported (out of 1457) |
| after | 1181 pass, 266 fail, 2 skip, 8 unsupported (out of 1457) |

**Predicted 5 to 8 units, realised 8**, and the failing sets differ by
exactly those eight lines with nothing newly failing:
`functionality-clash` (2 units), `New-Feature-Keys-006` (3) and
`Plus and Minus Zero are Distinct` (3). The two
`WebOnt-miscellaneous-203`/`204` units in the same group did NOT close,
as the prediction said: they compare two `rdf:XMLLiteral` fillers, and
`XSD.termProvablyDistinct` does not reach the `rdf:XMLLiteral` value
space.

`New-Feature-Keys-006` is scored under prp-key in the ranking table and
closed by the prp-fp row. That is method note 2 of the ranking working
as stated: the tier gate reads constructs, and a premise can be
inconsistent for a reason other than the one its most prominent
construct suggests.

Diagnostics: `clashes` 54 → 62, `closure_rounds` 5682 → 5684,
`cap_hits` 0, `parse_failures` 1 — all unchanged apart from the eight
new clashes.

#### Gates

| Gate | Before | After |
|---|---|---|
| `lake build` | green | green, 942 jobs |
| ConsistencyTest, RL | 761 pass, 1 fail (out of 762) | 761 pass, 1 fail (out of 762) |
| InconsistencyTest, RL | 54 pass, 106 fail (out of 160) | 62 pass, 98 fail (out of 160) |
| NegativeEntailmentTest, RL | 38 pass, 0 fail (out of 38) | 38 pass, 0 fail (out of 38) |
| RDF 1.1 | 1031 pass, 0 fail (out of 1031) | 1031 pass, 0 fail (out of 1031) |
| SPARQL 1.1 | 631 pass, 0 fail (out of 631) | 631 pass, 0 fail (out of 631) |
| `--dl`, `profile-RL.rdf`, closure alone | 117 pass, 9 fail (out of 126) | 120 pass, 6 fail (out of 126) |
| `--dl`, `profile-RL.rdf`, closure or refutation | — | 121 pass, 5 fail (out of 126) |

ConsistencyTest unchanged is the soundness gate: a clash row that fires
on a consistent premise makes the engine deny a satisfiable ontology,
which is worse than a missing row. 762 consistent premises, no new
clash on any of them.

#### The two cost gates

| | Before | After |
|---|---|---|
| `lake build L4Factoidal.OWL.RLSemantics`, user time | 86.9 s | 124.2 s |
| RL corpus, peak resident (`/usr/bin/time -l`) | 216 MB | 238 MB |
| RL corpus, user time | 40.1 s | 72.2 s |
| `--dl`, `profile-RL.rdf`, peak resident | — | 28 MB |

Wall clock is not reported: another agent's `--dl` corpus run held the
machine at 9 to 50 percent CPU for this session, so every wall figure
here is contention, not work. User time and peak resident are the
comparable numbers.

The elaboration cost is +37 s user on `RLSemantics`, and it is the
`RlClashConditions` structure gaining a seventeenth field, not the row
body. That is well under the 26 s to 189 s regression that reverted a
row family earlier, and it is recorded so the next row can be compared
against it.

#### What a new RL clash row actually costs

Recorded because the ranking's Tier A is 19 units and each of its four
groups pays this same bill. Adding one row to `RLClosure.clashRows`
touched six files, not two:

1. `OWL/RLClosure.lean` — the row, plus the `asLit` reader.
2. `OWL/RLClosureIndexed.lean` — the store mirror, so
   `clashFromS_ofGraph` still closes by `rfl`.
3. `OWL/RLRules.lean` — a `Clash` constructor, and a case in
   `Clash.mono`.
4. `OWL/RLTheorems.lean` — a soundness lemma and a case in
   `clashFrom_sound`.
5. `OWL/RLSemantics.lean` — an `RlNCond*` interpretation condition, a
   field on `RlClashConditions`, and a case in `rl_clash_holds_false`.
6. `OWL/RLHerbrand.lean` and `Unified/OwlRlSchema.lean` — the
   discharge of that condition in the completeness model and in the
   schema bridge.

Step 6 is where a row can fail outright. The Herbrand model's fragment
clause (a) forbids a literal object, so a row whose premises put a
literal in object position holds VACUOUSLY there — the same boundary
the three cardinality rows sit on. Three new lemmas make that argument
at a QUANTIFIED property (`listMember_no_literal`,
`listDenotes_no_literal`, `no_literal_object_any`); the existing
`no_literal_object` needs the property to be a known non-reserved IRI,
which a row with a variable property does not have.

The schema bridge cannot carry the row at all: `rlNegRowRule` builds
first-order sentences over term variables, and this row's side
condition is the SYNTACTIC decision
`RLRules.valuesProvablyDistinct`. It joins `OwlRlInterpCond`, the
bundle of rows carried as a hypothesis on the interpretation.

Consequence for the ranking's other three Tier A groups: dt-not-type
also puts a literal where the Herbrand fragment forbids one, so it can
follow the same route. `ICEXT(I(owl:Thing)) = IR` cannot — it is about
an interpretation's domain being non-empty, which is a condition the
Herbrand model does meet, so its discharge is real work rather than a
vacuity.
