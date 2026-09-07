# The Lean OWL corpus gap against F\*, measured

2026-09-07. Worktree `wt/lean-cov-owl`. Engines: `formal/lean4`
(`lake exe l4owl-probe`) and the committed F\* runner logs in
`formal/fstar/ocaml-output/owl_*_results.log`.

## 1. The regime finding, before any score

The 266 Lean failures are NOT all comparable with F\*. The F\* logs
record the regime each catalog was scored under:

| catalog | F\* regime |
|---|---|
| `profile-RL.rdf` | RL |
| `profile-EL.rdf` | RL |
| `profile-QL.rdf` | RL |
| `type-positive-entailment.rdf` | DL |
| `type-inconsistency.rdf` | DL |
| `type-consistency.rdf` | DL |

The Lean probe's DEFAULT is the RL closure alone. So the default Lean
run is like-for-like with F\* on the three profile catalogs only. On the
three `type-*` catalogs it compares an RL closure against
`capped_is_inconsistent closure || dl_refutes closure_rl ||
class_size_refutes ...` (`bin/owl-runner/owl_runner.ml`, lines 1032,
1058, 1865) — a tableau and a Farkas counting oracle that the default
Lean run does not consult. Reporting that difference as a Lean rule gap
would be an anti-pattern-28 measurement error: the method cannot see
the thing it is being asked about.

The comparison this record uses:

* profile catalogs — Lean default (RL) against F\* RL.
* `type-*` catalogs — Lean `--dl` against F\* DL.

## 2. Baseline (Lean, default RL regime, reproduced 2026-09-07)

```
profile-RL.rdf:               120 pass,  6 fail, 0 skip, 0 unsupported (out of 126)
profile-EL.rdf:               105 pass, 15 fail, 1 skip, 0 unsupported (out of 121)
profile-QL.rdf:                82 pass,  5 fail, 0 skip, 0 unsupported (out of  87)
type-positive-entailment.rdf: 333 pass, 75 fail, 0 skip, 4 unsupported (out of 412)
type-inconsistency.rdf:        38 pass, 89 fail, 1 skip, 0 unsupported (out of 128)
type-consistency.rdf:         503 pass, 76 fail, 0 skip, 4 unsupported (out of 583)
TOTAL:                       1181 pass, 266 fail, 2 skip, 8 unsupported (out of 1457)
```

## 2b. The `type-*` catalogs under `--dl`, which is the F\* regime

Measured 2026-09-07, `l4owl-probe --dl`, default caps
(`--cap-ms 30000`). `type-consistency.rdf` is measured at
`--refute-budget 16` rather than the default 64: at the default it does
not finish inside 40 minutes on this machine, and `--cap-ms` bounds the
CLOSURE only — the probe puts no wall-clock bound on the refuter, so a
slow case has nothing to trip. A smaller refuter budget can only LOSE
refutations, so its 531 pass, 48 fail is a LOWER BOUND on the
default-budget figure.

| catalog / unit | Lean RL | Lean `--dl` | F\* DL |
|---|---|---|---|
| `type-inconsistency.rdf` Inconsistency | 38 pass, 89 fail | **116 pass, 11 fail** | 126 pass, 1 fail |
| `type-positive-entailment.rdf` PE | 129 pass, 75 fail | **157 pass, 47 fail** | 195 pass, 9 fail |
| `type-positive-entailment.rdf` Consistency | 204 pass, 0 fail | 204 pass, 0 fail | 199 pass, 5 fail |
| `type-consistency.rdf` (all units) | 503 pass, 76 fail | **531 pass, 48 fail** (`--refute-budget 16`) | 558 pass, 21 fail |

So the regime accounts for 78 of the 89 `type-inconsistency` failures
and 28 of the 75 `type-positive-entailment` PE failures. The Lean
`--dl` figures also BEAT F\* on `type-positive-entailment`'s
ConsistencyTest section (204 pass, 0 fail against 199 pass, 5 fail —
F\*'s five are `unsupported` cap escapes, #326).

On `type-consistency.rdf` the `--dl` closure alone (RL closure plus the
materialisation pass) is 505 pass, 74 fail, and the refuter takes it to
531 pass, 48 fail. Against F\*'s 558 pass, 21 fail that is a gap of at
most 27 units, measured at the reduced budget.

## 3. The like-for-like gap: profile catalogs, RL against RL

F\* scores every unit of all three profile catalogs PASS
(`owl_profile_rl_results.log` 30/6/76/14, `owl_profile_el_results.log`
29/6/71+1unsupported/13+1skip, `owl_profile_ql_results.log` 20/3/58/6).
Every Lean failure in these catalogs is therefore an F\*-passes /
Lean-fails unit. There are **26** of them over **17 distinct test ids**.
`--wildcard-match` closes none of them, so the conclusion-matching rule
is not the cause.

### 3a. PositiveEntailmentTest (17 units, 10 ids)

| test id | catalogs | missing conclusion triple |
|---|---|---|
| `New-Feature-DisjointDataProperties-002` | RL, EL, QL | `_:b1 rdf:type owl:AllDifferent` |
| `New-Feature-DisjointObjectProperties-002` | RL, EL, QL | `_:b1 rdf:type owl:AllDifferent` |
| `WebOnt-I4.6-005-Direct` | RL, EL, QL | `C2 rdfs:comment "An example class."` |
| `WebOnt-I5.5-005` | RL, EL, QL | `_:b0 owl:unionOf _:b1` |
| `New-Feature-ObjectPropertyChain-BJP-002` | RL, EL | `_:owlfs_chain0 rdf:first ex:p` |
| `bnode2somevaluesfrom` | EL | `_:b1 owl:someValuesFrom owl:Thing` |
| `somevaluesfrom2bnode` | EL | `ex:a ex:p _:b1` |
| `WebOnt-someValuesFrom-003` | EL | `fred parent _:b1` |
| `New-Feature-Keys-001` | EL | `Peter owl:sameAs Peter_Griffin` |
| `New-Feature-SelfRestriction-002` | EL | `Peter rdf:type _:b1` |

### 3b. InconsistencyTest (9 units, 7 ids)

All report `no clash row fired on a premise asserted inconsistent`.

| test id | catalogs | what makes it inconsistent |
|---|---|---|
| `string-integer-clash` | RL, EL | `DataPropertyRange(hasAge xsd:integer)` with `hasAge "aString"^^xsd:string` |
| `New-Feature-BottomDataProperty-001` | EL | member of `∃ owl:bottomDataProperty . rdfs:Literal` |
| `New-Feature-BottomObjectProperty-001` | EL | member of `∃ owl:bottomObjectProperty . owl:Thing` |
| `WebOnt-Restriction-001` | EL | member of `∃ op . owl:Nothing` |
| `WebOnt-Restriction-002` | EL | member of `∃ op . owl:Nothing` |
| `New-Feature-Keys-002` | EL | `owl:hasKey` |
| `WebOnt-Thing-003` | EL, QL | `owl:Thing owl:equivalentClass owl:Nothing` |

## 3c. The F\* RL regime is not the RL closure alone either

`bin/owl-runner/owl_runner.ml` scores PositiveEntailmentTest through
`apply_closure_with_witnesses`, in BOTH regimes. That calls
`OWL.Closure.fsti`'s `owl_rl_closure_with_reflexivity_and_witnesses_mode`
(line 6584): the RL closure, then `cls-hasself2-synth`,
`cls-svf-thing-materialize`, `cls-svf-thing-witness`, then eight
comprehension rules (`comp_singleton_union`, `comp_min1_restriction`,
`comp_oneof_union`, `comp_union_oneof`, `comp_enum_range_value`,
`comp_range_avf`, `comp_range_intersection`,
`comp_pinned_domain_enum`), then one plain re-closure. Its own banner
records why the layer is kept out of the shared fixpoint: folding it in
took DL-regime `type-inconsistency.rdf` from 124 pass, 3 fail to 63
pass, 64 fail.

ConsistencyTest and InconsistencyTest do NOT see that layer — they run
`apply_closure_stages`, which in RL is the plain closure. So the F\* RL
figures are two different pipelines under one heading, and the Lean
default matches the second but not the first. That is why every
remaining profile-catalog PE failure is a comprehension-witness gap and
every Inconsistency failure was a clash-row gap.

## 4. Clusters

* **C1 — three missing clash rows.** `OWL.Closure.fsti`'s
  `is_inconsistent` has twelve checks; `OWL/RLClosure.lean`'s
  `detectClash` has seventeen rows covering only checks (1)-(9). Checks
  (10) `dt-range-clash`, (11) bottom-property existential clash and
  (12) `cls-svf-bot` have no Lean counterpart. Targets
  `string-integer-clash`, `New-Feature-BottomDataProperty-001`,
  `New-Feature-BottomObjectProperty-001`, `WebOnt-Restriction-001`,
  `WebOnt-Restriction-002` — 6 units.
* **C2 — someValuesFrom existential PE.** `bnode2somevaluesfrom`,
  `somevaluesfrom2bnode`, `WebOnt-someValuesFrom-003`,
  `New-Feature-SelfRestriction-002` — 4 units. The conclusion asserts a
  witness edge the RL closure does not create.
* **C3 — comprehension-shaped PE.** `WebOnt-I5.5-005`,
  `New-Feature-Disjoint{Data,Object}Properties-002`,
  `New-Feature-ObjectPropertyChain-BJP-002` — 11 units. The conclusion
  asserts an ANONYMOUS class expression or list cell the premise never
  writes.
* **C4 — annotation carry-over.** `WebOnt-I4.6-005-Direct` — 3 units.
* **C5 — `owl:hasKey` and `owl:Thing ≡ owl:Nothing`.**
  `New-Feature-Keys-001`, `New-Feature-Keys-002`, `WebOnt-Thing-003` —
  5 units.

## 5. A defect in the F\* rule, recorded rather than ported

`OWL.Closure.fsti` check (10) `dt-range-clash` reads:

> `P` has a declared `rdfs:range D_range` … and some `(x P v)` asserts a
> literal `v` whose OWN datatype `D_lit` … is neither `D_range` nor a
> (transitive) subtype of it in `xsd_hierarchy_edges`.

`xsd_hierarchy_edges` (line 3547) is a TREE, so two datatypes can
overlap without either being an ancestor of the other:
`xsd:int` and `xsd:nonNegativeInteger` share `xsd:integer` but neither
reaches the other. On that rule, `p rdfs:range xsd:nonNegativeInteger`
with `x p "5"^^xsd:int` is a clash — and `"5"^^xsd:int` IS a
non-negative integer. The rule's own premise ("value spaces are
identical, in a subtype relation, or fully disjoint") is false of the
DERIVED types it is applied to. No corpus test exercises the wrong
arm, so the F\* score does not move, but the check is unsound as
written.

The Lean port states the disjointness the rule needs instead of
inferring it from non-reachability: two recognised XSD datatypes clash
only when they sit in DIFFERENT families (`xsd:string`, `xsd:boolean`,
the numeric tower). That is weaker and sound, and it still fires on
`string-integer-clash`.

## 6. What C1 changes in the engine

`OWL/RLRules.lean` gains `ExtClash`, a THREE-row inductive kept apart
from `Clash`, plus `xsdValueSpacesDisjoint`, `cardinalityAtLeastOne`,
`isBottomProperty` and `existentialObligation`.
`OWL/RLClosure.lean` gains `dtRangeClashAt`, `bottomPropClashAt`,
`clsSvfBotAt`, `detectClashExt` and `detectClashPlus`;
`OWL/RLClosureIndexed.lean` gains the store mirrors and
`detectClashPlusI` with `detectClashPlusI_eq`.
`OWL/RLTheorems.lean` gains `detectClashExt_sound` and
`detectClashPlus_sound`. `OWL/RLSemantics.lean` gains
`RlExtClashConditions` and `rl_ext_clash_holds_false`.
`Harness/OwlProbe.lean` consults `detectClashPlusI`.

**Why `ExtClash` is a separate inductive and not three more `Clash`
constructors.** `Unified/OwlRlSchema.owlRlSchema_conditions` discharges
one `RlClashConditions` field per OWL 2 RL table row from RL schema
satisfaction alone. An extension row has no schema row to be discharged
from, so putting it in `Clash` would make that theorem unprovable —
`Clash` states the table, `ExtClash` states what the OWL 2 semantics of
`owl:Nothing`, the two bottom properties and the XSD datatype map force
beyond it. `detectClash` and `detectClash_sound` are byte-for-byte
unchanged.

## 7. Status — 2026-09-07, after C1 and the thing-nothing row

**Scores.** Full probe, default RL regime:

```
                              start of day       now
profile-RL.rdf                120 pass,  6 fail  121 pass,  5 fail (of 126)
profile-EL.rdf                105 pass, 15 fail  111 pass,  9 fail (of 121, 1 skip)
profile-QL.rdf                 82 pass,  5 fail   83 pass,  4 fail (of  87)
type-positive-entailment.rdf  333 pass, 75 fail  333 pass, 75 fail (of 412, 4 unsupported)
type-inconsistency.rdf         38 pass, 89 fail   44 pass, 83 fail (of 128, 1 skip)
type-consistency.rdf          503 pass, 76 fail  503 pass, 76 fail (of 583, 4 unsupported)
TOTAL                        1181 pass,266 fail 1195 pass,252 fail (of 1457)
```

Every ConsistencyTest section is unmoved throughout (76, 72, 58, 204 and
351 pass, with 0, 0, 0, 0 and 1 fail before and after), so the four new
rows fired on no premise the corpus asserts consistent — the check that
matters for a clash row.

**F\*-pass / Lean-fail gap, profile catalogs (RL against RL):**
26 units over 17 ids at the start of the day, **18 units over 11 ids
now**.

**Whole-corpus classification of every Lean failure**, each unit matched
against the committed F\* log for its catalog and test type (the
per-unit join `tools`-free script is in this record's commit message
trail; the F\* verdicts come from `formal/fstar/ocaml-output/`):

| | start of day | now |
|---|---|---|
| Lean FAIL units | 266 | 252 |
| … F\* records PASS | 249 | 235 |
| … F\* records FAIL | 16 | 16 |
| … F\* records no verdict | 1 | 1 |

The 235 is NOT a rule gap: 217 of it is on the three `type-*` catalogs,
where F\* ran DL and this column ran RL (§ 1, § 2b). The 16 F\*-also-FAIL
units are eight ids counted in two catalogs each — `WebOnt-Class-001`,
`WebOnt-Class-003`, `WebOnt-I5.3-014`, `WebOnt-I5.3-015`,
`WebOnt-I5.8-017`, `WebOnt-extra-credit-002`, `-003`, `-004` — so
neither engine passes them and they are not a Lean-side gap. The one
with no F\* verdict is `WebOnt-description-logic-909`, which the F\* log
records as skipped rather than passed.

**Closed.**

* **C1 — three clash rows** (`dt-range`, bottom-property existential,
  `cls-svf-bot`), commit `owl: three sound extension clash rows`. Six
  units: `string-integer-clash` (RL, EL),
  `New-Feature-BottomDataProperty-001` (EL),
  `New-Feature-BottomObjectProperty-001` (EL),
  `WebOnt-Restriction-001` (EL), `WebOnt-Restriction-002` (EL).
* **Part of C5 — `owl:Thing ≡ owl:Nothing`**, commit `owl: a fourth
  extension clash row`. Three units over one id: `WebOnt-Thing-003`
  (EL, QL, and `type-inconsistency`).

**Open.**

* **C2 — someValuesFrom existential witnesses**, 4 units:
  `bnode2somevaluesfrom` (EL), `somevaluesfrom2bnode` (EL),
  `WebOnt-someValuesFrom-003` (EL),
  `New-Feature-SelfRestriction-002` (EL). Needs
  `cls-svf-thing-materialize`, `cls-svf-thing-witness` and
  `cls-hasself2-synth` from § 3c.
* **C3 — comprehension**, 11 units: `WebOnt-I5.5-005` (RL, EL, QL),
  `New-Feature-DisjointDataProperties-002` (RL, EL, QL),
  `New-Feature-DisjointObjectProperties-002` (RL, EL, QL),
  `New-Feature-ObjectPropertyChain-BJP-002` (RL, EL). Needs the eight
  `comp_*` rules from § 3c. F\*'s own banner says folding that layer
  into the shared fixpoint took DL `type-inconsistency.rdf` from
  124 pass, 3 fail to 63 pass, 64 fail, so it must be a separate
  PE-only pass here too, never a closure extension.
* **C4 — annotation carry-over**, 3 units: `WebOnt-I4.6-005-Direct`
  (RL, EL, QL). NOT an annotation-filter gap: the Lean
  `OWL/DirectMappingFilter.lean` and the F\*
  `OWL.DirectMapping.Filter.fst` are the same function, and neither
  excludes the built-in `rdfs:comment`. F\* passes it through
  `owl_rule_named_equivalent_class_to_sameAs`
  (`OWL.Closure.fsti` line 2848): a GUARDED, DIRECT-semantics-gated
  rule emitting `C owl:sameAs D` from `C owl:equivalentClass D` when
  both are named classes and one carries some other property
  assertion, after which `eq-rep-s` copies the annotation across. The
  guard is load-bearing — `WebOnt-I4.6-004` is a NegativeEntailmentTest
  that a bare `equivalentClass` must NOT entail `sameAs` — and the rule
  must be gated on `test:semantics=DIRECT`, because the RDF-Based
  sibling `WebOnt-I4.6-005` has an identical premise and conclusion and
  expects the OPPOSITE verdict.
* **Rest of C5 — `owl:hasKey`**, 3 units: `New-Feature-Keys-001`
  (EL PE, 2 units incl. `type-*`), `New-Feature-Keys-002` (EL Inc).
  The Lean `prp-key` row exists; it does not fire because the premise
  writes `HasKey(owl:Thing () (:hasSSN))` and never types `:Peter` /
  `:Peter_Griffin` as `owl:Thing`, which no RL rule supplies.
* **The `type-*` catalogs under `--dl`** are measured for two of
  three (§ 2b); `type-consistency.rdf --dl` has no figure.

**Why C2, C3, C4 and the rest of C5 were not attempted here.** All four
need a new DERIVATION row, not a clash row. A clash row touches
`ExtClash`, one decision function, one store mirror, one soundness
lemma and one condition field. A derivation row touches `Derives`,
`conclusionsList`, the indexed store rows, `RlConditions`, the Herbrand
model discharge in `RLHerbrand.rlHerb_conditions` AND the schema bridge
in `Unified/OwlRlSchema.owlRlSchema_conditions` — and C4 additionally
needs a `test:semantics` mode threaded through the closure. That is a
different size of job and was not safe to start inside the remaining
window.

**Two of the 18 are already decided by machinery this tree has.**
`l4owl-probe --rl-refute` on the three profile catalogs:

```
                    closure alone      closure or refutation
profile-RL.rdf      121 pass,  5 fail  121 pass,  5 fail (of 126)
profile-EL.rdf      111 pass,  9 fail  113 pass,  7 fail (of 121, 1 skip)
profile-QL.rdf       83 pass,  4 fail   83 pass,  4 fail (of  87)
TOTAL               315 pass, 18 fail  317 pass, 16 fail (of 334)
```

The two the refuter decides are `bnode2somevaluesfrom`
(PositiveEntailmentTest) and `New-Feature-Keys-002`
(InconsistencyTest), both printed `DECIDED-BY-REFUTER`, so each is a
real refutation and not a pass by absence. They are NOT counted as
closed above, and the probe default is not being changed to pick them
up: the F\* RL regime never consults `dl_refutes` either
(`owl_runner.ml` line 1032, `Regime_RL -> false`), so scoring the Lean
profile catalogs with the refuter on would compare two different
procedures. The decision to keep the two score lines apart is
`docs/designissues/2026-09-04-owl-rl-resplit.md`. What this measurement
says is that the remaining profile gap is 16 units of missing rules
plus 2 units of regime choice, not 18 units of missing rules.

**The `type-inconsistency` gap that survives `--dl`.** Eleven ids, all
`no clash row fired`, against F\*'s 126 pass, 1 fail:
`Inconsistent Disjoint Dataproperties`,
`Inconsistent String Pattern with Disjoint Dataproperties`,
`Minus Infinity is not in owl:real`, `one=two`,
`WebOnt-description-logic-035`, `-040`, `-108`, `-502`, `-504`, `-909`,
`-910`. Two of those are not clean F\* passes either: `-909` is the
disputed fixture recorded as pending in
`docs/claude-rules/current-state.md`
(<https://github.com/danbri/factoidal/issues/299>), and `-910` is the
one test the F\* `type-inconsistency` log's
`HARNESS-DIAG-OWL … refuter_escapes:1` names. The remaining nine are
the real target for the next pass: the datatype-facet family
(`owl:real`, string patterns, disjoint data properties) and the
`WebOnt-description-logic` tableau family.

**Where a published result looks wrong.**

1. The F\* `dt-range-clash` check is unsound as written (§ 5). No corpus
   test exercises the wrong arm, so the F\* score does not move; the
   Lean port states the disjointness rather than inferring it, and
   `OWL/RLTests.lean` pins `p rdfs:range xsd:nonNegativeInteger` with
   `x p "5"^^xsd:int` as NOT a clash.
2. `docs/claude-rules/current-state.md`'s 2026-07-30 OWL update prints
   `type-consistency` Consistency as 337 pass, 15 fail (out of 352).
   The committed log
   `formal/fstar/ocaml-output/owl_type_consistency_results.log` line
   1226 says 340 pass, 12 fail (out of 352), 12 unsupported. The log is
   the measurement; the prose has drifted by three tests.
3. `WebOnt-I4.6-005-Direct` is a W3C-sanctioned VACUOUS entailment and
   is not a defect. Its `test:description` says "Under the direct
   semantics, test WebOnt-I4.6-005 must be treated as a positive
   entailment", and its conclusion ontology contains exactly one
   annotation axiom, which carries no Direct-Semantics content. Any
   engine passing it passes it by having no logical conclusion left to
   check. Recorded here because the `measuring-inference` rule against
   passing by deriving nothing would otherwise flag the fix as one, and
   because the F\* engine reaches the same verdict through a real
   derivation (the `sameAs` rule above) rather than through the empty
   conclusion.

## 8. Status — 2026-09-07 evening, after C2, C3, C4 and half of C5

**Scores.** Full probe, default RL regime, `lake exe l4owl-probe` from
`formal/lean4/`:

```
                              start of day       after C1           now
profile-RL.rdf                120 pass,  6 fail  121 pass,  5 fail  126 pass, 0 fail (of 126)
profile-EL.rdf                105 pass, 15 fail  111 pass,  9 fail  118 pass, 2 fail (of 121, 1 skip)
profile-QL.rdf                 82 pass,  5 fail   83 pass,  4 fail   87 pass, 0 fail (of  87)
type-positive-entailment.rdf  333 pass, 75 fail  333 pass, 75 fail  342 pass,66 fail (of 412, 4 unsupported)
type-inconsistency.rdf         38 pass, 89 fail   44 pass, 83 fail   44 pass,83 fail (of 128, 1 skip)
type-consistency.rdf          503 pass, 76 fail  503 pass, 76 fail  512 pass,67 fail (of 583, 4 unsupported)
TOTAL                        1181 pass,266 fail 1195 pass,252 fail 1229 pass,218 fail (of 1457)
```

`profile-RL.rdf` and `profile-QL.rdf` are **complete**: 126 of 126 and
87 of 87, with 0 fail in every one of the four test types.
`profile-EL.rdf` is 118 of 121 with 1 skip and 2 fail.

Every ConsistencyTest and NegativeEntailmentTest section is unmoved
across the whole day (76, 72, 58, 204, 351 pass with 0, 0, 0, 0, 1 fail;
6, 6, 3, 23 pass with 0 fail). That is the check that matters for both
kinds of change made here: a derivation row must not derive something a
premise asserts consistent, and a conclusion FILTER must not make a
negative test's conclusion easier to contain.

**Closed today, beyond C1.**

* **C2 — someValuesFrom existential witnesses** and **C3 —
  comprehension**, commit `owl(lean): the comprehension and
  existential-witness layer, PE-only`. New modules
  `L4Factoidal/OWL/Comprehension.lean` (eight rows in four stages,
  applied ONCE over the stable closure by `judgePositive` alone) and
  `L4Factoidal/OWL/ComprehensionTheorems.lean` (`CompStar` and
  `comprehensionLayer_sound`).

  C3 needed two rows the gap analysis had not named. The conclusion of
  `New-Feature-Disjoint{Data,Object}Properties-002` is a three-member
  `owl:AllDifferent` axiom, and nothing in the Lean closure produced the
  `owl:differentFrom` facts to build it from: the RL table states only
  the CLASH `prp-adp`, never its contrapositive. So the layer carries
  `pdw-diff`, the two contrapositives of `owl:propertyDisjointWith`
  (shared value, shared subject), before the `owl:AllDifferent` row.

  A note on how F\* passes those two, because the routes differ. F\*'s
  `eq-diff-adf` emits PAIRWISE two-member `owl:AllDifferent` scaffolds
  and its runner matches conclusions per-triple, so three pairwise
  witnesses satisfy a three-member conclusion pattern without any
  three-cell list existing. The Lean probe's default is the STRICT rule
  (one blank-node mapping for the whole conclusion graph, RDF 1.1
  Semantics interpolation lemma), under which a pairwise scaffold does
  not serve. The Lean row therefore builds the actual member list — and,
  because `owl:members` is a sequence whose order in a conclusion
  document is arbitrary, emits every permutation up to four members
  rather than one sorted order. A pass that depended on the engine's
  sort order agreeing with the conclusion would be a pass by
  coincidence.

* **C4 — `WebOnt-I4.6-005-Direct`**, commit `owl(lean): the built-in
  annotation properties are annotation properties`. `excludeAnnotation
  Triples` dropped a triple only when the graph itself typed the
  predicate `owl:AnnotationProperty`; the nine built-in annotation
  properties of Structural Specification § 5.5 carry no declaration
  triple, so `rdfs:comment` survived. Under the Direct Semantics an
  annotation assertion has no effect on the interpretation, so an
  annotation triple in a DIRECT-only conclusion is neither entailed nor
  refuted — which is what the test's own `test:description` says.

  **The F\* rule was NOT ported, deliberately.**
  `owl_rule_named_equivalent_class_to_sameAs` (`OWL.Closure.fsti` line
  2848) emits `C owl:sameAs D` from `C owl:equivalentClass D` for named
  classes under a DIRECT gate. That is unsound under both semantics.
  `EquivalentClasses(C D)` says the two class expressions have the same
  extension; it does not say the two IRIs denote the same resource.
  Under the Direct Semantics with punning the class and individual
  readings of an IRI are independent, so coextension says nothing about
  `SameAs`; under the RDF-Based Semantics `owl:equivalentClass` is
  § 5.8's condition on `ICEXT`, again not identity. The rule's DIRECT
  gate exists because `WebOnt-I4.6-004`, an RDF-Based
  NegativeEntailmentTest, would otherwise break — a description of what
  the gate avoids, not of what licenses the rule. This is the second
  entry in § 7's "where a published result looks wrong": the F\* score
  is right and the derivation behind it is not.

* **Half of C5 — `prp-key` on `owl:Thing`**, commit `owl(lean): a key on
  owl:Thing fires, and the refuter gets a wall clock`. `prp-key` needs
  `T(?x, rdf:type, ?c)`; when `?c` is `owl:Thing` no RL row supplies it.
  `ICEXT(I(owl:Thing))` is the set of all individuals (RDF-Based
  Semantics § 5.2), so the premise is discharged by the semantics rather
  than looked up, over IRI subjects (HasKey is about named individuals,
  Structural Specification § 9.5). Closes `New-Feature-Keys-001`.

* **The refuter's wall clock**, same commit. `--refute-budget` bounds
  BRANCH expansions; it does not bound the cost of one expansion, which
  is why `type-consistency.rdf --dl` did not finish in 40 minutes while
  `--cap-ms` bounded only the closure. `--refute-ms` (default 20000)
  stops the judge waiting on one call. The bound is on the HARNESS: the
  abandoned task runs until the process exits, because Lean cannot
  interrupt a pure computation. A timeout withholds a verdict, so the
  bound can only lose refutations, and each one prints a
  `REFUTER-WALLCLOCK` line.

**Still open.**

* **The other half of C5 — `New-Feature-Keys-002`** (EL
  InconsistencyTest, 1 unit). Same premise as Keys-001 plus
  `Peter owl:differentFrom Peter_Griffin`. The PE-only layer never sees
  an InconsistencyTest, so this needs an `ExtClash` row: a key on
  `owl:Thing`, two individuals agreeing on every key property, and an
  `owl:differentFrom` between them. Five files, the shape the C1 clash
  rows took.
* **`WebOnt-someValuesFrom-003`** (EL PE, 1 unit). Premise:
  `person ≡ ∃parent.person`, `fred a person`. Conclusion: two nested
  witness edges, `fred parent _:y`, `_:y parent _:z`, both typed
  `owl:Thing`. The layer's `svf-thing-wit` row covers the filler
  `owl:Thing` only; this needs the general `svf2` existential witness
  with a NAMED filler class, chained to depth two, which is a
  depth-capped rule (F\*'s `owl_rule_svf2_existential_witness`) and not
  a one-pass row. It is the one profile-catalog unit the F\* engine
  passes and this tree does not.
* **The model-theoretic soundness of `CompStar`** — see the OWL
  comprehension section of `docs/theorem-registry.md`.

## 9. The `type-*` catalogs under `--dl`, measured 2026-09-07 evening

`lake exe l4owl-probe --dl type-inconsistency.rdf
type-positive-entailment.rdf type-consistency.rdf` from
`formal/lean4/`, at the DEFAULT budgets (`--cap-ms 30000`,
`--refute-budget 64`, `--refute-ms 20000`). This is the regime the
committed F\* logs used for these three catalogs (§ 1).

**The whole run takes 8 min 37 s wall clock.** On the morning's tree
`type-consistency.rdf --dl` at the default refute budget did not finish
in 40 minutes, which is why § 2b measured it at `--refute-budget 16`
and could only report a lower bound. Two things changed. The comprehension
layer closes PE units in the closure, so fewer of them reach the
refuter at all; and `--refute-ms` bounds a single call. **The wall clock
tripped on no case in this run** (`grep -c REFUTER-WALLCLOCK` is 0), so
every figure below is a full-budget figure, not a withheld one.

| catalog / unit | Lean RL | Lean `--dl` closure alone | Lean `--dl` closure or refutation | F\* DL |
|---|---|---|---|---|
| `type-inconsistency.rdf` Inconsistency | 44 pass, 83 fail | 49 pass, 78 fail | **116 pass, 11 fail** (1 skip, of 128) | 126 pass, 1 fail |
| `type-positive-entailment.rdf` PE | 138 pass, 66 fail | 138 pass, 66 fail | **164 pass, 40 fail** (2 unsupported, of 206) | 195 pass, 9 fail |
| `type-positive-entailment.rdf` Consistency | 204 pass, 0 fail | 204 pass, 0 fail | **204 pass, 0 fail** (2 unsupported, of 206) | 199 pass, 5 fail |
| `type-consistency.rdf` PE | 138 pass, 66 fail | 138 pass, 66 fail | **164 pass, 40 fail** (of 206) | — |
| `type-consistency.rdf` NE | 23 pass, 0 fail | 23 pass, 0 fail | **23 pass, 0 fail** (of 23) | — |
| `type-consistency.rdf` Consistency | 351 pass, 1 fail | 351 pass, 1 fail | **351 pass, 1 fail** (2 unsupported, of 354) | — |
| all three catalogs | — | 905 pass, 209 fail | **1022 pass, 92 fail** (1 skip, 8 unsupported, of 1123) | 558 + 195 + 199 + 126 … see § 1 |

The `--dl` figure still BEATS F\* on `type-positive-entailment.rdf`'s
ConsistencyTest section (204 pass, 0 fail against 199 pass, 5 fail —
F\*'s five are cap escapes,
<https://github.com/danbri/factoidal/issues/326>).

The two score lines the probe prints under `--dl` are kept apart on
purpose: the closure is a sound consequence operator complete for the
RL profile, the refuter is a different procedure with a different
completeness claim, and a single number mixing them makes neither claim
statable (`docs/designissues/2026-09-04-owl-rl-resplit.md`).

The eleven `type-inconsistency` ids the refuter does not reach are
unchanged from § 7: the datatype-facet family (`owl:real`, string
patterns, disjoint data properties) and the `WebOnt-description-logic`
tableau family, two of which (`-909`, `-910`) are not clean F\* passes
either.


## 10. The 92 `--dl` failures by mechanism, 2026-09-07 night

Method: `lake exe l4owl-probe --dl type-inconsistency.rdf
type-positive-entailment.rdf type-consistency.rdf` from
`formal/lean4/`, default budgets. Every `FAIL` line carries the FIRST
conclusion triple the closure did not contain, or the clash-row
message; the grouping below is by the reasoning step that triple
needs, read against `OWL/Refute.lean` and
`OWL/NegationGoals.lean`. The F\* verdict column is the committed log
`formal/fstar/ocaml-output/owl_type_*_results.log`.

**The 92 units are 52 distinct ids.** A `PositiveEntailmentTest` id
appears in BOTH `type-positive-entailment.rdf` and
`type-consistency.rdf`, so each PE id costs 2 units; the 11
`InconsistencyTest` ids and the 1 `ConsistencyTest` id cost 1 each.
40 PE ids × 2 + 11 + 1 = 92. Any repair of a PE id is therefore worth
two units.

### 10.1 Where the refuter is never asked (28 PE ids, 56 units)

`negationGoals` answers `none` for these, so `--dl` falls back to the
closure verdict and the tableau is not run at all. `none` has two
causes, and they are different repairs.

**(a) The conclusion's content predicate has no goal builder — 6 ids,
12 units.** `negateContentTriple` covers class membership,
`rdfs:subClassOf`, `owl:equivalentClass`, `rdfs:subPropertyOf`,
`owl:equivalentProperty`, a named-subject `owl:complementOf` /
`owl:unionOf` / `owl:intersectionOf`, and a plain property assertion.
Everything else falls through to `none`.

| test id | conclusion predicate | F\* |
|---|---|---|
| `WebOnt-AllDifferent-001` | `owl:differentFrom` | PASS |
| `WebOnt-distinctMembers-001` | `owl:differentFrom` | PASS |
| `WebOnt-differentFrom-002` | `owl:differentFrom` | PASS |
| `rdfbased-sem-restrict-maxqcr-inst-obj-one` | `owl:sameAs` | PASS |
| `WebOnt-I5.21-002` | `owl:disjointWith` | PASS |
| `WebOnt-I5.24-004` | `rdfs:range` | PASS |

**(b) The conclusion has NO content triple at all — 12 ids, 24 units.**
`isStructuralTriple` classifies `rdf:type <meta type>` as scaffolding,
`isMetaTypeIri` lists the property characteristics and `owl:Thing`,
and `isStructuralPredicate` lists every class-expression builder. A
conclusion made only of such triples yields `contentTriples = []` and
`negationGoals = none`.

| test id | conclusion | F\* |
|---|---|---|
| `WebOnt-FunctionalProperty-004` | `prop rdf:type owl:FunctionalProperty` | PASS |
| `WebOnt-InverseFunctionalProperty-004` | `prop rdf:type owl:InverseFunctionalProperty` | PASS |
| `WebOnt-SymmetricProperty-002` | `p rdf:type owl:SymmetricProperty` | PASS |
| `WebOnt-I5.8-004` | `john rdf:type owl:Thing` | PASS |
| `WebOnt-I5.8-010` | `john rdf:type owl:Thing` | PASS |
| `WebOnt-AnnotationProperty-002` | `_:b1 rdf:type owl:Thing` | PASS |
| `WebOnt-Class-001` | `rdfs:Class rdf:type owl:Class` | FAIL |
| `WebOnt-Class-003` | `ex rdf:type rdfs:Class` | FAIL |
| `WebOnt-I5.5-001` | `rdf:first rdf:type owl:FunctionalProperty` | PASS |
| `WebOnt-I5.5-002` | `rdf:rest rdf:type owl:FunctionalProperty` | PASS |
| `WebOnt-imports-010` | `owl:imports rdf:type rdf:Property` | PASS |
| `WebOnt-Nothing-002` | `_:b0 owl:oneOf rdf:nil` | PASS |

The last six are RDF-Based-semantics claims about the OWL and RDF
vocabularies themselves, not Direct-Semantics axioms: a Direct
Semantics reasoner has no `rdf:first` to type. F\* answers them from
its RDF-vocabulary axiom table, not from its tableau. `WebOnt-Class-001`
and `-003` neither engine passes.

**(c) The conclusion asserts an ANONYMOUS class expression or list
cell the premise never writes — 10 ids, 20 units.** Same shape as § 7's
cluster C3 (comprehension), but in the DL regime; `negationGoals` sees
only structural triples again.

| test id | first missing triple | F\* |
|---|---|---|
| `WebOnt-description-logic-901` | `_:b1 owl:intersectionOf _:b3` | PASS |
| `WebOnt-description-logic-903` | `_:b1 owl:intersectionOf _:b3` | PASS |
| `WebOnt-I5.24-002` | `_:b0 owl:intersectionOf _:b1` | PASS |
| `WebOnt-I5.24-003` | `_:b1 owl:allValuesFrom A` | PASS |
| `WebOnt-unionOf-003` | `A-and-B owl:unionOf _:b1` | PASS |
| `WebOnt-unionOf-004` | `A-and-B owl:oneOf _:b1` | PASS |
| `WebOnt-cardinality-006` | `_:b0 owl:cardinality "1"^^xsd:nonNegativeInteger` | PASS |
| `WebOnt-extra-credit-003` | `_:b1 rdf:first N` | FAIL |
| `WebOnt-extra-credit-004` | `_:b1 rdf:first N` | FAIL |
| `WebOnt-someValuesFrom-003` | no single blank-node mapping serves every conclusion triple | PASS |

### 10.2 Where the refuter is asked and does not close (12 PE ids, 24 units)

`negationGoals` builds goals; `tableauConsistent` answers `some true`
or `none` on at least one of them. These are the tableau's own
incompleteness, and each names a rule.

| test id | conclusion | rule it needs | F\* |
|---|---|---|---|
| `Consistent-but-all-unsat` | `2a rdfs:subClassOf owl:Nothing` | nominals + counting (`owl:oneOf` size against inverse-functional chains) | PASS |
| `New-Feature-DisjointUnion-001` | `Stewie rdf:type Boy` | `owl:disjointUnionOf` — no axiom builder reads it | PASS |
| `WebOnt-unionOf-002` | `John rdf:type B` | union branching over a named class, with the disjunct closed by a nominal | PASS |
| `WebOnt-oneOf-003` | `myT rdf:type T2` | nominal (`owl:oneOf`) branching | PASS |
| `WebOnt-oneOf-004` | `i p "4"^^xsd:integer` | nominal branching over a data range | PASS |
| `WebOnt-complementOf-001` | `B owl:complementOf A` | the coverage half `¬A ⊑ B` — needs a nominal-free universal witness | PASS |
| `WebOnt-equivalentProperty-004` | `p owl:equivalentProperty q` | role inclusion both ways from `rdfs:subPropertyOf` pairs; the `¬q(a,b)` encoding needs a role successor the search does not build | PASS |
| `WebOnt-equivalentProperty-005` | as above | as above | PASS |
| `WebOnt-I5.3-014` | `x rdfs:subClassOf y` | subsumption through an `owl:imports` chain | FAIL |
| `WebOnt-I5.3-015` | `p rdfs:subPropertyOf q` | as above | FAIL |
| `WebOnt-I5.8-017` | `xx yy "1"^^xsd:decimal` | datatype VALUE equality on literals (`"1"^^xsd:decimal` vs `"1.0"`) | FAIL |
| `WebOnt-extra-credit-002` | `N-times-M owl:sameAs "345"^^xsd:int` | arithmetic over datatype values | FAIL |

### 10.3 InconsistencyTest, 11 ids, 11 units

| test id | mechanism | F\* |
|---|---|---|
| `Inconsistent Disjoint Dataproperties` | datatype facets: `>= 10` and `<= 10` force one value into two disjoint data properties | PASS |
| `Inconsistent String Pattern with Disjoint Dataproperties` | datatype facets: `xsd:pattern a(b\|c)` against disjoint data properties | PASS |
| `Minus Infinity is not in owl:real` | `owl:real` excludes the infinities; negative property assertion excludes 0 | PASS |
| `one=two` | nominals + inverse-functional counting (the class `a` is `{i,j,k}`, and a 1:1/2:1 chain over it) | PASS |
| `WebOnt-description-logic-035` | SHIQ ≤-rule over NAMED individuals | PASS |
| `WebOnt-description-logic-040` | as above, 1537 triples | PASS |
| `WebOnt-description-logic-108` | as above | PASS |
| `WebOnt-description-logic-502` | as above, 1114 triples | PASS |
| `WebOnt-description-logic-504` | as above, 1336 triples | PASS |
| `WebOnt-description-logic-909` | disputed fixture, <https://github.com/danbri/factoidal/issues/299> | pending |
| `WebOnt-description-logic-910` | the one F\* `refuter_escapes` case | FAIL |

### 10.4 ConsistencyTest, 1 unit

`type-consistency.rdf` carries one ConsistencyTest failure, unchanged
from § 9; it is a cap escape, not a wrong verdict.

### 10.5 The mechanism ledger, largest first

| mechanism | PE ids | Inc ids | units | where the repair goes |
|---|---|---|---|---|
| missing goal builder (§ 10.1a) | 6 | 0 | 12 | `OWL/NegationGoals.lean` |
| comprehension in a conclusion (§ 10.1c) | 10 | 0 | 20 | a PE-only materialisation pass |
| RDF-vocabulary meta claims (§ 10.1b) | 12 | 0 | 24 | an RDF/OWL vocabulary axiom table |
| nominals + counting | 4 | 2 | 10 | `OWL/Refute.lean` + `OWL/CountingOracle.lean` |
| SHIQ ≤-rule over named individuals | 0 | 5 | 5 | `OWL/Refute.lean` `isMergeableTerm` |
| datatype facets and value equality | 2 | 3 | 7 | `OWL/Refute.lean` + `XSD/Datatypes.lean` |
| role inclusion / imports subsumption | 4 | 0 | 8 | `OWL/Refute.lean` |
| arithmetic, disputed, cap | 2 | 1 | 6 | not planned |

Two of the eight rows are not Lean gaps against F\*: F\* also fails
`WebOnt-Class-001`, `-003`, `-extra-credit-002`, `-003`, `-004`,
`WebOnt-I5.3-014`, `-015`, `WebOnt-I5.8-017` and
`WebOnt-description-logic-910`, and `-909` is disputed. That is
9 ids — 17 units — where neither engine answers.

## 11. Completeness: what is proved, what is stated, what is open

Full SROIQ(D) completeness with a machine-checked proof is not
claimed, and nothing below should be read as claiming it.

### 11.1 The tableau has no blocking condition

`OWL/Refute.lean`'s `search` terminates on three caps, not on a
blocking condition:

* `maxWitnessDepth = 3` — the ∃-rule mints no successor below depth 3;
* `maxGeneratedWitnesses = 6` — at most six witnesses per node;
* the threaded `budget` (`--refute-budget`, default 64), plus the
  harness wall clock `--refute-ms`.

A cap and a blocking condition are different objects. Subset blocking
(Horrocks, Kutz and Sattler, *The Even More Irresistible SROIQ*, KR
2006, § 3; the pairwise / equality-blocking refinement for SHOIQ) stops
expansion when a node's label set is contained in an ancestor's, and
the argument that the branch still yields a model is what makes the
procedure a DECISION procedure: the blocked node is unravelled into an
infinite or cyclic model. A depth cap stops expansion at depth 3
whether or not the label set repeated, and the state left behind
witnesses nothing.

The consequence is already in the module header and is restated here
as a completeness statement: `tableauConsistent = some true` is NOT a
satisfiability claim, and no completeness claim follows from
termination. The engine is a SOUND REFUTATION procedure with an
INCOMPLETE search, and the corpus scores are scores of that.

### 11.2 The fragment a completeness proof is available for

The caps do not bite on

> **ALC ABox consistency with an acyclic (unfoldable) TBox**, where
> every concept has role-nesting depth ≤ 3 and no node carries more
> than 6 existential restrictions.

In that fragment the ∃-rule never reaches either cap, an acyclic TBox
unfolds in finitely many steps with no cycle for a blocking condition
to catch, and the search space is finite for a reason that is stated
rather than imposed. This is the fragment for which a completeness
theorem is worth attempting, and it is the smallest one that covers
any of the corpus ids in § 10.

### 11.3 What is proved

The LEAF of the completeness argument, in `OWL/TableauTheorems.lean`:

* `canon_models_all` — a label set of literals (atom, negated atom,
  `owl:Thing`) with no atom clash is satisfied, at a single domain
  element, by its own canonical interpretation. Depends on no axioms.
* `canon_rejects_bot` — `owl:Nothing` is in no model. Depends on no
  axioms.

Together they say the two clash conditions `Refuted.clash` and
`Refuted.botClash` are EXACTLY the obstructions to a model in the
literal fragment: clash-free means a model exists, and a model exists
means clash-free. That is the converse direction to `refuted_sound`,
restricted to the leaf.

### 11.4 The theorem still to prove, and what blocks it

    theorem search_complete_ALC
        (R : RoleAxioms) (A : List Assertion)
        (hFrag : InALC A) (hAcyclic : AcyclicTBox tb)
        (hDepth : RoleDepth A ≤ 3) (hEx : ExCount A ≤ 6) :
        ¬ Consistent R A → Refuted R A

Two things block it, and they are work items, not unknowns.

1. **The inductive lift.** `canon_models_all` covers the literal leaf.
   The lift needs the ⊓ / ⊔ decomposition cases and the ∀ / ∃
   successor construction — the canonical interpretation grows from
   one element to the expansion tree, and the role extension stops
   being `False`. This is ordinary structural induction over
   `Concept`; it is bounded work, not research.
2. **`search` is a `partial def`.** A completeness theorem about the
   EXECUTABLE engine needs an induction principle for it, and a
   `partial def` has none. The prerequisite is a fuel-indexed
   reformulation with a proof that the fuel-indexed and the partial
   versions agree — the same move `RLClosureIndexed.indexedClosure_eq`
   already made for the closure. The repository's no-new-`partial def`
   rule points the same way.

Until both land, the statement above stays an OBLIGATION in this
record, not a lemma with a hypothesis arranged to make it provable.

### 11.5 Features whose completeness is open, with the ids that need them

| feature | status | corpus ids that depend on it |
|---|---|---|
| blocking (subset / equality) | absent; replaced by a depth cap | every cyclic-TBox fixture; none of the § 10 ids is decided by it today |
| nominals (`owl:oneOf`) beyond the two size rules | partial | `one=two`, `WebOnt-oneOf-003`, `WebOnt-oneOf-004`, `WebOnt-unionOf-002`, `Consistent-but-all-unsat` |
| the counting oracle, wired into the search | `OWL/CountingOracle.lean` exists with a proved Farkas validator; `search` does not consult it | `one=two`, `Consistent-but-all-unsat` |
| SHIQ ≤-rule over named individuals | landed 2026-09-07 (§ 11.6); no id moved | `WebOnt-description-logic-035`, `-040`, `-108`, `-502`, `-504` |
| datatype facets in the clash rules | partial (`XSD/Facets.lean` value spaces; no pattern facet, no `owl:real`) | `Inconsistent Disjoint Dataproperties`, `Inconsistent String Pattern with Disjoint Dataproperties`, `Minus Infinity is not in owl:real`, `WebOnt-I5.8-017` |
| disjoint DATA properties | absent | the first two of the row above |
| role chains (`owl:propertyChainAxiom`) in the tableau | absent | none of the § 10 ids |
| `owl:disjointUnionOf` as an axiom source | absent | `New-Feature-DisjointUnion-001` |
| self restrictions (`owl:hasSelf`) as a labelled concept | graph-level only | `New-Feature-SelfRestriction-002` (profile-EL) |
| keys (`owl:hasKey`) beyond the graph-level rule | partial | `New-Feature-Keys-001` (profile-EL) |
| the RDF and OWL vocabulary axiom table | absent | § 10.1b, 12 ids |
| comprehension in a CONCLUSION under the DL regime | absent | § 10.1c, 10 ids |

### 11.6 A coverage defect in the ≤-rule, repaired

`isMergeableTerm` admitted blank nodes only, on the argument that a
named individual's graph-asserted edges cannot be rewritten. That
argument describes a rewriting merge the module no longer has:
`mergeInto` records an identification pair and `labelsOf` /
`successorsOf` pool the group through `identifiedWith`, over the input
graph as well as the expansion edges.

The exclusion was also unsound in the direction that matters. The
≤-rule refutes a node only when EVERY offered merge closes, and that is
an argument only if the offered merges COVER every coincidence a model
could choose. With `≤ k p` and more than `k` successors, pigeonhole
forces some two successor TERMS to denote one element; a pair the model
picks that was never offered breaks the cover. Offering only blank
nodes left every pair involving a named successor uncovered.

Named individuals are now offered. Literals stay out: a literal and an
IRI denote in disjoint domains (OWL 2 Direct Semantics § 2.2) and two
literals with different values are already `provablyDistinct`. The
residual, stated rather than hidden: a cardinality bound measured over
a LITERAL successor of an object property is outside this argument and
its cover is still incomplete.

Measured effect, `--dl type-inconsistency.rdf`: 116 pass, 11 fail
(1 skip, out of 128) before and after — the change closes no id. It is
landed as a soundness repair, not as a score move; the five
`WebOnt-description-logic` ≤-rule ids need the max-cardinality label to
reach the node first, which is a separate gap.
