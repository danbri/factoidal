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

Measured 2026-09-07, `lake exe l4owl-probe --dl`, default caps
(`--cap-ms 30000`). The run was stopped by the operator on a disk-space
floor part-way through `type-consistency.rdf`, so that catalog has no
`--dl` figure yet.

| catalog / unit | Lean RL | Lean `--dl` | F\* DL |
|---|---|---|---|
| `type-inconsistency.rdf` Inconsistency | 38 pass, 89 fail | **116 pass, 11 fail** | 126 pass, 1 fail |
| `type-positive-entailment.rdf` PE | 129 pass, 75 fail | **157 pass, 47 fail** | 195 pass, 9 fail |
| `type-positive-entailment.rdf` Consistency | 204 pass, 0 fail | 204 pass, 0 fail | 199 pass, 5 fail |
| `type-consistency.rdf` (all units) | 503 pass, 76 fail | not measured | 558 pass, 21 fail |

So the regime accounts for 78 of the 89 `type-inconsistency` failures
and 28 of the 75 `type-positive-entailment` PE failures. The Lean
`--dl` figures also BEAT F\* on `type-positive-entailment`'s
ConsistencyTest section (204 pass, 0 fail against 199 pass, 5 fail —
F\*'s five are `unsupported` cap escapes, #326).

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
