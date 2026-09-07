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

## 6. Status

See § 8 below, kept current as clusters close.
