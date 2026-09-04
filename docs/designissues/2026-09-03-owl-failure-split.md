# The OWL 2 conformance gap, split by cause

Date: 2026-09-03/04. Companion to
[`2026-09-03-fstar-lean-coverage-gap.md`](2026-09-03-fstar-lean-coverage-gap.md),
which measured OWL as the largest conformance gap between the F\* and the
Lean 4 trees. This document says WHAT KIND of failure the gap is made of,
because a fix plan built on the wrong kind sends the next session after a
phantom.

Tracked in <https://github.com/danbri/factoidal/issues/404>.

## The measurement this document is built on

Binary: `formal/lean4/.lake/build/bin/l4owl-probe`, built from commit
`6a0303372`. Corpus: `third_party/testing/owl`, six catalogs
(profile-RL, profile-QL, profile-EL, type-positive-entailment,
type-inconsistency, type-consistency). Per-closure cap 30000 ms, closure
fuel 100, refuter budget 64. One unit of score is a (test case, test type)
pair, the same unit the F\* `owl_runner` scores.

| Regime | Score |
|---|---|
| RL closure only | 1128 pass, 319 fail, 2 skip, 8 unsupported (out of 1457) |
| RL closure + class-expression materialisation + tableau refuter (`--dl`) | 1208 pass, 239 fail, 2 skip, 8 unsupported (out of 1457) |

⚠️ **Two figures in circulation are stale.** The `--dl` line quoted from
the 2026-08-23 parity ledger was 1193 pass, 254 fail; measured today it is
1208 pass, 239 fail. The RL line quoted in the coverage-gap document was
1131 pass, 316 fail; measured today it is 1128 pass, 319 fail. Use the
table above. The RL difference of 3 units is within the run-to-run
movement of the 30-second per-closure cap on a loaded machine (`cap_hits=4`
in this run); the `--dl` difference of 15 units is not, and the ledger line
predates measurement-tool repairs landed the same day.

## The four categories

- **A — the construct is absent.** The engine has no rule row for this
  axiom form. No proof fixes an absent row; this is coding.
- **B — the reasoning is incomplete.** The construct has a row, and the
  engine still does not derive (or wrongly derives) the entailment.
- **C — the test is not about the engine.** A parse failure, a manifest
  shape the runner does not read, a cap trip, a harness defect.
- **D — withdrawn or disputed upstream.**

### Counts

| Category | RL closure only | `--dl` |
|---|---|---|
| A — construct absent | 41 | 36 |
| B — reasoning incomplete | 274 | 202 |
| C — not about the engine | 4 | 1 |
| D — withdrawn upstream | 0 | 0 |
| **Total FAIL units** | **319** | **239** |

## The classification method, and what it cannot see

Stated next to the result, per anti-pattern 28.

1. Every FAIL line the probe prints carries a cause tag it assigned at the
   point of failure (`parser:`, `closure-gap:`, `cap:`, `harness:`) and,
   for a positive-entailment failure, the FIRST conclusion triple it could
   not find in the closure. `tag ∈ {parser, cap, harness}` is category **C**
   directly. That part is exact.
2. Category **D** was tested by scanning each catalog for XML comment
   blocks and collecting the `test:identifier` of every `test:TestCase`
   inside one. **No OWL catalog entry is commented out upstream.** The
   RDF/XML investigation earlier the same day found 7 such entries in the
   RDF test manifests; the OWL corpus has none, so no OWL failure is
   attributable to a withdrawn test.
3. Category **A** is decided by a marker, not by reading the engine's
   behaviour on the case. The implemented rows of
   `L4Factoidal/OWL/RLClosure.lean` (`conclusionsList` and `clashRows`)
   were listed and diffed against the OWL 2 Profiles §4.3 rule tables. A
   failing unit is category A when its premise or conclusion RDF/XML uses
   a construct whose ONLY relevant row is on the missing side of that diff.
4. Everything else is **B**.

**What the method cannot see.**

- The category-A marker is a construct-occurrence test, not a causal test.
  A case that uses `owl:hasSelf` incidentally while failing for an
  unrelated reason is counted A, which inflates A. A case that fails
  because of an absent row this diff did not spot is counted B, which
  inflates B. The marker is a work order, not a verdict; the honest
  correction is the MEASURED delta after the row lands, and that delta is
  recorded per fix commit below.
- The RL and `--dl` failures at a construct-marker are not disjoint from
  the tableau: the refuter closes 64 of the 97 RL-mode `type-inconsistency`
  failures, so a construct that looks absent in RL mode may already be
  decided by the refuter in `--dl` mode. That is why both columns are
  given.
- The probe reports only the FIRST missing conclusion triple. A conclusion
  missing five triples for five different reasons is classified on the
  first one.
- A cap trip is classified C, and a cap trip may be HIDING a category-A or
  category-B failure underneath it. There are 4 such units in RL mode, 1 in
  `--dl`.

## Category A, ranked by units blocked

The rule identifiers are the OWL 2 Profiles (2nd Edition) §4.3 table row
names. Each row named here has NO implementation in
`L4Factoidal/OWL/RLClosure.lean`; that was checked by name and by grep, not
inferred.

| Rank | Absent rows | Construct | RL units | `--dl` units |
|---|---|---|---|---|
| 1 | eq-diff2, eq-diff3 | `owl:AllDifferent` with `owl:members` / `owl:distinctMembers` | 16 | 14 |
| 2 | scm-svf1, scm-svf2, scm-avf1, scm-avf2, scm-hv, scm-op, scm-dp | schema-level restriction and property rows | 10 | 10 |
| 3 | cls-hs1, cls-hs2 | `owl:hasSelf` | 7 | 6 |
| 4 | none (RL has no row family) | user-defined datatypes: `owl:onDataRange`, `owl:withRestrictions`, `owl:datatypeComplementOf` | 3 | 2 |
| 5 | none | `owl:disjointUnionOf` | 2 | 2 |
| 6 | cls-maxqc3, cls-maxqc4 | `owl:maxQualifiedCardinality` = 1 | 2 | 2 |
| 7 | prp-adp | `owl:AllDisjointProperties` | 1 | 0 |

The engine's implemented clash rows are eq-diff1, prp-irp, prp-asyp,
prp-pdw, prp-npa1, prp-npa2, cls-nothing2, cls-com, cls-maxc1, cls-maxqc1,
cls-maxqc2, cax-dw and cax-adc — thirteen of the seventeen no-consequent
rows of the tables. The four absent ones are eq-diff2, eq-diff3, prp-adp
and dt-not-type.

## Category B, sub-divided

B is not one thing. Sub-buckets, by the same first-missing-triple evidence:

| Sub-bucket | RL | `--dl` |
|---|---|---|
| B5 — an assertional entailment (`rdf:type`, `owl:sameAs`, a domain property) is not derived | 107 | 97 |
| B3 — a premise asserted inconsistent produces no clash | 106 | 39 |
| B1 — the conclusion RESTATES a class expression (`owl:unionOf`, `owl:intersectionOf`, `rdf:first`, a cardinality triple) that the premise does not contain literally | 56 | 58 |
| B2 — an annotation (`rdfs:comment`, `rdfs:label`) is expected to travel across `owl:equivalentClass` | 5 | 5 |
| B4 — a consistent premise produces a clash, or the closure trips the cap | 0 | 3 |

Two observations that change what is worth doing:

- **The tableau refuter already earns its keep on B3** — 106 RL failures
  fall to 39 under `--dl`. Continued work on inconsistency detection
  belongs in the refuter, not in new RL clash rows.
- **B1 is a different problem from the rest.** These conclusions ask the
  engine to produce class-expression STRUCTURE, which neither an RL closure
  nor a tableau refutation produces. It needs either the comprehension
  principles of the OWL 2 RDF-Based Semantics or a conclusion matcher that
  works modulo blank-node structure. 56 to 58 units, one design decision.
- **Every NegativeEntailmentTest passes** in both regimes. No B failure is
  a negative-entailment failure.

## The tableau, its termination, and the 32 `partial def`

Finding, not a work order.

The OWL Lean tree holds 32 of the repository's 217 `partial def`. They are
in `L4Factoidal/OWL/Refute.lean` (14), `L4Factoidal/OWL/Materialise.lean`
(12), `L4Factoidal/OWL/FunctionalSyntax.lean` (5) and
`L4Factoidal/OWL/QueryMaterialise.lean` (1). `L4Factoidal/OWL/Tableau.lean`
itself holds none.

Only ONE of the 32 is the tableau expansion: `Refute.search`. The other 13
in `Refute.lean` are supporting recursions over class expressions and lists
(`nnf`, `ceDefinite`, `repOf`, `subpropertiesOfRaw`, …) whose termination
is a structural or a list-length argument, not a blocking argument. The 12
in `Materialise.lean` are the mutually recursive class-expression
membership test. The 5 in `FunctionalSyntax.lean` are parser recursions.

**Termination is not implicated in any failure measured here.** The probe
reports 4 cap trips in RL mode and 1 in `--dl` mode out of 1457 units, and
a cap trip is a wall-clock budget on the CLOSURE, not a non-terminating
tableau; the refuter runs under an explicit `--refute-budget` and returns.
No failure in either run was a hang.

**Recommendation.** Do not open the blocking-condition proof for
`Refute.search` on conformance grounds — the conformance evidence does not
ask for it. Open it on assurance grounds when the OWL work is otherwise
level, and open it as ONE issue for `Refute.search` alone: the other 31 are
ordinary structural recursions that should retire with a fuel parameter or
a well-founded measure, which is cheaper and unrelated to blocking. A
separate agent is working the `partial def` backlog in ShEx and RIF; the
OWL 32 must not be picked up in the same landing.

## What this says to do next

1. Close the ranked category-A rows. They are verbatim table transcriptions
   with an existing proof pattern per row. 41 RL units and 36 `--dl` units
   are marked, and the realised delta is the correction to that estimate.
2. Decide B1 (56 to 58 units) as a design question before writing code.
3. Leave B3 to the refuter.
4. Do not treat the OWL `partial def` count as conformance work.

## ⚠️ Every score above and below this line, until the conclusion-matcher row, was measured with a permissive conclusion matcher

Until 2026-09-04 the probe decided a PositiveEntailmentTest by letting
each conclusion triple choose its OWN witness for a blank node, so a
conclusion `_:x a C . _:x a D .` held on a closure with `a a C` and
`b a D`. RDF 1.1 Semantics asks for one functional mapping over the
whole conclusion graph. Every figure in this document that predates
the landing below is therefore an UPPER BOUND.

Measured cost of the correction, `f2988f1e6`, `cap_hits=0`:

| Regime | Permissive matcher | Corrected (one mapping) |
|---|---|---|
| RL closure only | 1160 pass, 287 fail, 2 skip, 8 unsupported (out of 1457) | 1158 pass, 289 fail, 2 skip, 8 unsupported (out of 1457) |
| `--dl` | 1294 pass, 153 fail, 2 skip, 8 unsupported (out of 1457) | 1291 pass, 156 fail, 2 skip, 8 unsupported (out of 1457) |

2 RL units and 3 `--dl` units, on two disjoint cases
(`WebOnt-I5.26-009` in RL, `WebOnt-someValuesFrom-003` in `--dl`).
NegativeEntailmentTest 38 pass, 0 fail (out of 38) in all four runs.
Reasoning, specification quotes and per-case detail:
[`2026-09-04-owl-conclusion-matching.md`](2026-09-04-owl-conclusion-matching.md).
`--wildcard-match` on `l4owl-probe` reproduces the superseded rule, so
any row above can be re-measured on its own terms.

## Fix landings measured against this split

| Commit | Rows added | RL before → after | `--dl` before → after |
|---|---|---|---|
| `ae73d6e7d` | cls-hs1, cls-hs2 (`owl:hasSelf`) | 1128 pass, 319 fail → 1135 pass, 312 fail | 1208 pass, 239 fail → 1211 pass, 236 fail |

**The marker over-counted, and by how much.** The marker put 7 RL units
and 6 `--dl` units on `owl:hasSelf`. The rows closed 4 RL units and 3
`--dl` units:

- RL, closed by the rows: `New-Feature-SelfRestriction-001` in three
  catalogs, and `Footnote-not-about-self [InconsistencyTest]`.
- RL, closed by nothing: `WebOnt-miscellaneous-001`, `-002` and `-011`
  `[ConsistencyTest]` tripped the 30-second closure cap in the before run
  and not in the after run. That is cap variance and is NOT credited to the
  rows. It also means the RL before figure of 319 fail carries three units
  of cap noise.
- `--dl`, closed by the rows: `New-Feature-SelfRestriction-001` in three
  catalogs. `Footnote-not-about-self` was already decided by the tableau
  refuter in this regime, so the row earns nothing there.
- Still failing with the rows in place: `New-Feature-SelfRestriction-002`,
  whose conclusion asks for the `owl:hasSelf` restriction triple itself.
  That is a category-B1 failure — a conclusion that restates a class
  expression — and no rule row closes it.

No test regressed in either regime.

### `a3eb7bd11` — eq-diff2, eq-diff3, prp-adp

| Rows added | RL before → after | `--dl` before → after |
|---|---|---|
| eq-diff2, eq-diff3, prp-adp | 1135 pass, 312 fail → 1138 pass, 309 fail | 1211 pass, 236 fail → 1211 pass, 236 fail |

**The marker over-counted again, and further.** It put 16 RL units on
eq-diff2/3 and 1 on prp-adp. The rows closed 3 RL units and 0 `--dl` units:
`rdfbased-sem-ndis-alldifferent-fw`,
`rdfbased-sem-ndis-alldifferent-fw-distinctmembers` and
`rdfbased-sem-ndis-alldisjointproperties-fw`, all `[InconsistencyTest]`.
The `--dl` column does not move because the tableau refuter already decided
all three. Most of the remaining marked units are B1: their conclusion asks
for the `owl:AllDifferent` triple itself, which no clash row produces. No
test regressed in either regime; cap hits were 0 on both sides.

**A soundness finding from this landing.** The engine rows take their pair
from two distinct list CELLS, not only from two distinct terms. The
distinct-term reading alone — which is what `caxAdcAt` uses — fires on
`WebOnt-miscellaneous-001`, `-002` and `-011`, which the corpus asserts
consistent: eq-rep-o copies an `rdf:first` value across
`vin:Red owl:sameAs food:Red`, so one list cell then carries two
co-referring members, and a term-distinct pair drawn from ONE cell is one
position of `LIST[?y, ?z1, ..., ?zn]`, not two. **`caxAdcAt` carries the
same exposure and was not changed.** It does not misfire on this corpus
today, and it should be narrowed the same way.

### `d980a444d` — the nine annotation-property axiomatic triples

| Rows added | RL before → after | `--dl` before → after |
|---|---|---|
| OWL 2 RDF-Based Semantics Tables 6.2 and 6.5, `owl:AnnotationProperty` typings | 1138 pass, 309 fail → 1156 pass, 291 fail | 1211 pass, 236 fail → 1229 pass, 218 fail |

Sub-bucket B5. Nine triples, transcribed from Section 6 "Axiomatic
Triples": `owl:versionInfo`, `owl:deprecated`, `owl:priorVersion`,
`owl:backwardCompatibleWith` and `owl:incompatibleWith` from Table 6.2,
and `rdfs:comment`, `rdfs:label`, `rdfs:seeAlso` and `rdfs:isDefinedBy`
from Table 6.5, each `rdf:type owl:AnnotationProperty`. The nine
`rdfbased-sem-prop-*-type` cases have an EMPTY premise ontology, so no
premise-driven row can reach them.

18 units closed in each regime, and they are the same 18: the nine
cases, each scored as a `PositiveEntailmentTest` in both the
`type-positive-entailment` and the `profile-RL` catalog. No test
regressed; `cap_hits` 0 before and after; `closure_rounds` unchanged.
**The prediction and the realised delta agree exactly** — the first
landing in this document where they do, and the reason is that the
prediction was made from the failing units' MISSING CONCLUSION TRIPLE,
not from a construct-occurrence marker.

Implementation note: the premise-free row `dtType1Builtin` was renamed
`premiseFreeAxiom` and its membership list widened from
`builtinDatatypeAxioms` to `premiseFreeAxioms`. The row already had a
`Derives` constructor, an `RlConditions` field, a Herbrand instance and
an object-language schema row, so widening the list reuses all four.
Any further axiomatic-triple table lands the same way, as a list
extension.

### `cc4049738` — the rest of Table 6.5

| Rows added | RL before → after | `--dl` before → after |
|---|---|---|
| OWL 2 RDF-Based Semantics Table 6.5, the other thirteen triples | 1156 pass, 291 fail → 1158 pass, 289 fail | 1229 pass, 218 fail → 1231 pass, 216 fail |

2 units in each regime, both `WebOnt-Class-002
[PositiveEntailmentTest]`: `rdfs:Class rdfs:subClassOf owl:Class` plus
cax-sco turns the premise `ex rdf:type rdfs:Class` into the conclusion
`ex rdf:type owl:Class`. No test regressed; `cap_hits` 0; closure rounds
5512 → 5572 (RL) and 6099 → 6159 (`--dl`).

**Table 6.1 was written, built and removed, and the measurement is the
reason.** Table 6.1 "Axiomatic Triples for the Classes of the OWL 2
RDF-Based Vocabulary" is 51 triples, and they put a CYCLIC
`rdfs:subClassOf` lattice over the whole OWL 2 class vocabulary into
every closure — `owl:Class rdfs:subClassOf rdfs:Class` from Table 6.1
against `rdfs:Class rdfs:subClassOf owl:Class` from Table 6.5, and
`owl:ObjectProperty rdfs:subClassOf rdf:Property` against
`rdf:Property rdfs:subClassOf owl:ObjectProperty`. scm-sco saturates
that lattice in every closure: six `RLTests` saturation guards went red
and `RLSemantics` elaboration went from 26 s to 189 s. This is the same
feedback the `drivesXsdAxioms` doc comment records for the XSD tower.
Table 6.1 needs a guarded form, not a longer unconditional list. Its
cost, unpaid, is `WebOnt-Class-003` (2 RL units), whose conclusion asks
the converse direction.

### `a32c3275a` — cax-adc takes its class pair from two distinct CELLS

| Rows changed | RL before → after | `--dl` before → after |
|---|---|---|
| cax-adc, narrowed to the cell walk | 1158 pass, 289 fail → 1158 pass, 289 fail | 1231 pass, 216 fail → 1231 pass, 216 fail |

The soundness exposure the `a3eb7bd11` landing recorded and did not
close. `caxAdcAt` read its member pair through `listElems` — two
distinct TERMS of the member list, with no requirement that they sit
in different positions of it — while eq-diff2, eq-diff3 and prp-adp
had already been given the distinct-CELL guard. It now walks
`listCells` and reads each cell's own `rdf:first`, matching
`eqDiff2At` exactly.

`Clash.caxAdc` is unchanged and still asks only for two distinct-TERM
`ListMember`s, so the engine row stays strictly weaker than the
specification row it discharges. `caxAdcAt_sound` is rewritten through
`listCells_sound`.

**Nothing moves in either regime.** Not one unit, and `clashes`
(53 RL, 124 `--dl`), `closure_rounds` and `cap_hits` (0 in both) are
identical before and after. The narrower guard costs nothing on this
corpus; what it removes is the exposure, not a test.

### scm-svf1, scm-svf2, scm-avf1, scm-avf2, scm-hv — landed, with the
materialiser budget repaired first

Rank 2 of the category-A table. The five rows are transcribed verbatim
from OWL 2 Profiles (2nd Edition) 4.3 Table 9. They were written and
measured on 2026-09-04, could not be landed that day because the `--dl`
regime ran out of memory, and are landed now with the defect that
caused it repaired.

| Regime | before → after (out of 1457) |
|---|---|
| RL closure only | 1162 pass, 285 fail → 1173 pass, 274 fail |
| `--dl` | 1316 pass, 131 fail → 1326 pass, 121 fail |

Both baselines were re-measured on `2a382b853`; `cap_hits` is 0 before
and after in both regimes.

#### The blow-up was NOT in the refuter, and not in the closure

Three agents worked this case and the first two were each partly
wrong, so the evidence is recorded with the method that produced it.

- The first reading, written into this document and into
  `skills/measuring-inference` section 10, was that "the refuter reads
  the extra `rdfs:subClassOf` edges between restriction nodes as
  general class inclusions and branches on each one". **That is
  false.** With `tableauConsistent` stubbed to `none` the case still
  died, at 414 s and 10.08 GB; with `--refute-budget 1`, 344 s and
  9.14 GB.
- The RL closure does not grow enough to matter either. The case the
  run dies on is `WebOnt-description-logic-202
  [PositiveEntailmentTest]`, whose first closure is 500 premise triples
  to 1 869 triples in 6 rounds, in 39 ms, with the five rows in place.

The blow-up is inside `OWL.Mat.materialiseWithBudget`, and it was
localised by timing its parts: witnesses 0 ms, subject collection 36
ms, `eqcExpansion` 0 ms, `directBooleanSubclasses` 14 ms, and
`membershipsForBNodeCes` never returned. Narrowing further, ONE
(individual, class expression) pair did not return: the individual
`test#V8472` against the blank node `_:b3`, which parses as
`∃ R1 . C10`.

#### The mechanism: an un-memoised depth-8 branching walk

`isMember` on `∃ p . c` that finds no witness edge falls back to
`typeCEsOf`, which expands each named type of the individual through
`namedSuperCEs` — the class expressions provably above it, followed
through further named classes to a depth of 8. That walk had **no
visited set**: it re-descended into every named superclass along every
path. A named class with `k` outgoing `rdfs:subClassOf` /
`owl:equivalentClass` edges therefore cost of the order of `k ^ 8`.

The five `scm` rows add `rdfs:subClassOf` edges between restrictions,
scm-sco closes them transitively, and named classes inherit them. In
the closure of `WebOnt-description-logic-202` there are 818
`rdfs:subClassOf` triples and one class, `test#C76`, carries 18 of
them. `18 ^ 8` is about `1.1 × 10^10`.

The repair is a breadth-first walk with a visited set
(`namedSuperCEsGo`). The RESULT SET is unchanged — a named class
contributes the same expansion however it is reached, breadth-first
reaches each class at its shortest distance, and every consumer reads
the list with `List.any` — so this is a speed change, not a semantic
one. With it, the pair that did not return in eight minutes is part of
an 11 ms materialisation pass.

#### The budget counted pairs, and a pair count is not a cost

`materialiseWithBudget` capped the pass at 400 000 (individual, class
expression) PAIRS. The pass that exhausted 9.1 GB and was killed
presented **12 596 pairs** — thirty-two times under the cap. A budget
in pairs cannot see a change that raises the cost of every pair while
moving the pair count not at all, which is exactly what a rule row
that adds `rdfs:subClassOf` edges does.

The budget now counts the WORK. One counter (`Mat.Work`, a
`StateM`) runs across the whole pass — witnesses and both membership
passes. Every `isMember` entry spends one unit, and every class
expression a superclass walk hands back spends one unit. Running out
answers `none`, the same answer an unreadable expression gets, and
raises `hit` so the caller reports a cap hit instead of reading a
truncated pass as a complete one.

📊 The new default, 4 000 000 units, comes from a measurement. On the
whole OWL corpus under `--dl` the most expensive single
materialisation pass spends about 400 000 units; the budget is ten
times that, so no case on this corpus trips it (`cap_hits` 0) and a
premise an order of magnitude harder than anything in the corpus still
gets a reported cap rather than an unbounded run.

#### The measured cost of the landing

`/usr/bin/time -l`, `type-positive-entailment.rdf` alone (412 units)
and the whole corpus (1457 units), on `2a382b853` and after:

| Run | wall | peak resident | score |
|---|---|---|---|
| catalog, `--dl`, before | 269 s | 136 MB | 356 pass, 52 fail (out of 412) |
| catalog, `--dl`, after | 571 s | 138 MB | 361 pass, 47 fail (out of 412) |
| corpus, `--dl`, before | 653 s | 237 MB | 1316 pass, 131 fail (out of 1457) |
| corpus, `--dl`, after | 2173 s | 212 MB | 1326 pass, 121 fail (out of 1457) |
| corpus, RL, before | 122 s | 203 MB | 1162 pass, 285 fail (out of 1457) |
| corpus, RL, after | 26 s | 223 MB | 1173 pass, 274 fail (out of 1457) |

Peak resident memory does not move. Wall clock does: the five rows
make the closure larger and the refuter has more class inclusions to
work with. That is a cost to watch, not a blow-up.

The guarded form (`c1 ≠ c2` on the executable row) that the earlier
agent proposed is NOT needed and was not taken: the rows are landed
verbatim, so `RLTheorems` T4 stays a completeness theorem over the
printed table row.

### `cb1883e0f` — scm-op and scm-dp

| Rows added | RL before → after | `--dl` before → after |
|---|---|---|
| scm-op, scm-dp | 1158 pass, 289 fail → 1160 pass, 287 fail | 1231 pass, 216 fail → 1233 pass, 214 fail |

OWL 2 Profiles (2nd Edition) 4.3 Table 9, verbatim:
`T(?p, rdf:type, owl:ObjectProperty) | T(?p, rdfs:subPropertyOf, ?p)
T(?p, owl:equivalentProperty, ?p)`, and the same two conclusions from
`owl:DatatypeProperty`.

2 units in each regime, and they are the same 2: both
`rdfbased-sem-eqdis-eqprop-rflxv [PositiveEntailmentTest]`, scored in
the `type-positive-entailment` and the `type-consistency` catalog.
**Predicted 2, realised 2 in RL and 2 in `--dl`**, no regressions in
either regime; `cap_hits` 0, `clashes` 53 (RL) and 124 (`--dl`) and
`closure_rounds` 5572 (RL) and 6159 (`--dl`) all unchanged. The case needs BOTH rows: its premise
declares one `owl:ObjectProperty` and one `owl:DatatypeProperty` and
its conclusion asks for `owl:equivalentProperty` on each.

The `--dl` cost gate above was run first: 130 s and 141 MB peak on the
`type-positive-entailment` catalog, against 109 s and 141 MB without
the rows. Peak memory does not move.

### The conclusion matcher: one blank-node mapping, not a per-triple wildcard

| Change | RL before → after | `--dl` before → after |
|---|---|---|
| `graphInClosure?` replaces per-triple `inClosure` as the default | 1160 pass, 287 fail → 1158 pass, 289 fail | 1294 pass, 153 fail → 1291 pass, 156 fail |

A CORRECTION, not a regression: the two units and the three units were
passes that no computed entailment supported. See the banner above and
[`2026-09-04-owl-conclusion-matching.md`](2026-09-04-owl-conclusion-matching.md).

## The `--dl` cost of the five restriction rows: NOT intrinsic

Date 2026-09-04. The five `scm-svf1/svf2/avf1/avf2/hv` rows landed in
`9ce7191ab`, bought 11 RL and 10 `--dl` units, and took the
whole-corpus `--dl` run from about 653 s to over 3000 s. The section
above recorded the FIRST cost gate — peak resident memory, repaired in
`e970afc51` — and left the time cost unexplained, with the reasonable
suspicion that the tableau simply branches on the extra
`rdfs:subClassOf` edges and the cost is real.

**It is not real.** The time was two accidental blow-ups, one in the
store the TBox pass reads and one in the TBox it builds. With both
repaired the corpus tests FEWER axioms per tableau pass WITH the five
rows than it did without them.

### Method, stated beside the result

1. `/usr/bin/sample <pid> 20 1` against a running `l4owl-probe --dl` —
   a call-tree attribution over 14,419 samples of the working thread,
   not a guess from reading the code. Repeated against the repaired
   binary, and against the unrepaired binary on the same catalog.
2. `l4owl-probe --tbox-census`, added for this work: for every case it
   computes the `--dl` premise closure, then prints the closure size,
   the TBox size, how many of its axioms are STRUCTURALLY DISTINCT, the
   node and label counts of the initial tableau state, and the
   axiom-test count of one `onePass`. `onePass` folds over the whole
   TBox once per node in `injectGlobalAxioms`, once per LABEL in
   `applyAxioms`, once in `applyAxiomsEdges` and once in
   `applyAxiomsConj`, so

       tests_per_pass = tbox * (3 * nodes + labels)

   and `search` runs it up to `--refute-budget` (default 64) passes per
   goal. **A count does not move when the machine is loaded.** That
   mattered: load average on this laptop moved between 2 and 51 on 8
   cores across the day, and every wall clock taken on it is worth less
   than the count.

### Defect one: the TBox pass read the graph by list scan

`Refute.collectAxioms` built its store with `Store.ofGraph`, whose
`withSubjPred` is `g.filter`. It parses a class expression for BOTH
sides of every `rdfs:subClassOf`, `owl:equivalentClass`,
`owl:disjointWith` and `owl:complementOf` triple, and each parse makes
several subject-plus-predicate lookups, so the pass is quadratic in the
closure — and the refuter pays it once per goal.

The sample was unambiguous: of 14,419 samples, 13,272 were inside
`tableauConsistent`, 13,267 of those inside `collectAxioms`, and the
leaf was `RL.withSubjPred`'s `List.filter` loop (7,661) with `Subject`
decidable equality under it (5,517). 92 per cent of the run.

`Materialise.lean` and `Refute.initState` already read through
`Store.ofIndex (Index.ofGraph g)`, whose lookups are hash lookups.
`collectAxioms` did not. The list-scan definition is kept as
`collectAxiomsS (Store.ofGraph g)` and `collectAxiomsRaw_eq` proves the
two equal through `Store.ofIndex_eq (Index.Wf.ofGraph g)`, so the
change is the same function by proof.

Measured on the tree WITHOUT the five rows, whole corpus, `--dl`, both
halves at about 92 per cent of one core:

| Store | user CPU | wall | peak resident | score |
|---|---|---|---|---|
| list scan | 1215.98 s | 2072 s | 244 MB | 1316 pass, 131 fail, 2 skip, 8 unsupported (out of 1457) |
| hash index | 804.48 s | 1651 s | 246 MB | 1316 pass, 131 fail, 2 skip, 8 unsupported (out of 1457) |

`cap_hits` 0 in both. On `type-positive-entailment` alone the same pair
is 628.40 s and 174.73 s of user CPU, 3.6 times.

### Defect two: two thirds of every TBox was duplicate axioms

With the store fixed, the sample moves to `Refute.search.tryAll` with
`ceDefinite`, `ClassExpr.beq`, `applyAxioms` and `applyAxiomsEdges` at
the leaves — the axiom folds. `--tbox-census` then says why, whole
corpus, 923 cases:

| Quantity | without the rows | with the rows | with the rows, deduplicated |
|---|---|---|---|
| Sum of `tests_per_pass` | 176,696,806 | 537,586,682 | **118,870,270** |
| TBox axioms, all cases | 122,253 | 214,466 | 73,653 |
| Structurally distinct | 64,958 | 73,653 | 73,653 |
| Cases with duplicate axioms | 923 of 923 | 923 of 923 | 0 of 923 |

The rows tripled the axiom tests and **almost everything they added was
a duplicate**. On the heaviest case, `WebOnt-miscellaneous-011`, the
TBox goes 3,872 → 18,099 axioms while the DISTINCT count goes
2,552 → 2,964: 97 per cent of what the rows add is structurally equal
to an axiom already there. The node and label counts do not move at all
(814 nodes, 3,145 labels before and after), so the rows do not change
the tableau's shape — they only lengthen the list it folds over.

`collectAxioms` emits one axiom per triple, and two restriction nodes
with the same `owl:onProperty` and the same filler parse to the SAME
class-expression pair. Table 9's schema rows create exactly that.

A repeated axiom changes nothing: `applyAxioms` and
`injectGlobalAxioms` fold with `addLabel`, which returns unchanged when
the label is present, and `applyAxiomsEdges` and `applyAxiomsConj`
guard on `memCe a ls` before firing. Nothing else reads the TBox —
`pendingUnion`, `pendingMerge` and `clashNodes` read labels and nodes.
And the failure direction is safe: if that argument were wrong,
dropping a copy could only give a node FEWER labels, hence fewer
clashes, hence a WITHHELD refutation, never a manufactured one. A wrong
deduplication loses conformance units, which the corpus score sees; it
cannot invent an entailment.

### The gate

Per catalog, `--dl`, on the tree WITH the five rows, the two binaries
run CONCURRENTLY so they carry the same contention:

| Catalog | index store | index store + dedup |
|---|---|---|
| profile-QL | 0 s | 0 s |
| profile-EL | 1 s | 0 s |
| profile-RL | 0 s | 1 s |
| type-inconsistency | 9 s | 4 s |
| type-consistency | 1571 s | 529 s |
| type-positive-entailment | 630 s | 234 s |
| **total** | **2211 s** | **768 s** |

Every catalog reports the SAME two score lines in both runs, and on
`type-positive-entailment` every diagnostic counter is identical as
well: `closure_rounds` 1750, `clashes` 26, `cap_hits` 0,
`refuter_passes` 26, `refuter_flips_to_fail` 0, `pe_countermodel` 19.

    profile-QL                82 / 83 pass  (out of 87)
    profile-EL               108 / 114 pass (out of 121)
    profile-RL               120 / 121 pass (out of 126)
    type-inconsistency        45 / 116 pass (out of 128)
    type-consistency         505 / 531 pass (out of 583)
    type-positive-entailment 335 / 361 pass (out of 412)

(closure alone / closure or refutation.)

### What this corrects

- **The rows are not expensive.** The `--dl` blow-up they appeared to
  cause was a pre-existing quadratic in `collectAxioms` that they
  multiplied, plus a duplicate-axiom list they lengthened. Both were
  already present without the rows.
- **The ordering of the two defects matters.** Until the store defect
  was repaired, `applyAxioms` was NOT the dominant cost — 92 per cent
  of the run was inside `collectAxioms`'s list scan and the axiom folds
  were invisible under it. A recommendation to add absorption or lazy
  unfolding FIRST would have bought nothing measurable.
- **Absorption and lazy unfolding are still the right next lever**, and
  the census is the way to decide it: `tests_per_pass` is still
  118.9 million corpus-wide, 81.7 per cent of it in twelve cases, and
  `injectGlobalAxioms` still scans the whole TBox per node regardless
  of that node's labels.

### The measurement rule this paid for

**Run `l4owl-probe --tbox-census` before and after any rule row, and
put a catalog directory per catalog rather than timing the whole
corpus.** Four of the six catalogs finish in under 15 seconds
together; the other two are the fifty minutes. A count is immune to a
loaded machine and a stopwatch is not, and this laptop was never quiet
for long enough to trust one.

## B5 enumerated: how, and what the method cannot see

Done 2026-09-04 against `l4owl-probe` at commit `8029b7c1c`. The
baseline reproduced the split's figures exactly: RL 1138 pass, 309 fail
(out of 1457); `--dl` 1211 pass, 236 fail (out of 1457); `cap_hits` 0
in both.

**Method.** Of the 309 RL FAIL lines, 308 carry the `closure-gap:` tag
and 1 carries `parser:`. The 308 split into 201 that name a MISSING
CONCLUSION TRIPLE and 107 that say "no clash row fired on a premise
asserted inconsistent" (B3). A unit is B5 when its missing triple's
predicate is `rdf:type`, `owl:sameAs`, `owl:differentFrom`, or an
ontology's own property IRI. That is 104 of the 201 by predicate: 85
`rdf:type`, 7 `owl:sameAs`, 6 `owl:differentFrom`, 12 an ontology
property. The split's figure of 107 was produced by a slightly wider
reading; the difference is 3 units and does not move any cluster.

**What the method cannot see.** It is the FIRST missing triple of each
conclusion, so a conclusion missing several triples for several reasons
is classified on the first. It also cannot tell a missing rule row from
a rule that fires and whose premise was never derived — that
distinction came only from reading each cluster's premise documents.

## B5, clustered by the missing rule

Ranked by RL units, counting PREMISE occurrences as the marker
correction requires. Units are the pre-landing figures.

| Cluster | RL units | What is missing | Status |
|---|---|---|---|
| Vocabulary axiomatic triples, annotation properties | 18 | Section 6 Tables 6.2, 6.5 | **landed `d980a444d`** |
| Description-logic `2xx` cases (`WebOnt-description-logic-201`, `-202`, `-205`, `-206`, `-208`) | 10 | a class-expression instance check the RL closure cannot do | belongs to the refuter, not to B5 |
| Property-characteristic transfer (`WebOnt-FunctionalProperty-003`/`-004`/`-005`, `-InverseFunctionalProperty-003`/`-004`, `-SymmetricProperty-002`/`-003`, `-TransitiveProperty-002`) | 16 | mixed: `-FunctionalProperty-003` and `-InverseFunctionalProperty-003` are one schema row (`P owl:inverseOf Q`, `P` functional ⊢ `Q` inverse-functional); the rest need a `owl:oneOf` singleton-range argument | 4 units are a rule row, 12 are refuter work |
| `owl:AllDifferent` ⊢ pairwise `owl:differentFrom` (`WebOnt-AllDifferent-001`, `-differentFrom-002`, `-distinctMembers-001`) | 6 | Table 5.10 "Semantic Conditions for N-ary Disjointness", rows 1 and 3 | open, see below |
| `rdfs:Class` / `owl:Class` interchange (`WebOnt-Class-002`, `-003`) | 4 | Section 6 Tables 6.5 and 6.1 | 2 landed `cc4049738`, 2 blocked on Table 6.1's cost |
| `x rdf:type owl:Thing` for an individual (`WebOnt-I5.8-004`, `-010`, `-AnnotationProperty-002`) | 6 | `ICEXT(I(owl:Thing)) = IR` (Table 5.2) as a comprehension over every term of the graph | open; unconditional and expensive, same hazard as Table 6.1 |
| `owl:hasKey` ⊢ `owl:sameAs` (`New-Feature-Keys-001`) | 3 | prp-key IS implemented; the row does not fire on this premise | open, a rule bug not a missing row |
| Existential witnesses (`WebOnt-someValuesFrom-001`/`-003`, `somevaluesfrom2bnode`, `WebOnt-oneOf-004`, `-I5.8-017`) | 12 | a witness individual for `owl:someValuesFrom` / a value choice for `owl:oneOf` | belongs to the refuter, not to B5 |
| `_:b1 rdf:type owl:AllDifferent` and `Peter rdf:type _:b1` (`New-Feature-DisjointObjectProperties-002`, `-DisjointDataProperties-002`, `-SelfRestriction-002`, `-ObjectQCR-001`, `-DataQCR-001`) | 18 | the CONCLUSION asks for the axiom or the class expression itself | **B1, not B5** |

### Units this agent moved out of B5

- 18 units (the five `New-Feature-*` cases above) are **B1**: their
  conclusion restates a class expression or an `owl:AllDifferent`
  axiom. No rule row produces structure.
- 22 units (the description-logic `2xx` cases, the existential-witness
  cases, and the `owl:oneOf` singleton-range half of the
  property-characteristic cluster) need the tableau. They are **B3
  work in a positive-entailment costume**: the entailment is decided by
  refuting the premise plus the negated conclusion, not by a closure
  row.

### `owl:AllDifferent` ⊢ `owl:differentFrom`, scoped but not landed

The rule is OWL 2 RDF-Based Semantics Table 5.10, rows 1 and 3: a
sequence `a1, …, an` that is the `owl:members` (row 1) or
`owl:distinctMembers` (row 3) of a `z ∈ ICEXT(I(owl:AllDifferent))`
has `aj ≠ ak` for every `j ≠ k`. Three cases need it and no other row
reaches them.

It is a DRIVEN row, not an axiom list, so it costs a `Derives`
constructor, an `RlConditions` field with its Herbrand instance, an
object-language schema disjunct, the executable row in both
`RLClosure.lean` and `RLClosureIndexed.lean` with their equality
theorem, and soundness plus completeness arms — about fourteen sites,
against `caxAdcToDwFor` as the template.

**It must use the distinct-CELL guard**, not the distinct-TERM guard.
Table 5.10 indexes `j` and `k` over POSITIONS in the sequence. Two
distinct terms drawn from ONE cell — which `eq-rep-o` produces by
copying an `rdf:first` across an `owl:sameAs`, as recorded above for
`caxAdcAt` — are one position, and a row that fires on them derives a
`owl:differentFrom` that the premise does not entail. `ListMember` is
not enough for this; the spec side needs a cell-indexed membership
relation beside it.

### What the two landings say about the marker

The marker predicted 24 RL units across the three constructs and delivered
7. Treat every remaining number in the category-A table as an upper bound
of the same kind: a construct-occurrence count, not a count of tests the
row will close. A marked unit whose CONCLUSION contains the construct is
usually B1, because a conclusion that names a class expression or an
`owl:AllDifferent` axiom asks the engine to produce structure, and no rule
row produces structure. A future ranking should count only units whose
PREMISE carries the construct.

### B1 — decided, and 53 of its 58 `--dl` units closed

The decision, with the specification quotations that settle it, is in
[`2026-09-04-owl-b1-class-expression-structure.md`](2026-09-04-owl-b1-class-expression-structure.md).
The paragraph above that offers "either the comprehension principles of
the OWL 2 RDF-Based Semantics or a conclusion matcher that works modulo
blank-node structure" names two routes and NEITHER is the one taken.

- The comprehension conditions are informative in the OWL 2 RDF-Based
  Semantics 2nd Edition, not normative.
- The probe's present matcher already treats a conclusion blank node as
  matching any term per triple, so a single-mapping check is STRICTER
  than what runs today and closes nothing here.
- The W3C definition of an entailment test is model-theoretic over
  ontologies. Under the Direct Semantics `Ont(d1) ⊨ Ont(d2)` iff
  `Ont(d1) ∪ ¬Ont(d2)` is unsatisfiable, which the landed tableau
  refuter decides. `OWL/NegationGoals.lean` held that half of the port
  with no caller.

Landing: the `--dl` positive-entailment judgement gains a refutation
FALLBACK after containment fails.

| Rows / change | RL before → after | `--dl` before → after |
|---|---|---|
| PE-via-refutation fallback in `Harness/OwlProbe.lean` | 1138 pass, 309 fail → 1138 pass, 309 fail | 1211 pass, 236 fail → 1264 pass, 183 fail |

53 `--dl` units closed, 0 RL (the fallback is `--dl` only), no
regression, `cap_hits=0` in every run. NegativeEntailmentTest stayed at
38 pass, 0 fail (out of 38).
### `084a59ac6` — literal distinctness decided on VALUES (refuter)

| Change | RL before → after | `--dl` before → after |
|---|---|---|
| `Refute.provablyDistinct` compares data values, not lexical forms | 1138 pass, 309 fail → 1138 pass, 309 fail | 1211 pass, 236 fail → 1218 pass, 229 fail |

Sub-counts, `--dl`: ConsistencyTest 758 pass, 4 fail — unchanged.
NegativeEntailmentTest 38 pass, 0 fail — unchanged. InconsistencyTest
121 pass, 39 fail → 128 pass, 32 fail. RL sub-counts all unchanged.

Closed: `functionality-clash` (two catalogs), `Plus and Minus Zero are
Distinct` (three catalogs), `WebOnt-miscellaneous-203` and `-204`.
`WebOnt-miscellaneous-202`, the consistent premise whose two
`rdf:XMLLiteral` fillers differ only in insignificant whitespace, still
passes and is now pinned by a `#guard`.

Wall clock, `--dl` over the six catalogs: 5 min 02 s → 5 min 38 s, both
runs at 94 to 97 per cent CPU utilisation. Stronger and about 12 per
cent longer.

### `fceeff81d` — the existence clash reads asserted `rdfs:range` (refuter)

| Change | RL before → after | `--dl` before → after |
|---|---|---|
| `Refute.datatypeRangeClash` meets the ∀-intersection with `st.ranges` | 1138 pass, 309 fail → 1138 pass, 309 fail | 1218 pass, 229 fail → 1221 pass, 226 fail |

Sub-counts, `--dl`: ConsistencyTest 758 pass, 4 fail — unchanged.
NegativeEntailmentTest 38 pass, 0 fail — unchanged. InconsistencyTest
128 pass, 32 fail → 131 pass, 29 fail.

Closed: `string-integer-clash` in profile-RL, profile-EL and
type-inconsistency. Wall clock, `--dl`: 5 min 38 s → 4 min 18 s — the
rule decides before the search branches.

## B3 under `--dl`, worked through: the 39, and what is left

Method. The 39 units are the `FAIL … [InconsistencyTest]` lines of
`l4owl-probe --dl` over the six catalogs, each tagged
`closure-gap: no clash row fired on a premise asserted inconsistent`.
They are 33 distinct test cases; six of them are typed in two or three
catalogs and score once per catalog. What the method cannot see: a
premise the engine judges inconsistent for a WRONG reason still counts
as a pass here, and this list says nothing about those.

**The budget is not a cause of any of them.** `--refute-budget 512`,
eight times the default 64, scores 1221 pass, 226 fail (out of 1457) —
identical to budget 64 — and leaves exactly the same 29 B3 failures.
`cap_hits` is 0 in every catalog in both runs. The split's earlier text
called a budget trip rare; on B3 it is absent.

| Cause | Units of the 39 |
|---|---|
| A clash condition missing or too weak | 10 — all closed by the two landings above |
| An expansion rule missing | 29 |
| The budget stops the search early | 0 (measured, see above) |

The 29 that remain, by the expansion each needs:

- **23 units, the OilEd `WebOnt-description-logic-*` cases.** Each
  asserts an anonymous individual into a named class whose
  `owl:equivalentClass` is an intersection over `owl:someValuesFrom`,
  `owl:maxCardinality` and an INVERSE object property, with
  `owl:complementOf`/`owl:unionOf` branching underneath. The refuter
  mints witnesses to `maxWitnessDepth` 3 and `maxGeneratedWitnesses` 6
  and does not propagate an inverse role onto a minted witness, so the
  clash node is never built. This is one expansion family, not 23
  separate gaps.
- **2 units, `New-Feature-Keys-002`.** `owl:hasKey`. The RL row
  `prp-key` is documented in `RLRules.lean` and implemented nowhere,
  and the refuter has no key rule. OWL 2 Syntax §9.5: a key applies to
  NAMED individuals only, which is what makes a graph-level violation
  the right shape for it.
- **2 units, `Inconsistent Disjoint Dataproperties` and `Inconsistent
  String Pattern with Disjoint Dataproperties`.** The
  disjoint-data-property pattern collision, which `Refute.lean`'s own
  header already names as absent.
- **1 unit, `Minus Infinity is not in owl:real`.**
  `NegativeDataPropertyAssertion` must remove a member from the
  `owl:oneOf` filler set; the refuter does not read negative property
  assertions into the datatype layer.
- **1 unit, `one=two`.** A 1:1 role chain over an `owl:oneOf` of three
  individuals. `OWL/CountingOracle.lean` exists with a proved Farkas
  validator and is still not consulted from the search.

## ⚠️ A located soundness defect: the materialiser mints a shared witness

`WebOnt-description-logic-018`, `-020` and `-021` are asserted
CONSISTENT and fail under `--dl` only. They are the whole of B4. The
row and the mechanism are now isolated (2026-09-04), and neither
landing above changes them.

`detectClash` is FALSE on the RL closure of each premise and TRUE after
`OWL.Mat.materialise`, and the row that fires is **cls-com**. On
`-018`: the materialiser mints one witness
`_:bw_b40__…#r` for the `owl:someValuesFrom` obligation on `r` at node
`b40`, then writes that ONE witness into `p1`, `p2`, `p3` and two
anonymous classes. The premise says `p1 ⊑ ¬(p2 ⊔ p3 ⊔ p4 ⊔ p5)`, so
`p1` and `p2` on one node is already a contradiction; reclosure lifts
it to `b24` and `b25` with `b24 owl:complementOf b25`, and cls-com
fires.

The defect is that several existence obligations on one property are
satisfied by ONE minted filler. `Refute.lean` states the rule the
materialiser breaks, in its own words beside `existsUnsatisfiableWitness`:
"two DIFFERENT existence obligations on one property are NEVER combined
WITH EACH OTHER … Combining two `∃p.Dᵢ` would assume they share one
filler, which is false for a non-functional property." The fix belongs
in `L4Factoidal/OWL/Materialise.lean`: one witness per obligation, or
withhold the membership.

## The B4 soundness fix and two refuter rules, 2026-09-04

Baseline reproduced exactly at `0f0ad2b7d`: RL 1158 pass, 289 fail;
`--dl` 1294 pass, 153 fail (out of 1457 each); `cap_hits` 0.

| Commit | Change | RL before → after | `--dl` before → after |
|---|---|---|---|
| `c3d5d7a57` | one existential witness per OBLIGATION in `Materialise.lean`, not per `(individual, property)` | 1158 pass, 289 fail — unchanged | 1294 pass, 153 fail → 1295 pass, 152 fail |
| `21ebe2be9` | the counting clash: pairwise-disjoint existentials against an at-most bound | unchanged | 1295 pass, 152 fail → 1297 pass, 150 fail |
| `b4394b608` | the `owl:hasKey` graph-level violation | unchanged | 1297 pass, 150 fail → 1299 pass, 148 fail |

`ConsistencyTest` under `--dl`: 758 pass, 4 fail → **761 pass, 1 fail**
(out of 762). `NegativeEntailmentTest` 38 pass, 0 fail throughout.
`InconsistencyTest` 131 pass, 29 fail → 133 pass, 27 fail (out of 160).
`cap_hits` 0 in every run. No cap was raised: `maxWitnessDepth` is
still 3 and `maxGeneratedWitnesses` is still 6.

### B4 closed

`witnessBNodeId` keyed the minted blank node on `(individual,
property)`, so `p1 ⊑ ∃r.A` and `p2 ⊑ ∃r.B` were discharged by ONE
filler carrying both `A` and `B`. That is the assumption `Refute.lean`
forbids beside `existsUnsatisfiableWitness`, and OWL 2 Direct
Semantics §2.2 reads `ObjectSomeValuesFrom(r C)` as one successor in
`C`, never as one successor in the intersection of every such `C`. The
identifier now carries the class expression that raised the
obligation, and `witnessBreachesBound` counts the witnesses the pass
has already minted for the pair so several obligations cannot each
slip past one at-most bound.

`WebOnt-description-logic-018`, `-020` and `-021` [ConsistencyTest] —
the whole of B4 — are closed. `-019` and `-022` [InconsistencyTest]
were lost by the same commit: both had been passing ONLY through the
shared filler, so those passes were accidental. `21ebe2be9` recovers
both by an argument that holds.

### The 29 B3 units, re-read

The split says the 23 OilEd units "are one expansion family, not 23
separate gaps". The test descriptions do not support that. They are
`t4.1` dynamic blocking, `t6.1`/`t6f.1` DOUBLE blocking, two 3-SAT
encodings (`-502`, `-504`), two integer-multiplication encodings
(`-909`, `-910`), a `owl:oneOf`-plus-inverse spy point (`-035`) and
the `t3.x`/`t7.x`/heinsohn counting cases. Only the last group is one
family, and `21ebe2be9` closes the two of them that the corpus asserts
inconsistent and the merge search cannot reach. The blocking and
propositional-encoding cases need a complete `SHOIQ` calculus with
blocking, which is not an expansion rule.

### ⚠️ The `scm-svf`/`scm-avf`/`scm-hv` memory blow-up is NOT in the refuter

Measured 2026-09-04 on this worktree with the category-A agent's
`scm-guarded.patch` applied, `type-positive-entailment.rdf` only:

| Regime | Wall | Peak RSS | Finished |
|---|---|---|---|
| RL closure only | 8.6 s | 141 MB | yes, 331 pass, 77 fail (out of 412) |
| `--dl` | 433 s | 5.94 GB | no, SIGKILL |
| `--dl --refute-budget 1` | 344 s | 9.14 GB | no |
| `--dl`, `countingClash` removed | 334 s | 9.48 GB | no |
| `--dl`, `tableauConsistent` stubbed to `none` | 414 s | 10.08 GB | no |

The last row disables the tableau refuter completely and the run still
takes 10 GB and dies. The only other thing `--dl` adds is
`OWL.Mat.materialise`, so the blow-up is in the MATERIALISATION PASS,
not in the refuter's branching. The refuter's budget makes no
difference to it, and the new counting clash is not implicated.

A global node cap in `ensureWitnesses` (`maxSearchNodes`, tried at
200) does not bound it either, which is the same evidence read a
second way. It was measured and NOT landed.

Where to look next: `materialiseWithBudget` budgets (individual, class
expression) PAIRS at 400 000 and each pair costs one `isMember` at
fuel 64 over the class-expression graph. The `scm` rows add
`rdfs:subClassOf` edges BETWEEN restrictions, which is what makes that
graph deep, so the per-pair cost is what grew — the pair budget cannot
see it.
