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
