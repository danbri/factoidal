# Lean DL completion and scale

Date: 2026-09-08. Work in progress.

Owner direction: “Most urgent complete DL/tableau for 100% coverage and
performant speeds, scaling to interesting dataset sizes.” A subagent is
also assigned to bring the SPARQL 1.0 suite up to specification.

Baseline source: `0c331255b3a0fec0306b5459a944749364db891f`.
The [standards review](20260908-lean-standards-status-and-codex-skills.md)
contains manifests and raw evidence. Native DL inconsistency was freshly
measured at 116 pass, 11 fail, 1 skip out of 128. The three-catalog DL
result was freshly rerun on the baseline native binary on 2026-09-08:
1032 pass, 82 fail, 1 skip, 8 unsupported out of 1123, matching the
2026-09-07 record. Wall time was 718.18 seconds and peak RSS was
346,914,816 bytes, during concurrent builds. The fixed catalogs include
RDF-Based/Full as well as Direct-Semantics/DL test cases.

## Acceptance boundaries

- Corpus coverage uses fixed manifests and retains failures, skips,
  unsupported syntax, and timeouts in the denominator. A passing corpus
  does not establish completeness for OWL 2 DL.
- Algorithm completeness requires the supported OWL language and model
  construction argument to be stated. Current witness caps and incomplete
  expansion rules do not establish it. A quiescent search is not a proved
  model.
- Proof coverage distinguishes the sound declarative calculus from the
  missing executable graph-to-certificate bridge. Removing a `partial`
  search definition proves termination of that function, not OWL completeness.
- Scale requires input sizes, meaningful inferred results or detected
  contradictions, phase times, peak memory, and timeouts. Use real QUDT
  and schema.org data with growing instance populations, plus adversarial
  shapes. Report timings taken during concurrent builds as such.

## Current independent assignments

1. SPARQL: shared RDF result-set decoding and RDF/XML result dispatch,
   followed by residual semantic/parser failures; preserve the measured
   SPARQL 1.1 and 1.2 floors of 631 and 254 passes.
2. DL: total branch search and the public indexed closure are integrated.
   Nominal identification, named Boolean class definitions, and
   group-aware distinctness are integrated. Next: reduce measured branching
   and witness-freshness costs without discarding satisfiable alternatives.
3. DL datatypes: exclusions and complete collections are integrated. The
   indexed initialization substitution is proved. Next: prove and measure
   class-axiom filtering before addressing the label-insertion bottleneck.

The parent reviews soundness and measures phase costs before choosing
performance changes. Relevant open work:
[OWL completion](https://github.com/danbri/factoidal/issues/651),
[remaining DL families](https://github.com/danbri/factoidal/issues/672),
[executable tableau certificates](https://github.com/danbri/factoidal/issues/586),
[total definitions](https://github.com/danbri/factoidal/issues/617), and
[DL performance](https://github.com/danbri/factoidal/issues/549).

## Measurements and integration

The [qualified merge and closure analysis](designissues/2026-09-08-qualified-tableau-merges-and-public-closure.md)
records a reproduced false inconsistency and real-vocabulary timing/memory
baselines. Correcting qualified merge selection takes priority over coverage
gains. The previous public list closure exceeded 30 seconds on each of
schema.org and QUDT. The public path now uses the existing indexed equality
proof through a wrapper-level compiler simplification theorem.

Integrated locally: [total tableau search and qualified-merge correction](20260908-owl-total-search.md),
plus the [SPARQL RDF result-set decoder](20260908-lean-sparql10-rdf-result-sets.md).
The DL inconsistency floor remains 116/11/1 out of 128; the SPARQL 1.0
floor improves to 419/62 out of 481. The integrated total-search and result-decoder tree passed the complete
1196-job Lake build and the Lean trust audit (171 existing partial
definitions; zero new prohibited trust constructs).

The [public indexed closure](20260908-owl-indexed-public-closure.md) was
subsequently integrated and its targeted build passed. The emitted native C
calls the indexed wrapper in all three public OWL operations. Closure-only
measurements were 9.23 seconds on schema.org and 88.17 seconds on QUDT. A
separate public consistency run on schema.org completed in 16.747 seconds
with 150,994,944 bytes peak RSS and returned `true`; that result is the
existing quiescence verdict, not a certified model. QUDT consistency hit
the 300-second limit (300.083 seconds, 1,711,718,400 bytes peak RSS, no
verdict). These consistency runs also had concurrent builds. Further
phase measurements and datatype/nominal work continue.


### Fresh three-catalog baseline

| Catalog | Pass | Fail | Skip | Unsupported | Total | Catalog wall time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| type-inconsistency.rdf | 116 | 11 | 1 | 0 | 128 | 3.689 s |
| type-positive-entailment.rdf | 373 | 35 | 0 | 4 | 412 | 193.752 s |
| type-consistency.rdf | 543 | 36 | 0 | 4 | 583 | 520.228 s |
| Total | 1032 | 82 | 1 | 8 | 1123 | 717.669 s |

The command used `l4owl-probe --dl` with the default per-case closure cap
30,000 ms, refutation budget 64, and refutation time cap 20,000 ms. There
were no recorded cap hits. One parse failure was `FS2RDF-literals-ar`.
The refuter recovered 127 units beyond closure alone. The catalogs contain
482 distinct test identifiers: all 206 positive-entailment identifiers
also occur among the 354 consistency-catalog identifiers, alongside 128
inconsistency identifiers. The 1123 denominator counts all requested
catalog/type judgments, including overlap; it is not 1123 distinct tests.
These are baseline
measurements, before the new datatype and nominal changes.


### Datatype and collection integration

The [datatype/list change](20260908-owl-datatype-witness-exclusions.md) is
integrated with total search and public indexed closure. The focused Lake
build passed, followed by
a native inconsistency run: 118 pass, 9 fail, 1 skip, no unsupported or
cap hits, out of 128 (5.180 seconds during concurrent work). It closes
three old datatype failures and exposes the malformed RDF/XML collection
in `New-Feature-Rational-002`; the well-formed neighboring graph still
refutes. The complete three-catalog result above remains the baseline,
not a score for this integrated change. The subsequent complete integrated
Lake build passed all 1198 jobs.

### Native component measurements

A temporary native Lean probe forces each pure result through an `IO.Ref`
between monotonic clock reads, then prints sizes and total elapsed time.
It parses Turtle directly; public CLI measurements also include their
format-conversion and output work, so these are separate measurements.

For schema.org: 17,949 input triples became 60,770 closure triples, with
8,573 distinct TBox axioms and 4,912 tableau nodes. Closure took 1.028 s,
axiom collection 1.475 s, initialization 1.234 s, and search 15.089 s.
A separately timed first saturation pass took 7.015 s; that extra pass is
included in the 25.995 s probe total but is not counted twice in search.

For QUDT: 130,404 input triples became 638,420 closure triples. Closure
took 19.018 s and axiom collection 13.081 s. Initialization did not finish
within the remaining part of the 300 s process cap (1,509,408,768 bytes
peak RSS). A second component probe on the datatype-integrated tree
measured the index at 0.998 s and list-backed `unsatNamedClasses` at
60.312 s, then reached another slow phase while parsing anonymous ranges.
That second run also reached the 300 s cap, while still parsing anonymous
ranges (over 209 s in that phase). The next optimization is an exact
indexed-store substitution for setup.
All runs had concurrent builds; these phase observations localize costs
and are not idle-machine throughput claims.

Raw logs, phase results, and the temporary native probe sources are saved in
[the scale evidence](20260908-lean-dl-scale-evidence.json).


### Fixture triage and functional-syntax gaps

`FS2RDF-literals-ar` is not an Arabic-text parser failure. Its RDF/XML
premise puts a nested `rdf:RDF` element inside a property carrying
`rdf:datatype` (also misspelled `rdf:xmlliteral`). The literal-property
grammar requires text content; embedded XML needs the distinct
`rdf:parseType="Literal"` form. The parser rejection is consistent with
[RDF/XML §7.2.16](https://www.w3.org/TR/rdf-syntax-grammar/#literalPropertyElt).
The raw failure remains in the fixed denominator. Its separately supplied
functional-syntax representation is different evidence, not a reason to
silently substitute for the malformed RDF/XML.

The eight unsupported judgments come from two functional-syntax-only
identifiers, each repeated across catalogs and test types:
`Qualified-cardinality-boolean` and `Qualified-cardinality-restricted-int`.
Both need `DataExactCardinality` parsing and qualified finite data-space
cardinality reasoning with exclusions. They respectively force both Boolean
values and all three integers from the interval [1,3]. These are genuine
implementation gaps in the work tracked by
https://github.com/danbri/factoidal/issues/651.


### Nominals and indexed initialization

The [nominal change](20260908-owl-nominal-identification.md) and
[indexed initialization](20260908-owl-refute-indexed-initialization.md)
are integrated. The combined focused build passed 465 jobs. The root
inconsistency catalog remains 118 pass, 9 fail, 1 skip out of 128, but
wall time rose from 5.180 to 80.813 seconds after nominal integration.
The expanded branch search therefore needs performance work; this is
not a performance acceptance pass. Both runs had concurrent agent work.
The nominal agent's 379/29/0/4 positive-entailment result is from its
isolated snapshot, not a measurement of this whole integrated tree.

On QUDT's 638,420-triple closure, the compiled public
`unsatNamedClasses` phase now takes 1.369 seconds versus the earlier
60.312 seconds and returns the same empty list as the direct indexed
implementation. Initialization then exposes slow initial label insertion.
A schema.org saturation-pass diagnostic attributed 3.868 seconds to
label-axiom applications, 3.488 seconds to edge-axiom applications,
0.587 seconds to global axioms, and 0.582 seconds to conjunction axioms
(8.626 seconds total). This motivates proved filtering of irrelevant
axioms before each repeated fold.

### SPARQL numeric integration and comparator repair

The reviewed numeric and term-comparison changes build and move the
legacy catalog to 445 pass / 36 fail out of 481. The first root SPARQL 1.1 run was 629/2: SUM and AVG returned expanded
binary floating-point values that the result comparator did not match
to expected short decimal spellings. The comparator now compares the
exact IEEE values for float/double while retaining exact decimal and
integer comparisons and rejecting mismatched datatypes. Root reruns
restore SPARQL 1.1 to 631/0 and SPARQL 1.2 to 254/0. This repair uses
no numeric tolerance. The combined freshness/comparator focused build
passed 542 jobs.


### Growing instance-population baseline

A generated ABox has 100, 500, or 1,000 individuals, each in
`U = A union B` and `NotA = complement(A)`. Its satisfiable control has
a direct model with all individuals in B. The inconsistent neighbor
also puts the final individual in `NotB = complement(B)`. This requires
DL disjunction reasoning beyond the initial RL closure.

All six public `owl-consistent --fuel 64` runs return unknown because
the current search branches on each disjunction even when one alternative
is explicitly excluded. Times are about 0.07–0.33 seconds at 100,
0.47–0.49 seconds at 500, and 1.74–1.75 seconds at 1,000; these are
budget-exhaustion times, not reasoning throughput. Peak RSS ranges
from 23.6 to 32.3 MB. The fixed schema has seven triples; each instance
adds two and the inconsistent neighbor adds one more.

Deterministic propagation of forced union members is now assigned before
any budget increase. The paired controls and generator are retained in
the scale evidence.


### Native timeout defect and per-case costs

The indexed-freshness root run remains 118/9/1 and takes 78.414 seconds.
A temporary native copy of the unchanged judge records each case's
elapsed time: description-logic-502 takes 40.019 seconds, one=two
23.803 seconds, description-logic-035 3.609 seconds, and -040 1.361
seconds. There are no printed refuter timeout lines.

Inspection of generated `Harness/OwlProbe.c` explains why the configured
20-second refuter cap did not intervene: the compiler evaluates
`Refute.refute` before `lean_io_as_task`, and the task only wraps its
precomputed result. The source-level match inside the IO action did not
prevent this hoisting. Prior tables record configured cap parameters;
they do not establish an effective native wall-clock bound. The task
wrapper and elapsed-time polling are now assigned for repair under
[timeout tracking](https://github.com/danbri/factoidal/issues/655).

The [TBox prefilter](20260908-owl-refute-tbox-prefilter.md) is integrated.
Three isolated schema.org trials have median unfiltered/filtered/public
pass times of 5.910/2.887/2.854 seconds, with a theorem proving exact
full-state equality. This leaves initial label insertion as the next
QUDT setup bottleneck.


### Root forced-union integration and population scaling

Named complement equivalences, explicit-complement disjunction filtering,
zero-choice clashes, and sole-live-choice propagation are integrated.
The root focused build passed 465 jobs, including the filter proofs.
All ten public population runs now match their constructed satisfiable
or inconsistent neighbor at the unchanged fuel 64:

| Individuals | Input triples, control / contradiction | Open control | Refutation |
| ---: | ---: | ---: | ---: |
| 100 | 207 / 208 | 0.282 s | 0.049 s |
| 500 | 1007 / 1008 | 0.145 s | 0.120 s |
| 1000 | 2007 / 2008 | 0.429 s | 0.253 s |
| 4000 | 8007 / 8008 | 4.240 s | 1.497 s |
| 8000 | 16007 / 16008 | 14.156 s | 5.156 s |

These runs had concurrent agent work. The previous 100/500/1000 controls
and contradictions all exhausted the same budget. The new larger-size
curve remains superlinear, consistent with list-based label bookkeeping;
this is progress on a measured reasoning workload, not general DL scale
acceptance. The open control has an explicit mathematical model, while
the engine's returned true still carries no executable model certificate.
The large W3C 502 and 504 cases remain separate failures after this change.


### Subsequent public-path review

With union propagation and axiom filtering integrated, public schema.org
consistency now returns its existing open-branch true verdict in 9.271
seconds, with 149,766,144 bytes peak RSS. The earlier indexed-closure
public run took 16.747 seconds. Both had concurrent agent work.

The caller-deadline wrapper repair is integrated: inputs are read through
IO inside the worker, results are forced before the completion timestamp,
and refuter timeouts have a distinct counter. The isolated 1,000 ms
negative test reports a caller timeout at 1,015 ms, but its whole native
process still takes 110.94 seconds because runtime shutdown waits for
the pure worker. A hard process cap remains separate work; do not run
large batches of abandoned workers as a performance acceptance test.

A [public entailment freshness counterexample](designissues/2026-09-08-qualified-tableau-merges-and-public-closure.md#public-entailment-goal-name-collision)
is now prioritized before further nominal search heuristics. A valid
blank-node alpha-renaming changes a non-entailment answer from false
to true by colliding with a fixed negation-goal identifier. Its paired
regression and API/harness repair are in progress.

### Resume and integration checks

The owner reported that the laptop was off and offline during this session.
The large gaps between tool timestamps are therefore suspension intervals,
not evidence of stalled reasoning. Their exact start and end are not known.
Keep the recorded timing samples, but treat elapsed-time comparisons as
provisional until fresh uninterrupted runs confirm them. Test verdicts,
source counterexamples, and kernel-checked equalities remain separate from
those timing claims. Record process CPU time alongside elapsed time in the
follow-up measurements; CPU time is not a substitute for latency.

The subsequent full build after union propagation, dataset scoping, and
the caller-deadline integration failed in
`L4Factoidal.SHACL.SparqlTheorems`: its pre-binding proof still assumes
the earlier numeric literal promotion. The SPARQL task is repairing both
the substitution implementation and its existing equality theorem. The
previous focused successes do not establish a green full build for this
new combined snapshot.

Fresh root dataset-scoping suite runs give SPARQL 1.0 456/25 of 481,
SPARQL 1.1 631/0, and SPARQL 1.2 254/0. These precede the pending
open-world equality and SHACL integration corrections. The dataset work
preserves blank-node identity between named graphs, scopes default-graph
merge inputs apart, loads local FROM sources, and avoids duplicate named
graphs. Raw suite output is retained in the evidence JSON.

The post-resume public schema.org plus instance baseline uses a copied
binary with SHA-256 recorded in the evidence, fuel 64, and an external
60-second process cap. Each individual has four asserted triples; seven
schema triples define the paired disjunction workload.

| Added individuals | Input triples, control / contradiction | Control elapsed / CPU | Contradiction elapsed / CPU |
| ---: | ---: | ---: | ---: |
| 1000 | 21956 / 21957 | 22.338 / 22.072 s | 9.642 / 9.452 s |
| 4000 | 33956 / 33957 | timed out at 60.033 / 44.726 s | 30.701 / 26.563 s |

The 1000 control returns the existing open-branch true verdict; both
contradictions return false. The 4000 control has no verdict and is not
a performance pass. CPU is user plus system time; concurrent agent work
is recorded. The controls add no designed contradiction but do not prove
the consistency of the entire imported vocabulary. Indexed initial labels
are not yet integrated in these samples.

The [witness-depth review](designissues/2026-09-08-qualified-tableau-merges-and-public-closure.md#witness-depth-exhaustion-produces-a-false-satisfiability-verdict)
also reproduces false true verdicts at depths four and five on explicit
existential/universal contradictions. Depth-two and depth-three neighbors
are refuted. This is assigned as a correctness repair; a later unknown
verdict would expose incompleteness, not close the completion task.

The negation-goal namespace repair is now integrated in the shared library,
public API, and corpus harness. The root 465-job focused build passes and
the native ABI smoke suite passes all 128 checks. Both the ordinary and
adversarial name-collision public probes now return unknown, and the
explicitly asserted positive neighbor returns true. Unsupported conclusion
forms and uncertified open branches now return null/unknown; they no longer
claim non-entailment. Harness telemetry calls the latter `pe_refuter_open`
instead of `pe_countermodel`. This changes the public result contract for
those cases and preserves the distinction between missing evidence and a
negative answer. It does not repair the separate witness-depth consistency
counterexample yet.

The initial-label optimization review requires one more proof before integration:
its first candidate proved indexed grouping equal to a newly factored list
specification, but did not connect that specification to the original
`initState` fold through `addLabel`. The agent is restoring the exact public
definition and proving that bridge. The phase timings are promising, but
are not a substitute for preserving the prior public semantics.

The documentation sweep also corrected `CountingOracle.lean`'s old claim
that counting is the tableau's only remaining fragment. Its arithmetic
certificate checker is not called by the executable refuter and does not
prove that the extracted class-size constraints follow from a graph.
`one=two` explicitly depends on a finite enumeration; its own fixture
description notes that the unbounded infinite case can have a model.
Any integration must justify finiteness as well as the individual linear
constraints. The source comment now records that boundary.

The SHACL pre-binding implementation and unchanged promotion-equality
theorem are repaired. The root full build now passes all 1198 jobs;
the hygiene audit scans 671 Lean files and 934 axiom reports, finds no
prohibited trust mechanisms, and retains 171 partial definitions against
the updated 171 baseline. This build includes the namespace repair,
its positive refutation neighbor, and the integrated dataset changes.
Pending indexed-label, depth-limit, and further equality work is not part
of this full-build claim.

### Indexed initial labels integrated

The revised [initial-label patch](20260908-owl-refute-indexed-initial-labels.md)
preserves the original `initState` definition and proves equality through
the actual `addLabel` graph fold before enabling `@[csimp]`. The root
465-job focused build passes, and generated C for `tableauConsistent`
calls `initStateIndexed`. Both SHACL pre-binding theorem audits also
report only the accepted foundations. The EBV correction passes its
235-job focused build and root SPARQL suites remain 456/25, 631/0, 254/0.

Post-integration reruns use the same schema.org population fixtures,
fuel 64, external 60-second cap, and a copied binary whose digest is
recorded. The depth-limit correction is not in this binary.

| Added individuals | Control elapsed / CPU | Contradiction elapsed / CPU |
| ---: | ---: | ---: |
| 1000 | 20.025 / 19.521 s | 7.308 / 7.298 s |
| 4000 | 40.565 / 40.489 s | 13.112 / 13.090 s |

All four finish with the existing control true / contradiction false
verdicts. The earlier 4000 control was stopped at 60.033 seconds and
had no verdict. Concurrent agent work remains recorded, so these are
observations of completed public requests, not an isolated throughput
acceptance claim. Peak RSS is about 179–289 MB after integration.
The fresh schema.org pass profile still attributes 2659 of 3405 ms
to `applyAxioms`, which scans the TBox for each visited label. Proved
indexed dispatch is now the next performance task.

### Bounded witness repair checked on the root tree

The [bounded-obligation repair](20260908-owl-refuter-bounded-obligations.md)
passes the root full 1198-job build and all 128 native ABI smoke checks.
The hygiene audit reads 946 axiom reports, retains 171 partial definitions,
and finds no prohibited mechanisms across 671 Lean files. Public depth-two
and depth-three controls/contradictions return true/false; both depth-four
and depth-five pairs now return unknown. This prevents the reproduced
depth-limit false consistency result and leaves completion unfinished.

The `owl:Thing` membership goal works in isolation, including an empty
premise. However, the actual `WebOnt-I5.8-010` case still produces no goals:
its conclusion also asserts a literal-valued data-property triple, which
the negation builder does not handle. A one-case extraction from the
positive-entailment catalog scores 1 pass / 1 fail across its Consistency
and PositiveEntailment judgments. No full-catalog improvement is inferred
from the isolated Thing guard.

A further [zero-bound counterexample](designissues/2026-09-08-qualified-tableau-merges-and-public-closure.md#required-witnesses-and-a-zero-bound-on-a-superproperty)
uses `x : exists p.C`, `x : max 0 q`, and `p subPropertyOf q` and
incorrectly returns true. It is paired with satisfiable maximum-one and
reverse-subproperty controls. Generated edges are missing from the zero
bound's clash check; one required edge is enough to violate zero, without
the pairwise-distinctness evidence needed for larger bounds. This remains
assigned for repair after hard process timeout isolation.


### Named dispatch and QUDT public result

The [named TBox dispatch](20260908-owl-refute-named-tbox-dispatch.md)
now passes the root full build (1198 jobs). It preserves the original
ordered `onePass` result through proved compilation substitution. The
fresh schema.org instrumented pass median falls from 3405 to 1406 ms;
public end-to-end measurements after this change remain to be run.

Before named dispatch, the public QUDT consistency request completes in
38.468 seconds (37.613 CPU seconds), at 1,439,744,000 bytes peak RSS,
with a false consistency verdict. The same 130,404-triple fixture had
previously reached a 300-second external cap without a verdict. Binary
and fixture hashes, exact arguments and outputs are in the evidence JSON.
This fresh run does not span the laptop suspension. Concurrent agent work
means these figures are observed request costs, not isolated throughput.

A native diagnostic locates an initial maximum-one `qudt:id` clash on
`datatype:BOOLEAN`. The source declares `qudt:id` functional, declares
`qudt:ansiSQLName` a subproperty, and gives BOOLEAN the distinct string
values `T000-01` and `BOOLEAN`. These source statements license the
contradiction. A reduced source subset retaining BOOLEAN's type returns
false; replacing the strings with one value or removing functionality
returns true. This is a local contradiction witness, not a completeness
claim for the whole OWL DL language.

The reduced graph also exposes another defect: deleting BOOLEAN's type
assertion makes the contradictory functional-property case return true.
Initial node creation currently depends on type assertions, so global
functionality can miss an untyped property subject. The six paired probes
are preserved in the evidence JSON and this correctness repair is assigned
under [OWL completion](https://github.com/danbri/factoidal/issues/651).


Fresh public population runs after named dispatch keep the same verdicts:

| Added individuals | Control elapsed / CPU | Contradiction elapsed / CPU |
| ---: | ---: | ---: |
| 1000 | 8.844 / 8.504 s | 4.417 / 4.378 s |
| 4000 | 21.574 / 21.535 s | 8.282 / 8.243 s |

The previous indexed-label-only controls took 20.025 and 40.565 seconds;
contradictions took 7.308 and 13.112 seconds. These use unchanged fixture
hashes and fuel 64, with concurrent agent work recorded. Peak RSS is
174–289 MB. The root full build passes 1198 jobs and the hygiene audit
reads 954 axiom reports with no prohibited mechanisms (171 partials).


### Hard process timeout integrated

The [subprocess repair](20260908-owl-refuter-hard-timeout.md) passes the
root 104-job probe build. A one-second focused 502 call exits the whole
process in 1.296 seconds with 1.044 CPU seconds; the timeout counter is one.
This replaces the earlier caller-only deadline and runtime shutdown wait.
Parent serialization is measured separately and precedes the child deadline.
A fresh full three-catalog run uses the default 20-second child deadline,
closure fuel 100, closure cap 30000 ms and tableau visit budget 64.

The first two completed catalogs are 118/9/1/0 of 128 and
380/28/0/4 of 412 (pass/fail/skip/unsupported). Compared with the original
baseline, inconsistency repairs remove failures for disjoint data properties,
finite disjoint string patterns and minus infinity outside owl:real; the
malformed Rational-002 list is now withheld, giving a net gain of two.
Positive entailment gains eight cases (DisjointUnion-001, Nothing-002,
cardinality-006, complementOf-001, oneOf-003, unionOf-002/003/004), while
`WebOnt-description-logic-206` now fails at the enforced deadline. That is
an outstanding nominal-search performance regression, not a removed test.
The completed third catalog is 550/29/0/4 of 583.


The completed default-budget run totals **1048 pass, 66 fail, 1 skip,
8 unsupported out of 1123 judgments**, covering the same 482 distinct IDs.
It finishes in 376.060 seconds (369.682 CPU seconds), with eight refuter
timeouts and no closure caps. The original baseline was 1032/82/1/8 in
718.179 seconds with ineffective refuter deadlines. This is a net gain of
16 judgments; duplicated positive-entailment cases contribute twice to that
number. The evidence JSON records the exact removed/new failure IDs,
commands, binary digest and full raw log. Peak recorded process RSS is
368,705,536 bytes; it is not a sum of simultaneously resident processes.
No certificate or algorithm-completeness claim follows from this score.


### Untyped subjects and parser delta integrated

The [untyped-subject repair](20260908-owl-refute-untyped-functional-subjects.md)
now explicitly seeds graph subjects before the type-label fold. This changes
the initialization specification to repair the missed global constraint;
the indexed implementation is proved equal to that updated specification.
The root full build and public paired probes are in progress. The preceding
1048-judgment score was measured before this change.

The separate legacy SPARQL parser delta adds IRI function calls after FILTER,
standalone nonempty collections, ampersand-leading IRI references and validated
leading Unicode escapes. It addresses the ten baseline syntax verdict failures.
Further comparison changes remain under review; the agent's combined suite
score must not be attributed to this parser-only integration.


The six public subject-seeding probes now return false for the contradictory
typed and untyped graphs and true for all four satisfiable controls. Root
SPARQL suites are **466/15 of 481**, **631/0 of 631**, and **254/0 of 254**.
All 199 legacy syntax cases pass. The full build currently fails in
`TokenizerLemmas` and `AskBgpRoundTripString`: proofs that unfold the old
IRI-token guard need the expanded disjunction. Their original theorem
statements remain required; the parser agent is repairing the proofs.
