---
name: measuring-inference
description: How to measure what an inference engine actually does — closure/entailment performance, and whether a green test measured anything at all. Use before optimising any reasoning path, when a perf claim needs an acceptance criterion, when a suite is green but you suspect it is not exercising the rules, when choosing benchmark shapes, or when a plausible-sounding mechanism is about to become a work order. Every rule here was paid for by a wrong confident claim in this repo, each one named with its date and its correction.
---

# Measuring inference behaviour

Reasoning engines mislead measurement in ways ordinary code does not. A
parser either parses or does not; a closure can produce a green suite, a
fast benchmark and a proved theorem while doing almost nothing.

Every rule below is followed by the specific wrong claim that produced
it. They are kept because the pattern recurs — during 2026-07-30/31, four
confident causal stories about this engine's performance were overturned
by measurement, three of them the orchestrator's own.

---

## 1. A plausible mechanism is not a measured one

**Never write an acceptance criterion for a fix until you have measured
which phase the time is actually in.**

> 🔴 **2026-07-31.** "The RDFS rules slowed the closure, so
> `WebOnt-description-logic-501` blew its CPU budget; recovering closure
> speed will bring it back." A 33× closure speedup later, the suite ran
> **1064.73 s → 1064.11 s** and the test was still capped. The cost was
> in the DL clash-seeking tableau, which is what the test's own
> diagnostic had said all along. The rules had knocked it out by making
> the closed graph **bigger**, not slower to produce — and no closure
> optimisation shrinks its output.

Before optimising: measure the phase split. `entail` time is not
`closure` time; a suite's wall clock is not the component you are about
to change.

## 2. Synthetic shapes lie about real vocabularies

**Benchmark on real vocabularies before believing a synthetic speedup.**

> 🔴 **2026-07-31.** A `subClassOf` chain went 109 s → 3.24 s, a 33×
> improvement, exponent ~3.0 → ~2.3. The same change on **schema.org**
> (17949 triples): 5.00 s → 4.82 s, **~4%**. Real vocabularies are wide
> and shallow — no deep transitive closure to skip. The chain is a
> pathological shape our data does not have.

Cover at minimum: chain (transitive worst case), wide-flat (instance
rules), diamond/DAG (multiple derivation routes), and **real
vocabularies** — SKOS, schema.org, FOAF, Dublin Core, GO. Report the
real ones first; they decide whether the work mattered.

Corollary: **the shape that matters is schema + instance data together.**
Measured 2026-07-31, that regime was already near-linear (n¹·²⁹) and the
real limit was throughput — ~2,500 input triples/sec — not complexity.
An asymptotic fix aimed at a non-asymptotic problem buys nothing.

## 3. A negative test passes for free when the engine derives nothing

A test asserting "X must NOT be entailed" is passed trivially by an
engine that derives nothing at all.

> 🔴 **2026-07-31.** `tools/negative-test-vacuity.py` found **19 of 42**
> negative tests vacuous. `rdf-mt` scored 39 pass, 0 fail with exactly
> **one** of its negatives doing on-target work. After the RDFS rules and
> the regime un-shadowing landed, vacuity fell 19 → 3 and 21 tests
> changed status, every one an improvement — movement that **no W3C
> score showed**, in either direction.

Run `tools/negative-test-vacuity.py` after any change to a rule set or an
entailment regime. Its criterion subtracts the closure of the *empty*
graph first, because RDFS injects 16 axiomatic triples into every result
and "the closure grew" would otherwise score every test as working.

⚠️ The "this test legitimately expects nothing" carve-out must come from
a **checkable property of the test's own data** — never a hand-kept list
of inconvenient names.

## 4. A theorem whose hypothesis is unsatisfiable proves nothing

> 🔴 **2026-07-30.** A draft `rdfs_closure_sound` assumed
> `forall h. ig_wf_sp (build_indexed h)`. That is **false** — a
> blank-node label containing U+001F breaks it — so the theorem was
> vacuous. It verified cleanly.

Exhibit a witness. `formal/fstar/RDF.Semantics.HypothesisWitness.fst`
holds satisfiability witnesses for the hypothesis predicates the
refinement theorems restrict on, and proves the fifteen-conjunct
`rdfs_conditions` bundle is jointly satisfiable *and* admits a model that
falsifies a graph — without which `rdfs_entails` would be the
everything-relation.

⚠️ Satisfiable is not the same as instantiable: `closure_chain_wf` is
mathematically satisfiable but **no graph in the tree can be shown to
satisfy it**, so the RDFS fixed-point theorem has no machine-checked
instance (#338).

## 5. Verify output identity byte-for-byte, not by count

> **2026-07-31.** Every closure change this week was validated with
> `sort | cmp`, not triple counts. Counts can match while contents
> differ.

Include the awkward term kinds — language-tagged literals, typed
literals, blank nodes — and a **reflective-trap graph**, where a rule
injects a schema edge that transitivity must then run over.

## 6. Real vocabularies violate the pre-conditions you would like to assume

**Prefer a post-hoc check to an a-priori side condition.**

> 🔴 **2026-07-31.** A fast path was designed around "no
> `rdfs:subPropertyOf` declaration targets `rdf:type`". Three of eight
> real vocabularies violate the condition, and **schema.org contains
> `schema:additionalType rdfs:subPropertyOf rdf:type`** — the reflective
> trap itself, in a vocabulary millions of sites use. Gating a-priori
> would have silently excluded it.

The landed design runs the fast path, then **checks** the property the
enumeration exists to establish, and discards the result for the general
path if it fails. A hole in the reasoning then costs speed, never
correctness. Given how often confident reasoning about this rule set has
been wrong, not trusting an enumeration at runtime is the correct
default.

## 7. Do not assume a rule is non-recursive because it looks like it

> 🔴 **2026-07-31.** "rdfs1, rdfs4a, rdfs4b, rdfs8 and rdfs13 are
> non-recursive, so hoist them out of the fixed-point loop." **All five
> are recursive.** rdfs13 produces `x rdfs:subClassOf rdfs:Literal`,
> which rdfs9 consumes; rdfs1 feeds rdfs13 feeds rdfs9. The counterexample
> is "declare a datatype, then use it" — ordinary data. The hoist would
> have silently lost derivations.

Derive stratification from the **conclusion templates in the rule
table**, not from a rule's appearance. What landed instead — emit-once,
each rule emitting each result once rather than once per round — kept all
twelve rules in the loop and still measured 3.7×.

## 8. A silent cap is a lie with a green face

> ⚠️ `rdfs_closure` returns its input unchanged when `fuel` runs out — no
> error, no marker. A graph needing more than 100 rounds yields a
> silently incomplete closure.

Same family as the OWL cap-escapes (#326) and the vacuous negatives
(#333). Any budget that can be exhausted must **say so in the result**.
Fixing #326 is why a capped OWL test now reports `unsupported` instead of
passing.

> 🔴 **2026-08-26 (`owl2_dl_inconsistency`, per-test cap).** The
> aggregated JSON records a cap trip as an ordinary `fail`. The runner
> log prints `[owl_refuter_escape] tableau_consistent abandoned
> (Owl_runner.Owl_closure_timeout); the clash search did not finish`,
> but `docs/test-results/latest.json` carries only `pass`, `fail`,
> `skip` and `oracle_assisted`. A reader of the dashboard cannot tell a
> wrong answer from an unfinished search.
>
> The score is therefore load-dependent. `generate-report.sh` sets
> `FACTOIDAL_OWL_CAP_SEC=20` for each test. In the full-suite run of
> 2026-08-26 the `type-inconsistency.rdf` catalog scored **125 pass,
> 2 fail (out of 127)**. Three consecutive runs of the SAME binary over
> the SAME catalog on an idle machine scored **126 pass, 1 fail (out of
> 127)**. The difference is `WebOnt-description-logic-502`, whose
> tableau clash search sits near the 20-second boundary.
> `WebOnt-description-logic-909` fails in all four runs.
>
> Cost: the extraction-drift repair gate of 2026-08-26 read RED on this
> suite, and the decrease was investigated as a possible regression
> from the restored extraction output. It was not one. The committed
> `latest.json` for that run records 125 pass, 2 fail with no marker
> that a cap tripped.
>
> Rule: before you attribute a suite decrease to a code change, run
> that suite alone on an idle machine and compare. Any budget that can
> be exhausted must be reported in the result; until it is, treat every
> capped suite as load-sensitive.

## 9. A timer around a pure `let` in Lean measures nothing

**Force the value between the two clock reads with an I/O action that
consumes it (an `IO.Ref` write), and print a total the parts must add
up to.**

> 🔴 **2026-08-22 (Lean, OWL RL closure).** The first per-row profile of
> `OWL.RL.step` read `rows total … ms=587` and `cls-int1 … ms=0` — every
> row 0 ms, the round seconds. Lean's compiler had moved the pure
> `let out := g.flatMap (f g)` past the second `IO.monoMsNow`, to the
> point where `out` was first used. The numbers were internally
> consistent enough to read as "the cost is somewhere else". With the
> value forced through an `IO.Ref` between the reads, the same row read
> `cls-int1 … ms=6443` of `ms=6640` — 97 % of the round, one quadratic
> join (every subject × a `memB` scan per class). That row alone kept
> WebOnt-miscellaneous-001 from finishing one round in 20 s
> (`cls-int1 … ms=20634` of `ms=20724`); the index that replaced the
> scan took the round to 88 ms.

A per-part timing whose parts do not sum to the whole it sits inside is
an instrument that did not run. The same applies to `decide`/`rfl`
over results: keep measurement in `IO`, force it, and cross-check the
sum.

## The standing discipline

1. State the acceptance criterion **as a number**, before the work.
2. Measure the phase you intend to change, not the wall clock around it.
3. Measure on real vocabularies, not only synthetic shapes.
4. Verify output identity byte-for-byte.
5. Re-run the vacuity checker; a change with no vacuity movement and no
   score movement may have changed nothing.
6. Let the number rewrite the plan. It did, twice, on 2026-07-31 —
   `docs/designissues/2026-07-31-rdfs-performance-scalability.md` §0.5 is
   the reprioritisation that measurement forced.

**A measured 15% is a useful result. A claimed 5× that does not survive
re-measurement is worse than nothing.**

## Related

* `skills/perf-benchmarking/SKILL.md` — timing harnesses, baselines,
  profiling policy generally.
* `skills/test-suites/SKILL.md` — suites and score-reporting discipline.
* `docs/designissues/2026-07-31-rdfs-performance-scalability.md` — the
  live plan, its measurements, and what measurement ruled out.
* `tools/negative-test-vacuity.py` — the vacuity checker.
* `formal/fstar/RDF.Semantics.HypothesisWitness.fst` — theorem-vacuity
  witnesses.
