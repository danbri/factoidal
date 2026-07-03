# 2026-07-03 — OWL-RL sameAs closure blow-up: diagnosis (#262)

**Status:** diagnosis only — no code changed. Measurements taken at
commit `42b8409` with the committed `bin/linux-x86_64/owl_runner`.
Follow-up to
[`2026-05-15-cottas-literal-lookup-and-owl-rl-blowup.md`](2026-05-15-cottas-literal-lookup-and-owl-rl-blowup.md)
§2, which characterised the explosion but did not localise it. #263
(owl_runner RDF/XML "stall") was already confirmed a duplicate of this.

## 1. Summary

- The blow-up is real and now localised: the per-step cost of the
  sameAs cluster inside `owl_rl_closure_step`
  ([`RDF.Graph.Executable.fst:3661`](../../formal/fstar/RDF.Graph.Executable.fst))
  is **O(k⁶) in the sameAs-clique size k**, even though the closure's
  *output* for a k-clique is only O(k²) sameAs triples plus O(k·d)
  copied assertions. Measured wall-time exponent on synthetic cliques:
  log–log slope **5.3 over k = 8…24**, rising to **6.4 between k = 16
  and k = 24** (§4), consistent with the k⁶·log k analysis in §5.
- Two compounding causes, neither of which is the #259 index build:
  (a) rules emit unchecked duplicates and **later rules in the same
  step re-scan those duplicates as premises**, so duplicate
  multiplicity compounds multiplicatively through the rule chain
  before the single end-of-step dedup at
  [`RDF.Graph.Executable.fst:3761`](../../formal/fstar/RDF.Graph.Executable.fst);
  (b) the three `eq-rep-*` rules do an **O(list-length) inner scan per
  sameAs list entry** instead of using the per-step index that #259
  already builds.
- Contrary to the working hypothesis in issue #262's dashboard
  framing: **the blow-up is not why the profile-RL score is 20 pass,
  10 fail (out of 30)**. A full instrumented run (§3) shows all 30
  PositiveEntailmentTests complete in 11.88 s total with zero
  timeout-cap trips; the 10 failures are wrong-answer/missing-rule
  failures. The blow-up instead surfaces as (i) two 30 s cap trips
  inside the ConsistencyTest section — which then *pass by fallback*,
  masking the problem — and (ii) the `entailment/simple1` stall in the
  SPARQL entailment-regime suite documented in the 2026-05-15 doc.

## 2. Where the code stands

All references are to
[`formal/fstar/RDF.Graph.Executable.fst`](../../formal/fstar/RDF.Graph.Executable.fst).

| Piece | Line | Behaviour |
|---|---|---|
| `add_triple_unchecked` | 937 | `t :: g` — O(1) prepend, no dedup (per #259) |
| `graph_dedup_sort` | 980 | O(N log N) sort + collapse; run **once per step** |
| `owl_rule_sameAs_reflexivity` | 1660 | emits `(x sameAs x)` for **every** IRI/bnode node, every step, unconditionally (all duplicates after step 1) |
| `owl_rule_sameAs_symmetry` | 1670 | folds over the live list; re-emits the mirror of every sameAs entry, duplicates included; no reflexive skip |
| `owl_rule_sameAs_transitivity` | 1703 | folds over the live list; per sameAs entry does an `ig` lookup (k successors) and emits all compositions; no reflexive skip |
| `owl_rule_sameAs_replace_subject` (eq-rep-s) | 1722 | per non-reflexive sameAs entry, **inner `fold_left` over the entire live list** (1739–1746) |
| `owl_rule_sameAs_replace_object` (eq-rep-o) | 1753 | same shape, inner scan at 1764–1771 |
| `owl_rule_sameAs_replace_predicate` (eq-rep-p) | 1779 | same shape, inner scan at 1789–1797 |
| `owl_rl_closure_step` | 3661 | 28 rules chained `g1 … g28`; index `ig` built once from the step input (3664, snapshot semantics); single dedup at 3761 |
| `owl_rl_closure` | 3767 | fixpoint on `graph_len` equality (3774) — sound, since each step ends deduped and is monotone |
| `owl_rl_closure_with_reflexivity` | 3888 | RDFS closure + Group E `owl:Thing` axioms, then the OWL-RL fixpoint |

Two details matter for the cost model:

1. **Each rule folds over its own input parameter `g` as both premise
   source and accumulator seed.** Inside a step, `g8 =
   owl_rule_sameAs_transitivity g7a ig` scans `g7a` — which already
   contains every unchecked duplicate emitted by reflexivity and
   symmetry earlier in the same step. The `ig` snapshot is deduped;
   the live list is not, and the sameAs cluster's outer folds walk the
   live list.
2. **The eq-rep-\* guards added after the first #262 diagnostic**
   (comments at 1730–1736 referencing the "cascade diagnostic") skip
   reflexive pairs in `eq-rep-s/o/p`, but reflexivity still re-emits n
   duplicate `(x sameAs x)` entries per step, and symmetry and
   transitivity still process them and every other duplicate.

## 3. The 10 failing profile-RL PositiveEntailmentTests are not timeouts

Full catalog run, committed binary, from the repo root
(`timeout 600 ./bin/linux-x86_64/owl_runner -v`, default
`FACTOIDAL_OWL_CAP_SEC=30`, per-line timestamps on stderr; log
preserved during the session at `scratchpad/rl-catalog-run.log`):

- The PE section: **20 pass, 10 fail (out of 30) in 11.88 s** —
  matching `docs/test-results/latest.json`
  (`owl_rl_positive_entailment: pass 20, fail 10, total 30`). **No
  `[owl_closure_timeout]` fired during the PE section**, so raising
  the cap cannot change this score.
- Per-test wall time from the `[pe-running]` stderr timestamps: 24 of
  30 tests take < 0.05 s; the six sameAs/equivalence-shaped tests
  each take ≈ 1.8–1.9 s (`WebOnt-I4.6-003`, `WebOnt-I4.6-005-Direct`,
  `WebOnt-equivalentClass-002/-003/-008-Direct`, `WebOnt-sameAs-001`)
  — i.e. the sameAs cluster already dominates the runtime of the
  *passing* tests.
- The 10 failures, by shape:
  - **7 missing bnode-structured class-expression conclusions** (the
    closure never materialises these constructs):
    `DisjointClasses-001`, `DisjointClasses-003`,
    `New-Feature-ObjectQCR-002` (missing `owl:complementOf` bnode
    structure); `New-Feature-DisjointDataProperties-002`,
    `New-Feature-DisjointObjectProperties-002` (missing
    `rdf:type owl:AllDifferent` bnode structure); `WebOnt-I5.5-005`
    (missing `owl:unionOf` structure); `WebOnt-I5.26-010` (missing
    `rdf:type owl:Restriction`).
  - **2 XSD datatype-hierarchy range derivations**: `WebOnt-I5.8-008`
    (expects `rdfs:range xsd:unsignedShort`), `WebOnt-I5.8-009`
    (expects `rdfs:range xsd:short`) — `scm-rng2` + the XSD hierarchy
    rule do not cover these edges.
  - **1 harness-level failure**: `New-Feature-ObjectPropertyChain-BJP-002`
    is `FAIL/no-premise` (the catalog entry's premise literal is not
    picked up).
- Where the blow-up *does* bite in this catalog: two
  `[owl_closure_timeout]` cap trips at t = 50.97 s and t = 81.04 s,
  both inside the 76-test ConsistencyTest section (81.82 s total).
  `apply_closure`'s timeout fallback returns the **un-closed** graph
  ([`bin/owl-runner/owl_runner.ml:455-462`](../../bin/owl-runner/owl_runner.ml)),
  and an un-closed graph is trivially marker-free, so both tests are
  recorded PASS. The dashboard's "75 pass, 1 fail (out of 76)"
  consistency score therefore includes two tests whose reasoning
  never ran. That masking is worth its own line in #262.

So #262 gates: the SPARQL entailment-regime suite (`simple1`, per the
2026-05-15 doc), the two masked consistency tests, and any future use
of the closure on data-scale graphs. It does not gate the 20/30 PE
number; that is missing-rule territory and should be tracked
separately from #262.

## 4. Synthetic repro: wall time vs sameAs-clique size

Generator: a one-test catalog whose premise is a sameAs *chain*
`a1 sameAs a2 … a(k-1) sameAs ak` (the closure derives the full
k-clique) plus 3 property assertions on `a1`; conclusion
`ak sameAs a1` and `ak p1 v1`. Run:
`FACTOIDAL_OWL_CAP_SEC=590 timeout 600 ./bin/linux-x86_64/owl_runner <catalog>`.
Every k ≤ 24 passes the entailment check, confirming the closure is
*correct*, just slow.

| k (clique size) | premise triples | wall time |
|---:|---:|---:|
| 2 | 6 | 0.03 s |
| 4 | 6 | 0.08 s |
| 8 | 10 | 0.50 s |
| 12 | 14 | 2.89 s |
| 16 | 18 | 12.22 s |
| 24 | 26 | 163.87 s |
| 32 | 34 | **> 590 s (cap trip; FAIL by fallback)** |

Pairwise exponents (`ln(t2/t1)/ln(k2/k1)`): 8→12: 4.3; 12→16: 5.0;
16→24: **6.4**. Least-squares log–log slope over k ≥ 8: **5.3**.
Extrapolating the 16→24 slope to k = 32 predicts ≈ 740 s, matching
the observed > 590 s cap trip. The exponent climbing with k (4.3 →
6.4) is the signature of an asymptotic k⁶-per-step law with
lower-order terms still visible at small k — see §5.

For calibration: the true fixpoint for k = 32 is ~1 000 sameAs triples
plus ~100 copied assertions. A thousand-triple output taking ten
CPU-minutes is the bug in one sentence.

## 5. Cost model: why k⁶

Steady-state step on an already-closed clique (k² sameAs triples
including reflexives, D data triples), tracking the *live list length*
(dedup only happens at line 3761, after all 28 rules):

1. `sameAs_reflexivity` (1660): re-emits one `(x sameAs x)` per node —
   all duplicates. Minor by itself.
2. `sameAs_symmetry` (1670): scans the live list; mirrors each of the
   k² sameAs entries → sameAs multiplicity 2 (**2k² entries**).
3. `sameAs_transitivity` (1703): scans the live list; each of the 2k²
   sameAs entries triggers an `ig` lookup returning k successors and
   emits every composition → **≈ 2k³ sameAs list entries** (each
   distinct pair now present with multiplicity ≈ 2k). No reflexive
   skip, so the n reflexive entries also churn.
4. `sameAs_replace_subject` (1722): for each of the ≈ 2k³ non-reflexive
   sameAs entries, the inner fold at 1739 walks the **entire live
   list** (length ≈ 2k³ + D) → **≈ 4k⁶ triple comparisons**. Emissions
   are only ≈ 2k³·(D/k), but the scan dominates.
5. `sameAs_replace_object` (1753) and `sameAs_replace_predicate`
   (1779): same shape, each another O(k⁶) pass over an even longer
   list.
6. `graph_dedup_sort` (3761) finally collapses the list back to
   k² + O(k·d) — after the O(k⁶) work is spent.

The fixpoint needs ≈ log₂ k productive iterations (transitivity against
the snapshot index doubles reachable path length per step) plus one
no-change iteration that costs the same as a productive one. Total:
**O(k⁶ log k)** — versus O(k² log k) output. The measured 5.3→6.4
exponent brackets this (D-dominated terms flatten the curve at small
k).

The #259 fix (index built once per step, O(N log N) dedup per step)
addressed the *inter*-step cost. What it left in place is the
*intra*-step duplicate amplification: rules 2–5 read the live
duplicate-laden list instead of the deduped `ig` snapshot, and the
`eq-rep-*` inner loops ignore `ig` entirely even though `ig_subj` /
`ig_obj` buckets (lines 291–292) hold exactly the triples they scan
for.

## 6. Fix sketch (commit-sized): snapshot-driven sameAs cluster

Evaluated shapes, in ascending order of invasiveness:

- **(C) "bound output with `graph_add_unchecked` + one-shot
  canonicalise"** — this is the status quo post-#259 and is
  demonstrated insufficient by §4; the dedup runs after the O(k⁶)
  scans. Rejected.
- **(B) snapshot-driven rules + deduped pair list + index-backed
  eq-rep-\*** — recommended first commit; detailed below. Removes both
  causes without changing what any rule emits (modulo duplicates), so
  conformance risk is near zero.
- **(A) canonical-representative (union-find) sameAs handling** —
  asymptotically right (O(N α(N)) for the equivalence part, clique
  product materialised once at the end instead of per step), but it
  changes evaluation order for every rule that pattern-matches on
  individuals mid-step (`prp-key`, `cls-maxc2`, the contrapositive
  differentFrom rules, `is_inconsistent`'s sameAs/differentFrom clash
  scan), and canonical-pick interacts with bnode-vs-IRI conclusion
  matching in the runner. Right destination for data-scale workloads;
  wrong first commit. File as the follow-on once (B) has re-baselined
  the suites.

### (B) concretely

One new helper plus rewrites of the five sameAs-cluster rules
(reflexivity, symmetry, transitivity, eq-rep-s/o/p all keep their
names and signatures `rdf_graph -> indexed_graph -> rdf_graph`):

```fstar
(* Deduplicated, non-reflexive sameAs pairs drawn from the step-input
   snapshot. O(S log S) via the same sort used by graph_dedup_sort.
   Literals never appear (term_to_subject filters them). *)
let sameas_pairs (ig : indexed_graph) : list (subject * subject) =
  let raw =
    List.Tot.fold_left
      (fun (acc : list (subject * subject)) (t : triple) ->
        if t.p = owl_sameAs then
          match term_to_subject t.o with
          | Some y -> if subject_eq t.s y then acc else (t.s, y) :: acc
          | None -> acc
        else acc)
      [] ig.ig_triples
  in
  dedup_pairs_sorted raw   (* sortWith on subject_to_key pairs + adjacent collapse *)
```

```fstar
(* eq-rep-s, index-backed: per pair, bucket lookup instead of the
   O(list) inner fold at 1739. Same emissions, minus duplicates. *)
let owl_rule_sameAs_replace_subject (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let srcs = bucket_lookup ig.ig_subj (subject_to_key x) in
      List.Tot.fold_left
        (fun (acc2 : rdf_graph) (src : triple) ->
          if src.p <> owl_sameAs
          then add_triple_unchecked acc2 { s = y; p = src.p; o = src.o }
          else acc2)
        acc srcs)
    g (sameas_pairs ig)
```

`eq-rep-o` mirrors this with `bucket_lookup ig.ig_obj` (sameAs objects
are never literals, so the literal-free `ig_obj` bucket is exact);
`eq-rep-p` with `bucket_lookup ig.ig_pred`. Symmetry and transitivity
fold over `sameas_pairs ig` (k² entries, not 2k³); transitivity keeps
its `find_objects_indexed` successor lookup. Reflexivity switches its
emission to `add_triples_if_new`-style presence checks against `ig`
(or keeps unchecked emission — n duplicates per step is tolerable once
nothing downstream re-scans them).

Cost after (B): symmetry O(k²), transitivity O(k³) emissions,
eq-rep-s/o O(k²·d) — per step **O(k³ + k²·d)** instead of O(k⁶), with
the same O(log k) step count. k = 32 lands in milliseconds-to-seconds
territory.

Semantics delta to state in the commit message: the sameAs cluster
becomes a pure function of the step-input snapshot. Today, sameAs
facts emitted *earlier in the same step* (notably by
`owl_rule_named_equivClass_to_sameAs`, deliberately ordered before the
cluster at line 3687) are consumed within that step; under (B) they
are consumed one fixpoint iteration later. The fixpoint (fuel 100,
length-compare at 3774) converges to the identical closure — the
snapshot-semantics comment at 3662 already declares this the intended
model. Tests whose fixpoint takes +1 iteration:
`WebOnt-I4.6-005-Direct`, `WebOnt-equivalentClass-008-Direct` are the
ones to watch.

### Gates

Anything touching this cluster must re-run, and report in labelled
full-sentence form:

1. Profile-RL PositiveEntailmentTests — expect exactly **20 pass, 10
   fail (out of 30)** before and after; the 10 fails are unrelated to
   #262 (§3). Any delta means the rewrite changed semantics, not just
   cost.
2. Profile-RL Negative/Consistency/Inconsistency sections — currently
   3 pass of 6, 75 pass of 76, 4 pass of 14. The two masked
   consistency cap-trips should stop tripping; watch for a *newly
   honest* result there (a previously masked test may legitimately
   change outcome once its closure actually completes).
3. SPARQL 1.1 entailment-regime suite — 70 of 70 must hold, and
   `entailment/simple1` (the #262 poster child, currently stalling per
   the 2026-05-15 doc §2) must terminate; that test is the
   end-to-end proof the fix landed.
4. Full W3C SPARQL (631 of 631) and RDF (1031 of 1031) — untouched
   paths, but the dashboard regenerates from the same binary.
5. The §4 synthetic curve re-measured: k = 32 must complete well under
   the 30 s default cap, and the log–log slope should drop below 3.

### Follow-ups to file alongside the fix

- Make `apply_closure`'s timeout fallback visible per test type: a
  ConsistencyTest that falls back to the un-closed graph currently
  records PASS ([`owl_runner.ml:600-606`](../../bin/owl-runner/owl_runner.ml));
  it should record a distinct `FAIL/no-closure` (the outcome variant
  the #263 comment already names) or at minimum print which test
  tripped the cap.
- Split the "10 failing PE tests" work off #262: 7 need bnode-level
  class-expression materialisation, 2 need XSD hierarchy range edges,
  1 is a manifest/premise-extraction bug (`FAIL/no-premise`).
- Re-check `tests/unit/owl_direct_pipeline_timing.ml` (16-triple
  `simple.ttl`, currently "fuel=2 never returns in 5 min" per the
  2026-05-15 doc) after (B); it is the cheapest regression canary for
  the non-clique variant of the blow-up (reflexivity × functional-
  property interaction).
