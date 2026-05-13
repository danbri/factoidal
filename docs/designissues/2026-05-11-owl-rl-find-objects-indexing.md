# Indexed `find_objects` / `find_subjects` for RDFS / OWL-RL closure

**Date:** 2026-05-11. Plan output by Plan-agent dispatch from the #200 closeout session.
**Goal:** retire the second perf cliff in the closure rules, after the
`add_triple_unchecked` + `graph_dedup_sort` fix in `eace203` cleared the first.

## Background

The `add_triple_if_new` → `add_triple_unchecked` swap (`eace203`) cleared one
O(N) factor from each closure rule. The remaining cliff: rules call
`find_objects g …` / `find_subjects g …` (RDF.Graph.Executable.fst:1081-1082,
1085+) which walk the entire graph linearly:

```fstar
let rec find_objects_acc (acc : list rdf_term) (g : rdf_graph)
  (subj : subject) (pred : wf_iri)
  : Tot (list rdf_term) (decreases g) =
  match g with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
    if subject_eq hd.s subj && hd.p = pred
    then find_objects_acc (hd.o :: acc) tl subj pred
    else find_objects_acc acc tl subj pred
```

Each rule wraps these in an outer `List.Tot.fold_left (fun acc t -> … find_objects g …) g g`.
Per rule: O(N) outer × O(N) `find_objects` = O(N²). For 27K-triple disease.ttl:
730M ops × ~28 OWL-RL rules × multiple iterations → > 60s.

The repo already has the right structure: `indexed_graph` with `ig_sp` /
`ig_pred` / `ig_po` buckets, built once via `build_indexed g`
(RDF.Graph.Executable.fst:449, now O(N log N) per the #259 fix). Missing:
`find_objects_indexed` / `find_subjects_indexed` and the rule-body rewiring.

## 1. Indexed lookup primitives

Insert directly after `bucket_lookup` (line 377), or after `ig_to_list`. Keys
reuse the helpers already defined: `subject_to_key` (338), `term_to_key_opt`
(348), `sp_key` (359), `po_key_opt` (362).

```fstar
(* Index-backed (s, p, ?) lookup. Bucket: ig_sp.
   Same return contract as find_objects. *)
let find_objects_indexed (ig : indexed_graph) (subj : subject) (pred : wf_iri)
  : list rdf_term =
  let bucket = bucket_lookup ig.ig_sp (sp_key subj pred) in
  List.Tot.map (fun (t : triple) -> t.o) bucket

(* Index-backed (?, p, o) lookup. Bucket: ig_po when o is non-literal,
   ig_pred fallback otherwise (then filter by object). *)
let find_subjects_indexed (ig : indexed_graph) (pred : wf_iri) (obj : rdf_term)
  : list subject =
  let bucket =
    match po_key_opt pred obj with
    | Some k -> bucket_lookup ig.ig_po k
    | None ->
      List.Tot.filter
        (fun (t : triple) -> rdf_term_eq t.o obj)
        (bucket_lookup ig.ig_pred pred)
  in
  List.Tot.map (fun (t : triple) -> t.s) bucket
```

Termination trivial (no recursion). `Tot` checks: identical to existing
bucket helpers.

## 2. Rule-body rewrite contract

**Signature decision:** every rule that calls `find_*` switches to
`(g : rdf_graph) (ig : indexed_graph) : rdf_graph`. The closure-step caller
builds `ig` once and threads it. Building inside each rule would re-incur
the (now O(N log N)) bucket build 35× per fixpoint iteration.

`g` itself is still passed because some rules iterate the triple list as
the outer driver; this remains an O(N) walk independent of the inner
lookup. Could later be replaced with `ig.ig_triples` and `g` dropped.

### RDFS rules (lines 1175-1310)

| Rule | Definition line | `find_*` call site(s) |
|---|---|---|
| `rdfs_rule_subPropertyOf` | 1175 | 1178 |
| `rdfs_rule_domain` | 1194 | 1197 |
| `rdfs_rule_range` | 1210 | 1213 |
| `rdfs_rule_subClassOf` | 1229 | 1235 |
| `rdfs_rule_subClassOf_trans` | 1250 | 1258 |
| `rdfs_rule_subPropertyOf_trans` | 1272 | 1278 |
| `rdfs_rule_container_membership` | 1295 | (no `find_*`; touch for sig only) |

### OWL-RL rules with `find_*` (lines 1581-3915)

`owl_rule_scm_eqc2` 1634 (1644), `owl_rule_scm_eqp2` 1661 (1669),
`owl_rule_transitive_property` 1709 (1727), `owl_rule_inverseOf_domain_range_flip` 1751,
`owl_rule_inverse_of` 1786, `owl_rule_sameAs_transitivity` 1878 (1884),
`owl_rule_sameAs_replace_subject` 1897, `owl_rule_sameAs_replace_object` 1919,
`owl_rule_sameAs_replace_predicate` 1941, `owl_rule_functional` 1967 (1988),
`owl_rule_inverse_functional` 2005 (2021), `owl_rule_pdw_to_differentFrom` 2062 (2086),
`owl_rule_fp_diff_to_diff` 2109, `owl_rule_ifp_diff_to_diff` 2144,
`owl_rule_svf2_existential_witness` 2496 (2507/2515/2526), `owl_rule_minc1_bridge` 2555 (2561),
`owl_rule_cls_svf2_qualified` 2651 (2670), `owl_rule_cls_minc_qual1` 2708 (2719),
`owl_rule_cls_maxqc1` 2849 (2860+helpers 2829/2836), `owl_rule_cls_exactqc1` 2905 (2916),
`owl_rule_cls_maxc2` 2962 (2970/2976/2980), `owl_rule_cls_avf1` 3020 (3029/3035/3039),
`owl_rule_property_chain_2` 3202 (3216+chain helpers), `owl_rule_property_chain_n` 3310,
`owl_rule_chain_to_transitive` 3353, `owl_rule_named_sameAs_to_equivClass` 3382 (3384),
`owl_rule_named_equivClass_to_sameAs` 3423 (3425), `owl_rule_prp_key` 3565 (via `agree_on_property` 3520-21),
`owl_rule_scm_dom2` 3757 (3763), `owl_rule_scm_rng2` 3781 (3787).

**Helpers also requiring `ig`:** `count_p_successors_typed_c` (2826),
`agree_on_property` (3516), `is_class` closures inside 3382/3423,
`decode_chain_pair` (3173), `decode_chain_list` / `decode_chain_list_fuel`
(3267/3241), `find_chain_endpoints` (3280), `decode_iri_list` (3454).

**Rules without `find_*`** (don't take `ig`): `owl_rule_equivalent_class` 1581,
`owl_rule_equivalent_property` 1610, `owl_rule_symmetric_property` 1683,
`owl_rule_sameAs_reflexivity` 1835, `owl_rule_sameAs_symmetry` 1845,
`owl_rule_differentFrom_symmetry` 1863, `owl_rule_reflexive_property` 3090,
`owl_rule_disjoint_with_propagation` 2417, `owl_rule_scm_cls_restriction` 3131,
`owl_rule_xsd_*` 3730/3812. Smaller diff.

## 3. Closure step orchestration

Both `rdfs_closure_step` (1317) and `owl_rl_closure_step` (3819) gain one
line at the top: `let ig = build_indexed g in`. Each `let gN = owl_rule_X gN-1 in`
passes `ig` as the second arg where applicable. The trailing
`graph_dedup_sort gN` (line 1330 / 3915) stays.

**Build cadence:** once per closure *step* (NOT per rule). Cost is
O(6 · N log N); doing it 35× per step would cost roughly the same as the
trailing `graph_dedup_sort`. Once-per-step preserves the existing
"see freshly added triples on the next iteration" semantics.

**Combining outputs:** unchanged — each rule still threads its accumulator;
`add_triple_unchecked` cons-prepends; trailing `graph_dedup_sort` collapses.

**Fixed-point check:** unchanged. `graph_len g' = graph_len g` (1339, 3928)
compares post-dedup lengths between successive steps; the index is never
compared, never persisted across iterations.

**Cross-step caching:** not worth it. Per-step rebuild is the sweet spot.

## 4. Soundness / correctness

The current code already uses an "index built from start-of-step `g`"
semantics: every rule body reads `g` (the parameter, NOT the in-flight
accumulator `acc`) when calling `find_objects g …`. E.g. line 1178: outer
fold's accumulator is `acc`, but `find_objects` reads `g`. So the existing
list-scan implementation already gives each rule a frozen snapshot view of
the graph at step entry. Replacing the snapshot with `ig = build_indexed g`
(also at step entry) is semantically identical.

**Trace: `rdfs_rule_subPropertyOf_trans` (1272).** At iteration N, suppose
the graph contains `(P sP Q)` and `(Q sP R)` but no `(P sP R)`. The current
step runs `rdfs_rule_subPropertyOf` first — that doesn't add subPropertyOf-
of-subPropertyOf triples (it only fires on `(a P b)` and emits `(a Q b)`
for non-`sP` `Q`). Then `rdfs_rule_subPropertyOf_trans` runs, looks up
`find_objects g6 q_subj rdfs_subPropertyOf`. Under current code reads
`g6`; under new code reads `ig` (= `build_indexed g`, the start-of-step
graph). Since no earlier rule in this step added subPropertyOf triples,
both reads see the same data. The fixed-point loop catches any inter-rule
lost-update on the next iteration regardless.

**Conclusion:** rebuilding the index once per step preserves *exact*
semantics with the existing implementation. No rule depends on intra-step
reading-from-acc.

## 5. Lemma impact

- 13 lemmas in `RDF.Graph.Executable.fst:528-575` (basic equality
  reflexivity + add/remove correctness). None mention `find_objects`,
  `find_subjects`, `rdfs_rule_*`, `owl_rule_*`, or any closure step.
  Zero invalidation.
- `SPARQL11.Algebra.fst:4767+` `eval_bgp_store` lemma cluster operates
  over `graph_store` / `triple_pattern_bound`; it does not mention closure
  rules or `find_*`. The closure path runs at ingest (before store
  materialisation — see `entailment_closure` 4187), so its primitives are
  outside the eval_bgp lemma scope. Zero invalidation.
- `Tableau.fst:111, 298, 336, 339, 917` also call `find_objects` /
  `find_subjects` directly — they keep the legacy list-scan signatures
  (we're *adding* indexed variants beside, not removing). No changes.

## 6. Effort estimate

- **New code in indexed primitives:** ~25 lines.
- **Rules to touch:** 7 RDFS + ~22 OWL-RL with `find_*` + ~6 helpers.
  Per rule: add `(ig : indexed_graph)` parameter, swap
  `find_objects g …` → `find_objects_indexed ig …`. Net ~2 lines per rule.
- **Closure step edits:** 2 lines added + parameter forwarding.
- **F\* verification risk:** very low. All primitives `Tot`; no new
  recursion. Termination metrics on existing recursive helpers
  (`decode_chain_list_fuel` etc.) are on `fuel` / `chain`, not on `g`,
  so adding `ig` doesn't perturb them.
- **Behavioural risk:** none — semantics-preserving by §4.

**Wall-clock:** 4-6 hours of mechanical edits + verification.

## 7. Recommended commit boundaries

1. **Commit A — indexed primitives + 7 RDFS rules + `rdfs_closure_step`.**
   Lowest risk; clears the RDFS half of the cliff. Self-contained
   verification target. Bench: lifesci 27K disease.ttl RDFS-only closure
   should drop from > 60s to ~few seconds.
2. **Commit B — OWL-RL rule batch + helpers + `owl_rl_closure_step`.**
   Larger but mechanical. Land after Commit A's CI is green. Re-run lifesci
   benchmark + W3C OWL-RL test suite.
3. **(Optional Commit C, follow-up):** incremental index updates inside
   `add_triple_unchecked` → drop the per-step rebuild entirely. Defer;
   only worth it if A+B don't fully clear the cliff.
