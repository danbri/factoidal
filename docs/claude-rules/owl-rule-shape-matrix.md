# OWL.Closure rule shape matrix — the proof fan-out dispatch map

Surveyed 2026-08-04 (agent read of `OWL.Closure.fsti`) for the
rule-by-rule proof program. Shapes drive dispatchability:

- **SINGLE-FOLD** — one `fold_left`, guards/`existsb` inside the step
  are fine. PROVABLE TODAY with the established skeleton (verbatim
  local lambda + `fold_left_inv` + `assert_norm`); index-reading
  guards take `ig_wf_sp` + `ig.ig_triples == g` hypotheses.
- **NESTED-SINGLE** — outer fold binds a single triple/subject,
  inner fold inside. The `rdfs_rule_domain_sound` shape; expected
  provable (first test case: prp-trp licensing, in flight).
- **NESTED-PAIR** — outer step binds/destructures a pair. BLOCKED:
  two real proofs fail undischargeably at the outer step obligation;
  cause unknown (tuple-binder hypothesis REFUTED by
  `formal/fstar/repro/TupRepro1-10.fst`); bisection in progress.
  Task #36.
- **LIST-WALK** — `decode_iri_list`/`decode_chain_list` traversal.
  Needs the `decode_iri_list_sound` bridge (exists — used by
  cls-oo's truth-preservation); licensing analogues not yet
  attempted.
- **OTHER** — multi-nested or fixed-table; case-by-case.

⚠️ Provenance: rows through `owl_rule_differentFrom_to_allDifferent`
were read; the final few `comp_*` rows were INFERRED by the surveyor
from partial reads — re-verify before relying on them (marked ✱).

| rule | shape | indexes | source |
|---|---|---|---|
| equivalent_class | SINGLE-FOLD | none | g |
| equivalent_property | SINGLE-FOLD | none | g |
| scm_eqc2 | SINGLE-FOLD | find_objects | g |
| scm_eqp2 | SINGLE-FOLD | find_objects | g |
| symmetric_property | NESTED-SINGLE | none | collected list, then g |
| transitive_property | NESTED-SINGLE | find_objects | collected, then g + index |
| inverseOf_domain_range_flip | NESTED-PAIR | none | g × g |
| inverse_of | NESTED-PAIR | none | g × g |
| sameAs_reflexivity | SINGLE-FOLD | none | collected nodes |
| sameAs_symmetry | SINGLE-FOLD | snapshot pairs | sameas_pairs |
| differentFrom_symmetry | SINGLE-FOLD | none | g |
| sameAs_transitivity | NESTED-SINGLE¹ | find_objects | sameas_pairs × index |
| sameAs_replace_subject | NESTED-SINGLE¹ | ig_subj | sameas_pairs × bucket |
| sameAs_replace_object | NESTED-SINGLE¹ | ig_obj | sameas_pairs × bucket |
| sameAs_replace_predicate | NESTED-SINGLE¹ | ig_pred | sameas_pairs × bucket |
| functional | NESTED-SINGLE | find_objects | collected × index |
| inverse_functional | NESTED-SINGLE | find_subjects | collected × index |
| pdw_to_differentFrom | NESTED-PAIR | find_objects | collected × g × index |
| pdw_shared_value_to_differentFrom | NESTED-PAIR | find_subjects | collected × g × index |
| fp_diff_to_diff | NESTED-SINGLE | none | collected × g |
| ifp_diff_to_diff | NESTED-SINGLE | none | collected × g |
| disjoint_with_propagation | SINGLE-FOLD | none | g |
| disjoint_to_complement | NESTED-SINGLE | find_subjects | g × index |
| svf2_existential_witness | OTHER | both | g, four nested folds |
| minc1_bridge | NESTED-SINGLE | find_objects | g × index |
| cls_hv1 | NESTED-SINGLE | both | g × index |
| cls_hv2 | NESTED-SINGLE | both | g × index |
| cls_svf2_qualified | NESTED-SINGLE | find_objects | g × index |
| cls_minc_qual1 | NESTED-SINGLE | find_objects | g × index |
| cls_hasself1 | NESTED-SINGLE | both | g × index |
| cls_hasself2_synth | SINGLE-FOLD | none | g |
| cls_svf_thing_materialize | SINGLE-FOLD | none | g |
| cls_svf_thing_witness | NESTED-SINGLE | both | g × index |
| cax_dw_to_differentFrom | NESTED-PAIR | find_subjects | collected × index, double |
| cls_maxqc1 | NESTED-SINGLE | find_objects | g × index + count |
| cls_exactqc1 | NESTED-SINGLE | find_objects | g × index |
| cls_maxc2 | OTHER | both | g, triple nested |
| cls_maxqc_comp | OTHER | both | g, quadruple nested |
| cls_avf1 | OTHER | both | g, quadruple nested |
| reflexive_property | NESTED-SINGLE | none | collected × collected |
| scm_cls_restriction | SINGLE-FOLD | none | g |
| property_chain_2 | NESTED-SINGLE | find_objects | g × g |
| property_chain_n | LIST-WALK | ig_pred, find_objects | g + chain decode |
| chain_to_transitive | SINGLE-FOLD² | none | g |
| transitive_to_chain | SINGLE-FOLD³ | none | g |
| named_sameAs_to_equivClass | SINGLE-FOLD | find_objects | g |
| named_equivClass_to_sameAs_mode | SINGLE-FOLD | find_objects | g |
| named_equivClass_to_sameAs | SINGLE-FOLD | find_objects | g (wrapper) |
| cls_int1 | LIST-WALK | find_subjects | g + list decode |
| cls_oneof | LIST-WALK | none | g + list decode |
| cls_uni | LIST-WALK | none | g + list decode |
| cls_uni_elim | LIST-WALK | find_subjects | g + list decode |
| oneof_set_equivalence | SINGLE-FOLD | none | collected, double fold |
| prp_key | OTHER | find_objects | collected, triple nested |
| xsd_datatype_axioms | OTHER | none | mention-check + fixed lists |
| dt_range_intersect | NESTED-SINGLE | find_objects | g × index + table |
| scm_dom2 | NESTED-SINGLE | find_objects | g × index |
| scm_rng2 | NESTED-SINGLE | find_objects | g × index |
| subprop_domain_range | NESTED-SINGLE | both | g × index |
| symmetric_metapredicates | SINGLE-FOLD | none | g |
| inverse_characteristics | NESTED-SINGLE | find_objects | g + transfer helper |
| equivalent_property_characteristics | NESTED-SINGLE | find_objects | g + transfer helper |
| cardinality_to_min_max | NESTED-SINGLE | find_objects | g + emit helper |
| cls_maxqc34 | OTHER | both | g, quadruple nested |
| fp_pinned_subproperty | OTHER | find_objects | g, triple+ nested |
| singleton_nominal_functionality | NESTED-SINGLE | find_subjects | g + list length + index |
| hasvalue_card_disjoint | NESTED-PAIR | find_objects | pins × pins |
| avf_thing_to_range | NESTED-SINGLE | find_objects | g × index |
| extensional_symmetry | SINGLE-FOLD | both | g + extension helper |
| xsd_core_datatype_axioms | OTHER | none | fixed list |
| builtin_vocabulary_axioms | OTHER | none | fixed list |
| all_disjoint_classes | NESTED-SINGLE | none | g + chain decode + pairs |
| all_disjoint_properties | NESTED-SINGLE | none | g + chain decode + pairs |
| allDifferent_to_differentFrom | LIST-WALK | find_subjects | g + chain decode |
| differentFrom_to_allDifferent | LIST-WALK | find_objects | g + chain decode |
| rdf_based_full_meta_axioms_mode | OTHER | none | mode-gated fixed groups |
| comp_singleton_union ✱ | SINGLE-FOLD | none | base overlay |
| comp_min1_restriction ✱ | SINGLE-FOLD | none | base overlay |
| comp_oneof_union ✱ | LIST-WALK | find_objects | base + list decode |
| comp_union_oneof ✱ | LIST-WALK | find_subjects | base + list decode |
| comp_enum_range_value ✱ | OTHER | both | base, nested |
| comp_range_avf ✱ | OTHER | both | base, nested |
| comp_range_intersection ✱ | OTHER | find_objects | base, nested |
| comp_pinned_domain_enum ✱ | OTHER | both | base, nested |

² `decode_chain_pair` is a fixed two-hop read, not a recursive walk —
SINGLE-FOLD confirmed; truth-preservation proved (Soundness Rule 11)
with the `decode_chain_pair_sound` bridge.

³ Shape confirmed, but truth-preservation is UNPROVABLE in the
fixed-assignment pilot shape: the rule MINTS FRESH BNODES
(canonical chain-cell labels), and no RDF-Based table asserts the
existence condition their truth would need — a genuine model can
declare P transitive with rdf:first/rdf:rest relating nothing.
Needs a model-extension/Skolem lemma shape or the licensing-side
treatment the comprehension-witness rules get. Finding recorded in
Soundness's Rule 12 comment block (2026-08-05).

¹ The scout classified the sameAs-cluster rules NESTED-SINGLE, but
their outer fold walks `sameas_pairs ig` — the step BINDS A PAIR
(`let (x, y) = xy` or destructuring), which is the parked shape:
eq-trans is one of the two failing proofs. Treat the four
sameas-pair-outer rules as NESTED-PAIR until the bisection verdict.

Proved so far (2026-08-04): licensing — eq-sym, eq-ref, prp-symp,
scm-eqc1, scm-eqp1 (5); truth-preservation — prp-symp, rdfs2, rdfs3,
eq-sym, cls-oo, scm-eqc1, scm-eqp1, eq-ref, eq-diff-sym (9);
extension — differentFrom_symmetry (1). In flight: prp-trp +
scm-eqc2 licensing, bisection + two encoding experiments on the
parked shape.
