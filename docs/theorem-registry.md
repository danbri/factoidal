# Theorem registry

Deliverable 1 of goal G1 in
[`designissues/2026-08-05-semantics-proposal-adoption.md`](designissues/2026-08-05-semantics-proposal-adoption.md).
G1's aim: a W3C-domain expert can review Factoidal's semantics — the
table rows, the spec predicates that transcribe them, and this
registry's status column — and know the reviewed definitions are not
overridden by implementation detail, without reading a single F\*
proof. The proofs' only job is the "not overridden" guarantee, checked
by `make verify-rdf-mt` (20 modules, listed under Trust surface below).

**Maintenance**: hand-curated. There is no generator. Update this file
in the same commit as any proof landing that changes a status cell —
a new `_licensed`/`_sound`/`_true` lemma, a STOP/impossibility finding,
or a ledger-drift correction. A stale registry is worse than none: it
is exactly the "reviewed definitions overridden by implementation
detail" failure G1 exists to prevent.

**Date**: 2026-08-05. **Tree state**: commit `27c23d5` (HEAD at time of
writing) plus a read-only survey of the four proof files below; no
`.fst`/`.fsti`/Makefile edits were made to produce this registry.

**Scope, honestly stated**: this registry covers the OWL 2 RL/RDF
rule-by-rule licensing + truth-preservation program
(`OWL.RL.Spec.fst` / `OWL.RL.Refinement.fst` / `OWL.Semantics.Soundness.fst`)
and the RDF / RDFS / Simple entailment rungs
(`RDF.Entailment.*.fst`). It does NOT cover: SHACL, RDFC-1.0
canonicalization, SPARQL algebra/evaluation correctness, the parser
layer, or the storage/COTTAS backend — those have their own test
suites (`skills/test-suites/SKILL.md`) but no model-theoretic proof
program yet. Counts below are always **N of M**, both labelled.

## 1. OWL 2 RL/RDF — licensing and truth, per engine rule

The 84-function engine ledger (foot of
[`../formal/fstar/OWL.RL.Spec.fst`](../formal/fstar/OWL.RL.Spec.fst))
classifies every `OWL.Closure` rule function as `[row]` (implements a
named W3C table row), `[ext]` (sound extension, justified in the
rule's own banner — no table row exists to license against), `[axm]`
(materialises an axiomatic-triple table, not a rule), or `[mode]`
(fires only under a catalog semantics mode). This table is that
ledger, plus two proof columns:

- **Licensing** — "every emission is input or one W3C-row
  application" (`OWL.RL.Refinement.fst`). Applies only to `[row]`
  entries (an `[ext]`/`[axm]`/`[mode]` entry has no row to license
  against by definition).
- **Truth** — "every emission is true in every model of the row's
  condition" (`OWL.Semantics.Soundness.fst`, banner-numbered "Rules
  1-20"). Applies to `[row]` and `[ext]` entries alike.

Status values: **PROVED**, **PARKED(reason)**, **IMPOSSIBLE(evidence)**,
**UNATTEMPTED**, **N/A** (proof kind does not apply to this entry
class).

**Licensing count: 23 of 34 `[row]` table-row obligations proved**,
using the ledger's own accounting (`subprop_domain_range` and
`cls_maxqc34` each count as covering TWO rows; `property_chain_2`/
`property_chain_n` count as covering ONE row between them — the
arithmetic the ledger's closing comment states). This matches the
count commit `27c23d5` itself reports ("Licensing count: 23 of 34 rows
proved"). **Verified independently for this registry**: counting
`owl_rule_*_licensed` lemmas directly in `OWL.RL.Refinement.fst` gives
**22 lemmas**; two of them (`inverse_of`, `subprop_domain_range`) each
license TWO distinct `_derives` predicates in one lemma. Taking
`inverse_of`'s pair as counting ONE unit (the convention the ledger's
"34" arithmetic implies, symmetric with how `property_chain`'s two
functions collapse to one row) reproduces 23 exactly. Taking it as
counting two units (the literal reading — Table 4 lists prp-inv1 and
prp-inv2 as two separate rows with distinct premises) gives **24**.
**Discrepancy flagged, not resolved**: the "34" denominator's footnote
only names `subprop_domain_range` and `cls_maxqc34` as double-counted;
it does not say `inverse_of` is single-counted despite covering two
literal table rows the same way `subprop_domain_range` does. Someone
should either adjudicate this explicitly in the ledger comment or
accept the count is 23-or-24 depending on convention.

**Truth count: 29 of ~32 attempted rules proved** (wave 2, Rules 28-32, landed 2026-08-06: scm-dom1/rng1 realizations, subprop_domain_range, cls-int1/cls-uni realizations) (`OWL.Semantics.Soundness.fst`
"Rules 1-27" banner numbering; two banner slots, 2b and 16→17, are a
sub-rule and a superseded first attempt, so 27 banner numbers cover 26
distinct engine rules); **3 of those 26 are IMPOSSIBLE** with recorded
evidence (fresh-bnode-minting rules); the remaining ~58 of 84 ledger
entries are UNATTEMPTED for truth (no `_sound` lemma exists yet).
G3 M4 wave 1 (2026-08-06) landed Rules 21-27: `scm_eqp2`, `sameAs_
transitivity`, `transitive_property`, `functional`, `inverse_functional`,
`inverse_of`, and `prp_key` — all seven target rules PROVED, including
prp-key against the UNWEAKENED `cond_haskey` condition (the bridging
fact the registry asked for, `cond_literal_term_eq_respecting` +
`lemma_rdf_term_eq_denot`, was proved rather than needed as a park).
Six new semantic conditions landed in `OWL.Semantics.fst`:
`cond_mutual_subproperty_equivalent`, `cond_transitive`,
`cond_functional`, `cond_inverse_of`, `cond_literal_term_eq_respecting`,
`cond_haskey`; a seventh, `cond_inverse_functional`, landed in
`OWL.Semantics.Soundness.fst` next to Rule 25 (mirrors `cond_functional`,
symmetric in which side of the pair is fixed).

| W3C id / marker | Spec predicate | Engine function | Licensing | Truth | Hypotheses / fragment notes | Notes |
|---|---|---|---|---|---|---|
| scm-eqc1 | `scm_eqc1_derives` (OWL.RL.Spec.fst) | `equivalent_class` | ✅ PROVED | ✅ PROVED | none beyond `holds_all`/graph membership | Ledger-drift #1 (commit `7ba8bb1`): entry previously claimed cax-eqc1/eqc2; corrected to scm-eqc1 while writing the licensing lemma. |
| scm-eqp1 | `scm_eqp1_derives` | `equivalent_property` | ✅ PROVED | ✅ PROVED | none | Ledger-drift #2 (commit `78e9c0c`): previously claimed prp-eqp1/eqp2; same disease as scm-eqc1. |
| scm-eqc2 | `scm_eqc2_derives` | `scm_eqc2` | ✅ PROVED | ✅ PROVED | `ig_wf_sp`, `ig.ig_triples == g` | Truth proof needed a guard-depth flattening (2026-08-05) after a first attempt hit depth-4 SMT witness chains (Rule 16 in Soundness banner records the parked first attempt; Rule 17 is the pass). |
| scm-eqp2 | `scm_eqp2_derives` | `scm_eqp2` | ✅ PROVED | ✅ PROVED | `ig_wf_sp`, `ig.ig_triples == g`, `cond_mutual_subproperty_equivalent` | Rule 21 (Soundness banner); mirrors Rule 17's guard-depth-flattened scm-eqc2 proof exactly, one level down (properties instead of classes). |
| prp-symp | `prp_symp_derives` | `symmetric_property` | ✅ PROVED | ✅ PROVED | none | — |
| prp-trp | `prp_trp_derives` | `transitive_property` | ✅ PROVED | ✅ PROVED | `ig_wf_sp`, snapshot semantics, `cond_transitive` | Rule 23 (Soundness banner); NESTED-SINGLE, same collect-then-emit shape as Rule 1 (prp-symp) one indexed-lookup deeper. |
| [ext] | n/a — no table row; banner in OWL.Closure.fsti | `inverseOf_domain_range_flip` | N/A | UNATTEMPTED | — | Domain/range of P become range/domain of P⁻¹. |
| prp-inv1 + prp-inv2 | `prp_inv1_derives` / `prp_inv2_derives` | `inverse_of` | ✅ PROVED (both, one lemma) | ✅ PROVED (both, one lemma) | `cond_inverse_of` (iff, symmetric in which direction fires) | Licensing: solved via the closure-identity / PROOF-FRIENDLY GUARD RULE fix (`OWL.Closure.inverse_of_emit`, task #36, commit `fb8d98f`) — first rule proved after the nested-pair closure-identity obstruction was diagnosed. Truth: Rule 26 (Soundness banner), reuses the same named `inverse_of_emit` symbol so the nested-pair step obligation carries no fresh closure-identity risk. |
| eq-ref | `eq_ref_derives` | `sameAs_reflexivity` | ✅ PROVED | ✅ PROVED | none | — |
| eq-sym | `eq_sym_derives` | `sameAs_symmetry` | ✅ PROVED | ✅ PROVED | none | First licensing lemma landed in the program. |
| [ext] | n/a | `differentFrom_symmetry` | N/A | ✅ PROVED | none | Table 5.13's differentFrom condition is symmetric in its arguments; first `[ext]` entry to get a truth proof. |
| eq-trans | `eq_trans_derives` | `sameAs_transitivity` | ✅ PROVED | ✅ PROVED | `ig_wf_sp`, `cond_sameas_identity` | Rule 22 (Soundness banner); carried entirely by `cond_sameas_identity`'s iff (both directions), no dedicated transitivity condition needed. |
| eq-rep-s | `eq_rep_s_derives` | `sameAs_replace_subject` | ✅ PROVED | ✅ PROVED | `ig_wf_subj` | — |
| eq-rep-o | `eq_rep_o_derives` | `sameAs_replace_object` | ✅ PROVED | ✅ PROVED | `ig_wf_obj` | — |
| eq-rep-p | `eq_rep_p_derives` | `sameAs_replace_predicate` | ✅ PROVED | ✅ PROVED | `ig_wf_pred` | — |
| prp-fp | `prp_fp_derives` | `functional` | ✅ PROVED (commit `27c23d5`) | ✅ PROVED | needs named top-level helpers (`owl_prp_fp_collect_step`/`emit`/`step`) — lambda-lift landed same commit; truth adds `cond_functional`, `cond_sameas_identity` | Rule 24 (Soundness banner); references the engine's own named helpers directly — cleanest of the G3 M4 wave 1 rules, no closure-identity risk at any fold level. |
| prp-ifp | `prp_ifp_derives` | `inverse_functional` | ✅ PROVED (commit `27c23d5`) | ✅ PROVED | `ig_wf_po`, `ig_wf_pred`, `graph_literal_match_exact`; needed `RDF.Indexed.fsti` helper naming (`triple_obj_matches`, `triple_subject_of`); truth adds `cond_inverse_functional`, `cond_sameas_identity` | Closure-identity law applies one level down through `find_subjects_indexed`'s filter/map, not just the emit fold. Truth: Rule 25 (Soundness banner) reuses the licensing proof's `lemma_find_subjects_indexed_wf` verbatim via `open OWL.RL.Refinement` in `OWL.Semantics.Soundness.fst` (new cross-file dependency, no cycle). |
| [ext] | n/a | `pdw_to_differentFrom` | N/A | UNATTEMPTED | — | Disjoint properties force distinct subjects on a shared object. |
| [ext] | n/a | `pdw_shared_value_to_differentFrom` | N/A | UNATTEMPTED | — | Sibling of the above. |
| [ext] | n/a | `fp_diff_to_diff` | N/A | UNATTEMPTED | — | Functional property + different objects force different subjects. |
| [ext] | n/a | `ifp_diff_to_diff` | N/A | UNATTEMPTED | — | Inverse-functional mirror. |
| [ext] | n/a | `disjoint_with_propagation` | N/A | ✅ PROVED | none | Disjointness inherits down `rdfs:subClassOf` (cites cax-dw + cax-sco); second `[ext]` truth proof landed. |
| [ext] | n/a | `disjoint_to_complement` | N/A | UNATTEMPTED | — | `disjointWith` into `complementOf` scaffolding for the clash checker. |
| [ext] | n/a | `svf2_existential_witness` | N/A | UNATTEMPTED | — | Comprehension-witness layer (four nested folds). |
| [ext] | n/a | `minc1_bridge` | N/A | UNATTEMPTED | — | Comprehension-witness layer. |
| cls-hv1 | `cls_hv1_derives` | `cls_hv1` | UNATTEMPTED | UNATTEMPTED | — | — |
| cls-hv2 | `cls_hv2_derives` | `cls_hv2` | UNATTEMPTED | UNATTEMPTED | — | — |
| [ext] | n/a | `cls_svf2_qualified` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `cls_minc_qual1` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `cls_hasself1` | N/A | UNATTEMPTED | — | ObjectHasSelf semantics (Table 5.x); `hasSelf` has no RL table row. |
| [ext] | n/a | `cls_hasself2_synth` | N/A | ❌ IMPOSSIBLE (mints a fresh bnode; Rule 15 in Soundness banner) | — | Same STOP shape as `transitive_to_chain`/`cls_svf_thing_materialize`: a comprehension-witness existence condition the W3C tables do not assert, under the fixed-assignment shape. |
| [ext] | n/a | `cls_svf_thing_materialize` | N/A | ❌ IMPOSSIBLE (mints a fresh bnode; Rule 14) | — | Mints `canonical_svf_thing_restriction_bnode`; no premise in g asserts that resource already exists. Closing it needs a model-EXTENSION lemma (Henkin/Skolem-style), a different lemma shape than Rules 1-11/13 use. |
| [ext] | n/a | `cls_svf_thing_witness` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `cax_dw_to_differentFrom` | N/A | UNATTEMPTED | — | Disjoint classes force `differentFrom` on their members. |
| cls-maxqc1 (clash) | `cls_maxqc1_clash` | (clash checker; part of `table5_clashes`) | UNATTEMPTED | N/A (clash/inconsistency row, not derivation) | — | Ledger lists this as `[row] cls-maxqc1`; the row is actually an inconsistency-trigger, transcribed as a CLASH predicate, not a `_derives` triple-derivation predicate. |
| [ext] | n/a | `cls_exactqc1` | N/A | UNATTEMPTED | — | Exact qualified cardinality decomposes into min+max; no RL row of its own. |
| cls-maxc2 | `cls_maxc2_derives` | `cls_maxc2` | UNATTEMPTED | UNATTEMPTED | — | — |
| [ext] | n/a | `cls_maxqc_comp` | N/A | UNATTEMPTED | — | The #236 anchor machinery. **Known sound-but-narrow** (see CLAUDE.md "Known sound-but-narrow rewrites"): drops vacuous-truth individuals and OWL-Full punned class-individuals; the internal-variable LEAK the 2026-07-09 strict runner found is FIXED (task #100, `strip_rewrite_internal_vars`). |
| cls-avf | `cls_avf_derives` | `cls_avf1` | UNATTEMPTED | UNATTEMPTED | — | — |
| [ext] | n/a | `reflexive_property` | N/A | UNATTEMPTED | — | ReflexiveProperty semantics; RL profile has no prp-rfl row. |
| [ext] | n/a | `scm_cls_restriction` | N/A | ✅ PROVED | none, single-fold, no fresh bnodes | `owl:Restriction rdfs:subClassOf owl:Class` (Table 5, Axiomatic Triples) read through the RDFS class-extension condition. |
| prp-spo2 (n=2) | `prp_spo2_derives` | `property_chain_2` | UNATTEMPTED | UNATTEMPTED | — | Splits one row across two engine functions by chain arity. |
| prp-spo2 (n≥3) | `prp_spo2_derives` | `property_chain_n` | UNATTEMPTED | UNATTEMPTED | — | See above. |
| [ext] | n/a | `chain_to_transitive` | N/A | ✅ PROVED | no recursion needed (unlike Rule 4's list-walk) | A chain p·p → p IS transitivity; bridge, banner proof. |
| [ext] | n/a | `transitive_to_chain` | N/A | ❌ IMPOSSIBLE (mints two fresh bnodes; Rule 12) | — | Converse bridge. Needs `canonical_chainl1_bnode`/`_chainl2_bnode` witnesses (rdf:first/rdf:rest list cells) with no premise in g requiring their existence — an existence condition, not an implication, that no W3C RDF-Based table asserts. STOP per the two-attempt rule; would need a model-extension lemma or a licensed-by-g (syntactic-provenance) reframing instead. |
| [ext] | n/a | `named_sameAs_to_equivClass` | N/A | UNATTEMPTED | — | RDF-Based semantics: sameAs classes are equivalentClass (Table 5.x). |
| [mode] | n/a | `named_equivClass_to_sameAs_mode` | N/A | UNATTEMPTED | — | Converse, catalog-gated (`owl_semantics_direct`). |
| [mode] | n/a | `named_equivClass_to_sameAs` | N/A | UNATTEMPTED | — | Wrapper of the above. |
| cls-int2 | `cls_int2_derives` | `cls_int1` | ✅ PROVED (today's precursor, commit `2e482d3`) | ✅ PROVED (Rule 31) | list-walk bridge (`decode_iri_list_sound`) | **MISNAMED function**: reads x typed into intersection C, emits x typed into every member Cᵢ — cls-int2's shape, not cls-int1's (which synthesises C-membership from a batched premise). No engine function realises the literal cls-int1 row. Corrected 2026-08-05 (ledger drift #5/#6, commit `72a965c`). |
| cls-oo | `cls_oo_derives` | `cls_oneof` | ✅ PROVED | ✅ PROVED | list-walk bridge | — |
| scm-uni (Table 8) | `scm_uni_derives` | `cls_uni` | ✅ PROVED (today's precursor, commit `2e482d3`) | ✅ PROVED (Rule 32) | list-walk bridge | **MISNAMED function**: emits `Cᵢ rdfs:subClassOf C` per member — Table 8's schema row, not Table 5's cls-uni type-propagation row. The `owl:disjointUnionOf` branch additionally emits an EXTENSION (plain-unionOf restatement + pairwise disjointWith), no W3C row of its own. Corrected 2026-08-05 (commit `72a965c`). |
| [ext] | n/a | `cls_uni_elim` | N/A | UNATTEMPTED | — | Union-membership elimination under disjointness side conditions. |
| [ext] | n/a | `oneof_set_equivalence` | N/A | UNATTEMPTED | — | oneOf lists with equal member sets name equivalent classes. |
| prp-key | `prp_key_derives` (row) / `prp_key_derives_approx` (proved against) | `prp_key` | ✅ PROVED, **WEAKENED ROW** (commit `c600646`) | ✅ PROVED, **UNWEAKENED** | `ig_wf_sp`, `ig.ig_triples == g`, `cond_haskey`, `cond_sameas_identity`, `cond_literal_term_eq_respecting` | Engine's `agree_on_property` uses `rdf_term_eq` (RDF-1.1 value equality — case-insensitive lang tags, XMLLiteral c14n, #337) where the row's `shares_key_values` uses plain `==`. Machine-checked counterexample (`"Alice"@en` vs `"Alice"@EN`) shows the engine accepts strictly MORE value pairs as "shared" than the literal row licenses — an OVER-approximation on the value-sharing axis (opposite direction from the cls-int/scm-uni narrowing above). `owl_rule_prp_key_licensed` is proved against the local weakening, not `prp_key_derives` itself. WEAKENED-ROW CONFIRMATION, not a ledger drift — the row transcription is faithful to Table 4. **Truth closes the gap the licensing weakening left open** (G3 M4 wave 1, 2026-08-06): `cond_literal_term_eq_respecting` + `lemma_rdf_term_eq_denot` (`OWL.Semantics.fst`) establish that `rdf_term_eq`-equal literals denote the SAME domain element under any genuine interpretation — RDF 1.1 Concepts §3.3 already treats case-different-but-equal language tags as the SAME abstract literal term, not two co-denoting ones — so the engine's "extra" accepted pairs are one value read through two spellings, not a semantic overreach. Rule 27 (Soundness banner) is proved against the UNWEAKENED `cond_haskey` (no local weakening needed on the truth side). |
| [axm] | n/a | `xsd_datatype_axioms` | N/A | N/A (axiomatic table, not a rule) | — | dt-type1 instantiated at supported XSD datatypes. |
| [ext] | n/a | `dt_range_intersect` | N/A | UNATTEMPTED | — | Two ranges compose to their intersection (WebOnt-I5.24-002); explicitly NOT a minimality claim. |
| scm-dom1 | `scm_dom1_derives` | `scm_dom2` | ✅ PROVED (commit `276ee77`) | ✅ PROVED (Rule 28) | — | **MISNAMED function**: lifts domain up subClassOf — scm-dom1's work, refuted-by-counterexample against scm-dom2 (whose subPropertyOf logic lives in `subprop_domain_range` below). Third ledger misclassification, caught by counterexample (commit `276ee77`). |
| scm-rng1 | `scm_rng1_derives` | `scm_rng2` | ✅ PROVED (commit `276ee77`) | ✅ PROVED (Rule 29) | — | Same story as scm_dom2 above, mirrored for range. |
| scm-dom2 + scm-rng2 | `scm_dom2_derives` / `scm_rng2_derives` | `subprop_domain_range` | ✅ PROVED (both, one lemma, commit `16caed4`) | ✅ PROVED (Rule 30) | `ig_wf_sp`, `ig.ig_triples == g` | This is the function that actually realises the genuine scm-dom2/scm-rng2 rows (subPropertyOf-lifting) — a THIRD name distinct from the misleadingly-named `scm_dom2`/`scm_rng2` functions above. Two sequential inner folds per outer item (new fold shape for the module). |
| [ext] | n/a | `symmetric_metapredicates` | N/A | ✅ PROVED | none | Group E(a): OWL metapredicates whose semantic condition is argument-symmetric (complementOf, disjointWith, inverseOf, …). |
| [ext] | n/a | `inverse_characteristics` | N/A | UNATTEMPTED | — | Characteristics transfer across `owl:inverseOf`. |
| [ext] | n/a | `equivalent_property_characteristics` | N/A | UNATTEMPTED | — | Characteristics transfer across `equivalentProperty`. |
| [ext] | n/a | `cardinality_to_min_max` | N/A | UNATTEMPTED | — | `owl:cardinality` decomposes into min+max (OWL 2 structural equivalence). |
| cls-maxqc3 + cls-maxqc4 | `cls_maxqc3_derives` / `cls_maxqc4_derives` | `cls_maxqc34` | UNATTEMPTED | UNATTEMPTED | — | One function realises two rows (like `subprop_domain_range`). |
| [ext] | n/a | `fp_pinned_subproperty` | N/A | UNATTEMPTED | — | Banner proof (referenced by the prp-fp closure-identity fix). |
| [ext] | n/a | `singleton_nominal_functionality` | N/A | UNATTEMPTED | — | Banner proof. |
| [ext] | n/a | `hasvalue_card_disjoint` | N/A | UNATTEMPTED | — | Banner proof. |
| [ext] | n/a | `avf_thing_to_range` | N/A | UNATTEMPTED | — | `avf` under `owl:Thing` IS a range fact (WebOnt-I5.24-004). |
| [ext] | n/a | `extensional_symmetry` | N/A | UNATTEMPTED | — | Group E(h): right-to-left half of Table 5.14; banner carries the pinned-extension argument. |
| [axm] | n/a | `xsd_core_datatype_axioms` | N/A | N/A | — | dt-type1 core set. |
| [axm] | n/a | `builtin_vocabulary_axioms` | N/A | N/A | — | Built-in vocabulary axioms. |
| cax-adc | (`cax_adc_clash` — clash form) | `all_disjoint_classes` | UNATTEMPTED | N/A (clash row) | — | Table row is an inconsistency trigger, not a triple-derivation rule. |
| prp-adp | (`prp_adp_clash` — clash form) | `all_disjoint_properties` | UNATTEMPTED | N/A (clash row) | — | Same shape as cax-adc. |
| eq-diff2 / eq-diff3 | (`eq_diff2_clash`/`eq_diff3_clash` — clash form) | `allDifferent_to_differentFrom` | UNATTEMPTED | N/A (premise expansion feeding a clash row) | — | Materialises `owl:AllDifferent` membership lists into pairwise `owl:differentFrom` — the premise infrastructure eq-diff2/eq-diff3's clash check consumes, not the clash itself. |
| [ext] | n/a | `differentFrom_to_allDifferent` | N/A | UNATTEMPTED | — | Converse packaging. |
| [mode] | n/a | `rdf_based_full_meta_axioms_mode` | N/A | UNATTEMPTED | — | RDF-Based Semantics meta-axioms, catalog-gated. |
| [ext] | n/a | `comp_singleton_union` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `comp_min1_restriction` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `comp_oneof_union` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `comp_union_oneof` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `comp_enum_range_value` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `comp_range_avf` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `comp_range_intersection` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `comp_pinned_domain_enum` | N/A | UNATTEMPTED | — | Comprehension layer. |

**Row count**: 84 (34 `[row]`, 42 `[ext]`, 4 `[axm]`, 4 `[mode]`, per
the ledger's own tally — matches the count transcribed independently
above).

## 2. RDFS entailment (RDF 1.1 Semantics § 9) — 13 rows

All thirteen rows have spec predicates
(`RDF.Entailment.RDFS.Spec.fst`, `rdfsN_derives`). **11 of 13** have a
genuine shipping engine rule with BOTH licensing
(`RDF.Entailment.RDFS.Refinement.fst`) and truth
(`RDF.Entailment.RDFS.ModelTheory.fst`, `rdfsN_true`) proved. The
remaining 2 rows (rdfs6, rdfs10) have truth proved at the spec-predicate
level but no sound engine counterpart: the shipping engine only ships
an UNSOUND reflexivity over-approximation for them (finding RS-1, fixed
2026-07-31 by being correctly flagged unsound, not by being replaced).
rdfs12 sits in between: truth is proved for the literal row, but the
shipping engine's `rdfs_rule_container_membership` licenses against
the axiomatic-triple table instead (it is an unconditional axiom
emitter over a finite `rdf:_1..rdf:_5` slice, not a premise-driven rule
— sound, but not a licensing proof of the rdfs12 row itself).

| Row | Spec predicate | Engine function | Licensing | Truth | Notes |
|---|---|---|---|---|---|
| rdfs1 | `rdfs1_derives` | `rdfs_rule_recognized_datatypes` | ✅ PROVED | ✅ PROVED | Added 2026-07-31 closing finding RS-2 (was previously unimplemented). |
| rdfs2 | `rdfs2_derives` | `rdfs_rule_domain` | ✅ PROVED | ✅ PROVED | Interleaved into the OWL-RL fixpoint too (covers prp-dom). |
| rdfs3 | `rdfs3_derives` | `rdfs_rule_range` | ✅ PROVED | ✅ PROVED | Finding RS-3: silently drops the literal/triple-term-object case (needs a literal subject, generalized-RDF delta D5); `rdfs3_derives` carries the same premise, so the refinement is EXACT — the incompleteness is in the term algebra, not the proof. Covers prp-rng in the OWL-RL fixpoint. |
| rdfs4a | `rdfs4a_derives` | `rdfs_rule_resource_subject` | ✅ PROVED | ✅ PROVED | Added 2026-07-31 closing RS-2. |
| rdfs4b | `rdfs4b_derives` | `rdfs_rule_resource_object` | ✅ PROVED | ✅ PROVED | Added 2026-07-31 closing RS-2; RS-3 applies here too (literal-object case). |
| rdfs5 | `rdfs5_derives` (`rdfs5_derives2` two-source form) | `rdfs_rule_subPropertyOf_trans` | ✅ PROVED | ✅ PROVED | Two-source (snapshot vs accumulator) split for fixed-point composition. |
| rdfs6 | `rdfs6_derives` | none (only the unsound `rdfs_reflexivity_axioms` approximation) | N/A — no sound engine rule | ✅ PROVED (spec-predicate level) | RS-1: `rdfs_reflexivity_axioms` emits `P rdfs:subPropertyOf P` for every P typed `owl:ObjectProperty`/`owl:DatatypeProperty` — NOT RDFS-entailed (an RDFS interpretation may read `owl:Class`/`owl:ObjectProperty` as an arbitrary IRI). Machine-checked witness: `owl_reflexivity_axioms_not_rdfs_sound`. |
| rdfs7 | `rdfs7_derives` | `rdfs_rule_subPropertyOf` | ✅ PROVED | ✅ PROVED | Covers prp-spo1 in the OWL-RL fixpoint. |
| rdfs8 | `rdfs8_derives` | `rdfs_rule_class_subclass_resource` | ✅ PROVED | ✅ PROVED | Added 2026-07-31 closing RS-2 (spec comment "NOT IMPLEMENTED" predates this landing — stale at the file's own top-of-file banner, current at the rule definition site). Covers cax-sco in the OWL-RL fixpoint. |
| rdfs9 | `rdfs9_derives` (`rdfs9_derives2` two-source form) | `rdfs_rule_subClassOf` | ✅ PROVED | ✅ PROVED | Two-source split, same shape as rdfs5. |
| rdfs10 | `rdfs10_derives` | none (only the unsound reflexivity approximation) | N/A — no sound engine rule | ✅ PROVED (spec-predicate level) | RS-1, mirrored: `C rdfs:subClassOf C` for every C typed `owl:Class` is not RDFS-entailed either. Covers scm-sco naming in adjacent docs. |
| rdfs11 | `rdfs11_derives` (`rdfs11_derives2`) | `rdfs_rule_subClassOf_trans` | ✅ PROVED | ✅ PROVED | Two-source split. |
| rdfs12 | `rdfs12_derives` | `rdfs_rule_container_membership` | N/A — engine licenses against the axiomatic table, not this row | ✅ PROVED (spec-predicate level) | Shipping rule is an unconditional axiom emitter over `rdf:_1..rdf:_5` (finite slice — incomplete w.r.t. the infinite family, RS-2, never unsound); its own licensing lemma (`rdfs_rule_container_membership_licensed`) is stated against `rdfs_axiomatic \/ rdfs_member_subproperty`, not `rdfs12_derives`. |
| rdfs13 | `rdfs13_derives` | `rdfs_rule_datatype_subclass_literal` | ✅ PROVED | ✅ PROVED | Added 2026-07-31 closing RS-2. |

**Count: 11 of 13 rows PROVED at both licensing and truth** (all
except rdfs6/rdfs10, whose only shipping approximation is unsound, and
rdfs12, whose shipping rule realizes the axiomatic table rather than
the premise-driven row). **13 of 13 have truth proved at the spec-predicate level.**
Composite theorems built on top of the 11: `rdfs_licensed_true` (any
row-licensed triple is true), `rdfs_closure_step_sound` (one closure
step preserves truth), and `rdfs_rule_*_preserves` per-rule bridges
(licensing ∘ truth). The old-2004-syntax variant `rdfs1_2004_derives`
(bnode-substituting form) is UNATTEMPTED/deliberately out of scope —
same fresh-term shape as the OWL-RL IMPOSSIBLE rules above.

## 3. Simple / RDF entailment rungs

| Rung | Theorem | Status | Fragment / hypotheses | Notes |
|---|---|---|---|---|
| Simple entailment (RDF 1.1 Semantics § 5) | `Simple.ModelTheory.interpolation_lemma` | ✅ PROVED — full iff | `graph_tt_free` (RDF 1.2 triple-term-free fragment) | Herbrand construction (`herbrand`). Stronger than what the adoption proposal asked for ("complete simple entailment characterization"). |
| Simple entailment, composed with shipping search | `simple_entails_iff_model_theory` | ✅ PROVED | plus `graph_exact` soundness boundary, SE-1 witness | End-to-end: model theory iff the shipping search's answer. |
| Simple entailment, spec-text instance-subgraph form | (unnamed converse) | PARKED (choice-based image construction not built) | — | One direction only; the interpolation lemma above is the stronger result actually used. |
| Simple entailment, merging lemma | `Simple.ModelTheory` bnode-disjoint union lemmas | ✅ PROVED (7a98202) | bnode-disjoint g1, g2 | Adoption item A5; union satisfaction iff component satisfaction, plus the entailment corollary. |
| Simple entailment, bnode-restriction | `graph_bnodes_complete` | ✅ PROVED (7a98202) | — | Satisfaction depends only on the assignment's restriction to the graph's own bnode labels (Q3's finite-assignment refinement, without changing the total-assignment convention). |
| RDF rung, finite axiomatic-table soundness | `finite_rdf_axioms_sound` + `is_rdf_axiomatic_triple` | ✅ PROVED (7a98202) | soundness direction ONLY | No completeness claim against the infinite `rdf:_n` family, per the proposal's own rule. |
| **rho-df completeness** (RDFS rung) | `RDFS.Completeness.rho_df_closed_iff` / `rho_df_saturation_iff` / `rdfs_closure_rho_df_complete` | ✅ PROVED (e94e7ad) | `rho_df_frag_graph` (literal-free + tt-free objects, IRI objects on subPropertyOf) + `rho_df_closed` / `is_subgraph` / fragment-preservation of the closure result (M1b/M2 discharge) | FINDING C-1: the naive statement vs full RDFS entailment is FALSE — machine-checked reflexivity + universality witnesses (`rho_df_entailment_strictly_stronger`); correct form reduces the interpretation class to the six rho-df conditions. FINDING C-2: shipping twelve-rule closure gets completeness only; the iff needs the six-rule operator (M1b). |
| Simple entailment, parser-boundary label-independence | `Boundary.entails_ntriples_boundary` | ✅ PROVED | — | — |
| RDF entailment (§ 8), rdfD2 | `rdfD2_derives` / `rdfD2_true` / `rdf_property_axiom_closure_licensed` | ✅ PROVED — licensed + true, at rule and closure level | — | — |
| RDF entailment (§ 8), rdfD1 | `rdfD1_derives` | UNATTEMPTED — deliberately unimplemented | mints a fresh blank node (Skolem-family row) | Same fresh-term shape as the OWL-RL IMPOSSIBLE rules; excluded from `rdf_closed` on purpose, not by oversight. |
| RDF entailment, completeness | — | N/A — no completeness theorem exists at this rung | — | Axiomatic tables + `rdf:_n` schema transcribed; no claim of completeness against the infinite family. |
| RDFS entailment, rho-df completeness (fragment iff, abstract saturation) | `RDF.Entailment.RDFS.Completeness.rho_df_saturation_iff` | ✅ PROVED (G3 M1, landed) — `rho_df_entails g e <==> simple_entailment_spec c e` for any `c` extensive/sound/rho-df-closed over `g` | `rho_df_frag_graph c`, `graph_tt_free e` | Herbrand technique from the Simple rung, reused verbatim. Supersedes the "UNATTEMPTED" row this replaces (#347/#348 index-completeness landed 90e2801). Findings C-1 (the coverage doc's literal gap-1 statement — `rdfs_entails d_minimal g e <==>` closure-then-simple-entailment — is FALSE; machine-checked witness `rho_df_entailment_strictly_stronger`) and C-2 (the shipping 12-rule `rdfs_closure` cannot instantiate `c` in the SOUNDNESS direction) are recorded in the module banner. |
| RDFS entailment, rho-df closure operator (G3 M1b) | `RDF.Entailment.RDFS.RhoDFClosure.rho_df_closure` (6 rows: rdfs2/3/5/7/9/11, reusing the shipping `rdfs_rule_*` functions, fuel/length-test loop) | see the 5 theorems below | — | Answers finding C-2: the six-rule operator `rdfs_closure` does not expose. |
| — extensivity | `rho_df_closure_extensive` | ✅ PROVED — `is_subgraph g (rho_df_closure g fuel)` | `rho_df_chain_canonical g` (`no_dup_keys` at every fuel-visited graph) | Composes the six per-row extensivity lemmas `RDF.Entailment.RDFS.FixedPoint` already proves, reused (not re-derived). |
| — soundness | `rho_df_closure_sound` | ✅ PROVED — `rho_df_entails g (rho_df_closure g fuel)` | `rho_df_chain_wf g` (`ig_wf_sp` at every fuel-visited graph) | Condition-usage audit (the task's explicit ask): each of the six `_true` lemmas (`ModelTheory.fst`) needs EXACTLY one `rho_df_conditions` conjunct and no other — no finding, the hypothesis-weakening replay the brief predicted. |
| — closedness | `rho_df_closure_closed` | ✅ PROVED (conditional) — at a fuel witness where the length test passes, `rho_df_closed (rho_df_closure g fuel)` | `rho_df_frag_graph c`, `ig_wf_sp (build_indexed c)`, `rho_df_subclass_subjects_iri c`, `no_dup_keys (rho_df_closure_step_pre_dedup c)`, `no_repeats_p c`, `no_repeats_p (rho_df_closure_step c)`, `graph_len (rho_df_closure_step c) = graph_len c` | `rdfs7_reaches_fact c` DROPPED 2026-08-06 (statement strengthening) — discharged by `rdfs_rule_subPropertyOf_reaches`, see the RESOLVED row below. One of the seven remaining hypotheses is still a FINDING carried as an explicit fact rather than derived (F-2); the other six are the "same shape as `lemma_len_eq_saturated`" hypotheses the brief authorized carrying. |
| — fragment preservation | (no unconditional lemma — see finding F-1) | ❌ REFUTED as a flat implication | — | `rho_df_frag_graph g ==> rho_df_frag_graph (rho_df_closure g fuel)` is FALSE. Machine-checked witness `rho_df_frag_preservation_fails`: `g = [P rdfs:subPropertyOf rdfs:subPropertyOf; a P _:b1]` satisfies the fragment predicate; one rdfs7 step derives `a rdfs:subPropertyOf _:b1`, violating F2 (subPropertyOf-object-must-be-IRI). Carried as an explicit hypothesis into the payoff theorem instead. |
| — the payoff | `rho_df_closure_decides` | ✅ PROVED (conditional) — `rho_df_entails g e <==> simple_entailment_spec (rho_df_closure g fuel) e` | `rho_df_chain_canonical g`, `rho_df_chain_wf g`, `rho_df_frag_graph c`, `ig_wf_sp (build_indexed c)`, `rho_df_subclass_subjects_iri c`, `no_dup_keys (rho_df_closure_step_pre_dedup c)`, `no_repeats_p c`, `no_repeats_p (rho_df_closure_step c)`, `graph_len (rho_df_closure_step c) = graph_len c`, `graph_tt_free e` (c := `rho_df_closure g fuel`) | `rdfs7_reaches_fact c` DROPPED 2026-08-06, same reason as closedness above (feeds `rho_df_closure_closed`). Instantiates `rho_df_saturation_iff` with the four theorems above. |
| — FINDING F-2 (rdfs9/subClassOf completeness gap) | `rdfs_rule_subClassOf_reaches_iri` (IRI-class case only) | 🟡 PARTIAL — proved for `S_IRI`-typed classes only | `rho_df_subclass_subjects_iri c` closes the gap for `rho_df_closure_closed`/`_decides` | The shipping `rdfs_rule_subClassOf` only chases `T_IRI`-typed classes (`match t.o with T_IRI class_iri -> ... \| _ -> acc`); `rdfs9_derives`'s declarative `xs : subject` is unrestricted (also accepts `S_BNode`). Unlike RS-3 (rdfs3), the two are NOT in refinement here — a genuine completeness gap, not a proof-engineering one. Still open — untouched by the rdfs7 landing below. |
| — RESOLVED 2026-08-06 (rdfs7/subPropertyOf reaches) | `rdfs_rule_subPropertyOf_reaches` / `rdfs_rule_subPropertyOf_reaches2` | ✅ PROVED, unconditional — `rho_df_frag_graph g /\ ig_wf_sp (build_indexed g) /\ rdfs7_derives g t ==> memP t (rdfs_rule_subPropertyOf g (build_indexed g))` | — | Was PARKED after 3 proof-side attempts (`rdfs7_reaches_fact`, a carried hypothesis, not a proved lemma — five attempts total counting the two recorded here). Fix: the engine-side lambda-lift the proof side never tried — `RDFS.Closure.fsti` now names `rdfs7_emit (ig) (q) (acc2) (tt) = emit_once_term ig acc2 tt.s q tt.o` and `rdfs_rule_subPropertyOf`'s inner fold calls it directly (behavior-identical), giving the engine step and this proof the SAME first-order symbol instead of two independently-elaborated closures (the closure-identity law, `skills/proof-factory/SKILL.md`). First-attempt pass once the engine carried the named symbol. Ripple: `rdfs_rule_subPropertyOf_licensed` (`RDF.Entailment.RDFS.Refinement.fst`) and `lemma_rdfs_rule_subPropertyOf_extensive` (`RDF.Entailment.RDFS.FixedPoint.fst`) re-spelled their local `outer_step`/`inner_step` to the same named helper (mechanical, both re-verify). `rho_df_closure_closed`/`_decides` and the F-1 witness call site (`lemma_f1_bad_triple_derived`/`rho_df_frag_preservation_fails`) all had the `rdfs7_reaches_fact` hypothesis DROPPED, not just satisfied — see the two rows above. |
| RDFS entailment, unrestricted completeness | — | ❌ REFUTED (not merely unproven) | axiomatic tables unseeded | Stated explicitly in the coverage survey: this is FALSE, not an open question. |

## 4. Index / infrastructure lemmas

These are not W3C rows; they are the machinery the two families above
lean on to make `ig_wf_*` hypotheses real rather than assumed.

| Lemma family | Module | Status | Notes |
|---|---|---|---|
| Index well-formedness (5 buckets) | `RDF.Indexed.KeyInjectivity.fst` | ✅ PROVED — `ig_wf_sp`, `ig_wf_subj`, `ig_wf_obj`, `ig_wf_po`, `ig_wf_pred` (#338, closed 2026-08-04) | `sp_key`/`po_key`/subject-key injectivity, one-sided, on U+001F-free keys. |
| Bucket lookup completeness (converse direction) | `RDF.Indexed.Completeness.fst` | ✅ PROVED (90e2801) | Generic `lemma_build_bucket_complete` for any key_of + pred-bucket instantiation, no side condition; first consumer of the #347 StringOrder axioms. Its generic sortWith all-pairs-sortedness machinery also unblocked Gap B below. |
| Dedup-key injectivity (literal arm, #348 fix) | `RDF.Indexed.KeyInjectivity.fst` | ✅ PROVED (e137b5d) | `term_to_key_total`/`triple_to_key` full injectivity across all four term shapes under separator-free side conditions; `lemma_graph_full_sep_free_no_dup_keys`. Engine fix: literal keys now unit_sep-joined (extraction re-gate pending). |
| Closure-step no-repeats (Gap B) | `RDF.Entailment.RDFS.FixedPoint.fst` | ✅ PROVED (e137b5d) — UNCONDITIONAL | `lemma_rdfs_closure_step_no_repeats`; the noeq-vs-`sortWith_sorted` blocker fell to the Completeness module's eqtype-free sortedness proof. `lemma_len_eq_saturated_gapB` left only Gap A — CLOSED same day: `lemma_len_eq_saturated_sep_free` (Gap A landing) makes the termination test faithful for separator-free, tt-object-free, repeat-free inputs. NO open gaps on the termination path. |
| Row-level separator-freedom | `RDF.Entailment.RDFS.SepFree.fst` | ✅ PROVED — per-row conclusion cleanliness for rdfD2 and rdfs1-13 (checked directly: `lemma_rdfsN_sep_free` per row) | Feeds `ChainWf`. |
| Closure well-formedness chain | `RDF.Entailment.RDFS.ChainWf.fst` | ✅ PROVED — `graph_sep_free g ==> closure_chain_wf g`, empty + non-empty instances machine-checked | Makes `rdfs_closure_entails` apply to concrete graphs (hypothesis discharged non-vacuously). |
| Closure step extensivity + fixed-point | `RDF.Entailment.RDFS.FixedPoint.fst` | 🟡 LANDED WITH ADJUDICATION (commit `1aa4e71`) | Length-test fixed-point theorem holds under two explicit hypotheses (`no_dup_keys` on the pre-dedup intermediate graph), not unconditionally — the unconditional form is FALSE. Third finding from this landing: `term_to_key_total` literal keys use plain `"^^"` not `unit_sep`, a wider dedup-collision surface than #338 described (#348). |
| String ordering axioms | `RDF.Indexed.StringOrder.fsti` | ⚠️ 3 TRUSTED AXIOMS (#347) | See Trust surface. |

## 5. SPARQL algebra refinement (the query rung, G3 M3)

The layer that will connect closure results to query answers. Layer 2
landed 2026-08-06 (`SPARQL11.Algebra.BGPRefinement.fst`); layer 3
(the algebra lift + composed regime theorem) is queued.

| Theorem | Status | Fragment / hypotheses | Notes |
|---|---|---|---|
| `theorem_eval_bgp_subgraph` (shipping statement: every eval_bgp solution subset-matches) | ✅ PROVED | `bgp_frag` (tt-free, exact literals, not fulltext), `graph_frag` | Soundness direction of layer 2. |
| `theorem_eval_bgp_instantiates_into_graph` (`mu(BGP) ⊆ g` form) | ✅ PROVED | same | The form layer 3 consumes at `rdfs_closure g`. |
| `lemma_ig_search_sound` + 8 supporting lemmas (single-tp soundness, planner cover, fuel unfolds, extension-closed tp-match) | ✅ PROVED | per-lemma | Fills the gap `SPARQL11.Algebra.Refinement`'s banner recorded (index-probe soundness). |
| BGP completeness (every subset-matcher is found) | BLOCKED — named | needs bucket completeness for subj/obj/sp/po/so (only pred is proved, 90e2801); expected FALSE outside `term_exact` (probe accepts on `rdf_term_eq`, buckets key byte-exact) | Finding BR-4. |
| Domain clause `dom(mu) = var(BGP)` | UNATTEMPTED | — | Bookkeeping, no graph content; separate landing. |

Findings BR-1..BR-3 (module banner, machine-relevant divergences):
the fulltext triple-pattern path is NOT subset-matching (binds
subject only, applies a limit — excluded by hypothesis, not hidden);
query blank nodes match as CONSTANTS (identity renaming — exact for
bnode-free BGPs, the regime suite's class); statements are
set-membership, not multiset (§18.3.1 cardinality needs a
no-duplicates hypothesis, deferred to layer 3's inputs).

`SPARQL11.Algebra.Spec` / `SPARQL11.Algebra.Refinement` (landed
2026-08-03, pre-registry) are now in the verify-rdf-mt roster with
this layer; their per-lemma rows are a registry backfill task.

## Trust surface

What this registry's PROVED cells rest on, beyond F\*/Z3 itself:

- **`RDF.Indexed.StringOrder.fsti` (#347) — 3 axioms.** `FStar.String.compare`
  ships in ulib as an unspecified native primitive (extracts to OCaml
  `BatString.compare`, genuine byte-lexicographic order). Three facts
  are assumed here rather than proved: `compare a b = 0 <==> a == b`,
  antisymmetry, transitivity. One module, one banner, DO-NOT-WIDEN —
  the same shape as this file's own registry discipline. Anything
  derivable from these three (order totality, `<` irreflexivity,
  sortedness transfer) must be proved in a consumer module, not added
  here.
- **`assume val` realisations** — approximately 146 declarations
  across the tree (a direct count against the current tree; the
  project's own current-state doc records 141 from an earlier count,
  and this task's brief cited ~148 — treat all three as approximate
  and re-count before quoting a precise figure). The large majority
  are the COTTAS/HDT storage I/O layer (pure I/O under iron rule
  #11), not semantic logic. Full audited breakdown:
  [`designissues/fstar-ocaml-boundary-audit.md`](designissues/fstar-ocaml-boundary-audit.md).
- **Extraction step.** Every proof in this registry is a proof about
  the F\* SOURCE. The binding to the running binary goes through
  `fstar.exe --codegen OCaml` extraction, not through re-verifying the
  extracted OCaml. Mitigated by the W3C test suites (below) and the
  hash-witness round-trip pattern for byte-layout claims
  ([`designissues/2026-05-07-io-verification-and-third-party.md`](designissues/2026-05-07-io-verification-and-third-party.md)).
- **`make verify-rdf-mt`** — the model-theoretic layer's own gate, 20
  modules: `RDF.Entailment.Simple.Spec`, `RDF.Entailment.Simple`,
  `RDF.Entailment.Simple.ModelTheory`, `RDF.Entailment.Simple.Refinement`,
  `RDF.Entailment.Simple.Boundary`, `RDF.Entailment.RDF.Spec`,
  `RDF.Entailment.RDFS.Spec`, `RDF.Entailment.RDFS.ModelTheory`,
  `RDF.Entailment.RDFS.Refinement`, `RDF.Entailment.RDFS.SepFree`,
  `RDF.Entailment.RDFS.ChainWf`, `RDF.Entailment.RDFS.FixedPoint`,
  `RDF.Entailment.Regime`, `RDF.Semantics.HypothesisWitness`,
  `RDF.Indexed.KeyInjectivity`, `RDF.Indexed.Completeness`,
  `OWL.Semantics`, `OWL.Semantics.MemLemmas`, `OWL.Semantics.Soundness`,
  `OWL.RL.Refinement` (`formal/fstar/Makefile`, `RDF_MT_MODULES`). Run
  it by name to gate this registry's claims without re-verifying the
  whole corpus.
- **Test-suite gates** — the W3C rdf-mt, OWL 2, and RDFS conformance
  suites exercise the EXTRACTED, RUNNING engine and are the
  independent check that this registry's proofs correspond to
  observed behavior, not merely to what the F\* source says. See
  [`../skills/test-suites/SKILL.md`](../skills/test-suites/SKILL.md)
  for current pass/fail counts; this registry does not restate them
  because they move independently of proof landings.

## Calibrated claims (adoption item A4)

State this program as: "proved sound with respect to an independent
F\* formalization of the W3C RDF/RDFS/OWL semantics, under the stated
fragment restrictions and the trust surface above" — never as "a
complete formally verified implementation of RDF semantics." The
qualifier in CLAUDE.md iron rule #11 (parser and algebra spec verified
in F\*; on-disk backend has unverified OCaml-side optimization layers)
applies here unchanged.
