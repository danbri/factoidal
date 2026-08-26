# Theorem registry

Deliverable 1 of goal G1 in
[`designissues/2026-08-05-semantics-proposal-adoption.md`](designissues/2026-08-05-semantics-proposal-adoption.md).
Deliverable 2 (issue [#403](https://github.com/danbri/factoidal/issues/403), the curated review kernel — the minimal
subset a W3C-domain expert can read end to end, with the guarantee
nothing outside it overrides what it states) is
[`review-kernel.md`](review-kernel.md).
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

**Date**: 2026-08-06 (status cells for cls-hv1, cls-hv2, cls-avf and
prp-spo2 n=2 refreshed twice by the wave 3 relift and wave 4
truth landings; cax-adc, prp-adp, eq-diff2, eq-diff3, cls-maxqc1
clash rows adjudicated and cax-adc's detection-soundness lemma
landed by the CLASH-ROW landing). **Tree state**: commit `f70ed89`
plus the CLASH-ROW working tree (uncommitted at write time; the
orchestrator gates — `OWL.Closure.fsti` is extraction-affecting).
The original survey was read-only at `27c23d5`; since then the
relift and CLASH-ROW landings edited `OWL.Closure.fsti`
(behavior-identical lambda/boolean lifting only — PROOF-FRIENDLY
GUARD RULE banners), and wave 4 added three semantic conditions +
Rules 33-36 with no engine edits.

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

**Licensing count: 26 of 34 `[row]` table-row obligations proved**
(2026-08-06). The figure was 23 at commit `27c23d5`; wave 3 added
cls-hv2 (commit `06f3f20`, against the weakened row
`cls_hv2_derives_approx`), then cls-hv1 and cls-avf in the relift
landing. **prp-spo2 is NOT counted**: its row is shared between
`property_chain_2` and `property_chain_n`, and only the n=2 half is
proved — the row becomes coverable when `property_chain_n` follows.
The rest of this paragraph derives the 23 baseline, using the
ledger's own accounting (`subprop_domain_range` and
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

**CLASH-ROW adjudication landed 2026-08-06** (does not change the
counts above — clash rows are `[row]`-classed but their proof kind is
DETECTION SOUNDNESS, not the derives-style "every emission is
licensed" statement the 26-of-34 count above measures). The registry
flagged five clash-predicate rows (`cax-adc`, `prp-adp`, `eq-diff2`,
`eq-diff3`, `cls-maxqc1`) as "truth column N/A pending domain review"
since creation. Adjudicated: the engine's only consumer of any
`*_clash` predicate is `OWL.Closure.is_inconsistent`, called on the RL
closure fixpoint (`bin/owl-runner/owl_runner.ml`'s
`capped_is_inconsistent`, which is how every ConsistencyTest /
InconsistencyTest is actually scored) — so "the engine reports a
clash" concretely means one of `is_inconsistent`'s internal boolean
checks evaluates `true`, and the natural licensing statement is
DETECTION SOUNDNESS (`that boolean == true ==> the clash predicate(s)
it corresponds to hold of g`); the converse (detection COMPLETENESS)
is a separate, per-row-noted statement. Two checks (`is_inconsistent`
3 and 6, now named `owl_has_disjoint_class_clash` /
`owl_has_pdw_direct_clash` — hoisted out of anonymous `let`-bindings,
behavior-identical, `OWL.Closure.fsti`) turn out to be shared with an
EARLIER table's asserted-form sibling row (cax-dw, prp-pdw
respectively) — the boolean cannot tell whether the clash-causing
triple was asserted directly or materialised from an
AllDisjointClasses/AllDisjointProperties list, so the only TRUE
statement is the row UNION, not the single [row] alone. cax-adc's
union statement is PROVED (`theorem_cax_adc_cax_dw_detection_sound`,
`OWL.RL.Refinement.fst` section 30); prp-adp and eq-diff2/eq-diff3 are
PARKED with a precise obstruction recorded per row (a literal
value-vs-syntactic-equality gap, and a sameAs-direction/symmetry gap,
respectively); cls-maxqc1 is a confirmed engine GAP — no detector
exists for the row at all. Full reasoning in each row's Notes cell
below.

**Truth count: 33 of ~36 attempted rules proved** (wave 4, Rules
33-36, landed 2026-08-06: cls-hv1, cls-hv2, cls-avf, prp-spo2 n=2)
(`OWL.Semantics.Soundness.fst` "Rules 1-36" banner numbering; two
banner slots, 2b and 16→17, are a sub-rule and a superseded first
attempt, so 31 banner numbers cover 30 distinct engine rules); **3 of
those 30 are IMPOSSIBLE** with recorded evidence (fresh-bnode-minting
rules); the remaining ~54 of 84 ledger entries are UNATTEMPTED for
truth (no `_sound` lemma exists yet).

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
G3 M4 wave 4 (2026-08-06) landed Rules 33-36 — the truth-preservation
proofs for the four rules whose LICENSING landed earlier the same day
in the wave 3 relift (cls-hv1, cls-hv2, cls-avf, prp-spo2 n=2), all
four PROVED first attempt against the wave 3 relift's named
top-level engine helpers. Three new semantic conditions landed in
`OWL.Semantics.fst`: `cond_hasvalue` (Table 8 HasValue, stated as the
full iff — cls-hv1 reads the forward direction, cls-hv2 the backward
one, the same two-rule iff split `cond_inverse_of` already serves for
prp-inv1/prp-inv2), `cond_allvaluesfrom` (Table 8 AllValuesFrom, one
direction — the table's own condition is already one-directional, no
converse row exists the way cls-hv2 converses cls-hv1), and
`cond_chain2_compose` (Table 5's general 2-hop
SubObjectPropertyOf(ObjectPropertyChain(P1,P2),Q) composition
condition, distinct from Rule 11's `cond_chain2_transitive`, which
specialises the SAME table row to the self-composition case
Q=P1=P2=P). cls-hv1/cls-avf/prp-spo2 followed the DEPTH COROLLARY
(proof-factory skill): one standalone witness-assembly lemma per fold
level, referencing the wave 3 relift's named engine helpers directly
(`owl_cls_hv1_outer`/`_mid`/`_emit`, `owl_cls_avf1_outer`/`_prop`/
`_member`/`_emit`, `owl_chain2_outer`/`_mid`/`_emit`), no closure-
identity risk at any level. cls-hv2's engine function was NOT
lambda-lifted in the relift (its own licensing proof already
discharges with anonymous local lambdas), so its truth proof mirrors
that proof's local-verbatim-lambda skeleton instead, with only the
deepest semantic-assembly step pulled into a standalone lemma. cls-hv2
proves UNWEAKENED (no `_approx` predicate needed for truth, unlike its
licensing statement): the same `cond_literal_term_eq_respecting` +
`lemma_rdf_term_eq_denot` bridge that closed prp-key's engine-vs-row
gap (wave 1) closes cls-hv2's `rdf_term_eq`-vs-`==` gap here too.
prp-spo2 (n=2) reuses `decode_chain_pair_sound` (Rule 11) VERBATIM for
the list-decode half, per the BRIDGE-LEMMA COROLLARY, rather than
re-deriving a new list-walk bridge. `prp-spo2 (n≥3)` (`property_chain_
n`) remains UNATTEMPTED for both licensing and truth — out of scope
for this landing.

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
| cls-hv1 | `cls_hv1_derives` | `cls_hv1` | ✅ PROVED (2026-08-06, wave 3 relift) | ✅ PROVED (2026-08-06, G3 M4 wave 4) | `ig_wf_sp`, `ig_wf_po`, `ig.ig_triples == g`; needed named top-level helpers (`owl_cls_hv1_outer`/`_mid`/`_emit`); truth adds `cond_hasvalue` (forward direction) | First THREE-level fold rule proved. Four earlier attempts failed Error-19 on the `tu` eliminate with the engine's three lambdas still anonymous; the closure-identity law is what bit. Fix = lambda-lift ALL three engine levels + package each proof level as a standalone lemma taking the level above's witnesses as arguments (`lemma_cls_hv1_row_intro`), so the row's four-way existential is assembled in one flat context. Section 26. Truth: Rule 33 (Soundness banner); same named-helper reuse + one standalone witness lemma per level (`lemma_cls_hv1_witness_holds`) as the licensing sibling, first-attempt green. |
| cls-hv2 | `cls_hv2_derives` | `cls_hv2` | ✅ PROVED against `cls_hv2_derives_approx` (commit `06f3f20`) | ✅ PROVED, UNWEAKENED (2026-08-06, G3 M4 wave 4) | `ig_wf_sp`, `ig_wf_po`, `ig_wf_pred`, `ig.ig_triples == g`; truth adds `cond_hasvalue` (backward direction) + `cond_literal_term_eq_respecting` | WEAKENED ROW (same convention as prp-key): the engine's `find_subjects_indexed ig p v` falls back to an `rdf_term_eq` filter when `v` is a literal, which is coarser than the row's `==` (lang-tag case folding, XMLLiteral c14n). Machine-checked witness in section 27; row transcription itself is faithful, this is a confirmed engine-vs-row narrowing, not a ledger drift. Truth: Rule 34 (Soundness banner) closes the gap the SAME way prp-key's truth proof did — `cond_literal_term_eq_respecting` + `lemma_rdf_term_eq_denot` show rdf_term_eq-equal terms co-denote, so the proof goes through UNWEAKENED even though the licensing statement stays weakened. Engine not lambda-lifted (only cls-hv1/cls-avf/prp-spo2 were); truth proof mirrors the licensing proof's local-verbatim-lambda skeleton, with the deepest semantic-assembly step pulled into its own lemma (`lemma_cls_hv2_witness_holds`) per the depth corollary. |
| [ext] | n/a | `cls_svf2_qualified` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `cls_minc_qual1` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `cls_hasself1` | N/A | UNATTEMPTED | — | ObjectHasSelf semantics (Table 5.x); `hasSelf` has no RL table row. |
| [ext] | n/a | `cls_hasself2_synth` | N/A | ❌ IMPOSSIBLE (mints a fresh bnode; Rule 15 in Soundness banner) | — | Same STOP shape as `transitive_to_chain`/`cls_svf_thing_materialize`: a comprehension-witness existence condition the W3C tables do not assert, under the fixed-assignment shape. |
| [ext] | n/a | `cls_svf_thing_materialize` | N/A | ❌ IMPOSSIBLE (mints a fresh bnode; Rule 14) | — | Mints `canonical_svf_thing_restriction_bnode`; no premise in g asserts that resource already exists. Closing it needs a model-EXTENSION lemma (Henkin/Skolem-style), a different lemma shape than Rules 1-11/13 use. |
| [ext] | n/a | `cls_svf_thing_witness` | N/A | UNATTEMPTED | — | Comprehension layer. |
| [ext] | n/a | `cax_dw_to_differentFrom` | N/A | UNATTEMPTED | — | Disjoint classes force `differentFrom` on their members. |
| cls-maxqc1 (clash) | `cls_maxqc1_clash` | **NONE** (no engine detector) | GAP — no detection event exists to license | N/A (clash/inconsistency row, not derivation) | — | CLASH-ROW ADJUDICATION (2026-08-06): grepping `cls_maxqc1_clash` outside `OWL.RL.Spec.fst` finds nothing — no `is_inconsistent` arm, no other engine function, checks the "`?x owl:maxQualifiedCardinality 0 ...` plus a witness satisfying the forbidden class" pattern. `OWL.Closure.owl_rule_cls_maxqc1` is a SAME-NAMED but UNRELATED rule: per its own header (OWL.Closure.fsti ~2011-2106) it materialises `owl:maxQualifiedCardinality "1"` canonicals for parent7/parent8 SPARQL-entailment query answering, not a "0"-cardinality clash check. This is a genuine engine GAP against the row, not a proof-scoping decision — not attempted, since there is no boolean to state a lemma about. Needs a NEW `is_inconsistent` arm before a licensing lemma is meaningful. |
| [ext] | n/a | `cls_exactqc1` | N/A | UNATTEMPTED | — | Exact qualified cardinality decomposes into min+max; no RL row of its own. |
| cls-maxc2 | `cls_maxc2_derives` | `cls_maxc2` | UNATTEMPTED | UNATTEMPTED | — | — |
| [ext] | n/a | `cls_maxqc_comp` | N/A | UNATTEMPTED | — | The [#236](https://github.com/danbri/factoidal/issues/236) anchor machinery. **Known sound-but-narrow** (see CLAUDE.md "Known sound-but-narrow rewrites"): drops vacuous-truth individuals and OWL-Full punned class-individuals; the internal-variable LEAK the 2026-07-09 strict runner found is FIXED (task #100, `strip_rewrite_internal_vars`). |
| cls-avf | `cls_avf_derives` | `cls_avf1` | ✅ PROVED (2026-08-06, wave 3 relift) | ✅ PROVED (2026-08-06, G3 M4 wave 4) | `ig_wf_sp`, `ig_wf_po`, `ig.ig_triples == g`; needed named top-level helpers (`owl_cls_avf1_outer`/`_prop`/`_member`/`_emit`); truth adds `cond_allvaluesfrom` | The program's deepest rule — FOUR fold levels. Same two-part treatment as cls-hv1: lambda-lift every engine level, then one standalone lemma per proof level with the level above's witnesses as arguments (`lemma_cls_avf_row_intro` assembles the six-way existential flat). Section 29. Truth: Rule 35 (Soundness banner); `lemma_cls_avf_witness_holds` assembles the row's six-way existential flat, reusing `lemma_find_subjects_indexed_wf_subj` a second time in the same proof; first-attempt green. |
| [ext] | n/a | `reflexive_property` | N/A | UNATTEMPTED | — | ReflexiveProperty semantics; RL profile has no prp-rfl row. |
| [ext] | n/a | `scm_cls_restriction` | N/A | ✅ PROVED | none, single-fold, no fresh bnodes | `owl:Restriction rdfs:subClassOf owl:Class` (Table 5, Axiomatic Triples) read through the RDFS class-extension condition. |
| prp-spo2 (n=2) | `prp_spo2_derives` | `property_chain_2` | ✅ PROVED (2026-08-06, wave 3 relift) | ✅ PROVED (2026-08-06, G3 M4 wave 4) | `ig_wf_sp`, `ig.ig_triples == g`; needed named top-level helpers (`owl_chain2_outer`/`_mid`/`_emit`); truth adds `cond_chain2_compose` | Splits one row across two engine functions by chain arity. The list bridge `lemma_decode_chain_pair_licensed` is the syntactic twin of `decode_chain_pair_sound`, rebuilt in section 18's LIST-WALK spelling (served-object equation → bucket `memP` → `ig_wf_sp`-pinned triple → record-literal `memP _ g`); the parked attempt collapsed those four steps into one assert and Z3 could not e-match `ig_wf_sp` for two buckets at one node. Section 28. Truth: Rule 36 (Soundness banner); reuses `decode_chain_pair_sound` (Rule 11) VERBATIM for the list-decode half per the bridge-lemma corollary, and `cond_chain2_compose` (the GENERAL 2-hop composition condition, distinct from Rule 11's self-composition-only `cond_chain2_transitive`) for the semantic half; first-attempt green. |
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
| prp-key | `prp_key_derives` (row) / `prp_key_derives_approx` (proved against) | `prp_key` | ✅ PROVED, **WEAKENED ROW** (commit `c600646`) | ✅ PROVED, **UNWEAKENED** | `ig_wf_sp`, `ig.ig_triples == g`, `cond_haskey`, `cond_sameas_identity`, `cond_literal_term_eq_respecting` | Engine's `agree_on_property` uses `rdf_term_eq` (RDF-1.1 value equality — case-insensitive lang tags, XMLLiteral c14n, [#337](https://github.com/danbri/factoidal/issues/337)) where the row's `shares_key_values` uses plain `==`. Machine-checked counterexample (`"Alice"@en` vs `"Alice"@EN`) shows the engine accepts strictly MORE value pairs as "shared" than the literal row licenses — an OVER-approximation on the value-sharing axis (opposite direction from the cls-int/scm-uni narrowing above). `owl_rule_prp_key_licensed` is proved against the local weakening, not `prp_key_derives` itself. WEAKENED-ROW CONFIRMATION, not a ledger drift — the row transcription is faithful to Table 4. **Truth closes the gap the licensing weakening left open** (G3 M4 wave 1, 2026-08-06): `cond_literal_term_eq_respecting` + `lemma_rdf_term_eq_denot` (`OWL.Semantics.fst`) establish that `rdf_term_eq`-equal literals denote the SAME domain element under any genuine interpretation — RDF 1.1 Concepts §3.3 already treats case-different-but-equal language tags as the SAME abstract literal term, not two co-denoting ones — so the engine's "extra" accepted pairs are one value read through two spellings, not a semantic overreach. Rule 27 (Soundness banner) is proved against the UNWEAKENED `cond_haskey` (no local weakening needed on the truth side). |
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
| cax-adc | `cax_adc_clash` (union target: `table6_clashes` = `cax_dw_clash \/ cax_adc_clash`) | `all_disjoint_classes` (premise expansion) + `is_inconsistent` check 3, hoisted as `owl_has_disjoint_class_clash` | ✅ PROVED — detection-soundness against `table6_clashes`, **not** `cax_adc_clash` alone (`theorem_cax_adc_cax_dw_detection_sound`, `OWL.RL.Refinement.fst` section 30) | N/A (clash row) | `rdf_type_objects_resource g` (rdf:type objects are IRI/bnode, never literal — see banner) | CLASH-ROW ADJUDICATION (2026-08-06): the engine detects this row in TWO STAGES — `owl_rule_all_disjoint_classes` materialises pairwise `owl:disjointWith` from an `owl:AllDisjointClasses` membership list (premise infra, not itself a clash check), then `is_inconsistent`'s check 3 (now the named top-level `owl_has_disjoint_class_clash`, hoisted out of the anonymous `let`, behavior-identical) looks for two `rdf:type` triples on one subject whose objects are `owl:disjointWith`. That boolean CANNOT tell whether the `disjointWith` triple was asserted directly (cax-dw) or materialised from a list (cax-adc) — a graph with only an asserted cax-dw pair and no AllDisjointClasses node also flips it — so the only TRUE statement it licenses is the row UNION `table6_clashes`, proved here. Completeness (the converse: `table6_clashes g ==> owl_has_disjoint_class_clash g == true`) is PLAUSIBLE for the cax-dw disjunct (single step) but ENGINE-NARROWED for cax-adc: `owl_rule_all_disjoint_classes` uses `decode_chain_list`, an IRI-only `rdf:first`/`rdf:rest` decoder that returns `None` (no-op) on a member list containing a bnode class expression — the same narrowing already documented for `owl_rule_property_chain_n`/prp-key's list machinery — so completeness is NOT claimed for AllDisjointClasses lists with non-IRI members. |
| prp-adp | `prp_adp_clash` (union target: `prp_pdw_clash \/ prp_adp_clash`, both disjuncts of `table4_clashes_complete`) | `all_disjoint_properties` (premise expansion) + `is_inconsistent` check 6, hoisted as `owl_has_pdw_direct_clash` | PARKED — detection-soundness attempted, two-attempt-stop; see Notes | N/A (clash row) | — | CLASH-ROW ADJUDICATION (2026-08-06): SAME shape as cax-adc — `owl_rule_all_disjoint_properties` materialises pairwise `owl:propertyDisjointWith`, then `is_inconsistent` check 6 (hoisted as `owl_has_pdw_direct_clash`/`owl_is_pdw_pair`, `OWL.Closure.fsti`, behavior-identical) looks for two triples sharing subject AND object through a disjoint property pair — cannot attribute to prp-pdw (asserted) vs prp-adp (materialised), so the provable statement is the row union, same reasoning as cax-adc. PARKED, not proved: unlike cax-adc's `t1.o`/`t2.o` (rdf:type objects, provably IRI/bnode via `rdf_type_objects_resource`), check 6's shared object `t1.o == t2.o` (`rdf_term_eq t1.o t2.o`, required TRUE by the check) ranges over ARBITRARY property values, which legitimately include literals in real OWL RL data (`New-Feature-DisjointDataProperties-*`). `rdf_term_eq` on two literals is RDF-1.1 VALUE equality (case-insensitive lang tag, XMLLiteral c14n, [#337](https://github.com/danbri/factoidal/issues/337)) while `prp_pdw_clash`/`prp_adp_clash` need SYNTACTIC `==`; a graph with `t1.o = "V"@EN`, `t2.o = "V"@en` flips the check without giving a `==`-exact witness. Closing this needs either (a) a graph-level "literals `rdf_term_eq`-related implies `==`-equal" hypothesis (true for realistic non-adversarial data, mirrors prp-key's `cond_literal_term_eq_respecting` weakening pattern already accepted in this ledger), or (b) restating literal-value-aware `prp_pdw_clash`/`prp_adp_clash` variants in `OWL.RL.Spec.fst` using `rdf_term_eq`/`literal_value_eq` instead of `==` (the cls-hv2/prp-key WEAKENED-ROW precedent). Recipe otherwise identical to cax-adc's proved lemma; the hoisted `owl_has_pdw_direct_clash`/`owl_is_pdw_pair` are ready for whichever fix lands. Completeness note: same ENGINE-NARROWED `decode_chain_list` (IRI-only) caveat as cax-adc. |
| eq-diff2 / eq-diff3 | `eq_diff2_clash`/`eq_diff3_clash` (union target would be `eq_diff1_clash \/ eq_diff2_clash \/ eq_diff3_clash`) | `allDifferent_to_differentFrom` (premise expansion) + `is_inconsistent` check 2 (`differentFrom_in_graph`) | PARKED — detection-soundness attempted, two-attempt-stop; see Notes | N/A (clash row) | — | CLASH-ROW ADJUDICATION (2026-08-06): `owl_rule_allDifferent_to_differentFrom` materialises pairwise `owl:differentFrom` from BOTH `owl:members` and `owl:distinctMembers` lists in ONE fold (unioned before decoding), so the engine cannot distinguish eq-diff2 (`owl:members`) from eq-diff3 (`owl:distinctMembers`) even in principle — any provable statement is already a `eq_diff2_clash \/ eq_diff3_clash` disjunction at best, same row-union pattern as cax-adc/prp-adp (also joined by `eq_diff1_clash`, the asserted-form sibling `is_inconsistent` check 2 also flags). PARKED, not proved, for a DIFFERENT reason than prp-adp's literal gap: check 2 (`t.p = owl:sameAs && differentFrom_in_graph g (subject_to_term t.s) t.o`) tests a candidate `differentFrom` triple against BOTH directions of one FIXED, directional `sameAs` triple `t`. When only the "swapped" direction differentFrom witness exists (`d` relates `t.o` to `t.s`, not `t.s` to `t.o`), closing `eq_diff1_clash`'s order-rigid `u1.s==u2.s /\ u1.o==u2.o` needs a REVERSE `sameAs` edge (`t.o sameAs t.s`) that isn't among the two extracted witnesses — it is a fact about `g` having reached the eq-sym fixpoint (a standard, always-run RL rule at the real call site — `is_inconsistent` runs on the closure fixpoint output — but not a fact `is_inconsistent`'s own definition carries as a local hypothesis). Recipe for next attempt: add a `sameAs_symmetric g` hypothesis (mirrors `rdf_type_objects_resource`/prp-adp's literal hypothesis in kind), or restate against `entailment_closure`'s actual output where eq-sym is known to have fired. |
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

**Naming note (2026-08-08, owner decision)**: the fragment the rows
below call "rho-df" is the literature's **ρdf** — subPropertyOf /
subClassOf / type / domain / range, introduced by Muñoz, Pérez &
Gutierrez, "Simple and Efficient Minimal RDFS", J. Web Semantics
7(3), 2009 (author copy:
https://users.dcc.uchile.cl/~cgutierr/papers/jws09.pdf), whose
minimal deductive system also drops the reflexivity rows exactly as
these theorems do. The PUBLIC API name for this fragment is
**corerdfs** (`coreRdfsClosure` / `coreRdfsCheck`, with `rhoDf*` kept
as aliases); F\* module, function, and theorem names keep the
literature transliteration `rho_df` so this registry greps against
both the tree and the paper.

**RDFS-Plus tier (2026-08-09, owner-approved)**: `rdfs_plus_closure`
(RDF.Entailment.RDFSPlus.fst; public API `rdfsPlusClosure`) composes
the shipping `rdfs_closure_step` with 13 RDFS-Plus OWL rows —
eq-sym, eq-trans, eq-rep-s/o/p, prp-symp, prp-trp, prp-inv (both
directions), prp-fp, prp-ifp, cax-eqc, prp-eqp — under the same
dedup + fuel + length-test loop as `rho_df_closure`. Tier names:
"RDFS-Plus" (Allemang & Hendler, *Semantic Web for the Working
Ontologist*, 2008), "RDFS++" (Franz Inc., AllegroGraph). CLAIM
LEVEL: every OWL row runs under its proved licensing + truth lemmas
(section 1 of this registry); chain-level completeness is NOT
claimed — owl:sameAs equality breaks the Herbrand construction the
corerdfs completeness proof uses (that gap is task #10's embedding
problem, not an oversight). DEFINITION — "chain-level completeness"
(informal name, coined here; not a term of art): the completeness
half of the corerdfs tier's composed theorem chain surviving to the
query surface — concretely, the conjunction of
`rho_df_saturation_iff` + `rdfs_closure_rho_df_complete`
(Completeness.fst), `rho_df_closure_decides` (RhoDFClosure.fst), the
six-bucket index completeness theorems, and
`theorem_rdfs_regime_bgp_exact_answer` with its ASK corollaries
(SPARQL11.EntailmentRegime.RDFS.fst): every entailed consequence is
returned by the shipping query entry point, end-to-end, not
per-rule. A tier "lacking chain-level completeness" runs only
per-rule certificates (licensed + truth-preserving derivations, no
exhaustiveness claim against a model theory). eq-ref (sameAs reflexivity) is excluded
as a noise row, mirroring rho-df's exclusion of rdfs6/rdfs10.

**Experimental entailment regimes (2026-08-09, owner-approved)**:
`x-rdfscore` and `x-rdfsplus` are selectable per query
(`query(data, q, {entail: 'x-rdfscore'})`, CLI `--entail x-rdfscore`),
dispatched in F\* by `RDF.Entailment.RegimeDispatch.fst` — consumers
pass the string through verbatim. Both are materialisation-based
(answers = simple entailment over the named closure), the standard
construction for finite answer sets under SPARQL 1.1 Entailment
Regimes' extension point; the `x-` prefix marks them experimental.
`x-rdfscore` is the regime whose definition IS a theorem
(`theorem_rdfs_regime_bgp_exact_answer` + ASK corollaries — see the
chain-level completeness definition above); `x-rdfsplus` carries the
RDFS-Plus tier's per-rule certificates. The SPARQL Protocol endpoint
does not yet expose an entailment parameter — recorded follow-up, not
an accidental gap.

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
| RDFS entailment, rho-df completeness (fragment iff, abstract saturation) | `RDF.Entailment.RDFS.Completeness.rho_df_saturation_iff` | ✅ PROVED (G3 M1, landed) — `rho_df_entails g e <==> simple_entailment_spec c e` for any `c` extensive/sound/rho-df-closed over `g` | `rho_df_frag_graph c`, `graph_tt_free e` | Herbrand technique from the Simple rung, reused verbatim. Supersedes the "UNATTEMPTED" row this replaces ([#347](https://github.com/danbri/factoidal/issues/347)/[#348](https://github.com/danbri/factoidal/issues/348) index-completeness landed 90e2801). Findings C-1 (the coverage doc's literal gap-1 statement — `rdfs_entails d_minimal g e <==>` closure-then-simple-entailment — is FALSE; machine-checked witness `rho_df_entailment_strictly_stronger`) and C-2 (the shipping 12-rule `rdfs_closure` cannot instantiate `c` in the SOUNDNESS direction) are recorded in the module banner. |
| RDFS entailment, rho-df closure operator (G3 M1b) | `RDF.Entailment.RDFS.RhoDFClosure.rho_df_closure` (6 rows: rdfs2/3/5/7/9/11, reusing the shipping `rdfs_rule_*` functions, fuel/length-test loop) | see the 5 theorems below | — | Answers finding C-2: the six-rule operator `rdfs_closure` does not expose. |
| — extensivity | `rho_df_closure_extensive` | ✅ PROVED — `is_subgraph g (rho_df_closure g fuel)` | `graph_clean g` (separator-free labels, no triple-term object — decidable, INPUT graph only) | Hypothesis strengthened-away 2026-08-22 ([#474](https://github.com/danbri/factoidal/issues/474), backport of the Lean 4 `closure_extensive` plan): `rho_df_chain_canonical g` (`no_dup_keys` at every fuel-visited graph, uncheckable by any caller) is now DISCHARGED by section 2b, which proves `graph_clean` preserved by the six-rule step. Satisfiability of the new hypothesis is machine-checked (`lemma_graph_clean_satisfiable`). `rho_df_closure_extensive_chain` keeps the old statement for `rho_df_closure_decides`. FINDING X-1: the Lean theorem carries NO hypothesis and that form is FALSE here — `graph_dedup_sort` keeps one representative per `triple_to_key` STRING and that key is not injective on labels containing U+001F, so a two-triple key collision makes `rho_df_closure g fuel` a proper subset of `g`. Still composes the six per-row extensivity lemmas `RDF.Entailment.RDFS.FixedPoint` already proves, reused (not re-derived). |
| — soundness | `rho_df_closure_sound` | ✅ PROVED — `rho_df_entails g (rho_df_closure g fuel)` | `rho_df_chain_wf g` (`ig_wf_sp` at every fuel-visited graph) | Condition-usage audit (the task's explicit ask): each of the six `_true` lemmas (`ModelTheory.fst`) needs EXACTLY one `rho_df_conditions` conjunct and no other — no finding, the hypothesis-weakening replay the brief predicted. |
| — closedness | `rho_df_closure_closed` | ✅ PROVED (conditional) — at a fuel witness where the length test passes, `rho_df_closed (rho_df_closure g fuel)` | `rho_df_frag_graph c`, `ig_wf_sp (build_indexed c)`, `rho_df_subclass_subjects_iri c`, `no_dup_keys (rho_df_closure_step_pre_dedup c)`, `no_repeats_p c`, `no_repeats_p (rho_df_closure_step c)`, `graph_len (rho_df_closure_step c) = graph_len c` | `rdfs7_reaches_fact c` DROPPED 2026-08-06 (statement strengthening) — discharged by `rdfs_rule_subPropertyOf_reaches`, see the RESOLVED row below. One of the seven remaining hypotheses is still a FINDING carried as an explicit fact rather than derived (F-2); the other six are the "same shape as `lemma_len_eq_saturated`" hypotheses the brief authorized carrying. Of those, `no_repeats_p (rho_df_closure_step c)` is REDUNDANT since 2026-08-22 ([#474](https://github.com/danbri/factoidal/issues/474)): `lemma_rho_df_closure_step_no_repeats` proves it unconditionally and `rho_df_len_eq_saturated` no longer asks for it. It still appears in this `val` and in `rho_df_closure_decides` because `SPARQL11.EntailmentRegime.RDFS.rho_df_decides_hyps` transcribes that hypothesis list verbatim and machine-checks the transcription; deleting the clause is a two-file landing left on #474. |
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
| Index well-formedness (5 buckets) | `RDF.Indexed.KeyInjectivity.fst` | ✅ PROVED — `ig_wf_sp`, `ig_wf_subj`, `ig_wf_obj`, `ig_wf_po`, `ig_wf_pred` ([#338](https://github.com/danbri/factoidal/issues/338), closed 2026-08-04) | `sp_key`/`po_key`/subject-key injectivity, one-sided, on U+001F-free keys. |
| Bucket lookup completeness (converse direction) | `RDF.Indexed.Completeness.fst` | ✅ PROVED (90e2801) | Generic `lemma_build_bucket_complete` for any key_of + pred-bucket instantiation, no side condition; first consumer of the [#347](https://github.com/danbri/factoidal/issues/347) StringOrder axioms. Its generic sortWith all-pairs-sortedness machinery also unblocked Gap B below. |
| Bucket lookup completeness — the other FIVE buckets | `RDF.Indexed.Completeness.fst` stage 6 (2026-08-06) | ✅ PROVED | `lemma_build_indexed_complete_subj` / `_sp` (total keys, no side condition) and `_obj` / `_po` / `_so` (option keys — conditional on `bucket_key_X t == Some k`, because `build_bucket` files a literal-object or triple-term-object triple in NO binding). Each is the generic stage-5 lemma at one more `key_of`. Removes the first half of finding BR-4. |
| Dedup-key injectivity (literal arm, [#348](https://github.com/danbri/factoidal/issues/348) fix) | `RDF.Indexed.KeyInjectivity.fst` | ✅ PROVED (e137b5d) | `term_to_key_total`/`triple_to_key` full injectivity across all four term shapes under separator-free side conditions; `lemma_graph_full_sep_free_no_dup_keys`. Engine fix: literal keys now unit_sep-joined (extraction re-gate pending). |
| Closure-step no-repeats (Gap B) | `RDF.Entailment.RDFS.FixedPoint.fst` | ✅ PROVED (e137b5d) — UNCONDITIONAL | `lemma_rdfs_closure_step_no_repeats`; the noeq-vs-`sortWith_sorted` blocker fell to the Completeness module's eqtype-free sortedness proof. `lemma_len_eq_saturated_gapB` left only Gap A — CLOSED same day: `lemma_len_eq_saturated_sep_free` (Gap A landing) makes the termination test faithful for separator-free, tt-object-free, repeat-free inputs. NO open gaps on the termination path. |
| Row-level separator-freedom | `RDF.Entailment.RDFS.SepFree.fst` | ✅ PROVED — per-row conclusion cleanliness for rdfD2 and rdfs1-13 (checked directly: `lemma_rdfsN_sep_free` per row) | Feeds `ChainWf`. |
| Closure well-formedness chain | `RDF.Entailment.RDFS.ChainWf.fst` | ✅ PROVED — `graph_sep_free g ==> closure_chain_wf g`, empty + non-empty instances machine-checked | Makes `rdfs_closure_entails` apply to concrete graphs (hypothesis discharged non-vacuously). |
| Closure step extensivity + fixed-point | `RDF.Entailment.RDFS.FixedPoint.fst` | 🟡 LANDED WITH ADJUDICATION (commit `1aa4e71`) | Length-test fixed-point theorem holds under two explicit hypotheses (`no_dup_keys` on the pre-dedup intermediate graph), not unconditionally — the unconditional form is FALSE. Third finding from this landing: `term_to_key_total` literal keys use plain `"^^"` not `unit_sep`, a wider dedup-collision surface than [#338](https://github.com/danbri/factoidal/issues/338) described ([#348](https://github.com/danbri/factoidal/issues/348)). |
| String ordering axioms | `RDF.Indexed.StringOrder.fsti` | ⚠️ 3 TRUSTED AXIOMS ([#347](https://github.com/danbri/factoidal/issues/347)) | See Trust surface. |

## 5. SPARQL algebra refinement (the query rung, G3 M3)

The layer that connects closure results to query answers. Layer 2
landed 2026-08-06 (`SPARQL11.Algebra.BGPRefinement.fst`); layer 3 —
the composed regime theorem — landed 2026-08-06
(`SPARQL11.EntailmentRegime.RDFS.fst`). Both halves are now proved.
SOUNDNESS reached the SHIPPING selective-index store the same day
(finding RT-2 resolved: layer 2 parts 2b/8, layer 3 part 8).
COMPLETENESS landed 2026-08-06 as well, discharging finding BR-4
(layer 2 parts 2c/9/10/11/12) and removing BOTH named gaps from layer
3 — `eval_bgp_complete_at` and `eval_bgp_store_complete_at` — in part
9. Because layer 2's completeness is proved at an ARBITRARY store
(the same generalisation RT-2's soundness needed), the unconditional
theorems land at the `eval_bgp` proxy AND at the literal
`eval_ask_query` entry point. The regime iff is unconditional at the
ANSWER level; see findings BR-5 / RT-5 for why "answer level" and not
"list membership", and RT-6 for the one hypothesis that had to be
ADDED.

### Layer 2 — BGP refinement against a fixed graph

| Theorem | Status | Fragment / hypotheses | Notes |
|---|---|---|---|
| `theorem_eval_bgp_subgraph` (shipping statement: every eval_bgp solution subset-matches) | ✅ PROVED | `bgp_frag` (tt-free, exact literals, not fulltext), `graph_frag` | Soundness direction of layer 2. |
| `theorem_eval_bgp_instantiates_into_graph` (`mu(BGP) ⊆ g` form) | ✅ PROVED | same | The form layer 3 consumes at `rho_df_closure g fuel`. |
| `lemma_ig_search_sound` + 8 supporting lemmas (single-tp soundness, planner cover, fuel unfolds, extension-closed tp-match) | ✅ PROVED | per-lemma | Fills the gap `SPARQL11.Algebra.Refinement`'s banner recorded (index-probe soundness). |
| `lemma_ig_search_complete_selective` (+ the six gated bucket lemmas) — the index probe serves EVERY matching graph triple, at ANY `bucket_needs` | ✅ PROVED (2026-08-06, part 2c) | `bound_holds b t`, `bound_obj_exact b` (the bound object's `rdf_term_eq` class is a singleton) | Discharges finding BR-4. Mirrors `lemma_ig_search_sound_selective` branch for branch over the six `pick_smaller_bucket` candidates. `bound_obj_exact` is exactly the fragment where BR-4's predicted FALSITY ("x"@en vs "x"@EN) cannot occur — not a weakening, the true side condition. Arbitrary-`needs` for free, by the same flag split part 2b used for soundness: an unbuilt bucket is never OFFERED, and `bucket_cand_complete t None` is vacuously true. `lemma_ig_search_complete` / `lemma_store_search_complete` / `lemma_store_search_complete_for` are its three specialisations. |
| `theorem_eval_bgp_store_complete_fuel` / `theorem_eval_bgp_store_complete` — every explained BGP yields a returned solution `muo` with `binding_extends muf muo` | ✅ PROVED (2026-08-06, part 11) | `bgp_frag b`, `graph_frag gs.gs_graph`, `store_search_complete gs`, `bgp_subgraph_clause b gs.gs_graph muf` | The induction over the fan-out fold, counterpart of `theorem_eval_bgp_store_sound_fuel`, same fuel side condition, same named continuation `bgp_fanout_cont`, same store-generic hypothesis style. |
| `theorem_eval_bgp_store_complete_answer` / `_from_subset`, `theorem_eval_bgp_complete_from_subset`, `theorem_eval_bgp_store_for_complete_from_subset` — the returned solution instantiates the BGP to the SAME triples | ✅ PROVED (2026-08-06, part 12) | above plus `store_search_sound gs`, and (for `_from_subset`) `Some? (instantiate_tp p muf)` per pattern | The form layer 3 consumes, at the full-index store AND at the shipping `graph_to_store_for` store. Proof composes BOTH halves of layer 2: completeness supplies `muo`, then SOUNDNESS at `muo` supplies "every pattern instantiates under `muo`", which turns `binding_extends` into answer equality. |
| `memP muf (eval_bgp b g)` for a caller-supplied `muf` | ❌ FALSE — finding BR-5 | — | `sm_bind` conses, so the evaluator emits one binding ORDER fixed by `choose_best_tp`'s cost estimates; a same-bindings/different-order list is not `memP`. Two patterns and two variables exhibit it. Not a missing lemma — a wrong statement, corrected to the answer-equality form above. |
| Domain clause `dom(mu) = var(BGP)` | UNATTEMPTED | — | Bookkeeping, no graph content; separate landing. It is the ONLY thing between the answer-equality form and a literal `smap_eq` (hence a literal set equality). |

Findings BR-1..BR-3 (module banner, machine-relevant divergences):
the fulltext triple-pattern path is NOT subset-matching (binds
subject only, applies a limit — excluded by hypothesis, not hidden);
query blank nodes match as CONSTANTS (identity renaming — exact for
bnode-free BGPs, the regime suite's class); statements are
set-membership, not multiset (§18.3.1 cardinality needs a
no-duplicates hypothesis, deferred to layer 3's inputs).

### Layer 3 — the composed regime theorem (`SPARQL11.EntailmentRegime.RDFS.fst`)

Throughout, `c := rho_df_closure g fuel`. Hypothesis provenance is
labelled **L2** (layer 2), **D** (`rho_df_closure_decides`), or
**NEW** (introduced by this module).

| Theorem | Status | Hypotheses, with provenance | Notes |
|---|---|---|---|
| `theorem_rdfs_regime_bgp_sound` — `memP mu (eval_bgp q c) ==> rho_df_entails g (instantiate_bgp q mu)` | ✅ PROVED | **L2** `BR.bgp_frag q`, `BR.graph_frag c`; **D** the nine clauses of `rho_df_decides_hyps` (`rho_df_chain_canonical g`, `rho_df_chain_wf g`, `rho_df_frag_graph c`, `ig_wf_sp (build_indexed c)`, `rho_df_subclass_subjects_iri c`, `no_dup_keys (rho_df_closure_step_pre_dedup c)`, `no_repeats_p c`, `no_repeats_p (rho_df_closure_step c)`, `graph_len (rho_df_closure_step c) = graph_len c`) — transcribed verbatim, sufficiency machine-checked by `lemma_decides_hyps_suffices`; **NEW** none | The composed regime theorem's soundness half. Needs NO groundness condition (finding RT-1) and NO `graph_tt_free` (finding RT-3 — discharged from `graph_frag c` plus the layer-2 subset). |
| `theorem_rdfs_regime_bgp_complete` — `rho_df_entails g (instantiate_bgp q mu) ==> exists muo. memP muo (eval_bgp q c) /\ instantiate_bgp q muo == instantiate_bgp q mu` | ✅ PROVED — UNCONDITIONAL (2026-08-06) | **L2** `BR.bgp_frag q`, `BR.graph_frag c`; **D** `rho_df_decides_hyps g fuel`; **NEW** `graph_ground (instantiate_bgp q mu)` (the scoping decision); **NEW** `bgp_instantiable q mu` (finding RT-6) | The converse, with the BR-4 gap CLOSED. `eval_bgp_complete_at` is gone from the hypothesis list. `bgp_instantiable` replaces nothing — it repairs finding RT-6: `instantiate_bgp` silently drops a pattern it cannot instantiate, so `is_subgraph (instantiate_bgp q mu) c` alone is satisfied by a `mu` that binds nothing. |
| `theorem_rdfs_regime_bgp_exact_answer` — the iff | ✅ PROVED — UNCONDITIONAL (2026-08-06) | union of the two rows above | M3's target shape, delivered: the evaluator's ANSWER set over the rho-df closure IS the RDFS regime's answer set, on the fragment, for ground answers. Answer-level rather than list-level per finding RT-5 / BR-5. |
| `theorem_rdfs_regime_ask_complete` | ✅ PROVED — UNCONDITIONAL (2026-08-06) | same as the row above | ASK asks only for non-emptiness, so the RT-5 representation gap costs it nothing. |
| `theorem_rdfs_regime_bgp_complete_selective` — the same conclusion at the SELECTIVE store `graph_to_store_for` builds | ✅ PROVED — UNCONDITIONAL (2026-08-06) | same as the row above | The completeness counterpart of `theorem_rdfs_regime_bgp_sound_selective`. `eval_bgp_store_complete_at` is gone from the hypothesis list: layer 2 part 2c proves the probe complete at an arbitrary `bucket_needs`, exactly as part 2b did for soundness. |
| `theorem_rdfs_regime_ask_query_complete` — `eval_ask_query q c ds == true`, at the LITERAL shipping entry point | ✅ PROVED — UNCONDITIONAL (2026-08-06) | same, plus the bare-BGP ASK shape (`q_form == QF_Ask`, `q_pattern == GP_BGP bgp_q`, `q_dataset == []`, `q_values == None`) | Findings RT-2 and BR-4 both closed at one statement: the store is the selective one the shipping path actually builds, and the completeness fact about it is proved rather than assumed. Mirrors `theorem_rdfs_regime_ask_query_sound`. |
| `theorem_rdfs_regime_bgp_complete_conditional` | 🟡 SUPERSEDED (still true) | **D** `rho_df_decides_hyps g fuel`; **NEW** `graph_ground (instantiate_bgp q mu)`; **NEW** `eval_bgp_complete_at q c mu` | Retained. `eval_bgp_complete_at` cannot be discharged as written (finding RT-5 / BR-5: it asks for list membership of a caller-supplied mapping) but is usable by a caller holding the evaluator's own list. |
| `theorem_rdfs_regime_bgp_exact` — the conditional iff | 🟡 SUPERSEDED (still true) | union of the two rows above | Retained alongside `theorem_rdfs_regime_bgp_exact_answer`. |
| `theorem_rdfs_regime_bgp_complete_conditional_selective`, `theorem_rdfs_regime_ask_query_complete_conditional` | 🟡 SUPERSEDED (still true) | as above with `eval_bgp_store_complete_at q c mu` | RT-2's shipping-path conditional pair. Retained alongside the unconditional `theorem_rdfs_regime_bgp_complete_selective` / `theorem_rdfs_regime_ask_query_complete`. |
| `theorem_rdfs_regime_ask_sound` — `ask_bgp q c = true ==> exists mu. rho_df_entails g (instantiate_bgp q mu)` | ✅ PROVED | same as the soundness row, plus `ask_bgp q c == true` | ASK corollary. The algebra above BGP is entailment-agnostic (Entailment Regimes §2), so this is non-emptiness of the same solution sequence — inherited, not reproved. |
| `theorem_rdfs_regime_ask_complete_conditional` | 🟡 SUPERSEDED (still true) | same as the conditional completeness row | Mirror image; superseded by `theorem_rdfs_regime_ask_complete`. |
| GROUND-COLLAPSE BRIDGE, half one: `lemma_subgraph_implies_spec` — `is_subgraph e c ==> simple_entailment_spec c e` | ✅ PROVED — UNCONDITIONAL | none (holds for every `e`, RDF 1.2 triple terms included) | Via the identity substitution, named (`id_subst`) rather than a lambda — the closure-identity law. This is the half soundness consumes. |
| GROUND-COLLAPSE BRIDGE, half two: `lemma_spec_ground_implies_subgraph` — `simple_entailment_spec c e ==> is_subgraph e c` | ✅ PROVED | **NEW** `graph_ground e` | A ground triple's only instance is itself (`lemma_triple_inst_ground`). RDF 1.1 Semantics §4/§5.3: the interpolation lemma degenerates when `e` has no blank node. |
| `lemma_ground_entailment_collapse` — the iff at ground `e` | ✅ PROVED | **NEW** `graph_ground e` | The bridge as one statement. |
| `lemma_instantiate_bgp_ground` — decidable discharge of `graph_ground` | ✅ PROVED | **NEW** `bgp_ground_positions q /\ smap_ground mu` | Both conjuncts are syntactic checks on the query and on the candidate solution — the C1-style route a caller uses instead of inspecting the instantiated graph. |
| `lemma_decides_hyps_suffices` | ✅ PROVED | — | The machine check that the transcribed hypothesis bundle is SUFFICIENT for `rho_df_closure_decides` (catches weakening; verbatim transcription is what a reader checks for strengthening). |
| `lemma_eval_pattern_bgp_is_selective_store` | ✅ PROVED | — | The machine-checked record of finding RT-2: `eval_pattern` on a bare BGP uses `graph_to_store_for` (selective index), not `eval_bgp`'s `graph_to_store`. |

Findings RT-1..RT-4 (layer-3 module banner):

- **RT-1.** The ground collapse holds one way unconditionally and the
  other way only for ground `e`. This is why the soundness theorem
  carries no groundness hypothesis at all — putting one there would
  have been a silent strengthening of a theorem that does not need it.
- **RT-2.** The shipping ASK entry point does not go through
  `eval_bgp`. `eval_ask_query` calls `eval_pattern`, which builds its
  store with `graph_to_store_for` = `build_indexed_selective`
  (`SPARQL11.Algebra.fst:3588`), while layer 2's probe-soundness
  lemma is proved for `build_indexed` only. The ASK corollary is
  therefore stated at `eval_bgp`; closing the gap is a
  selective-index soundness lemma, one commit, and no entailment
  content changes.
- **RT-3.** `graph_ground` subsumes `graph_tt_free`, so the
  `graph_tt_free e` clause of `rho_df_closure_decides` never appears
  as a hypothesis of a layer-3 theorem — it is discharged on both
  routes.
- **RT-4.** "No query blank node" is NOT sufficient for a ground
  answer, and F\* refused the lemma until this was corrected. A
  `PT_TripleTerm` pattern with no blank node anywhere yields
  `Some (T_TripleTerm ...)` (`SPARQL11.Algebra.fst:397-409`), which
  layer 3 classifies as non-ground on purpose. The corrected
  predicates exclude both constructors. A STATEMENT bug caught by the
  proof, not proof engineering: the wrong version would have let a
  caller discharge `graph_ground` for an answer that is not ground.
- **RT-5** (2026-08-06). `memP mu (eval_bgp q c)` is the wrong
  conclusion and is FALSE. `solution_mapping` is an association list
  and `sm_bind` conses (`SPARQL11.Algebra.fst:103`), so the evaluator
  emits ONE permutation of the bindings — the one `choose_best_tp`'s
  cost ordering over the actual data dictates. A caller-supplied `mu`
  with the same bindings in another order is a different list. This is
  why neither `eval_bgp_complete_at` nor `eval_bgp_store_complete_at`
  could be discharged as written, and why the unconditional theorems
  conclude `instantiate_bgp q muo == instantiate_bgp q mu` instead.
  Nothing in layer 3 inspects a solution's list structure, so nothing
  is lost; the residual is the domain clause `dom(mu) = var(BGP)`.
- **RT-6** (2026-08-06). `is_subgraph (instantiate_bgp q mu) c` is
  STRICTLY WEAKER than the subgraph clause. `instantiate_bgp` silently
  drops a pattern it cannot instantiate
  (`SPARQL11.Algebra.fst:7557-7564`), so a `mu` binding nothing gives
  the empty instantiated BGP, a subgraph of everything. The missing
  clause is the new `bgp_instantiable q mu` hypothesis. Another
  statement bug the proof surfaced.

Layer-3 scoping decisions (settled in the module banner, part 1):
fragment-scoped BGPs only; groundness restricts the COMPLETENESS
direction only; RDF 1.2 triple terms are classified as non-ground
rather than waved through, so RT-3's subsumption is real rather than
definitional.

`SPARQL11.Algebra.Spec` / `SPARQL11.Algebra.Refinement` (landed
2026-08-03, pre-registry) are now in the verify-rdf-mt roster with
this layer; their per-lemma rows are a registry backfill task.

**`fexpr_congr` (g4-fexpr-congr, 2026-08-10).** `theorem_filter_card`'s
`fexpr_congr` hypothesis (18.5's bag-level Filter statement needs the
expression evaluator to respect `smap_eq`) is now DISCHARGED by
`lemma_eval_expr_congr` — structural induction over
`eval_expr_with_base`'s whole ~74-constructor `expr` language (plus
sibling lemmas for its four `and`-clique mates and one new helper for
`option expr` fields), ~230 lines. Every `mu`-read funnels through
`Lh.assoc_tr` (`sm_lookup`/`fx_ctx_get`), the same primitive
`S.sval`/`S.smap_eq` uses, so agreement at every key transfers
uniformly. **FINDING FC-1**: this does NOT reach the literal shipping
`eval_expr_ebv` — it and `eval_expr_fwd` are `irreducible`
(`SPARQL11.Algebra.fst` ~4487/4491), and the definitional equation
needed to cross back out to the wrapper (`eval_expr_ebv base e mu ==
ebv (eval_expr_with_base base e mu)`) is unreachable by every F*
technique tried (`assert_norm`, `norm [delta_only [...]]` in both
string and quoted-name form, blanket `delta`, `nbe`, `unfold_def`; same-
module and cross-module) — not a semantic falsity, a proof-engineering
wall the qualifier erects on purpose to keep the ~600-line evaluator
body out of unrelated callers' SMT context. `theorem_filter_card_eval_
expr_with_base` restates the card-spec UNCONDITIONALLY at
`eval_expr_ebv_transparent` (the wrapper's own body, copied verbatim
without `irreducible`); `theorem_filter_card` on the literal
`eval_expr_ebv` / shipping `filter_solutions` stays hypothesis-carrying
pending a dedicated commit auditing removal of `irreducible` across its
~13+ call sites (`SPARQL11.Algebra.Refinement.fst`, `SPARQL11.Expression.
Refinement.fst`, `SPARQL11.Store.fst`, `SPARQL.Service.Wrap.fst`).

**`theorem_project_card` (g4-project-card, 2026-08-10).** Project's bag-
layer clause (`project_card_spec`, Spec.fst:780 — length preserved plus
`occurs`-iff-`in_project_spec`) is now PROVED UNCONDITIONALLY of the
shipping `project_solutions` (`SPARQL11.Algebra.fst:5781`, `project`
:5761). No fragment hypothesis, matching `theorem_union_card`'s shape.
Unlike SR-1/SR-2/SR-3, `project` never compares two solution mappings
against EACH OTHER with `rdf_term_eq` — it is a per-row, per-variable
lookup — so the `rdf_term_eq`/`term_id_eqb` gap those three findings
turn on cannot arise here; `project_card_spec` itself is also already
stated at the right level (`occurs`/length, not raw list equality), so
it does not fall into the RT-5 assoc-list-order trap either. Built on
the existing `theorem_project_is_proj`, `theorem_project_solutions_
length`, `theorem_project_solutions_spec` assets plus two new
congruence lemmas on `is_proj`'s target argument
(`lemma_is_proj_unique`, `lemma_is_proj_congr_target`).
`theorem_distinct_card` on a smap_eqb-uniform (case-normalized lang
tag) fragment was attempted and judged NOT cheap: unlike Project,
`distinct_solutions`'s dedup (`sm_equal`, `rdf_term_eq`-based) would
need its whole mutual-submap structural correctness re-derived under
`term_id_eqb` to connect to `mult` — a second SR-1-scale proof, not a
~1-attempt lemma — so it was skipped per the task's stop rule rather
than forced.

## Trust surface

What this registry's PROVED cells rest on, beyond F\*/Z3 itself:

- **`RDF.Indexed.StringOrder.fsti` ([#347](https://github.com/danbri/factoidal/issues/347)) — 3 axioms.** `FStar.String.compare`
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

## 6. G4: response-path theorems (2026-08-09, wave 1)

| Stage | Theorem | Status | Notes |
|---|---|---|---|
| ORDER BY | `theorem_sort_solutions_permutation` | ✅ PROVED | Multiset-level, hand-derived (stdlib `sortWith_permutation` needs `eqtype`; noeq `rdf_term` fails it — reusable finding). Sortedness NOT claimed: comparator ties break antisymmetry; wave 2. |
| LIMIT/OFFSET | `theorem_slice_solutions_window` / `_length` | ✅ PROVED | Contiguous index-shifted window, all None/Some combinations. |
| DISTINCT | `theorem_distinct_complete` | ✅ PROVED | Representative-level, needs `noRepeats` domains hypothesis. |
| DISTINCT card | `theorem_sr3_distinct_card_spec_false` | ❌ SPEC FALSE | FINDING SR-3 ([#359](https://github.com/danbri/factoidal/issues/359)): dedup case-insensitive lang tags vs count exact — third strike of the SR-1/SR-2 equality gap. |
| SRJ (tree layer) | `lemma_json_val_of_{term,row,vars,rows,response,bool}_roundtrip` | ✅ PROVED | Exact equality, IRI+literal fragment (no bnodes/triple terms/dir literals yet), SPARQL.Protocol.RoundTrip.fst. |
| SRJ (text layer) | `Parser.FastString.Axioms.fsti` (8 facts / 9 vals, DO-NOT-WIDEN, justified line-by-line vs the OCaml realisation) + `lemma_byte_at_after_prefix` | ✅ PROVED, off trust surface (Step 4, 2026-08-10 — see "FastString migration Step 4" below; was 🟡 UNBLOCKED-as-axioms as of wave 1/2, now real theorems in `Parser.FastString.Axioms.fst`) | `fs_byte_length "ab" == 2` provable; all 8 facts now machine-verified true of the real definitions, not merely assumed. parse_json↔serialise text bridge still separately blocked by `FStar.String.sub`/`concat` gaps — see `docs/designissues/2026-08-10-string-foundation-decision.md`. |

**G4 wave 2b/2c (2026-08-09)**: ORDER BY sortedness —
`lemma_sortWith_sorted_by` (sorted-under-preorder for stdlib
quicksort; totality must be IF-form, OR-form refuted by 2-element
counterexample, in-file) + `theorem_sort_solutions_sorted`
(hypotheses carried; IRI fragment discharges via StringOrder axioms;
numeric fragment REFUTED — FINDING SR-4 [#362](https://github.com/danbri/factoidal/issues/362), unparseable literal
ties everything, transitivity false). FILTER de-vacuation steps 1-2:
`eval_expr_ebv`/`eval_expr_fwd` assume vals RETIRED — now real
`[@@ irreducible]` definitions over `eval_expr_with_base` (Part 8
block relocated; the "mutually recursive" banner was stale — Plan
agent identifier sweep); glue patch 62 narrowed to 3 symbols.
theorem_filter_sound/_complete now state semantics of the real
evaluator (existential-free fragment; production-path bridging lemma
= plan step 3, next commit).

**G4 wave 3 (2026-08-09)**: M2 expression semantics begins —
`SPARQL11.Expression.Refinement.fst` (proof-only module): `ebv_spec`
(independent §17.2.2 transcription) + error-tolerant §17.3 truth
tables + numeric/plain-string equality specs; 17 agreement lemmas on
the conforming classes; FINDINGS EX-1 (langString EBV truthy vs
spec Type Error) and EX-2 (And/Or/Not can never error — silent
collapse), both stated as divergence lemmas with witnesses, [#365](https://github.com/danbri/factoidal/issues/365).
Text-bridge: BLOCKED pending owner decision on FastString candidate
axioms 7-8 (value-level facts, documented in-file with OCaml
justification); tree-level remains the proved boundary meanwhile.

**G4 wave 4 (2026-08-09/10)**: EXISTS-cycle RESOLVED — `eval_exists_fwd`
assume val RETIRED via real mutual recursion (`pattern_size`/`expr_size`
metric + `lemma_substitute_pattern_preserves_size`, phase+size decreases
per the MathML.Present precedent; z3 cost 1.4-1.6x baseline, under the
3x gate; glue patch 62 down to 2 symbols). Full W3C on the branch:
SPARQL 631 pass, 0 fail (out of 631); RDF 1031 pass, 0 fail (out of
1031) — the 4 RIF failures of [#367](https://github.com/danbri/factoidal/issues/367) do NOT reproduce (stale-binary
measurement artifact suspected; see issue). RIF enters the theorems
zone — `RIF.Core.Refinement.fst`: `rif_fixpoint_extensive`/
`rif_one_round_extensive`/`rif_fire_rule_extensive` (UNCONDITIONAL —
finding E-1: no dedup-pass hypothesis needed, unlike rho-df),
`rif_derives` declarative spec + `fire_rule_licensed`/
`one_round_licensed`/`fixpoint_licensed` (two-graph snapshot idiom
forced by intra-round order-dependence). FINDING F-1 ([#367](https://github.com/danbri/factoidal/issues/367) candidate
cause): RIF import materialisation hard-codes OWL-Direct closure mode
for BOTH regime profiles (RIF.Core.Tests ~150-160 vs OWL.Closure.fsti
5747 mode split) — plausible, unconfirmed.

**G4 wave 5a (2026-08-10)**: N-Triples enters — `RDF.NTriples.RoundTrip.fst`
(proof-only): serializer-side INJECTIVITY family on the IRI/bnode
fragment (`lemma_nq_term_to_string_*` same-shape/cross-shape/injective +
pointwise graph level), on real FStar.String primitives. ROUND-TRIP
BLOCKED — two findings: the N-Triples PARSER is wholly FastString-based
(no tree stage to salvage; even the serializer's escape scan is
FastString-gated, blocking ALL literals), so text-level proofs need
value-content axioms beyond the approved 8 (extends [#358](https://github.com/danbri/factoidal/issues/358)) OR a
specified reimplementation of the fast path; and triple-line
injectivity is FALSE without a content-safety restriction (IRI
containing quote-gt-space forges line boundaries) — the
`iri_print_safe` predicate family is the required guard, aligning with
the M1 parser plan's same move.

**G4 wave 5b (2026-08-10)**: FastString axioms 7-8 PROMOTED
(owner-approved, [#358](https://github.com/danbri/factoidal/issues/358)) — set now 8, DO-NOT-WIDEN. New proved lexing
lemmas: `build_string` length/byte facts (induction over facts 1-4+7)
and `lemma_quoted_content_byte_sub` — the quoted-string read-back step
of the SRJ text bridge. FULL text bridge still blocked by a THIRD
string-spec wall: `FStar.String.concat` has ZERO lemmas in ulib
(checked; both parser and serializer sit on it). Candidate rule
documented in-file, owner-gated. Three walls, one pattern — feeds the
re-found-the-fast-path decision on [#358](https://github.com/danbri/factoidal/issues/358).

**FastString migration steps 0-1 (2026-08-10)**: baselines frozen
(docs/designissues/2026-08-10-faststring-baselines.md — parse 1M:
NT 71,304 tps, Turtle 80,143 tps, RDF/XML 27,669 tps; same-host
discipline; bench-turtle-metrics.sh found broken, fallback used,
repair noted). `Parser.FastString.Spec.fst` VERIFIED first-attempt:
UTF-8 codec mirroring fs_cp_at_impl branch-for-branch + full lemma
kit incl. `utf8_decode_encode_identity`. Steps 2+3 (the swap +
Option-B realisation + equivalence harness, merged together) next.

## 7. G4/M1: parser round-trip theorems

| Stage | Artifact | Status | Notes |
|---|---|---|---|
| Tokenizer, single-token | `SPARQL11.Parser.TokenRoundTrip.fst`: `tokenize_single_fragment_token` + 25 per-token `next_token_*_pre` lemmas | ✅ PROVED (9387b830e6) | Fragment: all single/two-char delimiter+operator tokens + bare `?`. Keywords/IRIs/vars/literals not yet. Canonical-token claim (case-folding bars text-level identity, banner-documented). |
| Tokenizer, multi-token list | `tokenize_fragment_roundtrip` (+ `combine_step`, `tokenize_loop_step_bridge`, `tokenize_loop_fragment`, six congruence-isolation lemmas) | ✅ PROVED (6c3b6f48d1) | Literal-reveal fix transferred as predicted; second obstruction (Z3 context blowup on inline concat asserts) solved by isolating steps into near-empty lemmas — pattern banner-documented for the keyword/VAR/IRI widening. |
| ASK+BGP print round-trip | commit 2 (AskBgpRoundTrip) | queued | Spec in task tracker; fuel-cost lemma per RDF.Indexed.Completeness style. |

**G4/M1 commit 2 (2026-08-10)**: `SPARQL11.Parser.AskBgpRoundTrip.fst`
— the ASK+flat-BGP parser chain proved correct at the TOKEN level:
`parse_select_query_token_level(_query)` (given print_query_1's token
list, the real parser reconstructs exactly q), via ~35 lemmas through
verb/object/subject/triples-block/ggp/ask-body dispatch, with the
fuel-cost formula ask_bgp_fuel_cost(n) = n + 11 derived from the real
call chain (n=5 → 16 ≪ the 10000 entry fuel; lemmas hold for ANY n).
FINDING (fourth string wall, corrects TokenRoundTrip's earlier
diagnosis): the TEXT-level theorem is PROVED IMPOSSIBLE with current
ulib — `FStar.String.sub`'s type gives the result LENGTH but says
NOTHING about its characters; blocks every payload-carrying token
(IRIs, vars, even keywords). Fix requires either a trusted ulib-level
sub-content rule or lexer changes off `substring` — owner-gated,
consolidated with the [#358](https://github.com/danbri/factoidal/issues/358) string-foundation decision.

**FastString migration steps 2+3 MERGED (2026-08-10)**: six primitives
are REAL Spec-backed F* definitions (assume vals retired; sole
survivor unsafe_char_of_d7ff in CharBoundary); patch 89 → 1 symbol;
fast OCaml now an experimental_ocaml_glue SPEED patch (rule 11(b)).
Gates: 233/234 verify (1 = pre-existing [#327](https://github.com/danbri/factoidal/issues/327)); extract/compile clean,
29 binaries; W3C SPARQL 631 pass 0 fail (of 631) + RDF 1031 pass 0
fail (of 1031), exact match (OWL DL suite not run, stated);
benchmarks ALL within the 10% gate vs frozen baselines (1M parse rows
FASTER: nt -8.0%, turtle -3.1%); equivalence 401/401 on valid UTF-8.
WALL (documented in the plan doc's Step 2/3 results): Spec's
utf8_bytes mixes two decoders that disagree on INVALID UTF-8 (665
divergences + one crash path) — the deletability promise holds for
valid input only until the Spec is re-founded on a single WHATWG
decoder; repair scheduled before step 4's axiom discharge.

**FastString [#374](https://github.com/danbri/factoidal/issues/374) repair (2026-08-10)**: Spec re-founded — the "second
decoder" was ulib's own list_of_string, which returns NEGATIVE
codepoints on invalid UTF-8 (measured -1670; a genuine F* stdlib bug,
upstream-reportable). Guards added in utf8_enc_char +
utf8_decode_all_aux (verified first-try; two new lemmas). Equivalence
corpus now COMPLETES CLEAN: 93,846 pass, 0 unexpected fail, 962
documented expected-fail rows (the necessity-forced byte_sub boundary
domain), no crash. Deletability contract now holds on ALL input. W3C
regression: RDF 1031/0 exact; SPARQL 627/4 with the 4 = the known
intermittent RIF quartet ([#367](https://github.com/danbri/factoidal/issues/367)'s environmental pattern). Residual:
decode-of-encode-vs-list_of_string theorem removed after 3 attempts
(in-file note with exact error); run-all.sh module-list gap found
(separate issue).

**FastString migration Step 4 (2026-08-10, branch `faststring-step4b`)**:
`Parser.FastString.Axioms.fst` lands — companion `.fst` proving ALL 8
facts (9 vals) `Parser.FastString.Axioms.fsti` states, from the real
`Parser.FastString.Spec` definitions via `Parser.FastString.fsti`'s
bridging lemmas. The axiom module is now off the trust surface
(theorems, not axioms). Two findings: (1) fact 6 (`fs_cp_at_ascii`)
was FALSE as originally stated — a machine-checked counterexample (`s
= ""`, `pos = 5`) shows `fs_byte_at`'s and `fs_cp_at`'s independent
out-of-range sentinels (`0` vs `0xFFFD`) disagree, so the unbounded
hypothesis did not imply agreement; fixed by adding the missing
`pos < fs_byte_length s` side condition (zero consumer churn, zero
current callers). (2) Fact 8 (`fs_byte_sub_self`) needed exactly the
"single-decoder round trip" theorem
(`utf8_decode_all_utf8_bytes_identity`) this file's own [#374](https://github.com/danbri/factoidal/issues/374)-repair
entry above records as "removed after 3 attempts" — proved this
session via an explicit non-recursive unfold lemma for
`utf8_decode_all_aux` plus a prefix-shift induction and a char-list
induction; full account in `Parser.FastString.Axioms.fst`. Verified:
`Parser.FastString.Axioms.fst`, `Parser.FastString.RoundTripLemmas
.fst`, `SPARQL.Protocol.RoundTrip.fst`, `RDF.NTriples.RoundTrip.fst`
(all `make <file>.checked`, rc=0). No admit, no `--lax`, no new
`assume val`. Companion owner-decision doc for the remaining ulib
string gaps (`FStar.String.sub`/`concat`, `list_of_string` on invalid
UTF-8): `docs/designissues/2026-08-10-string-foundation-decision.md`.

**G4 step 7 (2026-08-10)**: `eval_select_query` folded into the real
recursion — `eval_subselect_fwd` assume val RETIRED (patch 62 now ONE
symbol: eval_property_path_fwd). Metric extended: `query_size`,
GP_SubSelect counts its query, `pattern_size >= 1` refinement covers
the LATERAL edge free; two preservation lemmas
(`lemma_lateral_substitute_preserves_size` with a closure-identity
lambda-lift, and the unforecast
`lemma_rewrite_query_bnodes_pattern_preserves_size` — the bnode
rewrite walks into sub-queries, the one real gap found). No fuel
fallback needed anywhere. All four dependent proof modules re-verify
unchanged. W3C clean: SPARQL 631 pass 0 fail (of 631), RDF 1031 pass
0 fail (of 1031).

**FastString migration step 5 MERGED (2026-08-10)**: two new proof
assets. (a) `Parser.FastString.BaseCases.fst` (proof-only): 12
delimiter-character byte facts (quote/braces/brackets/colon/comma/
angle-brackets/space/newline/backslash — `fs_byte_at_*` +
`fs_byte_length_*` pairs) proved through the `.fsti` bridging lemmas +
`Spec.utf8_bytes_ascii_singleton`, deliberately independent of the
Axioms module; plus a Spec-direct ASCII-content family
(`lemma_build_string_utf8_bytes`/`_byte_length`/`_byte_at`). (b)
`Parser.FastString.ConcatSpec.fst` (wired, extracted): `concat_spec`
with proved equations `concat_spec_nil`/`_singleton`/`_cons` — closes
string wall (2) (ulib `FStar.String.concat` has zero equations);
proof-critical call sites migrated (`Parser.JSON.fst` 1 use,
`SPARQL.Protocol.fst` 6 uses). Gates: verify clean, extract/compile
clean, W3C SPARQL 627 pass 4 fail (of 631; the intermittent RIF
quartet [#367](https://github.com/danbri/factoidal/issues/367)) + RDF 1031 pass 0 fail (of 1031), benchmark every row
inside the 10% gate vs frozen baselines (all faster; attributed to a
quieter host, not the diff — stated in the plan doc). Unblocks the
SRJ text bridge (M4) and N-Triples parser-side proofs.

**G4 M4 first SRJ text-level lemmas (2026-08-10, branch
`srj-text-bridge`)**: `SPARQL.Protocol.RoundTrip.fst` +99 lines, three
lemmas verified (10/10 repeated runs, deterministic):
`lemma_concat_spec_two` (fully symbolic two-element decomposition of
`concat_spec ""` — the shape `serialise_response_json`'s terminal join
takes on 2+ result rows), `lemma_serialise_response_json_empty_literal`
(closed literal: `serialise_response_json [] []` equals the exact SRJ
empty-response string, by `assert_norm`), and
`lemma_serialise_response_json_two_empty_rows_literal` (two empty rows,
exercising `concat_spec_cons` end-to-end on a concrete list). FINDING
recorded in-file: the fully symbolic serializer statement does not
verify reliably — `Prims.strcat` is itself an opaque `val` with no
identity/associativity equations (same wall shape as
`FStar.String.concat`, different primitive; provable via
`FStar.String.list_of_concat` + list append lemmas +
`string_of_list_of_string`), and which statement failed shifted with
unrelated earlier declarations (Z3 context sensitivity). Next step:
interactive diagnosis via fstar-mcp, not batch retries.

**Task #48 streaming N-Quads, phase 1 (2026-08-11, branch
`streaming-nquads`)**: new `RDF.NQuads.Streaming.fst` (537 lines,
proof-only, verified clean, zero assume vals). Strategy B (common
line-splitter) on `FStar.String.list_of_string`/`string_of_list`
(their ulib round-trip lemmas are unconditional — avoids the parked
byte-level single-decoder round-trip, [#374](https://github.com/danbri/factoidal/issues/374)). PROVED: the split
machinery end-to-end — `split_complete_lines_reconstruct`
(`complete ^ carry == s`, nothing dropped or duplicated),
carry-never-contains-newline, "a chunk with no newline extends carry",
"a chunk ending in newline empties carry"; the streaming API
(`stream_state`/`feed_chunk`/`finish`/`stream_parse`) defined on the
UNMODIFIED `Parser.NQuads.parse_nquads_acc`;
`stream_parse_single_chunk_shape`; `cong_string_of_list` (finding:
`string_of_list` gets no SMT congruence from a variable equal to a
literal — helper proved by typing substitution, not Z3). Fuel: every
parse call runs a fresh string at position 0 with its own
`fs_byte_length + 1` fuel, so the batch entry point's sufficiency
argument applies verbatim. NOT PROVED (in-file FINDING, exact missing
lemmas named): `theorem_stream_eq_batch` — needs
`parse_nquads_acc_concat_line` via (1) a mechanical `fs_byte_index_eq`
bridging lemma and (2) a locality proof across `Parser.NTriples.fst`'s
recursive-descent stack, scoped as its own landing.

**G4 M1-adjacent: first N-Triples PARSER round-trip theorem
(2026-08-11, branch `ntriples-parser-lemmas`)**: three landings.
(1) `fs_byte_index_eq` added to `Parser.FastString.fst`/`.fsti` — the
one bridging lemma missing after the re-founding: parser byte-dispatch
reads through `fs_byte_index`, not `fs_byte_at`, and had no spec
bridge (probe-confirmed unprovable before). Also prerequisite (1) of
`theorem_stream_eq_batch` (task #48 finding). (2)
`checkpoint_a_closed_triple_round_trip` in `RDF.NTriples.RoundTrip.fst`:
`parse_triple` on the SERIALIZER'S OWN OUTPUT for a concrete all-IRI
triple returns exactly that triple — the statement the module banner's
FINDING 1 had recorded as unprovable for any concrete input. Plus
`lemma_extract_middle`, a reusable `fs_byte_sub` extraction helper
(Axioms facts only, deliberately avoiding the
`string_of_list`/`list_of_string` chain that fails even with every
fact in context). (3) FINDING (checkpoint (b) not landed): symbolic
term-level round-trip needs a `scan_iri_end` shift lemma, and one
layer below it, `"" ^ s == s` and `^`-associativity FAIL for SYMBOLIC
strings via plain SMT (concrete literals fine) — the route forward is
position/byte-value idioms (the `lemma_build_string_byte_at` family),
never raw symbolic string equality. All verified clean, no admits, no
new assume vals.

**Task #48 streaming phase 2 (2026-08-11, branch `streaming-phase2`)**:
two locality lemmas verified in `RDF.NQuads.Streaming.fst`:
`lemma_fs_byte_index_concat` (byte i of `a ^ b` reads from `a` or `b`
by position — closes the phase-1 FINDING's item 1 via the landed
`fs_byte_index_eq`) and `lemma_byte_index_at_middle` (LINE-level
locality: a line embedded at a position inside a larger string reads
byte-for-byte the same as the line alone). FINDING updated: item 2
(`parse_nquads_acc_concat_line`) deliberately NOT attempted — the
same proof shape for ONE combinator (`scan_iri_end`) is already
documented in `RDF.NTriples.RoundTrip.fst` Part 6 as needing a
multi-step induction beyond the 3-attempt guard; the full
`Parser.NTriples.fst` call graph is strictly larger. The remaining
work for `theorem_stream_eq_batch` is one dedicated landing: the
parser-locality induction over the recursive-descent stack, now
reduced to named lemmas with the byte-level base facts in place.

**G4 M4 symbolic strcat kit + single-row SRJ theorem (2026-08-11,
branch `srj-symbolic`)**: three strcat lemmas landed in
`Parser.FastString.ConcatSpec.fst` (the shared home — SRJ and future
N-Triples symbolic work both need them): `lemma_strcat_empty_l`
(`"" ^ s == s`), `lemma_strcat_empty_r` (`s ^ "" == s`),
`lemma_strcat_assoc` — proved via `FStar.String.list_of_concat` →
list `@` equations (`append_l_nil`/`append_assoc`) →
`string_of_list_of_string`, closing the symbolic-strcat wall both the
SRJ and N-Triples FINDINGs named. Then `SPARQL.Protocol.RoundTrip.fst`
Part 10: the SYMBOLIC single-row serializer theorem
(`serialise_response_json vars [r]` for symbolic `vars` and `r`)
verifies. FINDING: the two-row symbolic statement verifies STANDALONE
(3 of 3 probe runs) but fails in-file with a fast
`unknown (incomplete quantifiers)` — trigger sensitivity from earlier
declarations, not resources (#restart-solver + 6x rlimit ruled out);
exact query-stats + bisection plan recorded in-file. Next: the N-row
induction (may be easier than fixed two-row — the induction hypothesis
adds structure), with fstar-mcp for the bisection.

**Parser locality pilot PROVED (2026-08-11, branch `parser-locality`)**:
new proof-only `Parser.NTriples.Locality.fst`. `lemma_scan_iri_end_shift`
— the pilot of the locality induction both `theorem_stream_eq_batch`
(task #48) and the symbolic N-Triples round-trip need: if
`scan_iri_end` finds `>` inside a line, the same scan on the line
embedded in `prefix ^ (line ^ suffix)` finds it at the shifted
position. Proved first-attempt by a rec lemma mirroring the
combinator's own recursion branch-for-branch, entirely in
byte-index/position terms (never symbolic string equality — the one
register that avoids the strcat wall). Plus
`lemma_byte_index_at_middle` (self-contained restatement) and the
`i=0` corollary `lemma_scan_iri_end_shift_from_start` (the shape
`parse_iri_raw` calls). Template assessment (file-end banner):
`parse_iri_raw`/`parse_iri`/`pws` and the position-only skeleton of
`parse_subject`/`parse_object` are mechanical repetitions;
`parse_iri_body_acc` + `parse_literal` escape decoding are NEW
difficulty (accumulator finished with `FStar.String.concat` — the
separately-named wall; note the strcat kit in ConcatSpec may now
apply). No admits, no --lax, no new assume vals.

**Parser locality stages 1+2 (2026-08-11, branch `locality-fanout`)**:
`Parser.NTriples.Locality.fst` extended (7 commits, all verified).
STAGE 1 (mechanical fan-out of the pilot template): shift lemmas with
fuel headroom for `scan_iri_end`, the whitespace scanner
(`ptake_while_acc_pos`), `pws`, `parse_iri_raw` (fast path),
`parse_iri` (success case), `parse_subject`/`parse_object` (IRI
branches). STAGE 2: `lemma_parse_iri_body_acc_shift` — the
escape-handling accumulator combinator, first-attempt: NO concat
algebra needed; both runs build the SAME accumulator list, so the
final strings are equal by congruence (the pilot banner's
hard-prediction was wrong and has been corrected in-file — documented
guess vs measured outcome). One non-required statement failed 3
attempts (combined fast+escape `parse_iri_raw` lemma) — FINDING
in-file with all 3 attempts. STAGE 3 NOT started, per the brief's own
gate (stages 1+2 do not yet cover a whole line): remaining, in order —
blank-node locality (needs a new fs_cp_at fact, character level),
`parse_literal` (Stage-2 method expected to apply),
`parse_opt_graph_label`/`parse_graph_label`, comment/blank-line
scanners, whole-line `parse_nquad` shift,
`parse_nquads_acc_concat_line`, `theorem_stream_eq_batch` single-chunk
then general.

**Parser locality stage 3, items 1-5 (2026-08-11, branch
`locality-stage3`)**: `Parser.NTriples.Locality.fst` grown to ~2100
lines, all verified. Item 1 blank-node: `utf8_decode_at_join` +
`lemma_cp_at_at_middle` — `fs_cp_at` agrees under embedding given only
that the suffix's first byte is not a UTF-8 continuation byte (weaker
and more useful than byte-headroom; automatically true at every real
line-streaming call site), composed into
`lemma_scan_bnode_body_cp_shift_headroom`. Item 2 literal:
`lemma_parse_string_body_shift` (equal-accumulator),
fastpath/escapepath split lemmas, lang-tag + datatype shifts; FINDING —
the top-level `parse_literal` wrapper has a genuine non-local edge
case (mid ending exactly at the literal's end changes branch dispatch
under embedding). Item 3 graph labels: IRI branch done. Item 4:
`lemma_skip_eol_shift` done; NEW OBSTACLE CLASS —
`skip_comment`/`skip_line` wrap their scan loops in local unexported
`let rec`s, which no external lemma can name (confirmed against F*
name resolution, not inferred from failures); fix is the repo's
established source-level lift (task #36 pattern: name inner recursions
top-level), an extracted-code change out of scope for a proof-only
landing. Item 5: `lemma_parse_nquad_iri_nograph_shift` — whole-line
shift for all-IRI, no-graph-label, success case, first attempt. Items
6-8 (`parse_nquads_acc_concat_line`, `theorem_stream_eq_batch`)
correctly gated on: the skip_comment/skip_line lift + the
parse_bnode/parse_literal wrapper chaining — five NAMED remaining
pieces, third independent confirmation this is separate-landing work.

**Scanner lift + shift lemmas (2026-08-11, branch `scanner-lift`)**:
the stage-3 item-4 obstacle removed at the source level (task #36
pattern: name inner recursions top-level). `nt_skip_to_eol` lifted
from `skip_comment` (Parser.NTriples.fst); FIVE byte-identical local
`skip_line` loops (parse_nquads_acc, fold_nquads_acc,
count_nquads_acc, parse_nquads_12_acc, parse_nquads_flat_acc)
deduplicated into ONE top-level `nq_skip_line` (Parser.NQuads.fst).
Behavior-identical (same branches, arithmetic, fuel). Gates: verify
clean across the five affected proof modules; extract+compile OK;
W3C SPARQL 631 pass, 0 fail (out of 631) AND RDF 1031 pass, 0 fail
(out of 1031) — fully clean run. Shift lemmas
`lemma_nt_skip_to_eol_shift` + `lemma_nq_skip_line_shift` landed in
`Parser.NTriples.Locality.fst` with a corrected hypothesis
(`p + fuel > fs_byte_length mid`): these scanners RETURN the current
position on fuel exhaustion instead of failing (unlike scan_iri_end),
so unconditional fuel headroom is false — the condition matches every
real caller. Items 6-8 (parse_nquads_acc_concat_line,
theorem_stream_eq_batch) now have the scanner path open; they still
need the parse_bnode/parse_literal WRAPPER chainings (items 1-2
residue) first.

**Task #48: SINGLE-CHUNK STREAMING THEOREM (2026-08-11, branch
`stream-theorem`)**: `theorem_stream_eq_batch_single_chunk` PROVED in
`RDF.NQuads.Streaming.fst` — `stream_parse [c] == batch_parse c` for
any chunk that either contains no newline or ends in a newline, with
NO hypothesis on the chunk's RDF content (well-formed or not, any
shape, any escapes). Supporting landings in
`Parser.NTriples.Locality.fst`: `lemma_parse_bnode_shift` (wrapper
chain closed first-attempt, + subject/object/graph-label bnode
corollaries); `lemma_parse_literal_plain_shift` +
`lemma_parse_literal_lang_shift` (the `^^dt` datatype branch is a
FINDING — 3 structurally different attempts, identical Error 19,
same wall class as the abandoned parse_iri_raw capstone, third
independent confirmation); `lemma_parse_nquad_shift_generic` — a
more scalable design than 18 shape combinations: per-component
success supplied as external hypotheses, covering every shape by
composition. `parse_nquads_acc_concat_line`: BOTH boundary cases
(complete="" / carry="") closed fully generally — neither needed the
per-combinator induction the original FINDING predicted (STATUS
UPDATE banner corrects it). Remaining for the general multi-chunk
theorem: `lemma_parse_nquads_acc_restart` (named FINDING) — the
mid-line-split restart argument. No admits, no --lax, no new
assume vals.

**Gap 1 CLOSED — SPARQL lexer on fs_byte_sub (2026-08-11, branch
`lexer-faststring`, task #52, owner decision "1: A")**: the lexer's
single `substring` choke point (SPARQL11.Parser.fst:225, 13 call
sites) migrated from `FStar.String.sub` (no content spec in ulib) to
`Parser.FastString.fs_byte_sub` (fully proved). Byte-vs-codepoint:
the lexer was codepoint-indexed; byte-walking is behavior-identical
for THIS grammar because delimiter scans hunt single ASCII bytes
(UTF-8 self-synchronizing) and every non-ASCII classification uses
`code >= 0x80`, satisfied by every byte of a multi-byte sequence
exactly as by the codepoint; one genuine mixed-unit site
(`split_pname` length arg) found and fixed.
`SPARQL11.Parser.TokenRoundTrip.fst` fully re-proved (ascii_string
hypothesis threaded ~30 sites + a reusable ASCII↔fs_byte_* bridging
kit in RoundTripLemmas). Gates: W3C SPARQL 631 pass, 0 fail (of 631);
RDF 1031 pass, 0 fail (of 1031); bench within the 10% gate (RUNS=5,
largest delta +6.3%; a first RUNS=3 pass showed two rows over gate,
not reproduced). PAYOFF: `fs_sub_of_concat` +
`fs_sub_of_concat_literal` — the two probe lemmas AskBgpRoundTrip.fst
documented as IMPOSSIBLE against String.sub — now PROVE first-attempt,
plus `ask_keyword_recovered_from_prefix` (ASK keyword recovered from
a printed prefix with symbolic tail). Zero new assume vals, zero new
axioms. Full string-to-AST theorem remains scoped future work
(fragment widening at TokenRoundTrip scale).

**G4 M1: SYMBOLIC IRI round-trip theorem (2026-08-11, branch
`nt-symbolic2`)**: `RDF.NTriples.RoundTrip.fst` Part 7 (+191 lines).
`lemma_term_iri_round_trip_build_string` — parse of
(nq_term_to_string (T_IRI iri)) == the term, for a SYMBOLIC iri whose
text is `build_string cs` with `cs` any ASCII codepoint list of
IRI-safe characters (no escapes, no '>', no controls). The REAL
serializer, not a transcription. Sub-checkpoints:
`lemma_scan_iri_end_build_string` (b1 — the scan finds '>' right
after any safe IRI text, any suffix) and
`lemma_parse_iri_raw_build_string` (b2). Proof composes two prior
landings read-only: the strcat kit (ConcatSpec) and the scan shift
lemmas (Parser.NTriples.Locality) — first-attempt pass once composed;
the walls the original checkpoint-(b) attempt recorded are both
CLOSED by that prior work. Remaining narrowest gap: covering ANY
well-formed IRI string requires "s == build_string (codes of s)", the
known string-conversion mixing wall (already probed and blocked once,
per RoundTripLemmas' notes). No admits, no --lax, no new assume vals.

**FastString migration COMPLETE — steps 0-6 (2026-08-11, branch
`js-equivalence`, task #47)**: the final step-6 item landed — the
FastString equivalence corpus now runs UNDER NODE via js_of_ocaml
(same OCaml harness, bytecode → jsoo, product build flags):
93,846 pass, 962 expected-fail, 0 unexpected fail (out of 94,808) —
IDENTICAL to native (verified three ways: fresh node run, fresh
same-source native compile, prior recorded number). The plan's
UTF-16/jsoo risk is closed by measurement. Wired into
tests/unit/run-all.sh (--jsoo / WITH_JSOO=1) for CI. CORRECTION found:
the plan doc's "bytes-as-JS-chars" domain claim was wrong — jsoo
6.4.1 builds with use-js-string=true (checked in both the new test
JS and the product factoidal.js); plan doc corrected. The migration
end state: zero assume vals in the FastString family except the
documented unsafe_char_of_d7ff; all 8 axiom facts proved (one was
false and corrected); fast OCaml is a deletable rule-11(b) speed
patch; equivalence proven on all input classes, native AND node;
benchmarks inside the gate throughout; the String.sub and
String.concat ulib walls closed with zero new axioms.

**Task #48 general theorem, attempt round (2026-08-11, branch
`stream-general2`)**: two new primitives PROVED in
`RDF.NQuads.Streaming.fst`: `lemma_skip_comment_shift` (links
skip_comment to the lifted nt_skip_to_eol shift — the one-line gap the
file noted) and `lemma_nq_skip_line_shift_exact` (skip-line shift at
the EXACT fuel the engine passes, no headroom hypothesis needed).
General `theorem_stream_eq_batch`: NOT closed — 3 attempts on the
narrowest sub-case (blank-lines-only mid) failed, each after 10-16 min
of full z3 search (resource exhaustion, not quick rejection).
DIAGNOSIS recorded as the FINDING: the hypothesis was a forall over
positions with an inner match — no instantiation pattern for the
solver; every PROVEN lemma in these files instead passes per-position
facts as EXPLICIT witness parameters (stop_pos, gt_pos, ...). Fix
path: restate with explicit witnesses at each step. Failed code
removed; only proven code kept.

**Task #48: GENERAL single-chunk theorem via witness chains
(2026-08-11, branch `stream-witness`)**: the explicit-witness
restructure WORKED — the diagnosis was right. `RDF.NQuads.Streaming.fst`
+839 lines, 9 commits, every z3 query under 25 SECONDS (the forall
shape burned 10-16 minutes per failure). New witness types
(`line_kind`, per-kind witness records, `line_witness`,
recursive-chain predicates `chain_wf`/`chain_end`/`chain_ds_fold` —
structural induction, never forall-over-positions). ALL FOUR line
kinds proved first-try (blank, comment, quad-failure with stated
embedded-failure premise, quad-success composing
lemma_parse_nquad_shift_generic). LANDED:
`lemma_parse_nquads_acc_restart` (the FINDING's named target),
`lemma_parse_nquads_acc_concat_line_general` (the "genuinely hard
case"), and `theorem_stream_eq_batch_single_chunk_general` —
stream_parse [c] == batch_parse c for ANY chunk, any mix of
blank/comment/quad lines, any newline placement, given matching
witness chains for the split. REMAINING (FINDING, no wall): the
multi-chunk fold — one chain-concatenation lemma + a fold induction
carrying a witness-chain list; scoping choice, not a failure.

**Task #48 / [#402](https://github.com/danbri/factoidal/issues/402): MULTI-CHUNK STREAMING THEOREM (2026-08-11, branch
`stream-multichunk`)**: `theorem_stream_eq_batch` PROVED —
`stream_parse chunks == batch_parse (concat_all chunks)` for ANY list
of chunks, given a witness-chain pair per chunk (`stream_fold_wf`).
The terabyte-file question now has its answer as a machine-checked
theorem chain: split machinery → per-combinator locality → restart →
general concat-line law → single-chunk general → MULTI-CHUNK. Design
choice recorded: the fold asks the caller to supply remaining-tail
witness chains directly (less proof work, more caller burden) instead
of the FINDING's bottom-up chain-append route — and the reusable
`chain_append` lemma was ALSO landed separately (shifted, joined
chains cover `mid_a ^ mid_b`), with per-kind extend/shift sub-lemmas.
`string_concat_assoc` proved (not automatic). One non-required piece
open with a FINDING + exact fix path (`lw_ds_step_extend_right`, 3
attempts past the 3-min z3 cap). Whole module verifies in 43 seconds.
No admits, no --lax, no new assume vals.

**G4 M4: N-ROW symbolic SRJ theorem (2026-08-11, branch `srj-nrow`)**:
`lemma_srj_n_rows` in `SPARQL.Protocol.RoundTrip.fst` Part 11 —
`serialise_response_json vars rows` equals the fixed SRJ shape
(head/vars block ^ comma-joined row texts) for ANY variable list and
ANY row list of ANY length. First-attempt via induction; the fixed
two-row goal that kept failing in-file is now a definitional
instantiation. Helpers: `chunks_of`, `json_rows_joined`,
`lemma_json_rows_body_acc_is_rev_acc` (accumulator == rev_acc, list
facts only), `lemma_body_pieces_eq`, `lemma_concat_chunks` (strcat
kit inside the induction step, never one flat goal). Residual finding
kept: a separate NAMED two-row corollary lemma still trips the file's
trigger sensitivity (3 phrasings, same Error 19; one attempt flipped
pass→fail by removing an unrelated nearby declaration) — covered by
instantiation, not forced. Verified 3x alone + 3x in-file. No admits,
no --lax, no new assume vals.

**build_string totality wall — sharpened (2026-08-11, branch
`build-string-total`)**: `s == build_string (codes_of s)` NOT closed;
the finding is now precise. ROOT CAUSE (new, replaces the old
"chained equality" explanation): a SELF-RECURSIVE F* Lemma cannot use
`FStar.String.list_of_string`/`string_of_list` inside its own
recursive call — the failure is AT the recursive call, even when
nothing uses its result. Control tests: fuel/rlimit don't help;
reproduces with a plain `int` function; a helper lemma verifies alone
but fails inside the recursion; calc blocks and #restart-solver don't
help; ~20 probe files under `--split_queries always`. (Toolchain-shaped
finding — stays internal per the owner's no-upstream-filing rule.)
Route 2 (fs_byte_sub decomposition) needs a not-yet-proven
`slice_bytes`/`utf8_decode_all` base fact — a different, smaller wall,
noted at `fs_byte_sub_eq`. Findings recorded in
`Parser.FastString.RoundTripLemmas.fst` ("SHARPENED FINDING" section)
+ pointer updated in `RDF.NTriples.RoundTrip.fst`. No proof logic
changed; both files verify clean.

**[#402](https://github.com/danbri/factoidal/issues/402): CONSUMER layer theorems (2026-08-11, branch `consumer-hom`)**:
`RDF.NQuads.Streaming.fst` +~420 lines. API: `stream_consume` folds
each parsed quad into consumer state in ARRIVAL order; per-chunk state
is (consumer-state, stream_state) ONLY — no retained quads/dataset
(constant-memory observation documented definitionally). Reuses the
existing `Parser.NQuads.fold_nquads_acc` — no new parsing logic.
PROVED: single-chunk generic theorems
(`theorem_stream_consume_single_chunk{,_no_newline,_ends_in_newline}`,
generic in consumer type, no witness chains) and
`theorem_stream_consume_dataset_eq_batch` — fully general multi-chunk
for the dataset-building consumer, routed through
theorem_stream_eq_batch via the new witness-free bridge
`fold_nquads_acc_eq_parse_nquads_acc` (the two folds are
branch-identical under never_stop). DESIGN NOTE (argued, not just
asserted): grouped-by-graph output order is impossible for ANY
bounded-memory consumer when graphs interleave across chunks — arrival
order is the correct target. FINDING: the both-fully-generic theorem
(any consumer x any chunks) is mechanical over the witness-chain kit
but a ~670-line pass — separate landing. Verify clean, no admits, no
--lax, no new assume vals.

**Spec codec: slice law + parked identity RESOLVED (2026-08-11,
branch `slice-decode`)**: `Parser.FastString.Spec.fst` Section 7 —
`utf8_decode_all_concatMap_identity` (single-decoder round trip at
the codepoint-list level, NO string conversions in the induction —
sidesteps the recursion wall by construction) and its string-level
corollary `utf8_decode_all_utf8_bytes_identity`, which RESOLVES the
file's own item-6 "ATTEMPTED, PARKED" banner (banner kept with an
UPDATE paragraph, rule #14). THE SLICE LAW
(`utf8_decode_all_slice_by_charcount`): decoding a char-count-aligned
byte slice yields exactly the char segment. Stated in char-count form
(byte offsets = byte-lengths of encoded prefixes) — the
is_cp_boundary converse (arbitrary boundary position == some
char-count prefix length) is documented as the next rung, not
attempted, not needed for the targets. In RoundTripLemmas:
`fs_byte_sub_by_charcount` DISCHARGES fs_byte_sub_eq's pending
off-domain note by direct composition. Every lemma first-attempt
(technique pre-confirmed by Axioms.fst's private Fact-8 proof). All
six consumer modules re-verified clean. No admits, no --lax, no new
assume vals.

**G1 REVIEW KERNEL delivered (2026-08-11, branch `review-kernel`)**:
`docs/review-kernel.md` — 256 lines, readable in one sitting. 21
kernel statements: parser 4, expressions 2, filters 3, modifiers 4,
results 2, streaming 3, entailment chain 3 — each with the verbatim
F* statement + file:line, its spec predicates, its stated domain in
one sentence, and its honest boundary. Plus §8 five named
not-covered gaps, §9 trust-surface table (assume-val realisations,
z3, F*, the two documented toolchain findings), §10 the override
guarantee with exact re-verify commands (no-lax/no-admit claim
re-measured: zero pragma matches outside comments). Every file:line
read at source while writing. Four drift findings reported to the
hygiene tracker ([#198](https://github.com/danbri/factoidal/issues/198)), incl. a stale "admit()'d" banner over a
clean `()` body in the COTTAS backend.

**[#403](https://github.com/danbri/factoidal/issues/403) npm batch (2026-08-11, branch `npm-batch`)**: closure API
exposed on all three npm surfaces (index/wasm/fn):
coreRdfsClosure/coreRdfsCheck/rhoDfClosure/rhoDfFragmentCheck/
rdfsPlusClosure (+ owlIsConsistent/owlEntails already present).
CLAIMS BLOCK added to npm/factoidal/version.json — 8 items each
naming its theorem, file, and registry section (all verified to exist
verbatim before writing), including the four new landmarks
(multi-chunk streaming, N-row SRJ, symbolic IRI round-trip, completed
FastString migration); build-ocaml.sh's npm step now preserves the
block across rebuilds (verified byte-identical). Gates: npm units
169 pass, 0 fail, 1 skip (of 170); hub node 266 pass, 0 fail (of
266); headless browser 32 pass, 0 fail (of 32); smoke + dts-drift
clean. Bundle-sync drift found+fixed (hazard #12: npm copies 2 days
behind docs/fstar-extracted). DEFERRED with reasons: package rename
to `factoidal` (owner-decided; ~20-file migration, own dispatch);
[#344](https://github.com/danbri/factoidal/issues/344) (F* parser strictness, not ABI); wasm-entry ABI rebuild (needs
full extraction — pre-existing RDFS_Closure_SemiNaive.ml gap noted).

**[#401](https://github.com/danbri/factoidal/issues/401) M1: IRI round-trip GENERALIZED to plain strings (2026-08-11,
branch `iri-general`)**: `lemma_term_iri_round_trip`
(RDF.NTriples.RoundTrip.fst Part 8) — parse_object of
nq_term_to_string (T_IRI i) == ParseOk (T_IRI i) for ANY string i
satisfying is_iri + all_ascii + iri-body-chars; no caller-built
codepoint witness. Enabled by `lemma_ascii_string_is_build_string`
(+ `_bc` variant for BaseCases' nominally distinct pair) in
RoundTripLemmas — the ASCII instance of the build_string wall,
CLOSED. Route: never let Spec.utf8_bytes-of-build_string appear as a
goal inside recursion (that alone reopens the wall — measured, 109ms
Error 19); instead byte facts through the Axioms-opaque
lemma_build_string_byte_length/_byte_at + fs_byte_*_eq bridges, list
equality by index_extensionality, one plain list-level recursive
helper, composed with PR [#409](https://github.com/danbri/factoidal/issues/409)'s decode identity +
string_of_list_of_string. Also found: BaseCases'
lemma_build_string_utf8_bytes verifies in the "failing" shape —
candidate factors (cons-built RHS vs concatMap; default fuel vs 4/4)
recorded, not fully isolated. NOT covered: non-ASCII IRIs (needs
multi-byte scan_iri_end advance — separate rung); a generalized
checkpoint_a (arbitrary whole triple) is a new composition chain, not
mechanical. Full dependency chain re-verified clean. No admits, no
--lax, no new assume vals.

**[#402](https://github.com/danbri/factoidal/issues/402) COMPLETE: fully-generic consumer theorem (2026-08-11, branch
`generic-consumer`)**: `theorem_stream_consume_eq_batch` — for ANY
consumer type, ANY consume function, ANY chunk split (same
stream_fold_wf witness premise, same generality as the dataset
theorem). Design: generic layer ADDED ALONGSIDE the proven
dataset-specific layer, not a retrofit — the witness types and
position predicates were already consumer-free and reused unchanged;
only the per-step transform is parametrized (`lw_generic_step`,
`chain_generic_fold` + generic per-kind/restart/concat-line lemmas
targeting fold_nquads_acc). 430 new lines vs the ~670 estimate — the
low-level shift lemmas needed zero duplication, as predicted. ALSO
CLOSED first-attempt: `lw_ds_step_extend_right` via its FINDING's
recorded fix (match result stated as its own trivial lemma). Nothing
attempted was left unclosed; the superseded FINDING got a
forward-pointer (rule #14). Streaming program end state: parser
theorem + dataset consumer + generic consumer all proved; sole
residue = the ^^datatype literal-branch shift lemma (does not gate
any landed theorem). No admits, no --lax, no new assume vals.

**[#402](https://github.com/danbri/factoidal/issues/402) residue CLOSED: datatype literal branch (2026-08-11, branch
`dt-branch`)**: `lemma_parse_literal_datatype_shift` verifies. ROOT
CAUSE of the 3 prior failures (findings discipline vindicated again,
same class as Axioms fact 6): the statement was FALSE as written —
`dt` free over wf_iri includes rdf_lang_string/rdf_dir_lang_string,
where literal_wf fails and parse_literal returns ParseFail on BOTH
sides; the ensures only covered ParseOk/ParseOk. Z3 was correctly
refusing a false goal for three sessions; the old FINDING blamed
string-equality trigger behavior — WRONG, now corrected in the banner
(rule #14). With `dt <> rdf_lang_string /\ dt <> rdf_dir_lang_string`
added to requires, the proof is 3 lines, same shape and budget as the
plain-literal sibling. Witness-record hypotheses per the streaming
pattern. [#402](https://github.com/danbri/factoidal/issues/402)'s residue list is now EMPTY — every named theorem and
lemma of the streaming program is proved.

**[#401](https://github.com/danbri/factoidal/issues/401) M1 triple-composition checkpoints (2026-08-11, branch
`triple-roundtrip`, agent died mid-run — branch harvested)**: two
verified commits landed before the agent's death:
bracket-embedding prerequisites + a single-space pws lemma, and
bare-IRI + subject-wrapped IRI round-trip lemmas
(RDF.NTriples.RoundTrip.fst). Re-verified clean on the merged tree
(VERIFY_RC=0). The full arbitrary-triple composition
(subject-predicate-object chaining to parse_triple) was NOT reached —
remainder queued for a narrower re-dispatch. No admits, no --lax, no
new assume vals.

**[#381](https://github.com/danbri/factoidal/issues/381) FIXED: XML normalization (2026-08-11, branch `xml-norm`)**:
both XML 1.0 spec divergences closed in Parser.XML.fst as pre-passes —
`normalize_line_endings` (§2.11, byte-level scan, safe because CR/LF
are single-byte ASCII never appearing in UTF-8 continuations) at all
three document entry points, and `normalize_attr_literal_ws` (§3.3.3)
applied ONLY to raw literal runs, never to decoded char-ref output —
the literal-vs-reference distinction (&#9; stays a tab; a literal tab
becomes a space) holds by construction, confirmed by the control
fixture staying byte-identical. Parser.XML + 11 dependents verify
clean. Gates: both DIVERGES fixtures flipped to WORKS; xmlconf 1447
pass, 0 fail, 1138 skip (of 2585) — identical to baseline; SPARQL
631/0; RDF 1031/0 incl. rdf-xml 166/0. The RDF/XML proof program's
normalization precondition is now MET. SIDE FINDING (likely the [#367](https://github.com/danbri/factoidal/issues/367)
root cause): w3c_runner's rif_rules_path_for uses a hardcoded
relative path with no repo-root fallback — running from
ocaml-output/ instead of repo root produces EXACTLY 4 spurious
RIF-entailment failures; from repo root, 631/0 and 70/0. Follow-up
issue filed for the runner path resolution.

**[#324](https://github.com/danbri/factoidal/issues/324) SE-1 FIXED: simple_entails literal check (2026-08-11, branch
`simple-entails`)**: the loose `literal_eq` (case-folded language
tags; XML-canon-equated rdf:XMLLiterals) made simple_entails accept
non-entailed pairs — machine-checked witness stood in-code. Fixed:
new strict `literal_term_eq` (field-by-field; no folding, no canon),
simple_entails switched to it. Regression pins BOTH directions
(old accepted pair now REJECTED; real matches still accepted, per
the vacuity discipline). BONUS: `simple_entails_sound_ground` —
soundness with NO literal-content side condition for bnode-free
graphs, first attempt; the general theorem keeps graph_exact because
one smaller path (shared bnode binding twice across
tag-case/XML-form-differing literals) still uses the loose check —
documented in-code. Gates: 26 rdf-mt-layer modules verify; RDF
1031/0 (rdf-mt 39/0 — unchanged because the runner does not call
this F* function for the simple regime, SE-3 wiring tracked on
[#324](https://github.com/danbri/factoidal/issues/324)); SPARQL 631/0. NOTE: binary artifacts on the work branch now
mix two branch builds (one .cmi conflict resolved arbitrarily) — a
reconciling extract+compile on the merged tree follows the Turtle
([#334](https://github.com/danbri/factoidal/issues/334)) harvest.

**Runner truthfulness batch (2026-08-11, branch `runner-truth`)**:
(1) [#418](https://github.com/danbri/factoidal/issues/418) FIXED — rif_tc_base now uses the runner's standard
search-list; identity verified: SPARQL 631 pass, 0 fail (of 631) and
RDF 1031 pass, 0 fail (of 1031) from BOTH repo root and
ocaml-output/, all four RIF tests passing from both. The [#367](https://github.com/danbri/factoidal/issues/367)
intermittency mechanism is retired. (2) SE-3 DONE — the runner's
"simple" regime now dispatches to the F*-extracted
RDF_Entailment_Simple.simple_entails (rule-#15 violation removed);
verified by a true before/after binary diff: rdf-mt 39/0 → 39/0,
RDF 1031/0 → 1031/0, zero flips — the score now comes from the
VERIFIED function. (3) [#333](https://github.com/danbri/factoidal/issues/333) sharpened: all 10 vacuous passes
confirmed; they return Pass before any entailment function runs
(result_file None), and the real fix is datatype-clash/ill-formed-
literal detection under D-entailment in the F* engine (iron rule #1),
not runner wiring — scoped as [#333](https://github.com/danbri/factoidal/issues/333)'s follow-up. BONUS: nine modules
listed in build-ocaml.sh but never extracted/committed (incl.
RDFS.Closure.SemiNaive — the known full-js-rebuild blocker) are now
in ocaml-output/, all F*-verified clean, no patches needed.

**[#365](https://github.com/danbri/factoidal/issues/365) EX-1/EX-2 ALIGNED (2026-08-14, branch `ex-align`, owner decision
2026-08-11 verbatim "Align")**: the SPARQL expression evaluator's
boolean layer is now error-aware, closing both divergences the G4/M2
wave-1 agent found in `SPARQL11.Expression.Refinement.fst`. EX-1: EBV
(§17.2.2) now signals a Type Error for any value outside the table
(xsd:boolean, numerics, xsd:string/simple literals only) — a non-empty
rdf:langString is no longer truthy. EX-2: `E_And`/`E_Or`/`E_Not`
(§17.3) are now error-tolerant AND error-preserving — a determinate
false/true operand still dominates an erroring co-operand, but every
other combination now signals `ER_Error` instead of silently folding
to a definite bool. New engine functions in `SPARQL11.Algebra.fst`:
`ebv_checked : eval_result -> option bool` (the table, `None` = Type
Error; `ebv` is now defined via it, folding `None` to `false` so every
FILTER/HAVING/E_If call site keeps its "Type Error drops like false"
contract unchanged) and `bool_and_checked`/`bool_or_checked`/
`bool_not_checked : option bool -> option bool` (§17.3's tables,
literal copies of `SPARQL11.Expression.Refinement.fst`'s independently-
authored `spec_and`/`spec_or`/`spec_not`). The four pre-landing FINDING
(divergence) lemmas RETIRE into AGREEMENT lemmas of the same root name:
`lemma_ebv_langstring_finding` → `lemma_ebv_langstring_agrees`;
`lemma_eval_and_true_error_diverges_finding` →
`lemma_eval_and_true_error_agrees`;
`lemma_eval_or_false_error_diverges_finding` →
`lemma_eval_or_false_error_agrees`;
`lemma_eval_not_error_diverges_finding` → `lemma_eval_not_error_agrees`
— same witnesses, now provably matching the engine instead of
diverging from it. The expr-level corollaries
(`lemma_eval_and_matches_spec`/`_or_`/`_not_matches_spec`) are also
strengthened from a `Some b`-hypothesis-carrying form to full
unconditional agreement (every `eval_expr_with_base` outcome, error
case included). `SPARQL11.Algebra.Refinement.fst`'s ~74-case
congruence lemma (`lemma_eval_expr_congr`) needed no change: its
`E_And`/`E_Or`/`E_Not` cases only recurse into sub-expressions and let
SMT function-congruence carry the result through whatever pure
combinator the arm uses, so the new error-aware combinators verify
under the same proof shape.
Gates (2026-08-14, branch `ex-align`): 229 of 230 F* modules verify
clean (z3 4.13.3, no admits, no `--lax`) — the one exception,
`RDF.CottasStore.PageCache.Bounds.fst`, is a pre-existing failure
with zero dependency on this change (untouched by the diff, filed
separately as [#422](https://github.com/danbri/factoidal/issues/422)); SPARQL W3C 631 pass, 0 fail (of 631); RDF W3C
1031 pass, 0 fail (of 1031) — no test flipped. The new BIND/SELECT-
expression regression (`tests/local/cli_ex_align_regressions.sh`,
run through the real CLI backend path, not just the W3C runner's pure
algebra path) is 14 pass, 0 fail (of 14). FILTER/HAVING semantics are
unchanged by construction (Type Error still drops a row/group exactly
like `false`) except the one FILTER-visible flip EX-1 itself causes: a
bare non-empty langString literal in FILTER position used to keep the
row and now drops it, per the corrected EBV table — pinned in the same
regression script.

**[#334](https://github.com/danbri/factoidal/issues/334) FIXED: Turtle silent drops (2026-08-11, branch
`turtle-strict2`)**: an undeclared prefix made `Parser.Turtle.fst`
discard the statement and return SUCCESS — silent data loss (measured
before the fix: `factoidal dump` on a 3-statement file exited 0 and
printed 2 triples, no message). Fix: `turtle_doc_result` gains a
`tdr_error` field carrying the message + byte position (the
information was already computed, then thrown away); two new entry
points `parse_turtle_diagnostic` / `parse_turtle_with_base_diagnostic`
surface it through the parser's OWN existing ParseOk/ParseFail
convention (no new error mechanism); the CLI's Turtle load path exits
1 and prints message + position to stderr. Gates: regression 6 pass,
0 fail (of 6) — was 2 pass, 4 fail before the fix; W3C RDF 1031 pass,
0 fail (of 1031); SPARQL 631 pass, 0 fail (of 631); nothing flipped,
so no W3C test had been passing BECAUSE of the drop. This retires the
first half of the silent-drop class named in the streaming plan's
constraint 4. SCOPE (follow-ups on [#334](https://github.com/danbri/factoidal/issues/334)): Turtle Mode 1.2 (--rdf12),
TriG, and the manifest loader may carry the same defect — untouched
here.

**[#334](https://github.com/danbri/factoidal/issues/334) FOLLOW-UPS FIXED: Turtle Mode 1.2, TriG, manifest loader
(2026-08-14, branch `silent-drops2`)**: all three follow-ups named
above confirmed present and fixed, same mechanism as the RDF 1.1
Turtle fix.
- *Turtle Mode 1.2*: `parse_turtle_doc` already threaded `tdr_error`
  through Mode_12 parsing (shared code with Mode_11), but no Mode_12
  entry point surfaced it — the `--rdf12` CLI path called the
  always-succeeds `parse_turtle_with_base_12`. New
  `parse_turtle_diagnostic_12` / `parse_turtle_with_base_diagnostic_12`
  mirror the Mode_11 pair. Regression 6 pass, 0 fail (of 6) — was 2
  pass, 4 fail.
- *TriG*: `trig_parse_state` carried only `has_error: bool`, same gap
  as Turtle pre-fix. Added `terr: option (string \& nat)`, threaded
  through `parse_graph_body` and `parse_trig_doc`, and three new
  diagnostic entry points covering RDF 1.1 and `--rdf12`. Regression
  (both modes) 12 pass, 0 fail (of 12) — was 4 pass, 8 fail.
- *Manifest loader* (`bin/w3c-runner/w3c_runner.ml`'s `read_manifest`,
  consumer-side per iron rule #11): confirmed live —
  `third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl` line
  247 has an undeclared `test:` prefix (a typo for `rdft:`), silently
  dropping one metadata triple and holding `rdf12entail`'s
  `rdf-semantics` suite at 47 discovered tests instead of 48 — this is
  the exact mechanism [#334](https://github.com/danbri/factoidal/issues/334)'s body predicted for the `literal-type`
  disposition. POLICY CHOICE: lenient-with-report, not
  strict-with-report — going strict would zero out that whole
  manifest's ~48 test cases over one upstream typo we do not control,
  which is a worse failure mode for a test harness than a silently
  short denominator. Fix prints the error (message + byte offset,
  unconditional stderr) but keeps parsing the well-formed subset via
  the same lenient parse as before. Regression 6 pass, 0 fail (of 6)
  — was 3 pass, 3 fail. Verified this is diagnostic-only: rdf-semantics
  suite result is byte-for-byte unchanged (41 pass, 3 fail, 3 skip,
  discovered_tests: 47) before and after, only the stderr warning is
  new.

Gates (all three, from repo root, native binaries): W3C RDF 1031
pass, 0 fail (of 1031); SPARQL 631 pass, 0 fail (of 631) — both
unchanged from baseline, nothing flipped. This retires the [#334](https://github.com/danbri/factoidal/issues/334)
follow-up scope in full. SPARQL and JSON-LD context paths (also named
in [#334](https://github.com/danbri/factoidal/issues/334)'s task list as "check whether … share the lenient-drop
shape") are NOT covered by this landing — out of scope for the
branch that did this work.

**#16 DIFFERENTIAL TESTING vs Apache Jena (2026-08-11, branch
`diff-testing`)**: the missing independent cross-check now exists.
`tests/unit/run-jena-diff.sh` (opt-in, skip-with-reason when Jena is
absent) runs the vendored W3C Turtle + N-Triples corpus (389 files)
through BOTH factoidal and Jena 6.2.0 riot/rdfcompare and compares.
Only ONE normalization: blank-node labels compared by graph
isomorphism (implementations may name them freely); literals,
datatypes, language tags and IRI forms compared EXACTLY, so a
"disagree" is a real disagreement. Result: 261 agree-parse, 120
agree-reject, 2 disagree, 6 either-side-error (of 389). HARNESS BUG
CAUGHT BEFORE TRUSTING ANY RESULT: the first comparison target
(factoidal-dump-nq) silently drops bad input — a best-effort dump,
not the strict parser the W3C suite grades; 120 files looked like
disagreements that were not. Fixed by adding --strict routing through
the conformance parser entry points (bin/ consumer change), plus a
stale module list in build-ocaml-serializer.sh. TWO REAL PARSER BUGS
FOUND ([#425](https://github.com/danbri/factoidal/issues/425)), both in the Turtle number-literal classifier: leading-
dot numbers without exponent (.1, +.7) are tagged xsd:double but the
grammar says DECIMAL; 123.E+1 and -.2e3 are REJECTED but are legal
DOUBLE. Our own W3C Turtle suite reportedly scores 100% on these four
files — so the manifest expectations may ALSO be wrong; that check is
open on [#425](https://github.com/danbri/factoidal/issues/425). Adjudicated NOT a bug: 4 turtle-eval-bad cases where we
reject illegal raw IRI characters and Jena only warns — we are the
more conformant side.

**[#425](https://github.com/danbri/factoidal/issues/425) FIXED: Turtle number-literal classifier + the false-100%
mechanism (2026-08-11, branch `ttl-numbers`)**: both bugs the Jena
differential harness found are repaired in
`Parser.Turtle.fst:parse_numeric_literal`. Bug A — a leading-dot
number set the has-exponent flag TRUE before scanning any character,
so `.1`/`+.7` came out xsd:double instead of DECIMAL (flag
initialisation swapped). Bug B — after `123.`, the scanner only
continued past the dot for a DIGIT, so `E+1` was left unread and the
parse failed; fixed with an `is_valid_exponent_at` lookahead.
WHY OUR SUITE SCORED 100% ON THESE FILES (the finding that matters
more than the bugs): W3C positive-syntax tests are graded by
`ignore (parse_turtle_fstar content (Some base)); Pass` — the runner
throws the result away and asks only "did it parse", never "is the
produced RDF right", and it uses the LENIENT entry point while
`factoidal dump` uses the strict one. So 1031 pass, 0 fail was
truthful about "does not crash" and blind to datatype correctness.
The manifests are CORRECT — the gap is in the runner's grading logic;
filed separately. Gates: regression 20 pass, 0 fail (of 20) — 14
pass, 6 fail before; RDF 1031/0; SPARQL 631/0; JENA HARNESS 265
agree-parse, 120 agree-reject, 0 DISAGREE, 4 either-side-error (of
389) — the 2 disagreements are gone, the 4 remaining are the
already-adjudicated turtle-eval-bad cases where we are stricter than
Jena. Trap re-confirmed: `factoidal-dump-nq` is not rebuilt by the
main build script and needed its own rebuild for the harness to see
the fix.

**[#333](https://github.com/danbri/factoidal/issues/333) FIXED: RDFS D-inconsistency detection (2026-08-11, branch
`dtype-clash`)**: the ten vacuous rdf-mt passes now CHECK. New
`RDF.Entailment.RDFS.DatatypeClash.fst` detects (a) ill-formed
literals for recognized datatypes (reusing
`XSD.Datatypes.literal_ill_formed`) and (b) rdfs:range vs value
datatype clashes — both gated on the manifest's
`mf:recognizedDatatypes`, matching the rdf-mt rules. Runner's two
"no result file, so Pass" branches now DISPATCH to the extracted
detector (rule #15 respected — no semantics in the runner).
VACUITY EVIDENCE (the point of the exercise): six compile-time
`assert_norm` witnesses — three graphs that MUST be flagged, three
that must NOT — plus a live re-run of [#333](https://github.com/danbri/factoidal/issues/333)'s own corruption trick:
garbling the `datatypes-range-clash` input now flips PASS→FAIL,
where before the fix the suite did not notice. A bug in the detector
was itself caught this way: the first range-clash version searched
only part of the graph, and a should-flag witness refused to verify.
SCORES (labelled, and the total DROPS on purpose): rdf-mt 38 pass,
0 fail, 1 unsupported (of 39) — was 39 pass, 0 fail with 10 of them
unchecked; full RDF 1030 pass, 0 fail, 1 unsupported (of 1031) — was
1031/0; SPARQL 631/0 unchanged. The 1 unsupported is
`rdfs-entailment-test001`, which needs rdf:XMLLiteral validity
checking that this tree does not have (optional in RDF 1.1) — now
reported honestly instead of passing falsely. Nine tests match the
manifest exactly; no adjudication needed.

**[#401](https://github.com/danbri/factoidal/issues/401) M1: IRI round-trip WIDENED to non-ASCII (2026-08-11, branch
`iri-nonascii`)**: `lemma_term_iri_round_trip_utf8`
(RDF.NTriples.RoundTrip.fst Part 10) — parse_object of
nq_term_to_string (T_IRI i) returns the term for ANY i satisfying
`is_iri` + `chars_all is_iri_body_char`. The `all_ascii` hypothesis
is GONE. The feared obstacle (multi-byte scan advance) dissolved on
inspection: `scan_iri_end` already reads BYTE-wise, and every
forbidden byte (space, angle brackets, quote, braces, pipe,
backslash, caret, backtick) is below 0x80, while every byte of a
multi-byte UTF-8 sequence is 0x80 or above — so a multi-byte
character can never collide with a delimiter
(`lemma_utf8_enc_char_iri_safe` proves by `()` alone). Remaining
work was showing the scan walks a character's own 1-4 bytes: a
general step-by-step attempt failed with incomplete-quantifiers; a
BOUNDED case split on k=1..4 (UTF-8 is never longer) verified.
Bridging: `utf8_bytes_singleton` added to Parser.FastString.Spec.fst
— the ASCII-free twin of utf8_bytes_ascii_singleton — after which
the existing general facts carried the build_string bridge through.
No rebuild needed and VERIFIED as such: the extracted
Parser_FastString_Spec.ml contains ZERO lemmas (checked), so adding
a Lemma cannot change the built program. Part 8's ASCII lemma stays
for existing callers. Next: widen Part 9's triple-level lemmas the
same way.

**[#429](https://github.com/danbri/factoidal/issues/429) FIXED: syntax tests graded on the STRICT parser (2026-08-14,
branch `syntax-grading`)**: four RDF 1.1 positive-syntax test types
(Turtle, TriG, N-Triples, N-Quads) were graded
`ignore (parse ...); Pass` — result discarded, LENIENT parser used,
so a test passed even when the produced RDF was wrong. Now they use
the STRICT entry point, matching what `factoidal dump`/`validate`
do. AUDIT (docs/designissues/2026-08-14-syntax-grading-audit.md)
scoped the damage precisely: RDF 1.1 negative-syntax and eval tests
were ALREADY real; RDF 1.2 positive-syntax was already fixed under
epic [#305](https://github.com/danbri/factoidal/issues/305); SPARQL query/update syntax tests were already real (one
parser, no lenient/strict split); RDF/XML has no such test type. So
the vacuity was confined to those four arms. SCORE DROPS ON PURPOSE:
RDF 1.1 total 1028 pass, 2 fail, 1 unsupported (of 1031) — was 1030
pass, 0 fail, 1 unsupported. TWO REAL TriG ENGINE BUGS EXPOSED, both
reproduced independently against the CLI: [#433](https://github.com/danbri/factoidal/issues/433) (a collection used as
a normal SUBJECT is rejected — the graph-name guard over-applies)
and [#434](https://github.com/danbri/factoidal/issues/434) (a trailing `;` before `}` with no final `.` is rejected,
though TriG permits it). Jena cross-check unchanged at 0
disagreements (265 agree-parse, 120 agree-reject, 4 either-side-error
of 389) — that harness does not cover TriG yet, so it neither
confirms nor denies the two new bugs. Unrelated pre-existing gap
noted: `Math.Sigmoid.fst` has source but no committed extracted
output on main (same class as the [#422](https://github.com/danbri/factoidal/issues/422) sweep).

**[#422](https://github.com/danbri/factoidal/issues/422) FIXED + unlisted-module sweep (2026-08-14, branch
`cottas-bounds`)**: `RDF.CottasStore.PageCache.Bounds.fst` had been
broken since the Phase 2.5c API change ([#118](https://github.com/danbri/factoidal/issues/118)) turned the cache value
type from `list (option string)` into the abstract `cottas_column` —
three of its four lemmas used the old type, one called a
pre-migration decoder, one bounded a function the engine no longer
calls. Nothing noticed because the module is absent from
build-ocaml.sh's list ([#327](https://github.com/danbri/factoidal/issues/327)). Re-synced to the current API, verifies
clean, and ADDED to ALL_MODULES (proof-only: no compile-list entry
needed). SWEEP RESULT: 26 files were unlisted; 9 are .fsti paired
with a listed .fst, 2 are interface-only but covered through listed
consumers, and 15 are real .fst content — **all 15 verify clean, 0
fail (of 15)**. Measurement honesty note: a 300s-per-module cap first
reported `SPARQL11.Algebra.BGPRefinement.fst` as FAILING; an
unhurried retry verified it in 5m15s — slow, not broken, and the
agent corrected its own number rather than publishing it.
🔴 THE FINDING THAT MATTERS MORE: CI's `check-extraction.yml` (the
PR gate) runs only `build-ocaml.sh extract` — it NEVER runs
`make verify`. So those 15 modules, which include nearly every
theorem landed this session (RDF.NQuads.Streaming,
RDF.NTriples.RoundTrip, Parser.NTriples.Locality,
SPARQL11.Expression.Refinement, SPARQL11.Parser.TokenRoundTrip,
Parser.FastString.Axioms, ...), are guarded by NOTHING in CI. They
are correct today; nothing stops a future edit from silently
breaking one, exactly as PageCache.Bounds broke. Filed separately.

**[#433](https://github.com/danbri/factoidal/issues/433) + [#434](https://github.com/danbri/factoidal/issues/434) FIXED: two TriG parser bugs (2026-08-14, branch
`trig-bugs`)**: both exposed by the [#429](https://github.com/danbri/factoidal/issues/429) strict-grading fix, both
repaired in the PARSER — verified independently that
`bin/w3c-runner/w3c_runner.ml` has a ZERO-line diff, so the score was
not recovered by softening the gate. [#433](https://github.com/danbri/factoidal/issues/433): `Parser.TriG.fst`'s "RC3"
rule rejected `(` at the start of ANY top-level statement to stop a
collection being used as a graph name, but fired before
subject-position could be distinguished, so it also blocked the legal
`( 1 2 3 ) :p ( 4 5 6 ) .`. RC3 removed entirely — TriG's grammar
makes collection-as-graph-name unreachable anyway (a collection can
only be followed by a predicateObjectList, never `{`), so the case is
still rejected, now for the right reason. [#434](https://github.com/danbri/factoidal/issues/434):
`Parser.Turtle.fst`'s `parse_predicate_object_list_rev` /
`parse_trailing_semicolons_rev` treated `.`/`]`/`;`/`|` as
list-terminators but omitted `}`, so `...;}` tried to parse `}` as a
predicate; `}` (0x7D) added to both checks. SCORES: regression 11
pass, 0 fail (of 11) — was 5 pass, 6 fail; rdf-trig 356 pass, 0 fail
— was 354 pass, 2 fail; RDF total back to 1030 pass, 0 fail, 1
unsupported (of 1031) — and that number is now EARNED under strict
grading plus real rdf-mt checks, unlike the 1031/0 it replaced.
SPARQL 631/0 unchanged. Both modules verify clean, no admits, no
--lax, no new assume vals.

**[#436](https://github.com/danbri/factoidal/issues/436) FIXED: CI now VERIFIES the proofs (2026-08-14, branch
`ci-verify`)**: the PR gate ran `build-ocaml.sh extract` + `compile`
and never `make verify`, so a proof could break silently — the
mechanism behind [#422](https://github.com/danbri/factoidal/issues/422). Happy discovery: `formal/fstar/Makefile`'s
`verify` target already globs `$(wildcard *.fst)` from DISK, so it
covers all 231 files including the 15 absent from ALL_MODULES (216
entries) — it was simply never connected to CI. New workflow
`.github/workflows/verify-fstar.yml` runs `make -j verify` under z3
4.13.3, no --lax, and FAILS the PR on any verification failure.
Caching: its own GitHub Actions cache key for the `.checked` files,
deliberately NOT shared with the other workflows (theirs cache only
the 216-module list, which would leave the 15 cold every run) and
deliberately NOT the `checked-cache` git branch (that is a local
session-restore mechanism, not a gate input). BOTH DIRECTIONS
VALIDATED — the point, given this session's vacuity findings: clean
tree PASSES (exit 0, all 231 files, 22.7 min on 4 cores from a
half-warm cache), and a deliberately falsified lemma in a scratch
copy FAILS (exit 2, "Could not prove post-condition"). A gate that
cannot fail is the same trap in another costume. Honest gap: a fully
cold run is estimated 45-60+ min and was not measured; it happens on
first run and after F* version changes. Coverage was NOT narrowed to
make the job fast.

**[#430](https://github.com/danbri/factoidal/issues/430) FIXED + two coverage findings (2026-08-14, branch
`vacuity-tool`)**: `tools/negative-test-vacuity.py` crashed with
`TypeError: int + str` — a KEY CLASH: the per-suite dict uses
`"error"` for a COUNT, while the whole-manifest-load-failure early
return used the same key for a MESSAGE. Renamed to
`manifest_error`; added a "suites that could not be loaded" table
and a stderr warning, because before this a failed load reported 0
across every count, indistinguishable from "this suite has no
negative tests". Tool now runs to completion. VALIDATED BOTH WAYS:
emptying a premise to zero triples flips a real test's verdict to
`vacuous/closure-adds-nothing`; the current run's 3-of-19 rdf-mt
vacuous count matches the last known-good state recorded in
`skills/measuring-inference`. 🔴 FINDING 1 — the tool is BLIND to
the [#429](https://github.com/danbri/factoidal/issues/429) class and its in-code justification is WRONG about why:
it excludes positive-syntax tests reasoning that "a reject-all
parser fails these", but [#429](https://github.com/danbri/factoidal/issues/429)'s actual bug was IGNORE-AND-PASS, which
that argument does not cover. FINDING 2 — its `vacuous` verdict for
3 `mf:result false` tests is correct for the CLI path it measures
but no longer describes the graded suite: [#333](https://github.com/danbri/factoidal/issues/333)'s D-inconsistency
detector lives in the runner's dispatch and is unreachable via
`factoidal entail`/`--dump`. Also: `rdf12-semantics` cannot be
audited at all because its vendored manifest fails to load on the
SAME undeclared `test:` prefix typo the [#334](https://github.com/danbri/factoidal/issues/334) work found at
`rdf-semantics/manifest.ttl:247` — one upstream typo now blocks two
tools.

**[#443](https://github.com/danbri/factoidal/issues/443) + [#339](https://github.com/danbri/factoidal/issues/339) + [#445](https://github.com/danbri/factoidal/issues/445) + [#446](https://github.com/danbri/factoidal/issues/446) FIXED (2026-08-14/15)**: three serialization
defects (plus two latent siblings of [#445](https://github.com/danbri/factoidal/issues/445) found while fixing it), none
of which any W3C suite could see, plus one build-gate failure found on
the way. [#445](https://github.com/danbri/factoidal/issues/445) landed 2026-08-15 on branch `utf8-store`; the other three
landed 2026-08-14 on branch `claude/autoexec-scratchpad-assess-37oeok`.

🔴 **[#443](https://github.com/danbri/factoidal/issues/443) (with [#339](https://github.com/danbri/factoidal/issues/339)) — the store DESTROYED literals.** An RDF literal
whose lexical form held `"`, LF or `\` did not survive `import` ->
`query`: it returned as `_:cottas_decode_oor`. Three of six literal
classes lost. Cause: `RDF.Pretty.term_to_ntriples` wrote lexical forms
verbatim. Documented in two banners as "display, not wire" — while all
THREE of its callers were wire paths (`--dump`, the COTTAS object
column, the same column in the npm build). The `--dump` half was filed
in July as [#339](https://github.com/danbri/factoidal/issues/339) and pinned XFAIL; its scope table listed the other
SERIALIZERS and concluded "one function, not a systemic gap" — correct
about serializers, and the missing column was the other CALLERS.
DELETED rather than fixed: an escaping version is byte-identical to
`RDF.NQuads.Serialize.nq_term_to_string`, and a second name for one
rendering is what let them drift. **Trust-surface finding for this
registry: `RDF.NTriples.RoundTrip.fst` was SOUND throughout and simply
did not cover the function the CLI called. Proof coverage is a property
of the WIRING, not only of the statement** — the same shape as the
vacuity findings ([#333](https://github.com/danbri/factoidal/issues/333), [#429](https://github.com/danbri/factoidal/issues/429)). Recorded as hazard #25.

✅ **[#445](https://github.com/danbri/factoidal/issues/445) — the store corrupted ALL non-ASCII, FIXED 2026-08-15 (branch
`utf8-store`).** Found while validating [#443](https://github.com/danbri/factoidal/issues/443), by reading the store bytes
rather than the result table. `RDF.Bytes.bytes_of_string =
String.list_of_string` yielded CODEPOINTS; each was written as
`codepoint land 0xFF`. Verified against the stored bytes in four
scripts: `café`→`caf\xe9`, `λόγος`→`\xbb\xcc\xb3\xbf\xc2`, `日本語`→
`\xe5,\x9e`, `🎉`→`\x89`. Note the middle one: U+672C truncated to
`0x2C`, a literal COMMA inside a stored token — this could change how a
token PARSED, not only what it said. A second defect on the same path:
`BaseWriter.fst:177` wrote the length prefix as `write_uvarint
(String.length s)`, and F*'s `String.length` counts codepoints while the
payload is bytes; the two coincide for ASCII, which is why nothing
noticed. The property that would have caught all of it —
`bytes_to_string (bytes_of_string s) == s` for arbitrary `s` — is now
PROVEN, unconditionally (`RDF.Bytes.lemma_bytes_to_string_of_bytes_of_string`),
built on `Parser.FastString.Spec.utf8_decode_all_utf8_bytes_identity`
(landed 2026-08-11, itself once listed "parked" in that module's own
banner — the fix this issue needed had already landed one layer down,
just not wired up here yet). `RDF.Bytes.byte` is now a REFINED type
(`c:FStar.Char.char{int_of_char c < 256}`), so the old
`bytes_of_string = String.list_of_string` no longer typechecks — the
type now enforces the invariant its comment always claimed. Beyond the
three sites this issue named, the same audit found and fixed a fourth
live site in `BaseWriter.fst` (`write_dict_entry`, the RLE_DICTIONARY
path — live for real object literals, not just metadata) and a fifth,
`string_lengths`, feeding the DLBA length block that is the PRIMARY
value-storage path for all four columns in the v1 writer. Fixing
`RDF.Bytes` also turned up the identical latent defect, self-consistent
only under the old wrong `bytes_of_string`, in two sibling modules that
share its primitives: `RDF.Store.Columnar.DeltaLog.fst` (the durable-
UPDATE delta log — LIVE) and `RDF.CottasStore.DictWriter.fst` (a legacy
`.dict` writer with zero current callers) — both surfaced as build
failures, not by inspection, and both fixed the same way
(`field_byte_len`/`tok_byte_len` helpers replacing every
`String.length` used as a byte length or well-formedness bound).
Owner decision (2026-08-15, verbatim: "Version-bump the COTTAS header -
nobody is using our software yet except me... I can nuke and rebuild
it"): the COTTAS base file's `FileMetaData.version` field is now
stamped `445` by the writer and REJECTED by the reader if it doesn't
match — no migration path, no silent misread of a pre-fix store. The
XFAIL entry (`UTF8-STORE` in `tests/known-defects/run.sh`) is retired;
the standing regression pin moved to
`tests/local/cli_literal_escape_roundtrip.sh`.

✅ **[#446](https://github.com/danbri/factoidal/issues/446) — `xmlns:=` malformed default namespace.** Found by the Jena
differential harness on its FIRST RDF/XML run. `render_ns_decls` emitted
` xmlns:<p>="<u>"` for every declaration; the default namespace has an
empty prefix, so it wrote `xmlns:="..."`, which is not a legal XML
attribute name. Both witness files are commented OUT of the vendored
manifest, so `w3c_runner --rdf rdf-xml` never discovers them and
166 pass, 0 fail was accurate while this was live. **That is the
argument for differential testing in one sentence: a second engine
reached an input our own manifest excludes.** Fixed by a case split in
the render step. Open follow-up recorded on the issue: we hoist a
VISIBLY-USED default namespace to the root, Jena attaches it to the
element that uses it; the manifest's "implementation dependent" carve-out
covers only NOT-visibly-used namespaces, so placement is outside it and
wants a read of exc-c14n §2.

✅ **[#444](https://github.com/danbri/factoidal/issues/444) — Parser.XML was a marginal proof.** A full extract went red
on a module with no change to it: `parse_attributes`'s `fuel - 1` under
an `if fuel = 0` guard failed the subtyping check. Four causes ruled out
first, each of which would have been a real regression (the [#443](https://github.com/danbri/factoidal/issues/443) change:
outside its cone; CPU contention: reproduces alone; a stale
`Parser.FastString.fsti.checked`: regenerated, still red; the
`utf8_bytes_singleton` lemma landed the same day: reverted Spec.fst to
its parent, still red). Verifies at 60. Scoped `#push-options` around
that one function, no `--lax`, no `--admit_smt_queries`. A proof this
close to the line is a latent CI flake that fails with text reading like
a semantic regression; sweeping the corpus at a REDUCED rlimit would find
the rest before they fire.

**Jena differential harness extended to five formats** (from [#317](https://github.com/danbri/factoidal/issues/317)).
Labelled counts: turtle 317 files — 222 agree-parse, 91 agree-reject,
0 disagree, 4 either-side-error; ntriples 72 — 43/29/0/0; trig 357 —
242/111/0/4; nquads 89 — 55/34/0/0; rdfxml 173 — 128/31/4/10.
Combined 1008 files — 690 agree-parse, 296 agree-reject, 4 disagree,
18 either-side-error. Every non-agreement adjudicated: 13 are inputs the
W3C test says must fail and we correctly reject while Jena accepts;
2 are files where OUR output matches the official expected `.nt` and
Jena's does not; 2 are [#446](https://github.com/danbri/factoidal/issues/446); 5 are manifest-disabled. The harness was
PROVEN able to fail three ways (reinstated [#434](https://github.com/danbri/factoidal/issues/434) bug -> either-side-error;
one-value difference -> disagree; extra named graph -> caught). Its
declared blind spot: blank-node GRAPH names are pooled per side, so
content moving between two such graphs can hide (3 of 357 TriG files).

**Suite state after all of the above, re-measured on the rebuilt
binary**: SPARQL 1.1 631 pass, 0 fail (of 631); RDF 1.1 1030 pass,
0 fail, 1 unsupported (of 1031), rdf-xml 166 pass, 0 fail; RDF 1.2
242 pass, 0 fail (of 242); RDF 1.2 c14n 82 pass, 0 fail (of 82);
RDF 1.2 Semantics 41 pass, 3 fail, 3 skip (of 47, pre-existing and
already documented under [#305](https://github.com/danbri/factoidal/issues/305) P9); SPARQL 1.2 254 pass, 0 fail (of 254).
Every one byte-identical to its committed baseline — the serializer
change moved no score. OWL catalogs NOT re-measured: the run was capped
at 3000s and `semantics-direct` alone budgets 9000s, so the partial
logs were reverted rather than committed as scores.

**[#362](https://github.com/danbri/factoidal/issues/362) SR-4 FIXED (2026-08-16, branch `sr4-order`)**: `sparql_order`
read a numeric parse failure as a universal tie, breaking transitivity —
one ill-typed literal silently misordered the VALID numerics around it
(witness: 10, zzz, 3, 5, abc, plain). Owner-adjudicated rule, measured
against Jena 6.2.0: valid numerics numeric, ill-typed AFTER them,
lexical tie-break among ill-typed (datatype ignored). New
`sparql_order_numeric` (SPARQL11.Algebra.fst:5172); `numeric_compare`
unchanged for its other callers. Proofs in
SPARQL11.Algebra.Refinement.fst: `lemma_sparql_order_numeric_frag_totality`
+ `_trans` discharge `theorem_sort_solutions_sorted`'s hypotheses on the
`er_num_plain` fragment (ER_Num, or unparseable ER_Dec/ER_Dbl — the
issue's witness shape). OPEN: valid decimal-vs-double scale
normalization not covered; two same-text different-datatype unparseables
tie BY DESIGN (matches Jena). Witness after fix: 3, 5, 10, zzz, abc,
plain. Pin: cli_orderby_illtyped_numerics.sh, 4 pass, 0 fail (out of 4),
anti-vacuity arm included. Agent's comparator sweep found NO other
None-means-tie defect (dt_cmp, csvw_num_cmp, xn_compare, rat_cmp all
safe — xn_compare's caller already does the side-aware fix pattern).
Also surfaced: E_Var falls back to PLAIN LITERAL on failed integer
parse but stays NUMERIC on failed decimal parse — separate asymmetry,
follow-up issue owed. Gates on the merged binary: SPARQL 1.1 631 pass,
0 fail (of 631); RDF 1.1 1030 pass, 0 fail, 1 unsupported (of 1031);
SPARQL 1.2 254 pass, 0 fail (of 254); escape pin 5 pass, 0 fail — the
[#445](https://github.com/danbri/factoidal/issues/445) fix survives the merge on the same binary. NOTE per [#448](https://github.com/danbri/factoidal/issues/448): no W3C
test exercises an ill-typed numeric, so the suites certify only
no-regression; the pin is the evidence.

**[#448](https://github.com/danbri/factoidal/issues/448) wave 1, module 1: Parquet.Footer lifted merely-tot ->
algorithm-correctness (2026-08-16, branch `assure-parquet-footer`)**:
`lemma_version_field_roundtrip` (RDF.CottasStore.BaseWriter.fst:1272)
proves the on-disk READER returns what the WRITER wrote for the
FileMetaData version field: `parse_file_metadata_version_hex
(bytes_to_hex (write_field_i32 1 0 cottas_format_version)) == Some
cottas_format_version`. This is the fact the [#445](https://github.com/danbri/factoidal/issues/445) format gate depends
on — nothing previously forced writer and prober to agree, and a
disagreement would have made the gate reject every store or accept
every store, silently. Proved for the DEPLOYED value 445, not general
`v` (needs induction over the varint writer's recursion — documented
in-code as follow-on, and the narrow lemma is a true fact about the
shipping format, not a weakened general one). The decode logic was
refactored out of the probe function so the lemma names the EXACT
function the reader calls, not a copy. No admits, no --lax. Twelve
helper lemmas; F* needed three explicit congruence helpers to chain
rewriting steps (recorded in the lemma's comment). CLI pin
`parquet_footer_version_gate_roundtrip.sh` (3 pass, 0 fail of 3)
covers the file-I/O step the lemma cannot reach: real store via the
real CLI, then one byte flipped on disk must reject. Tier verified by
running the actual classifier, not asserted. 🔴 FINDING (rule #11):
`parquet_read_tail_hex`/`parquet_read_range_hex` realisations carry an
OCaml hex-encode step (`__mim2_hex_encode`) with no F* spec twin and
no hash-witness test — byte-layout logic in glue; follow-up owed.
Gates: RDF 1030 pass, 0 fail, 1 unsupported (of 1031); escape pin 5
pass, 0 fail; unit suite 20 pass, 28 fail (of 48) = baseline exactly.
📊 [#448](https://github.com/danbri/factoidal/issues/448) baseline moves 129 -> 128 merely-tot (of 231).

**[#448](https://github.com/danbri/factoidal/issues/448) wave 1, module 2: HDT.Container lifted merely-tot ->
algorithm-correctness (2026-08-16, branch `assure-hdt-container`)**:
HDT.Container is a pure READER (container skeleton framing over the
HDT v1 binary format -- cookie/format/props/CRC16 control-info blocks,
PFC/log-array/bitmap section-boundary arithmetic), no writer side, so
the writer/reader round-trip template (module 1's pattern) does not
apply. Chose instead the "only reads" template: prove corruption is
REFUSED, not silently decoded as noise. Two lemmas:
`lemma_parse_control_info_rejects_bad_cookie` -- a mismatched 4-byte
`$HDT` cookie makes `parse_control_info` return `None`, proved by
direct unfolding (`()`), no induction, no congruence bridging needed
(unlike module 1's version-field round trip, every hypothesis here is
a bare `byte_get` equality feeding a `match` the SMT encoding resolves
directly). `lemma_bad_global_cookie_rejects_container` is the
corollary at the shipping entry point every consumer actually calls:
a corrupted Global cookie at file offset 0 fails the WHOLE
`hdt_parse_inventory_hex`, not just the Global control-info block, by
forwarding `parse_control_info a 0`'s `None` verbatim. Both relate two
named shipping functions (`parse_control_info` /
`hdt_parse_inventory_hex`, plus `byte_get`) with no declarative
relation, so the classifier reads algorithm-correctness. `pfc_type`
refined from bare `nat` to `(t:nat{t = 2})` per the [#445](https://github.com/danbri/factoidal/issues/445) template --
was a comment-only invariant ("2 = Plain Front Coding"). Assume-val
audit: HDT.Container itself carries ZERO `assume val`s -- all file
bytes cross the boundary through Parquet.Footer's
`parquet_read_range_hex`, already audited under module 1's finding
above (nothing new here). CLI pin: `bin/hdt-probe/check.sh` gained a
corrupted-global-cookie arm (flip byte 0 of a real vendored `.hdt`
fixture, 0x24 -> 0x25, require the probe's loud `PARSE FAILED` and
rc=1) alongside the pre-existing truncation arms; 75 pass, 0 fail (of
75) end to end, plus `tests/local/hdt_stage4_parity.sh` (backend
parity against the same fixture) at 6 pass, 0 fail (of 6), both
unaffected by the refinement or the new lemmas since the shipping
functions' extracted behaviour is byte-identical. Tier verified by
running the actual classifier, not asserted. Gates: RDF 1030 pass,
0 fail, 1 unsupported (of 1031); escape pin 5 pass, 0 fail (of 5);
unit suite 20 pass, 28 fail (of 48) = baseline exactly.

**[#448](https://github.com/danbri/factoidal/issues/448) wave 1, module 3: RDF.Turtle.Serialize lifted merely-tot ->
internal-refinement (2026-08-16, branch `assure-turtle-serialize`)**:
new declarative relation `compacts_to_pname_safe` + lemma
`lemma_ts_abbreviate_iri_pname_safe` — the IRI-abbreviation step either
emits the full `<iri>` form or the compacted local name is PN_LOCAL-safe
per the Turtle grammar. No admits. ESCAPING QUESTION ANSWERED: the
module SHARES `RDF.NQuads.Serialize.nq_escape_literal` — no second
escaper exists, so no [#443](https://github.com/danbri/factoidal/issues/443)-shape divergence risk (checked, not
assumed). FINDING, verified by experiment: the term-level round-trip
`nq_escape_literal "a" == "a"` is NOT provable by normalization —
Error 19, the same computation wall RDF.NTriples.RoundTrip.fst hit,
STILL present after the 2026-08-10 change intended to clear it;
assert_norm witness batteries hit the same wall. What proof cannot
reach, the pin covers: `turtle_pretty_serialize_roundtrip.sh` (4 pass,
0 fail of 4) re-reads `--dump-turtle` output over the 10-literal
fixture with an anti-vacuity arm. Zero assume vals. Tier from a fresh
classifier run WITH --json. Gates: RDF 1030 pass, 0 fail, 1 unsupported
(of 1031); escape pin 5 pass, 0 fail; turtle_pretty_regressions 17
pass, 0 fail (of 17); unit suite at baseline.

**[#448](https://github.com/danbri/factoidal/issues/448) wave 1, module 4 (last of wave 1): RDF.Canonical lifted
merely-tot -> internal-refinement (2026-08-16, branch
`assure-rdf-canonical`)**: new declarative relation `is_issuer_label`
(existential: label == prefix ^ nat_to_string n) + `issuer_labels_wf`
+ five lemmas (`lemma_empty_issuer_wf`, `lemma_empty_temp_issuer_wf`,
`lemma_issue_fresh_preserves_wf`, `lemma_issue_identifier_preserves_wf`,
plus the two internal-refinement theorems the classifier counted:
`lemma_issue_fresh_label_shape`, `lemma_issue_identifier_fresh_label_shape`)
— proves every blank-node label `issue_identifier`/`issue_fresh` ever
mint, from `empty_issuer`/`empty_temp_issuer` onward, matches the
"_:c14nN" / "_:bN" shape the module banner already claimed in prose.
Refines the module banner's comment-claimed label format into a
checked type ([#445](https://github.com/danbri/factoidal/issues/445) template), needing ZERO string-content computation
(existential witness = the issuer's own counter) — sidesteps the
SMT-unfolding wall, confirmed directly against THIS module's own
`nat_to_string`/`digit_char` (Error 19 on both, even though neither
touches FastString's opaque primitives — the wall found by module 3
is broader than "FastString is opaque"; `assert_norm` succeeds only on
GROUND terms, so it cannot discharge the universally-quantified
injectivity goal a full no-duplicate-labels proof would need).
DETERMINISM/SERIALIZER QUESTIONS ANSWERED: full bnode-relabelling
determinism (candidate 1, the property VC signing depends on) and full
re-parse well-formedness (candidate 2) were investigated and rejected
as one-commit F* targets — determinism moved to
`cli_rdfc10_relabel_determinism.sh` (5 pass, 0 fail of 5: same-input
twice byte-identical, bnode-relabelled isomorphic variant
byte-identical to the original, anti-vacuity arm requiring a
non-isomorphic variant to differ). RDF.Canonical does NOT delegate to
`RDF.NQuads.Serialize`'s canonical functions (`nq_canon_term` etc.) —
it carries its OWN `canon_term`/`escape_lit` (the [#443](https://github.com/danbri/factoidal/issues/443) two-
implementations shape); investigated the divergence and found it real
but each side targets a DIFFERENT W3C spec (RDFC-1.0 dataset
canonicalization vs. the separate "RDF 1.2 canonical N-Quads" lexical
form) — `nq_canon_term` lowercases language tags and escapes the
U+FFFE/U+FFFF BMP noncharacters, `RDF.Canonical`'s does neither, yet
the 86/86 rdfc10 suite passes either way, so this is duplicated logic
that could drift, not a demonstrated bug. ASSUME-VAL AUDIT: also
refined `hash_sha256`/`hash_sha384`'s comment-claimed digest lengths
(64/96 hex chars) into a checked return-type refinement (erases at
extraction). Neither hash is HACL*-bound — both wire to
`Fstar_pure_hashes`, a hand-rolled pure-OCaml SHA-2 (issue [#63](https://github.com/danbri/factoidal/issues/63),
already tracked non-silently in `skills/crypto-policy/SKILL.md`
as "HACL* is NOT yet in use", not newly introduced here). Tier from a
fresh classifier run WITH --json:
`"assurance_tier": "internal-refinement"`, `"merely_tot": false`,
`assume_val_active: 2` (hash_sha256, hash_sha384), unchanged. Gates:
rdfc10 86 pass, 0 fail (of 86); RDF 1030 pass, 0 fail, 1 unsupported
(of 1031); escape pin 5 pass, 0 fail (of 5); relabel-determinism pin 5
pass, 0 fail (of 5); unit suite 20 pass, 28 fail (of 48) = baseline
exactly, no deltas. Wave 1 ([#448](https://github.com/danbri/factoidal/issues/448)) is now complete: Parquet.Footer
(module 1), HDT.Container (module 2), RDF.Turtle.Serialize (module
3), RDF.Canonical (module 4) all lifted merely-tot -> internal-
refinement.

**[#448](https://github.com/danbri/factoidal/issues/448) wave 2, module 1: Parser.BallyhooCOTTAS audited 17-of-17;
4 assume vals LIFTED to F* (2026-08-16, branch
`assure-ballyhoo-cottas`)**: `cottas_lookup_named_graph`,
`cottas_estimate`, `cottas_predicate_present_in_graph`,
`cottas_graph_candidates_for_predicate` are now real F* code — each
was a pure derivation of other store operations with no I/O of its
own. `cottas_estimate = length (cottas_search ds bound)` makes an
invariant F*-visible that previously lived only in glue ("estimate is
an exact count, never a heuristic"). Module assume-vals 17 -> 13; all
13 remaining are rule-#11(b) delegation (file I/O + hashtable lookups
over data resolved at open). Tier stays merely-tot and that verdict is
HONEST — boundary glue with no theorem to state beyond totality.
🔴 MAIN FINDING: `cottas_runtime.sh:93-184` hand-parses RDF term
syntax in OCaml (find_unescaped_quote / unescape_literal /
parse_literal_token / parse_subject...) — iron rule #4 violation, not
commit-sized, needs an F*-side `parse_stored_term` + column-decode
contract change. 🟡 minor: `cottas_search` re-implements the
3-way graph-bound semantics its .fst doc specifies; `build_summary`
hardcodes CE_Delta. FIXED IN PASSING (pre-existing): the glue's
stub-deletion anchors matched type-qualified signatures that fresh
extraction now prints differently (RDF_Graph_Executable.subject ->
RDF_Term.subject), so 10 raw stubs survived and would have SHADOWED
the real implementations on any from-scratch rebuild — re-anchored on
stable failwith text. FIXTURE REGENERATED: store_capabilities_sample
.cottas was pre-[#445](https://github.com/danbri/factoidal/issues/445) format and the version gate now (correctly)
rejects it; rebuilt from its documented source
(tests/local/data/cottas_sample.nq) with the current writer; smoketest
opens it (5 quads, 1 row group). Gates: RDF 1030 pass, 0 fail,
1 unsupported (of 1031); escape pin 5 pass, 0 fail; footer pin 3 pass,
0 fail; unit suite at baseline. Project assume-val total 133 -> 129.

**[#448](https://github.com/danbri/factoidal/issues/448) wave 2, module 2: Parser.BallyhooHDTQ audited 17-of-17;
4 assume vals LIFTED to F* (2026-08-16, branch
`assure-ballyhoo-hdtq`)**: `hdtq_lookup_named_graph`,
`hdtq_estimate`, `hdtq_predicate_present_in_graph`,
`hdtq_graph_candidates_for_predicate` are now real F* code — the same
four names, same derivations, as module 1's COTTAS lift
(`hdtq_estimate = length (hdtq_search ds bound)`, etc.). Module
assume-vals 17 -> 13; all 13 remaining are rule-#11(b) delegation
placeholders. 🔴 MAIN FINDING, different in kind from module 1's:
this module is DEAD END TO END. `grep -rl "hdtq_"
experimental_ocaml_glue/*.sh` returns nothing — there is no glue
script at all (not hand-parsed terms like [#454](https://github.com/danbri/factoidal/issues/454)'s COTTAS finding;
simply absent), so every one of the 13 remaining assume vals extracts
as a raw `failwith "Not yet implemented"` stub, and no other .fst
file calls any hdtq_* function (only `open Parser.BallyhooHDT` for
its TYPES, never its functions). Contrast COTTAS: RDF.CottasStore.fst
and RDF.Store.Loader.fst call into it, so it is live. Per [#448](https://github.com/danbri/factoidal/issues/448)'s own
per-module deliverable ("state ONE correctness property the module's
consumers rely on ... a module where no property can even be stated
is a finding, not a skip") — this module's finding IS that sentence:
it has no consumers to state a property about. 🟡 secondary finding:
`hdtq_close_dataset_store` (assumed, `Tot unit`, unreferenced) has NO
extracted OCaml symbol at all — F* elides an unused, unrealised,
unit-returning assume val rather than stubbing it (same elision
`Parser.BallyhooHDT.fst`'s *defined* `hdt_close_graph_store = ()`
gets, for the same reason). A future caller would hit a link error,
not a controlled runtime failwith. Sibling question answered:
`Parser.BallyhooHDT` carries 0 assume vals as of its 2026-07-06 stage
4 landing and needs no further wave-2 pass; `BallyhooHDTQ` does not
call into its already-verified per-graph reader today, which is a
design opportunity for whoever wires this module up, not an audit
action. No stub-anchor staleness (recurrence check 2): N/A, there are
no anchors to go stale. Forced `extract --force-full`; every hdtq_*
symbol appears exactly once in the fresh .ml. Tier from a fresh
classifier run WITH --json: `"assurance_tier": "merely-tot"`,
`"merely_tot": true`, `"assume_val_active": 13`
(`assume_other_active: 1` for the opaque `hdtq_handle` type) — HONEST,
boundary glue that doesn't exist yet has no theorem to state. Gates:
RDF 1030 pass, 0 fail, 1 unsupported (of 1031); hdt-probe 75 pass,
0 fail (of 75); hdt-stage4-parity 6 pass, 0 fail (of 6); escape pin
5 pass, 0 fail (of 5); unit suite 20 pass, 28 fail (of 48) = baseline
exactly, no deltas. Project assume-val total (active, per classifier):
125.

**[#448](https://github.com/danbri/factoidal/issues/448) wave 2, module 3: RDF.CottasStore.OnDiskRuntime audited
15-of-15; 0 lifted, 0 fixed — module is DEAD END TO END despite a
CLEAN realising glue (2026-08-16, branch `assure-ondisk-runtime`)**:
🔴 MAIN FINDING, contradicts this module's own dispatch brief ("the
LIVE on-disk query runtime... traversed by every `--data-cottas`
query"): it is not live. `grep -rn "OnDiskRuntime\." formal/fstar/
*.fst` outside the module's own file returns nothing — no other .fst
calls any `ondisk_*_indexed` / `ondisk_*_via_registry` function, and
the LazyDictRegistry it reads through (`RDF.CottasStore.
LazyDictRegistry.fst`) has no consumer outside this module either.
The production `--data-cottas` path (`RDF.Store.Capabilities.Cottas.
fst`'s `caps_of_cottas`) runs entirely through the token-shaped
`cottas_ondisk_search_tok` / `_estimate_tok` / `_count_exact_tok`
family in `RDF.CottasStore.fst` — real `Tot` functions, no assume
vals — per that module's own 2026-07-06 comment: the id-based
dictionary path was retired from the hot path in favour of direct
term<->token serialisation. The design doc this module cites
(`docs/designissues/2026-05-13-issue-118-cottas-ondisk-runtime-
retirement-plan.md`) already flagged this as "partially overtaken by
events" and named three non-production consumers still on the
id-based path (a tests/unit baseline, `cottas_ondisk_smoketest`,
`factoidal-explain`) — re-checked here and ALL THREE have since
migrated to `_tok` calls; none reference `OnDiskRuntime` or
`ondisk_*_indexed`/`_via_registry` today, so even that residual
consumer list is stale. The `.github/test-suites/local-cottas-
corpus.yaml` "direct-trigger" association the classifier surfaces is
a file-glob CI trigger-path listing (any `RDF.CottasStore*.fst`
change re-runs the suite), not evidence of exercise — verified by
reading the glob, not by suite content. 🧭 decision needed from
owner/maintainer, not inferred here: retire (delete the 15 assume
vals + `cottas_ondisk_runtime_indexed.sh` + the orphaned LazyDict/
LazyDictRegistry chain, ~2 commit-sized module 4/5 follow-ups) vs.
keep as scaffolding for the file's own noted "Future work (Phase
2.5h) re-introduces ondisk_search_indexed... once a perf-fast variant
lands again." Hazard 1 (hand-parsed RDF terms): CONFIRMED, same site
as [#454](https://github.com/danbri/factoidal/issues/454), reached only if this dead path is ever wired up —
`parse_iri_token` / `parse_literal_token` / `parse_subject_str` /
`parse_object_str` (`cottas_ondisk_runtime.sh:126-215`) populate the
Hashtbl tables that `ondisk_*_indexed`'s realising glue
(`cottas_ondisk_runtime_indexed.sh`) forwards to; per the brief, not
fixed here — filed as the same finding, second reachability path, not
a new site. Brief named `cottas_ondisk_runtime.sh` as this module's
glue; the module's actual realiser is the separate, smaller
`cottas_ondisk_runtime_indexed.sh` (161 lines) — a clean rule-#11(b)
dispatch shim with no parsing/byte-layout logic of its own; it calls
INTO `cottas_ondisk_runtime.sh`'s Hashtbl runtime for 8 of the 15,
and into `RDF.CottasStore.LazyDict`/`LazyDictRegistry` (separate
modules' own assume vals) for the other 7 — corrected here, not
silently substituted. Hazard 2 (stale stub-deletion anchors): NOT
FOUND — forced `rm` + fresh single-module extraction, 15/15 stubs
present exactly once pre-patch, all 15 anchors matched (`subn` count
1, zero WARN) post-patch, zero leftover `failwith "Not yet
implemented"` text, 15 unique `let ondisk_*` bindings post-patch, and
the freshly regenerated `.ml` is byte-identical to the committed one
(`git diff` empty) — this glue's anchors are healthy, unlike module
1's sibling. Lifts: NONE — the 8 indexed vals are asymmetric
encode(token->id)/decode(id->token) pairs over two different Hashtbl
directions built once at open time; there is no pure relationship
between them expressible without the ML-effected Hashtbl read itself
(unlike modules 1/2's `estimate = length(search)` shape), and the
module has no `_estimate`/`_search` pair at all (comment confirms:
those were retired to F* separately, before this module existed).
Type refinements: NONE — no comment in the module claims an
invariant its `option`/`nat` signatures don't already state (`id`
range and path-registration are already `option`-typed absences, not
stronger claims). Trace logging (`[qof3-trace]`/`[bet7-trace]`):
purely additive `Printf.eprintf` diagnostics in both glue files; none
gate control flow — confirmed by reading every call site. Tier from a
fresh classifier run WITH --json: `"assurance_tier": "merely-tot"`,
`"merely_tot": true`, `"assume_val_active": 15`,
`"foundational_path": false` — HONEST for a module with 15 assume
vals and 0 theorems, though the tier label alone does not surface the
dead-code finding above; that required call-graph grep, not the
classifier. No .fst changed, so no extract/compile/gate rerun was
needed; targeted `make verify-RDF.CottasStore.OnDiskRuntime` reverified
clean under z3 4.13.3, no `--lax`. Project assume-val total (active,
per classifier): 125, unchanged (no lift landed).

**[#448](https://github.com/danbri/factoidal/issues/448) wave 2, module 4: RDF.CottasStore.OnDiskIndex audited 7-of-7;
1 pure property landed (2026-08-16, branch `assure-ondisk-index`)**:
LIVE, contrary to modules 2/3's dead-end findings — confirmed by
`grep -rn "RDF_CottasStore_OnDiskIndex\." formal/fstar/ocaml-output/
*.ml`: called from `RDF_CottasStore.ml` (dict_decode_token/
dict_encode_token/read_dict_header/read_presence_header/Vav3_mmap —
the on-disk query path), `RDF_CottasStore_PresenceBitmap.ml`,
`RDF_CottasStore_CompoundPresenceBitmap.ml`,
`RDF_Store_Columnar_OffsetIndex.ml`,
`RDF_Store_Columnar_SubjectOffsetIndex.ml`. `RDF_CottasStore` is
called from `bin/factoidal-cli/factoidal_cli.ml`,
`bin/factoidal-http/factoidal_http.ml`, `bin/npm-entry/entry_jsoo.ml`.
`factoidal_http.ml`'s `prewarm_cottas_columns` calls
`Cottas_companion_boot.prewarm_via_companions` at boot (build-or-open
the 8 companion files); every on-disk triple-pattern lookup
thereafter goes through this module's dict encode/decode + presence
bit-test. Both import (lazy companion build on first open) and query
(every lookup) shipping paths reach it.

| assume val | role | verdict |
|---|---|---|
| `mmap_companion_open` | open+mmap a companion file, return byte length | (a) pure I/O |
| `mmap_companion_close` | release an mmap for a path | (d) DEAD — see finding below |
| `read_companion_u32_le` | LE u32 read from the mmap | (a) pure I/O |
| `read_companion_u64_le` | LE u64 read, with a native-int safety guard | (a) pure I/O — type gap, see below |
| `read_companion_byte` | single-byte read | (a) pure I/O |
| `read_companion_string` | byte-range slice to a string | (a) pure I/O |
| `companion_file_size` | stat-based existence+size, no content read | (a) pure I/O |

All 7 realise in one glue script,
`experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh`
(`Vav3_mmap`, `Unix.openfile` + `Bigarray.Array1` mmap held per-path
for the process lifetime) — rule-#11(a) conformant, no byte-layout or
semantic logic in the glue for these 7. 🔴 FINDING:
`mmap_companion_close` is declared and called from 4 sibling F*
modules (`RDF.CottasStore.PresenceBitmap.close_bitmap`,
`CompoundPresenceBitmap`, `RDF.Store.Columnar.OffsetIndex`,
`SubjectOffsetIndex` — each a one-line `mmap_companion_close h.*_path`
wrapper) but NONE of those 4 wrapper functions themselves have a live
caller, so F* extraction drops the entire chain: `mmap_companion_close`
has zero binding in the extracted `.ml` (confirmed: `grep close
RDF_CottasStore_OnDiskIndex.ml` finds nothing but the *reader's* own
`close_mmap`/`Unix.close` glue helper). Not a shipping gap — the glue's
own comment says the design is "held for the lifetime of the process,"
so the never-called close path is intentional, but the assume val is
genuinely unreachable at runtime, not merely unrealised.

Lift landed: `presence_bit_index_bounded` — pure nat-arithmetic lemma,
`rg < num_rgs /\ tok < num_tokens ==> rg*num_tokens+tok <
num_rgs*num_tokens` — wired load-bearing into `presence_test_bit`
(called, not decorative), tying the reader's computed `bit_index` to
the capacity the `.presence` writer sizes its buffer against
(`write_presence_file`'s `bytes = (rg_count*n+7)/8`). Same wave-1
HDT.Container "bounds respected" shape. Verified: `make
verify-RDF.CottasStore.OnDiskIndex`, z3 4.13.3, no `--lax`, no
`--admit_smt_queries`. Extraction confirms the lemma is proof-only —
`git diff` on the extracted `.ml` and the rest of `formal/fstar/` is
empty after a full rebuild; `presence_test_bit`'s extracted body is
byte-identical to before the lift (F* erases `Lemma`-typed calls).
🟡 type-gap finding, NOT landed this pass: `read_companion_u64_le`'s
signature is `Tot (option nat)` (unbounded), but the realisation
silently returns `None` whenever the top byte's high bit is set
(`b7 >= 0x80`, i.e. the on-disk value is `>= 2^63`) to avoid
truncating into OCaml's 63-bit native int — a real realisation
constraint the signature doesn't state. Tightening to
`Tot (option (n:nat{n < pow2 63}))` would make it F*-visible; deferred
to keep this pass one-commit-sized (would need a second
verify→extract→compile→gate cycle after the one already run here).

🔴 SECONDARY FINDING (hazard 2, stale anchor, this module's OWN glue,
Step C): the same glue script's later "Step C" block patches
`decode_subject_fast`/`decode_object_fast` in `RDF_CottasStore.ml` to
add a lazy-parse-on-cache-miss fallback; both anchors WARN "not found"
on every build (`[vav3-ondisk-index] WARN: decode_subject_fast anchor
not found`, same for `decode_object_fast`) because a *different*,
later-running sibling patch (`cottas_ondisk_z_lazy_open.sh`,
2026-07-19) already restructured both functions by removing the
`ensure_subjects_loaded`/`ensure_objects_loaded` calls Step C's anchor
expects — that same sibling patch's own comment documents WHY: the
id-based `cottas_ondisk_encode_subject`/`decode_subject`/
`encode_object`/`decode_object` F* functions these two OCaml functions
served were deleted from `RDF.CottasStore.fst` in the same 2026-07-19
commit ([#254](https://github.com/danbri/factoidal/issues/254)/[#118](https://github.com/danbri/factoidal/issues/118)), replaced by the token-shaped `_tok` family (same
retirement wave-2 module 3 found for `OnDiskRuntime`). Confirmed:
`decode_subject_fast`/`decode_object_fast` have zero callers anywhere
in `RDF_CottasStore.ml` or `bin/` today (`grep -n
"decode_subject_fast\b"` / `"decode_object_fast\b"` — only their own
definitions and stale comments). Not a live-path correctness bug (the
functions are dead), but the WARN is genuine drift: Step C has been a
silent no-op against a target that no longer exists since 2026-07-19,
never cleaned up. Not fixed here (glue cleanup is not this pass's
2 assume-val-realisation scope; flagging for whoever next touches this
glue file). Hazard 1 (hand-parsed RDF terms): CONFIRMED present via
composition, same site as [#454](https://github.com/danbri/factoidal/issues/454) — this module's own glue (bulk-load,
lines ~669-684) calls `Cottas_ondisk_runtime.parse_iri_token`
(defined in the separate `cottas_ondisk_runtime.sh`/`cottas_runtime.sh`
glue) to eagerly parse predicate/graph tokens during companion
bulk-load; per the brief, not fixed — third reachability path to the
same [#454](https://github.com/danbri/factoidal/issues/454) finding (module 1's COTTAS bulk path, module 3's dead
OnDiskRuntime path, now this module's live bulk-load path).

Stale-anchor check on the module's own 6 core stub replacements
(recurrence check 1): CLEAN — `grep -c "^let (mmap_companion_open|
read_companion_u32_le|read_companion_u64_le|read_companion_byte|
read_companion_string|companion_file_size)"` on the fresh `.ml` finds
exactly 6, each once, zero leftover `"Not yet implemented"` text.

Tier from a fresh classifier run WITH --json, corrected after a
misreading in an earlier draft of this entry (the classifier counts
the local `Lemma` declaration itself, not just its erased extraction
footprint): `"assurance_tier": "local-lemmas-only"` (moved from
`"merely-tot"`), `"local_refinement_lemma_count": 1`,
`"assume_val_active": 7` — HONEST for what landed: one local
correctness fact about the module's own arithmetic, zero W3C-
refinement or algorithm-correctness theorems (the lemma doesn't relate
two named shipping functions the way module 1/2's round-trip theorems
do, so it doesn't cross into `internal-refinement`/`algorithm-
correctness`). The tier move is real and modest — one honest rung up
from `merely-tot`, not the two-rung jump modules 1 and 3's own audits
describe for a round-trip- or corruption-rejection-shaped theorem.
Gates (full rebuild, no `.checked` cache in
this fresh worktree): RDF 1030 pass, 0 fail, 1 unsupported (of 1031);
`cli_literal_escape_roundtrip` 5 pass, 0 fail (of 5);
`parquet_footer_version_gate_roundtrip` 3 pass, 0 fail (of 3);
`cottas_ondisk_smoketest` opens `store_capabilities_sample.cottas`
cleanly, 5 quads; `tests/unit/run-all.sh` 20 pass, 28 fail (of 48) =
baseline exactly, no deltas. Project assume-val total (active, per
classifier): 125, unchanged (the lift is proof-only, does not retire
an assume val — `mmap_companion_close` stays counted as active despite
being unreachable, since the classifier counts declarations, not
reachability).

**[#448](https://github.com/danbri/factoidal/issues/448) "Delete & dedupe" — the DELETE half: three dead modules
removed (2026-08-17, branch `delete-dead-store-modules`)**: 🧹 the
owner decision on issue [#448](https://github.com/danbri/factoidal/issues/448), verbatim "Delete & dedupe", applied to
the three modules wave 2 audits above found dead end-to-end, each
re-verified dead again immediately before deletion (`grep` for the
OCaml module name and the F* qualified name found zero hits outside
each module's own files):

| module | assume val (before) | verdict |
|---|---|---|
| `Parser.BallyhooHDTQ.fst` | 13 | dead, no caller anywhere |
| `RDF.CottasStore.OnDiskRuntime.fst` | 15 | dead, superseded 2026-07-06 (module 3 above) |
| `Parser.BallyhooBloom.fst` | 0 | dead, zero callers anywhere |

Also removed: their `ocaml-output/*.{ml,cmi}` extracted artifacts, and
the OnDiskRuntime-exclusive glue script
`experimental_ocaml_glue/cottas_ondisk_runtime_indexed.sh` (confirmed
exclusive — its sibling `cottas_pagecache_indexed_runtime.sh` targets
`RDF.CottasStore.PageCache`, which has live callers besides
OnDiskRuntime, so that glue script stays). `RDF.Store.HDTTermCacheRegistry`
was explicitly NOT touched — it is live (called by the live
`Parser.BallyhooHDT.fst` reader); an earlier sweep had wrongly flagged
it dead, corrected by hand-check before this pass began.

Project assume-val total (active, per classifier): 125 -> 97 (-28,
exactly the sum of the three modules' own declared `assume val`s
above — no other module's count moved). `merely-tot` module count:
-3 for this deletion specifically (all three deleted modules were
classified `merely-tot`); the full inventory regeneration also shows
one unrelated, pre-existing, independent change (`RDF.CottasStore.
OnDiskIndex` moved `merely-tot` -> `local-lemmas-only`, a wave-2
module-4 lift already landed and described above, only now reflected
because the committed `assurance-inventory.json` had not been
regenerated since) — noted here so a reader diffing the committed
JSON against an older copy does not misattribute that unrelated
change to this deletion.

Rebuild: full `./build-ocaml.sh extract compile`, clean, no errors.
Gates: SPARQL 631 pass, 0 fail (of 631); RDF 1030 pass, 0 fail, 1
unsupported (of 1031); `hdt-probe` 75 pass, 0 fail (of 75);
`hdt_stage4_parity` 6 pass, 0 fail (of 6) — proves the LIVE HDT path
survived; `cli_literal_escape_roundtrip` 5 pass, 0 fail (of 5) —
proves the LIVE COTTAS path survived; `parquet_footer_version_gate_
roundtrip` 3 pass, 0 fail (of 3); `cottas_ondisk_smoketest` opens
`store_capabilities_sample.cottas` cleanly, 5 quads; `tests/unit/
run-all.sh` 20 pass, 28 fail (of 48) = baseline exactly, no deltas
(the 28 pre-existing build failures are unrelated missing-module
errors, e.g. `RDFS_Closure_SemiNaive`, not caused by this deletion).

Recovery path: the three modules' full source, their extracted `.ml`,
and the deleted glue script are all recoverable from git history —
see commit `0fa08a6f53b` "Delete three dead store/parser modules
([#448](https://github.com/danbri/factoidal/issues/448) delete half)" on branch `delete-dead-store-modules`.

## 8. Dep.Reachability — module-liveness deletion-safety ([#448](https://github.com/danbri/factoidal/issues/448))

Outside G1's RDF/SPARQL semantics scope (§ header above) — recorded
here per the standing "no proof landing without a registry entry"
rule, since it is a proved theorem with a real consumer
(`bin/depcheck`, `tools/module-liveness.py` v3).

| Stage | Artifact | Status | Notes |
|---|---|---|---|
| Reachability closure spec | `Dep.Reachability.fst`: `reaches` (inductive), `closure_fuel`/`reachable` (Tot, untrusted algorithm) | ✅ PROVED | `reaches` is the spec, independent of the algorithm; `closure_fuel`'s fuel-adequacy argument is stated but NOT relied on for soundness. |
| Deletion-safety theorem | `closed_set_catches_all`: `is_closed edges acc /\ mem r acc /\ reaches edges r n ==> mem n acc` | ✅ PROVED | Induction on the `reaches` derivation (`decreases h`); `RRefl` trivial, `RStep` uses `FStar.List.Tot.for_all_mem` to bridge `is_closed`'s `for_all` to the per-edge fact. |
| Contrapositive corollary | `no_root_reaches`: `is_closed edges acc /\ all_mem roots acc /\ not (mem n acc) ==> forall r. memP r roots ==> ~(reaches edges r n)` | ✅ PROVED | Built via `FStar.Classical.impl_intro` over a nested `Lemma False` helper (SMT closes the `mem n acc` / `not (mem n acc)` contradiction once both are literal ground facts in context). |

Gates (2026-08-17, `verified-liveness` branch, fresh full rebuild —
no `.checked` cache in this worktree before this landing):
`make verify-Dep.Reachability` clean (no `--lax`, no
`--admit_smt_queries`); `./build-ocaml.sh extract compile` green with
`Dep.Reachability.fst` in all three module lists (`ALL_MODULES`,
`COMMON_MODULES`, js `FSTAR_MODULES`) and `bin/depcheck` built as part
of the main native compile step (not an orphan binary — same
`$COMMON_MODULES` link line as `parquet_probe`/
`cottas_ondisk_smoketest`); `w3c_runner --rdf` 1030 pass, 0 fail, 1
unsupported (of 1031) — exact match, no regression; `tests/unit/
run-all.sh` 21 pass, 28 fail (of 49) = the pre-existing 20 pass, 28
fail (of 48) baseline plus `dep_reachability_unit` (10 pass, 0 fail)
newly passing.

**Design**: neither `closure_fuel`'s fuel bound nor its closure
implementation is trusted for soundness. `bin/depcheck` calls the
extracted `Dep_Reachability.reachable`, then RE-CHECKS
`is_closed`/`all_mem` — both DECIDABLE — on the actual output at
runtime, and refuses (exit 2) if either fails; `closed_set_catches_all`
is a fact about every set satisfying those two decidable premises, not
about this one algorithm. Confirmed working by feeding `depcheck` a
hand-doctored non-closed candidate set (a genuine graph's true closure
with one downstream node removed): `depcheck: REFUSED — reachable()
output is not closed under edges ... Not trusting this result.`
(exit 2), and separately a closed-but-root-missing set: `depcheck:
REFUSED — reachable() output does not contain all roots.` (exit 2).
The anti-vacuity arm of `tests/unit/dep_reachability_unit.ml` pins the
same property at the extracted-function level: `is_closed` accepts a
diamond graph's true closure and REJECTS a hand-built proper subset of
it.

**Tool replacement ([#448](https://github.com/danbri/factoidal/issues/448) Part 2)**: `tools/module-liveness.py` v3
drops the v2 `ocamlobjinfo <unit>.cmx` OCaml-layer oracle (required a
full prior native+consumer build) for `ocamldep -modules` run directly
over `bin/*/*.ml` and `formal/fstar/ocaml-output/*.ml` SOURCE, then
shells out to `bin/depcheck` (built standalone from just
`Dep_Reachability.ml` + `depcheck.ml`, not the full
`$COMMON_MODULES` chain, if no build-produced binary is already
present) as the reachability engine. `strace -e openat -f python3
tools/module-liveness.py 2>&1 | grep -c '\.cmx'` = 0.

v2-vs-v3 dead-set diff on the same fresh-rebuilt tree: v2 saw 200
project units (only modules with a committed `.cmx`) and reported 22
DEAD; v3 saw 221 project units (every extracted `.ml`, `.cmx` or not)
and reported 35 DEAD. The two universes are not the same set, so raw
counts do not compare directly — split by what each tool could see:
- **8 modules DEAD under v2, reachable under v3** (`Math_Diff`,
  `Math_Series`, `Math_Sigmoid`, `Math_Simplify`, `Math_Subst`,
  `MathML_Present`, `XForms_Bind`, `SPARQL_Plan_Pruning`) — the safe
  over-approximation direction the design predicts. Root cause
  confirmed by direct grep, not assumed: six of the eight are used
  only by `bin/npm-entry/entry_jsoo.ml`, a consumer v2 could never see
  as a root (no committed `.cmx` for the jsoo/npm surface — the same
  blind spot v2's own docstring names). `SPARQL_Plan_Pruning` is used
  by `SPARQL_Plan_AccessPath.ml` at the OCaml level; v2's
  `ocamlobjinfo` "Implementations imported" edge extraction missed
  that reference (plausibly a types-only/`.cmi`-level use that leaves
  no code-level implementation-import record) while `ocamldep`'s
  syntax-level parsing sees the `open` regardless of whether the
  reference is type-only or value-level — the documented v3 limit
  ("cannot distinguish opened-and-unused from opened-and-called")
  firing in the safe direction here.
- **21 modules DEAD under v3 that v2 never evaluated at all**
  (`OWL_Semantics*`, `OWL_RL_*`, `RDF_Entailment_*`,
  `SPARQL11_Algebra_Spec`/`Refinement`, `RDF_Indexed_KeyInjectivity`,
  `RDF_Semantics_HypothesisWitness`, `RDF_CottasStore_PageCache_Bounds`,
  `SPARQL_Protocol_RoundTrip`) — verify-only F* modules extracted to
  `.ml` (in `ALL_MODULES`) but never linked into any binary (absent
  from `COMMON_MODULES`), so v2's `.cmx`-keyed `project_units()` never
  counted them as project units in the first place — an uninspected
  blind spot, not a disagreement. v3 correctly classifies most of
  these `fstar-only referrers — proofs/types use it (erased)` (F*-side
  lemma/type consumers exist even though no OCaml binary links them),
  matching e.g. `RDF.Semantics.HypothesisWitness.fst`'s own header
  ("VERIFY-ONLY... not in any .ml link list").
- **14 modules DEAD under both** (`Parser_Ballyhoo`,
  `Parser_BallyhooBloom`, `Parser_BallyhooHDTQ`, `RDF_CottasInMem`,
  `RDF_CottasStore_OnDiskRuntime`, `RDF_Store_HDTTermCacheRegistry`,
  `RDF_Store_LazyTermCache`, `SPARQL_HTTP_Timing`,
  `SPARQL_Plan_Estimate`, `SPARQL_Plan_Explain`, `SPARQL_Plan_Loader`,
  `SPARQL_Service_Wrap`, `Service_wrap_http`, `Util_Log`) — full
  agreement. NOTE: this worktree forked before the coordinator's
  branch landed the `Parser.BallyhooHDTQ` / `RDF.CottasStore.
  OnDiskRuntime` / `Parser.BallyhooBloom` deletions, so those three
  names are expected to still appear DEAD here; the coordinator
  reconciles at merge, not this branch.
- Zero modules flipped from v2-reachable to v3-DEAD in the shared
  200-unit universe — the unsafe direction never fired.

Project assume-val total: unchanged (this landing adds proof-only F*
+ a non-`assume val` OCaml consumer, `bin/depcheck`, per iron rule
#11's "consumer tools ... belong in `bin/<consumer>/`").

## 9. Unified model theory ([#598](https://github.com/danbri/factoidal/issues/598))

Stage 1 (landed 2026-08-25): RDF core semantics + datasets embedded
into the CL/IKL theory layer (`formal/lean4/L4Factoidal/Unified/`),
proved adequate in BOTH directions against the native Lean
formalization. Design:
[`docs/designissues/2026-08-25-unified-semantics-lean.md`](designissues/2026-08-25-unified-semantics-lean.md)
(stage 1 correction notes there record the deviations: colon-free
bound-name spelling, tagged lift domain, unscoped named-graph bodies).
All rows below are Lean 4 (`L4Factoidal.Unified`), no `sorry` / user
`axiom` / `partial` / `native_decide`; axiom audit on every gate
theorem: `propext`, `Classical.choice`, `Quot.sound` only.

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `unified_adequate_simple` — `Entails [rdfToTheory g] (rdfToTheory h) ↔ RDF.SimpleEntailsMt g h` | `Unified/RdfAdequacy.lean` | `RDF.SimpleEntailsMt` (`RDF/Semantics.lean`) | ✅ PROVED (2026-08-25) — full iff | NONE — no triple-term-freedom hypothesis (both sides read RDF 1.2 triple terms as the same uninterpreted function) |
| `unified_adequate_simple_decided` — `... ↔ RDF.simpleEntails g h = true` | `Unified/RdfAdequacy.lean` | `RDF.simpleEntails_iff_mt` + `RDF.SimpleRefinement.simpleEntails_iff_spec` | ✅ PROVED (2026-08-25) | `GraphTtFree g`, `GraphTtFree h` (where the native Herbrand construction applies; hypotheses shown non-degenerately satisfiable in `Unified/Witnesses.lean`) |
| `rdfToTheory_merge` — merge is conjunction: `EntailEquiv [rdfToTheory (mergeGraphs g h)] [rdfToTheory g, rdfToTheory h]` | `Unified/RdfAdequacy.lean` | `Graph.prefixBnodes` renaming (`RDF/Graph.lean`, `RDF/DatasetMerge.lean`), `RDF.tripleHolds_agree` | ✅ PROVED (2026-08-25) — satisfaction-equivalence (stronger than mutual entailment) | — |
| `rdfToTheory_union_entails_left` / `_right` / `_merge` — shared-scope union entails each part and the merge | `Unified/RdfAdequacy.lean` | same | ✅ PROVED (2026-08-25) | — |
| `union_shared_scope_strict` — the converse REFUTED: separate closures do not entail the shared-label union (witness pair, decision-procedure separation `simpleEntails_merge_union_false` by `decide`) | `Unified/RdfAdequacy.lean` | `RDF.simpleEntails` | ✅ PROVED (2026-08-25) — strictness witness | concrete witness pair `unionG`/`unionH` |
| `satisfies_rdfToTheory_restrict` / `satisfies_rdfToTheory_lift` — the transport pair's satisfaction transfer, both directions, both interpretations | `Unified/RdfTransport.lean` | `RDF.Satisfies` (`RDF/Semantics.lean`) | ✅ PROVED (2026-08-25) — full iff each | — |
| `bnodeName_ne_iri` — bound-name freshness against EVERY well-formed IRI string, unconditional | `Unified/RdfEmbed.lean` | `RDF.isIri` | ✅ PROVED (2026-08-25) | — (colon-free spelling makes the design doc's freshness obligation hypothesis-free) |
| `datasetToTheory_asserts_default` — the dataset sentence entails its default graph's translation | `Unified/DatasetEmbed.lean` | `RDF.Dataset` (`RDF/Graph.lean`) | ✅ PROVED (2026-08-25) | — |
| `datasetToTheory_no_named` — a named-graph-free dataset translates to exactly its default graph's sentence | `Unified/DatasetEmbed.lean` | — | ✅ PROVED (2026-08-25) — definitional equation | — |
| `dataset_decoration_asserts_nothing` — a named-graph-only dataset does NOT entail its named graph's content (RDF 1.1 Concepts §4: datasets carry no entailment semantics). RESTATED SCOPE 2026-08-26: after the [#609](https://github.com/danbri/factoidal/issues/609) item-3 repair this is the statement about a named graph the default graph does NOT decorate with `urn:cl:def:asserts` — `decorationDataset` has an empty default graph. An ASSERTED named graph's content IS entailed (`embedding_entails_content`) | `Unified/Witnesses.lean` | separating model `namesOnlyInterp` | ✅ PROVED (2026-08-25, scope restated 2026-08-26) — refutation witness | concrete `decorationDataset` |
| `graphAsserted` + `assertedGraphAtom` + `sat_assertedGraphAtom` + `graphAsserted_eq_assertsDecorated` — **THE [#609](https://github.com/danbri/factoidal/issues/609) ITEM-3 REPAIR**: a named graph the DEFAULT graph decorates with `urn:cl:def:asserts` contributes the conjunct `atom (that (rdfBody G)) []` — CLIF's cancelling-parentheses assertion, and the position `CL.IklRespectsThat` constrains. `sat_assertedGraphAtom` is `CL.sat_assert_that` at that conjunct, so under IKL coherence it forces the graph's content exactly. `graphAsserted_eq_assertsDecorated` pins the unified layer's `urn:cl:def:asserts` test to the engine's `CL.assertsDecorated` (`rfl`) | `Unified/DatasetEmbed.lean`, `Unified/RdfEmbed.lean` | `CL.sat_assert_that` (`CL/Semantics.lean`); `CL.assertsDecorated` (`CL/IklRegime.lean`) | ✅ PROVED (2026-08-26) | none |
| `decorationOnlyToTheory` + `datasetToTheory_entails_decorationOnly` — the SUPERSEDED decoration-only reading, retained so the divergence theorems have a subject; the repaired reading entails it. The inclusion is PROPER — `decorationOnly_strictly_weaker` | `Unified/DatasetEmbed.lean` | — | ✅ PROVED (2026-08-26) — refinement | — |
| `rdfToTheory_satisfiable` / `datasetToTheory_satisfiable`, `unified_entails_not_everything`, `unified_entails_instance`, `propAlphaInvariant_satisfiable` / `_entails_not_everything` / `alphaKeyed_distinguishes` | `Unified/Witnesses.lean` | `RDF/SemanticsHypothesisWitness.lean` discipline | ✅ PROVED (2026-08-25) | non-vacuity guards: every stage 1 relation shown neither empty nor the everything-relation |

D-entailment landing (2026-08-25, `Unified/DSchema.lean`): the
datatype-map schema `dSchema D` (value identification via
`RDF.literalValueEq D` + ill-typed exclusion via
`RDF.literalIllFormed D`, design doc §2.5/§5.1) and the native
model-theoretic anchor `RDF.DInterpCond` / `RDF.DEntailsMt`
(`EntailsUnder` over the D-interpretations), introduced in the same
module because the native tree had none — `RDF/EntailmentTheorems.lean`
deliberately gives the `literalValueEq` regime variants no soundness
theorem. REPAIRED same day per
[#602](https://github.com/danbri/factoidal/issues/602): the exclusion
clause and schema now cover triple-term-INTERIOR ill-typed literals
(`RDF.termIllTypedMention`), mirroring RDF 1.2 Semantics WD
(7 April 2026) §5 `I(E) = IT(I(E.s), I(E.p), I(E.o))` composed with
§7.1 "cannot denote anything … any triple containing the literal must
be false" and the W3C rdf12 `malformed-literal` test; the pre-repair
top-level-only bundle survives as `DInterpCondTopLevel` with a
strictness separation. Axiom audit on every row below: `propext`,
`Classical.choice`, `Quot.sound` only.

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `unified_adequate_d` — `EntailsSchema condTrue (dSchema D) [rdfToTheory g] (rdfToTheory h) ↔ RDF.DEntailsMt D g h` | `Unified/DSchema.lean` | `RDF.DEntailsMt` (introduced there; design doc §4.1's parenthetical) | ✅ PROVED (2026-08-25) — full iff | NONE — no side condition, any `D`, any graphs |
| `unified_d_illtyped_entails_all` / `dEntailsMt_illtyped` / `RDF.dEntailsMt_illtyped_native` — a premise whose object MENTIONS an ill-typed recognised literal (top-level, or triple-term interior at any depth) entails everything (RDF 1.1 Semantics §7.2; RDF 1.2 Semantics WD §5 + §7.1) | `Unified/DSchema.lean` | `RDF.termIllTypedMention`; verdict agreement with `RDF.Regime.inconsistent` pinned by `#guard` | ✅ PROVED (2026-08-25, repaired form per [#602](https://github.com/danbri/factoidal/issues/602)) | any mentioned occurrence — the interior case is the `malformed-literal` shape |
| `dValueSchema_alone_insufficient` + `dSchema_exclusion_does_work` — the §5.1 separating model: `dSepInterp` satisfies the whole value-identification half plus the translated ill-typed graph and refutes the exclusion axiom, so value identification alone does not give the §7.2 everything-verdict and the exclusion rows do | `Unified/DSchema.lean` | separating model `dSepInterp` | ✅ PROVED (2026-08-25) — exclusion-schema non-redundancy | concrete witness `dBadGraph` (`"yes"^^xsd:boolean`) |
| `dEntailsMt_value_instance` / `unified_d_value_instance` / `dNum_not_simple` — `"1"^^xsd:integer` D-entails `"01"^^xsd:integer` in the same triple, and simple entailment refutes the pair: D strictly extends simple | `Unified/DSchema.lean` | `RDF.literalValueEq`, `RDF.simpleEntails_iff_mt` | ✅ PROVED (2026-08-25) | concrete witness pair `dNumG`/`dNumH` |
| `noRel_satisfiesSchema_d`, `dSchema_entails_not_everything`, `noExt_dCond`, `dEntailsMt_not_everything` | `Unified/DSchema.lean` | `RDF/SemanticsHypothesisWitness.lean` discipline | ✅ PROVED (2026-08-25) | non-vacuity guards: schema and condition bundle satisfiable for every `D`; neither relation is the everything-relation |
| `RDF.regimeEntails_d_sound_mt` — SOUNDNESS of the executable D-regime: `regimeEntails .d D g h = true → RDF.DEntailsMt D g h`, with no side condition (the [#602](https://github.com/danbri/factoidal/issues/602) repair makes the interior-collecting inconsistency shortcut sound; `termMatch_valueEq_denot` + `denot_instance_term` make value-equal matching sound, triple-term interiors included) | `Unified/DSchema.lean` | `RDF.regimeEntails .d` | ✅ PROVED (2026-08-25) | NONE — unconditional |
| `unified_adequate_d_decided_sound` — the decided corollary, SOUND HALF: executable `true` implies schema entailment (composition of the row above with `unified_adequate_d`) | `Unified/DSchema.lean` | `RDF.regimeEntails .d` | ✅ PROVED (2026-08-25) | NONE — unconditional |
| `dEntailsMt_tt_illtyped` / `wdMalformed_dEntailsMt` — the FLIPPED PIN of [#602](https://github.com/danbri/factoidal/issues/602): a used triple term with an ill-typed interior literal makes the premise D-inconsistent (the W3C rdf12 `malformed-literal` expectation); executable agreement pinned by `#guard`. The failing-pin run against the pre-repair semantics is recorded on the issue (the superseded `dEntailsMt_tt_gap` proved its negation and is REMOVED — its content survives as `topLevel_exclusion_insufficient_for_tt`, stated about the superseded bundle) | `Unified/DSchema.lean` | `RDF.dEntailsMt_illtyped_native`, witness `dTtGraph` / `wdMalformedGraph` | ✅ PROVED (2026-08-25) | concrete witnesses |
| `DInterpCondTopLevel` + `dInterpCond_topLevel` / `ttSep_not_dCond` / `topLevel_exclusion_insufficient_for_tt` — the pre-repair top-level-only bundle is a strict weakening: `ttSepInterp` meets it while satisfying `dTtGraph`, so the interior clause is the exact ingredient the repair added | `Unified/DSchema.lean` | separating model `ttSepInterp` | ✅ PROVED (2026-08-25) — clause non-redundancy | concrete witness `dTtGraph` |
| DECIDED COROLLARY, COMPLETE HALF — NOT CLAIMED: `RDF.DEntailsMt D g h → regimeEntails .d D g h = true`. Named open lemma; NOT a triple-term matter after the repair. Needs (a) a D-Herbrand interpretation quotienting literals by `literalValueEq D` (clause 1 forces value-equal literals to one denotation, so the plain term model does not qualify), and (b) completeness of `searchInstance` under the regime's restricted `Regime.bindable` (`entailsWith_complete` requires `bindable` universally true) | `Unified/DSchema.lean` | `RDF.regimeEntails .d` | ⬜ OPEN — named lemma pair (a)+(b) | expected hypotheses once attempted: none beyond `D ⊆ modelledDatatypes`; `GraphTtFree` is NOT expected to be needed (the D-Herbrand `iTt` can be injective, unlike the simple Herbrand constant) |

NOT claimed at stage 1: any RDFS/OWL/SPARQL row (stages 2+ —
`rdfSchema`'s rdfD2 typing rows and the `rdfs:range` clash rule of
`RDF/EntailmentRdfsDatatypeClash.lean` ride with stage 2, not with
`dSchema`), and the N-Quads round-trip corollary
(blocked on the general parser round-trip theorem,
[#576](https://github.com/danbri/factoidal/issues/576) — the native
theorem exists only for the empty graph).

Stage 2 (landed 2026-08-25, recovered from an interrupted agent run,
verified and completed): the ρdf / x-rdfscore schema
(`Unified/RhoDfSchema.lean`) and the full RDFS + RDFS+D schemas with
the `rdfs:range` clash family and the type-application bridge
(`Unified/RdfsSchema.lean`). Design-doc correction notes 8–10 record
the deviations (unconditional ρdf gate with hypotheses moved to the
decided corollary; full-iff RDFS adequacy where the design predicted
soundness-only; the bridge as a separate conservative schema; the
`rdf:XMLLiteral ∈ D` weakening on closure soundness). Axiom audit on
every row below: `propext`, `Classical.choice`, `Quot.sound` only
(in-source `#print axioms`).

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `satForall_plains` + `satisfies_hornRow_iff` + `liftInterp_sat_hornRow` — the Horn-row combinator: ONE satisfaction lemma characterising a universally quantified definite Horn row's CL satisfaction as its native reading over `restrictInterp`, plus the generic lift transport | `Unified/RhoDfSchema.lean` | `CL.SatForall` (`CL/Semantics.lean`), `restrictInterp`/`liftInterp` | ✅ PROVED (2026-08-25) — full iff (the combinator every schema row goes through) | row variables colon-free, row atoms scoped (decidable side conditions, discharged by `decide` per row) |
| `satisfies_rowRdfs{2,3,5,7,9,11}_iff`, `satisfiesSchema_rhoDf_iff` — the six ρdf rows are exactly the native condition bundle `RDF.RhoDfConditions` through the restriction | `Unified/RhoDfSchema.lean` | `OWL.CondDomain`/`CondRange`, `RDF.CondSubPropertyOf*`/`CondSubClassOf*` | ✅ PROVED (2026-08-25) — full iff each | — |
| `unified_adequate_rhoDf` — `EntailsSchema condTrue rhoDfSchema [rdfToTheory g] (rdfToTheory h) ↔ RDF.RhoDfEntails g h` | `Unified/RhoDfSchema.lean` | `RDF.RhoDfEntails` (`RDFS/RhoDfCompleteness.lean`) | ✅ PROVED (2026-08-25) — full iff, UNCONDITIONAL (stronger than the design §4.2 statement; correction note 8) | NONE |
| `RDF.rhoDf_derives_holds` — everything `RDFS.Derives` derives is true in every ρdf interpretation (interpretation-level rule soundness, introduced here); `RDF.rhoDfEntails_closure_iff` — ρdf entailment invariant under replacing the premise by its executable closure | `Unified/RhoDfSchema.lean` (`RDF` namespace) | `RDFS.closure_sound` / `closure_extensive` (`RDFS/ClosureTheorems.lean`) | ✅ PROVED (2026-08-25) | — |
| `RDF.rhoDfClosed_of_check` / `RDF.rhoDfModelFrag_of_check` — executable sufficient checks (`rhoDfClosedCheck` incl. the rdfs9 blank-node-class conclusions the engine step does not emit; `RDFS.isRhoDfFrag`) for the decided corollary's hypotheses | `Unified/RhoDfSchema.lean` (`RDF` namespace) | `RDF.RhoDfClosed`, `RDF.RhoDfModelFragGraph` | ✅ PROVED (2026-08-25) — sufficiency direction only | — |
| `unified_adequate_rhoDf_decided` — the decided corollary: schema entailment ↔ `RDF.simpleEntails (RDFS.closure g fuel) h = true` | `Unified/RhoDfSchema.lean` | `RDF.rhoDfClosed_iff` (Herbrand), `simpleEntails_iff_spec` | ✅ PROVED (2026-08-25) | `RhoDfClosed (closure g fuel)`, `RhoDfModelFragGraph (closure g fuel)`, `GraphTtFree h` — each `decide`-dischargeable via the checks; positive instance `unified_rhoDf_demo` discharges all three |
| `rhoDf_not_entails_selfLoop_unified` / `rhoDfEntails_not_selfLoop` + `rhoDfSchema_satisfiable` — Finding C-1's negative half at the unified level, plus non-vacuity | `Unified/RhoDfSchema.lean` | C-1 witness pair (`RDFS/RhoDfCompleteness.lean`) | ✅ PROVED (2026-08-25) — refutation + witness | concrete pair `c1Prem`/`c1Concl`; also the not-everything guard for `rhoDfSchema` |
| `unified_adequate_rdf` — `EntailsSchema condTrue rdfSchema … ↔ RDF.RdfEntails g h` (RDF rung: `rowRdfProperty` + the RDF axiom family incl. the infinite `rdf:_n` rows via `RDF.RdfAxiomatic`) | `Unified/RdfsSchema.lean` | `RDF.RdfEntails` (`RDF/EntailmentRdfsModelTheory.lean`) | ✅ PROVED (2026-08-25) — full iff, unconditional | `rdfSchema` carries no `D` parameter (correction note 9b) |
| `unified_adequate_rdfs` — `EntailsSchema condTrue (rdfsSchema Dset) … ↔ RDF.RdfsEntails Dset g h` (17 Horn rows + both axiom families + rdfs1 rows for `Dset` and `dMinimal`) | `Unified/RdfsSchema.lean` | `RDF.RdfsEntails` | ✅ PROVED (2026-08-25) — full iff, unconditional, every `Dset` (stronger than the design's soundness-only; correction note 9a) | NO decided corollary (Finding C-1 blocks the executable characterisation) |
| `RDF.derivesFull_holds` — truth preservation over `RDFS.DerivesFull` (one case per §8/§9 rule row); `RDF.axiomaticTriples_hold` — the engine's seeded axiom set holds under the conditions | `Unified/RdfsSchema.lean` (`RDF` namespace) | `RDFS.fullClosure_sound` (`RDFS/FullClosureTheorems.lean`) | ✅ PROVED (2026-08-25) | `axiomaticTriples_hold`: harvested `rdf:_n` slice genuine (`IsRdfMemberIri`) AND `rdf:XMLLiteral ∈ D` (correction note 10b; `#guard`s pin the seed-table/spec-table mismatch) |
| `unified_rdfs_closure_sound` — every triple of `RDFS.fullClosure D cmps g` is schema-entailed by `g`'s translation | `Unified/RdfsSchema.lean` | `RDFS.fullClosure` | ✅ PROVED (2026-08-25) — soundness only (completeness not claimed, C-1) | `∀ c ∈ cmps, IsRdfMemberIri c`; `rdf:XMLLiteral ∈ D` (recorded weakening, correction note 10b) |
| `rdfs_entails_selfLoop` / `rdfs_entails_selfLoop_unified` — C-1's positive half: the full RDFS schema entails the subClassOf self-loop the ρdf schema refutes → `rdfsSchema` STRICTLY stronger than `rhoDfSchema` | `Unified/RdfsSchema.lean` | IC condition + subClassOf reflexivity | ✅ PROVED (2026-08-25) | shared witness pair with the ρdf refutation |
| `rdfSchema_satisfiable` / `rdfsSchema_satisfiable` / `rdfSchema_entails_not_everything` / `rdfsSchema_entails_not_everything` | `Unified/RdfsSchema.lean` | `trivialInterp` / `separatingInterp` (`RDF/SemanticsHypothesisWitness.lean`) through the lift | ✅ PROVED (2026-08-25) | non-vacuity guards, every `Dset` |
| `RDF.DRangeCond` / `RDF.RdfsDInterpCond` / `RDF.RdfsDEntailsMt` — the combined RDFS+D condition bundle and its model-theoretic entailment, introduced natively here (the native tree had only the executable `rdfsDInconsistent`) | `Unified/RdfsSchema.lean` (`RDF` namespace) | `RDF/EntailmentRdfsDatatypeClash.lean` (executable side) | ✅ DEFINED (2026-08-25) | fragment of §7+§9 the executable machinery expresses; full §7 value-space completeness not claimed |
| `rangeClashSchema` + `satisfies_rangeClashAx_iff` + lift/restrict transfers — the `rdfs:range` datatype clash as a negated-existential axiom family (the `dExclusionSchema` pattern) | `Unified/RdfsSchema.lean` | `RDF.DRangeCond` | ✅ PROVED (2026-08-25) — full iff characterisation | one row per recognised `c ∈ D` and differently-typed literal |
| `unified_adequate_rdfs_d` — `EntailsSchema condTrue (rdfsDSchema Dset D) … ↔ RDF.RdfsDEntailsMt Dset D g h` | `Unified/RdfsSchema.lean` | `RDF.RdfsDEntailsMt` | ✅ PROVED (2026-08-25) — full iff, unconditional, every `Dset`/`D` | — |
| `rdfsDSchema_clash_unsat` / `unified_rdfsD_clash_entails_all` / `rdfsDEntailsMt_clash` / `rangeClash_demo` — a range/datatype-clash premise entails everything; concrete demo agrees with the executable detector (`#guard RDF.rdfsDInconsistent …`) | `Unified/RdfsSchema.lean` | `RDF.rdfsDInconsistent` rule (b) | ✅ PROVED (2026-08-25) | clash pattern hypotheses (decl + data triple shape); demo `rangeClashDemoG` |
| `rdfsDSchema_satisfiable_nil` / `rdfsDEntailsMt_not_everything_nil` / `rdfsDSchema_entails_not_everything_nil` — non-vacuity of the combined bundle and schema | `Unified/RdfsSchema.lean` | `trivialInterp` / `separatingInterp` | ✅ PROVED (2026-08-25) | stated at `D = []` (datatype clauses vacuous there); see the open-item row below for nonempty `D` |
| `typeBridge` + `satisfies_typeBridge_iff` + `bridgeify` + `restrictInterp_bridgeify` + `typeBridge_conservative` — the LBase type-application bridge `(forall (x c) (iff (rdf:type x c) (c x)))` as a SEPARATE schema, conservative over translated graphs (rel-surgery: unary predication redefined from the binary `rdf:type` extension, invisible to `restrictInterp`) | `Unified/RdfsSchema.lean` | LBase §2; `rdfsSchema` gate iff | ✅ PROVED (2026-08-25) — conservativity as full iff | bridge NOT foldable into `rdfsSchema` (correction note 9c) |
| `bridge_derives_classApp` / `rdfsSchema_no_classApp` — the bridge is NOT conservative outside the translated fragment, pinned on the class-application sentence `(C a)` | `Unified/RdfsSchema.lean` | `liftInterp`'s empty non-binary extensions | ✅ PROVED (2026-08-25) — separation pair | concrete `bridgeDemoG` |
| `rdfsCoreSchema` (= `rhoDfSchema`, definitional) — the x-rdfscore regime's schema, named for the stage 6 regime table | `Unified/RhoDfSchema.lean` | `RDFS/RegimeDispatch.lean` | ✅ DEFINED (2026-08-25) — `rdfsCoreSchema_eq : rdfsCoreSchema = rhoDfSchema` | — |
| FINITE-SLICE-SUFFICES (§5.7) NOT PROVED — consequences mentioning only harvested `rdf:_n` IRIs derivable from the harvested instances. NO landed theorem consumes it: the schemas index rows by the native predicates carrying the full infinite families, so both sides of every gate iff quantify over the same family. Load-bearing only for a decided full-RDFS corollary, which Finding C-1 independently blocks | — | RDF 1.1 Semantics Appendix A finite-enumeration recipe | ⬜ OPEN (recorded gap, correction note 10a) | — |
| RDFS+D SATISFIABILITY FOR NONEMPTY `D` NOT PROVED — a model of the full §9 bundle plus the D and range-clash clauses with recognised datatypes needs a term-model construction (`CondResource` reflexivity against literal-excluding conditions defeats finite ad-hoc models) | — | — | ⬜ OPEN (recorded gap; witnesses stated at `D = []`) | — |

Stage 3 (landed 2026-08-25): Datalog as the named computable-fragment
class of the unified theory — `Unified/Datalog.lean` (the class, its
Herbrand semantics, and the TWO GENERIC least-fixpoint theorems,
proved once for every program) and `Unified/DatalogClosures.lean`
(the closure engines exhibited as programs of the class, with the
class boundary recorded in that module's header). Design-doc
correction notes 12–15 record the deviations (term-valued predicate
position; well-formedness as a proof field, so existential heads are
unwritable; membership-equality exhibit statement with the stage 2
decided-corollary hypotheses; RIF Core deferred to its own stage — landed 2026-08-26, correction notes 38-41).
Axiom audit on every row below: `propext`, `Classical.choice`,
`Quot.sound` only (in-source `#print axioms`).

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `DTerm`/`DAtom`/`DRule`/`DatalogProgram` — definite Horn over n-ary predications, predicate position a term (variable predicates legal; CL is unsegregated), NO function symbols, NO existential heads and NO falsity heads BY CONSTRUCTION (`DatalogProgram.wf` is a proof field: definiteness + the colon-free variable discipline) | `Unified/Datalog.lean` | design doc §3 stage 3, §5.6 | ✅ DEFINED (2026-08-25) | `rdfD1Shape_not_wf` (`Unified/DatalogClosures.lean`) pins that a witness-minting rule shape fails the gate |
| `sat_datom` + `satisfies_ruleSentence_iff` — the n-ary generalisation of the stage 2 hornRow machinery: ONE satisfaction lemma characterising a rule sentence's CL satisfaction as its native reading at every valuation (`DAtom.Holds`, stated directly over `CL.Interp` — no arity-2 restriction) | `Unified/Datalog.lean` | `satForall_plains` (`Unified/RhoDfSchema.lean`), `CL.Sat` | ✅ PROVED (2026-08-25) — full iff | rule wf (colon discipline), carried by the program structure |
| `matchBody_sound` / `matchBody_complete` + `DRule.mem_conclusions_of_instance` — the executable substitution search is sound (every found binding instantiates the body into the fact set) and complete (every grounding substitution is found; definiteness turns body coverage into head coverage) | `Unified/Datalog.lean` | — (new executable layer) | ✅ PROVED (2026-08-25) | completeness needs `definiteB` — exactly what the class gate enforces |
| `DatalogProgram.lfp_sound` / `derives_mem_lfp` — the fuel-bounded least fixpoint against the rule relation `DatalogProgram.Derives`, both directions (the second under `FuelAdequate`, executable check `saturatedCheck`, `decide`-dischargeable — the `rhoDfClosedCheck` pattern) | `Unified/Datalog.lean` | `RDFS/FixedPoint.lean` shape | ✅ PROVED (2026-08-25) | — |
| `datalog_lfp_sound` — GENERIC theorem 1: every atom of any program's least fixpoint is entailed by the program-as-schema plus the facts over every CL interpretation (`step`-shaped induction, the `rhoDf_derives_holds` shape, done once for the class) | `Unified/Datalog.lean` | `EntailsSchema` (`Unified/Theory.lean`) | ✅ PROVED (2026-08-25) | NONE (any fuel, any facts) |
| `datalog_lfp_complete` + `herbInterp` / `herb_satisfiesSchema` — GENERIC theorem 2: every GROUND atom entailed by schema + ground facts is in the fuel-adequate fixpoint; the Herbrand interpretation of the fixpoint itself is the minimal model (the `RhoDfCompleteness` construction done once at the generic level) | `Unified/Datalog.lean` | Herbrand pattern of `RDFS/RhoDfCompleteness.lean` | ✅ PROVED (2026-08-25) | facts ground, atom ground, `FuelAdequate` — completeness claimed for GROUND-ATOMIC consequences only (design doc §5.6; that is the class's claim level, stated) |
| `datalog_lfp_iff_entails` — the stage 3 gate theorem (§4.3): fixpoint membership ↔ `EntailsSchema condTrue p.toSchema` for every well-formed program | `Unified/Datalog.lean` | both rows above | ✅ PROVED (2026-08-25) — full iff | union of the two rows' hypotheses |
| `toSchema_satisfiable` + `demo_path_entailed` / `demo_tri_entailed` / `demo_not_entailed_reverse` — non-vacuity: every program's schema is satisfiable; a transitive-closure demo (with an arity-3 rule pinning the n-ary machinery) has a positive, a ternary and a REFUTED instance, all end to end through the executable fixpoint | `Unified/Datalog.lean` | `SemanticsHypothesisWitness` discipline | ✅ PROVED (2026-08-25) | concrete `demoProgram`/`demoFacts` |
| `rhoDfProgram` + `derives_to_datalog` / `datalog_derives_mem_closure` — the ρdf closure as a Datalog program; the specification relation `RDFS.Derives` maps INTO the program's derivations (unconditional), and every program derivation decodes into a ρdf-CLOSED engine closure (via the DIAGONAL relations `Rdfs*Derives`, blank-node classes included) | `Unified/DatalogClosures.lean` | `RDFS/RdfsCore.lean`, `RDF/EntailmentRdfsSpec.lean`, `RDF.RhoDfClosed` | ✅ PROVED (2026-08-25) | decode: closure ρdf-closed + model fragment (the stage 2 decided-corollary hypothesis pair) |
| `rhoDf_closure_datalog_agree` + `rhoDf_lfp_image` — ρdf ENGINE / Datalog agreement, GENERAL graphs, as MEMBERSHIP equality; the fixpoint holds no atoms outside the encoding's image | `Unified/DatalogClosures.lean` | `RDFS.closure`, `RDFS.closure_sound` / `closure_extensive` | ✅ PROVED (2026-08-25) — membership iff | `rhoDfClosedCheck (closure g m)`, `isRhoDfFrag (closure g m)`, `saturatedCheck` fuel adequacy, `RhoDfModelObjectOk t.o` — all but the last `decide`-dischargeable; instance `rhoDf_demo_agree` discharges all |
| `rhoDf_engine_iff_datalog_entails` — the design doc §8.2 claim at its stated level: membership in the ρdf ENGINE's closure ↔ CL entailment of the triple's atom-sentence from the program-as-schema (ground-atomic consequences, ρdf model fragment) | `Unified/DatalogClosures.lean` | composition of the agreement row and the gate theorem | ✅ PROVED (2026-08-25) | same hypothesis set; decided instance `rhoDf_demo_entails` |
| `rdfsPlusProgram` (six ρdf rows + eq-sym/eq-trans/eq-rep-s/o/p, prp-symp, prp-trp, prp-inv1/2, prp-fp, prp-ifp, cax-eqc1/2, prp-eqp1/2 + the four schema-level inverseOf domain/range flips — the RL closure's non-list, non-clash core) + `rdfsPlus_demo_trp_agree` + `rdfsPlus_demo_entails` + `rdfsPlusDemoAgrees` `#guard`s | `Unified/DatalogClosures.lean` | `RDFS.rdfsPlusClosure` (`RDFS/RDFSPlus.lean`), `OWL/RLClosure.lean` row functions | ✅ PROVED (2026-08-25) — DEMO-INSTANCE membership equality, both directions: a `decide`d theorem on the TransitiveProperty demo; native-evaluated build-time `#guard` pins on the sameAs and inverseOf demos (their substitution closures exceed the kernel `decide` budget); engine saturation at the used fuel pinned by `#guard` | GENERAL bridging NOT claimed for this tier (correction note 14): the native tier claims no chain-level completeness, and the engine's `subjIri` guards restrict firings the program does not |
| DATALOG CLASS BOUNDARY — outside the class, each with its reason: rdfD1 / rdfs1-2004 / lg-gl (existential heads — unwritable by construction); the 13 RL clash rows (falsity heads — a `DRule` head is an atom; their schema-level home is `rangeClashSchema`); the RL list-valued rows prp-spo2, prp-key, cls-int1/2, cls-uni, cls-oo, cax-adc, scm-int, scm-uni (unbounded collection premises — infinite rule families, stage 4 material as sentence families); the infinite `rdf:_n` axiomatic fact families (finite slices only). rdfs6/rdfs10/eq-ref are IN the class but engine-excluded, so the exhibits exclude them for agreement | `Unified/DatalogClosures.lean` module header | design doc §5.6 | ✅ RECORDED (2026-08-25) | — |
| GENERAL RDFS-PLUS / RL-CORE BRIDGING NOT PROVED — a ρdf-style general membership iff for `rdfsPlusProgram` needs per-row diagonal specification relations + a closedness predicate for the tier (none exist natively) and a fragment predicate reconciling the engine's IRI-subject guards | — | — | ⬜ OPEN (recorded gap, correction note 14) | — |
| `rifCoreToTheory` + `rifDRules` / `rifCoreProgram?` / `rifCoreProgram_of_fragment` — a RIF Core rule set as universally closed implications, through the frame / member / subclass desugaring of the RIF/RDF/OWL combination specification §5; a positional atom becomes an n-ary predication at ANY arity (arity 2 IS the triple predication). Every rule set passing `rifCoreFragmentB` IS a program of the class, `DRule.wfB` discharged as the proof field | `Unified/RifEmbed.lean` | `RIF/Translation.lean` desugaring, `RIF/Syntax.lean` | ✅ DEFINED + PROVED (2026-08-26) | `rifCoreFragmentB` (see the FRAGMENT row below) |
| `rifTripleFact_sentence` / `rifGraphFacts_sentences` / `satisfiesAll_tripleAtoms_iff` / `satisfies_rdfToTheory_single` — the Datalog sentences ARE `Unified/RdfEmbed.lean`'s own triple predications on the IRI fragment (no tagged vocabulary of their own, unlike `Unified/DatalogClosures.lean`'s `"i:"`/`"b:"` encoding), and the premise list `g.map tripleAtom` is satisfaction-equivalent to `[rdfToTheorySk g]` | `Unified/RifEmbed.lean` | `tripleAtom`, `rdfToTheorySk`, `sat_rdfBody` | ✅ PROVED (2026-08-26) — equalities and full iffs | `TripleIriOnly` / `GraphIriOnly` |
| `rifCore_lfp_iff_entails_atom` — the RIF Core gate theorem, n-ary form: a ground atom is in the rule set's Datalog least fixpoint over a graph's facts ↔ `EntailsSchema condTrue (fun s => s ∈ rifCoreToTheory rs) [rdfToTheorySk g] a.sentence`. Obtained by instantiating `datalog_lfp_iff_entails`, not re-proved | `Unified/RifEmbed.lean` | `DatalogProgram.lfp`, generic theorems 1 and 2 | ✅ PROVED (2026-08-26) — FULL IFF | `p.rules = rifDRules rs`, `GraphIriOnly g`, atom ground, `FuelAdequate` (`saturatedCheck`, `decide`-dischargeable). NONE of the four mentions the conclusion |
| `rifCore_lfp_iff_entails` — §4.7's triple shape: `rifTripleFact t ∈ p.lfp (rifGraphFacts g) fuel ↔ EntailsSchema condTrue (fun s => s ∈ rifCoreToTheory rs) [rdfToTheorySk g] (rdfToTheory [t])`. The LEFT-HAND SIDE IS THE DATALOG LEAST FIXPOINT, NOT `RIF.Engine.saturate` — see the OPEN row below | `Unified/RifEmbed.lean` | `RIF/Saturate.lean` reading of a graph | ✅ PROVED (2026-08-26) — FULL IFF | as the row above, plus `TripleIriOnly t` |
| `rifCoreToTheory_satisfiable` + `rifCore_demo_member_entails` / `rifCore_demo_frame_entails` / `rifCore_demo_nary_entails` / `rifCore_demo_not_entailed` / `rifCore_demo_satisfiable` — non-vacuity: EVERY rule set's schema is satisfiable, and on a three-rule demo (membership, frame, ternary positional head) a membership, a frame and a TERNARY consequence are entailed while `ex:b # ex:D` is REFUTED through the completeness half. All `decide`d end to end | `Unified/RifEmbed.lean` | `toSchema_satisfiable`, `SemanticsHypothesisWitness` discipline | ✅ PROVED (2026-08-26) | concrete `demoRifRules` / `demoRifGraph` |
| RIF FRAGMENT BOUNDARY — outside the class, each with its reason and each pinned by a `decide`d rejection theorem: `Equal` and `External(pred:…)` body atoms (no equality atom, no built-in predicate in the class — all 197 RIF-DTB built-ins are therefore outside); `Or` and `Exists` bodies; `List` / `External(func:…)` / uninterpreted function terms (the class has NO function symbols); constants outside `rif:iri` space or with a non-IRI lexical form; colon-carrying variable names; unbound head variables (`rifExistentialHeadRule_rejected`). DATA side: blank-node and literal terms, because `bnodeName` is colon-free by construction and `embedTerm` maps a literal to a FUNCTIONAL term | `Unified/RifEmbed.lean` module header | design doc §5.6, `Unified/RdfEmbed.lean` | ✅ RECORDED + PINNED (2026-08-26) | — |
| §4.7's `unified_adequate_rifCore` AGAINST THE NATIVE ENGINE NOT PROVED — `RIF/Engine.lean`'s `groundTm`, `matchFormula` and `qualifyTm` are `partial def`: opaque to the kernel, no equation lemmas, so nothing about what `matchFormula` COMPUTES is available to a proof and `decide` cannot evaluate it either. `RIF/EngineTheorems.lean` is written around the same limit (its `Licensed` predicate mentions `matchFormula`'s output rather than characterising it, and it declines to call itself soundness). Agreement between `RIF.Saturate.saturateGraph` and the Datalog fixpoint is pinned by `rifEngineDatalogAgrees` `#guard`s under COMPILED evaluation — evidence at the strength of the RDFS-Plus demo pins, not a theorem. Prerequisite: make the three definitions total | `Unified/RifEmbed.lean` `#guard`s only | `RIF.Saturate.saturateGraph`, `RIF.closure` | ⬜ OPEN (recorded gap, correction note 38) | — |
| RIF ENGINE / DESUGARING DIVERGENCE — `RIF/Saturate.lean` reads a triple as a frame, and additionally as membership/subclass for `rdf:type`/`rdfs:subClassOf`, but does NOT re-enter a DERIVED membership as a frame. The desugaring here collapses both readings onto one triple predication, so a rule with a `?x[rdf:type -> ?c]` body fires on a derived membership in the Datalog reading and not in the engine. Programs of that shape are outside what the `#guard`s pin; the theorems never mention the engine | `Unified/RifEmbed.lean` module header | `RIF/Saturate.lean` `factsOfTriple` / `tripleOfGAtom` | ✅ RECORDED (2026-08-26) | — |

Stage 4 (landed 2026-08-26): OWL 2 RL under the unified theory —
`OWL/RLSemantics.lean` (per-row `RlCond*` conditions + the soundness
induction over `OWL.RL.Derives`), `OWL/RLHerbrand.lean` (the enriched
Herbrand completeness model), `Unified/OwlRlSchema.lean` (the rule
table as an axiom schema, built row-family-wise) and
`Unified/OwlRlAdequacy.lean` (the gate theorems). Design-doc
correction notes 16-20 record the deviations. Axiom audit on every row
below: `propext`, `Classical.choice`, `Quot.sound` only (in-source
`#print axioms`).

Row-family counts (re-measured 2026-08-26 after the cardinality-row
and list-valued-row landings): 67 plain Horn rows as `DRule`s indexed
by `RlRowId`; 5 guarded / table-indexed `DRule` families (eq-ref
predicate conclusion at a non-reserved IRI, cax-adc-dw at a distinct
IRI pair, dt-type1 over `builtinDatatypeAxioms`, dt-rng-intersect over
`rangeIntersectLicenses`, xsd-axioms over datatype-position predicate x
XSD IRI x `xsdAxiomTriples`); 2 per-length `DRule` families (prp-spo2,
prp-key, one rule per collection length); 12 plain clash rows plus 1
clash family (cax-adc) as falsity-headed `DNeg` sentences; 3 rows in
the interpretation-class condition `OwlRlInterpCond`. Total 91 rows:
88 as object-language sentences, 3 as interpretation conditions.
(Before 2026-08-26: 66 Horn / 0 per-length / 9 clash / 9 bundled, i.e.
82 and 9.)

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `RlCond*` (79 rows) + `RlNCond*` (13 rows) + the bundles `RlConditions` / `RlClashConditions` — one model-theoretic condition per `OWL.RL.Derives` constructor and per `Clash` constructor, in the OWL 2 RL/RDF table-row citation discipline | `OWL/RLSemantics.lean` | `OWL/RLRules.lean` constructors; OWL 2 RDF-Based Semantics | ✅ DEFINED (2026-08-25) | reserved `urn:cl:def:listMember` / `urn:cl:def:typedAllMembers` helper predicates give the `ListMember`-shaped rows a Horn form |
| `rl_derives_holds` — truth preservation: every derivable triple holds at `rlExtend i A` in every interpretation meeting `RlConditions` | `OWL/RLSemantics.lean` | `OWL.RL.Derives` | ✅ PROVED (2026-08-25) | `RlReservedFree g` (load-bearing: a graph using the reserved vocabulary can make the engine conflate a user blank node with a comprehension witness) |
| `rl_clash_holds_false` — a `Clash` configuration is false under every assignment in every interpretation meeting `RlClashConditions` | `OWL/RLSemantics.lean` | `OWL.RL.Clash` | ✅ PROVED (2026-08-25) | `AdcMembersIri g` (the cax-adc IRI-member narrowing) |
| `rlHerb` + `rlHerb_conditions` — the enriched Herbrand interpretation of a `Derives`-closed, clash-free fragment graph meets all 79 derivation-row conditions | `OWL/RLHerbrand.lean` | `RDF/Semantics.lean`'s `herbrand` | ✅ PROVED (2026-08-26) | `RlHerbFrag c` clauses (a)-(d); saturation `hcut`; `¬ Clash c` |
| `rlHerb_clash_conditions` — the same model meets all 13 falsity-headed rows | `OWL/RLHerbrand.lean` | `OWL.RL.Clash` | ✅ PROVED (2026-08-26) | `RlHerbFrag c`, `¬ Clash c`; cls-maxc1 / cls-maxqc1 / cls-maxqc2 hold VACUOUSLY (their premise needs a literal object, which fragment clause (a) forbids) — stated, not hidden |
| `rlHerb_atom_decode` / `rlHerb_triple_decode` — satisfaction of a ground atom at a non-reserved predicate decodes back to closure membership | `OWL/RLHerbrand.lean` | — | ✅ PROVED (2026-08-26) | non-reserved predicate; triple-term-free object |
| `RlRowId` + `rlRowRule` + `owlRlHornSchema` + `cond_*` (66 rows) — the plain Horn rows as `DRule`s, schema membership O(1) by enumeration index, one `cond_*` per row taking schema satisfaction to the row's `RlCond*` at `restrictInterp` | `Unified/OwlRlSchema.lean` | `satisfies_ruleSentence_iff` (`Unified/Datalog.lean`) | ✅ PROVED (2026-08-26) — one direction per row (correction note 17: an iff is FALSE — the sentence quantifies the predicate position over the whole domain, the condition over `WfIri`) | none beyond `DRule.wfB` |
| `ruleEqRefP` / `ruleCaxAdcToDw` / `ruleDtType1` / `ruleDtRangeIntersect` / `ruleXsdAxiom` + `owlRlFamilySchema` + their `cond_*` — the five guarded and table-indexed families, one rule per instance of a decidable side condition | `Unified/OwlRlSchema.lean` | `OWL/RLRules.lean` tables | ✅ PROVED (2026-08-26) | — |
| `DNeg` + `satisfies_negSentence_iff` — a falsity-headed row as the universal closure of the negated conjunction of its premises, with ONE satisfaction lemma (the `dExclusionSchema` / `rangeClashSchema` pattern at n-ary arity) | `Unified/OwlRlSchema.lean` | `Unified/DSchema.lean`, `Unified/RdfsSchema.lean` | ✅ PROVED (2026-08-26) — full iff | atom well-formedness (colon discipline) |
| `RlNegRowId` + `rlNegRowRule` + `negCaxAdc` + `owlRlClashSchema` + `ncond_*` — 12 plain clash rows plus the cax-adc distinct-IRI-pair family | `Unified/OwlRlSchema.lean` | `OWL.RL.Clash` | ✅ PROVED (2026-08-26; cls-maxc1 / cls-maxqc1 / cls-maxqc2 added same day) | — |
| `DTerm.lit` + `dlit` + `dlit_val` — a `DTerm` constructor carrying an `RDF.WfLiteral`, `toCl` = `embedTerm (.literal l)`, `val` = the denotation `restrictInterp` gives `iLit`. What makes a cardinality-literal row an ordinary `DAtom` | `Unified/Datalog.lean`, `Unified/OwlRlSchema.lean` | `Unified/RdfEmbed.lean`'s `embedTerm`; `Unified/RdfTransport.lean`'s `restrictInterp` | ✅ PROVED (2026-08-26) — `dlit_val` is `rfl` | none in the model-theoretic layer (`DTerm.wfB` holds of every literal) |
| `DTerm.litFreeB` / `DAtom.litFreeB` / `DRule.litFreeB` — the Herbrand-universe restriction the new constructor forces on the OPERATIONAL layer. `herbInterp`'s domain is the constant names, so a rigid literal term denotes outside it; `herb_holds_iff`, `herb_ground_mem_iff`, `herb_satisfiesSchema`, `datalog_lfp_complete` and `datalog_lfp_iff_entails` now carry it as a hypothesis | `Unified/Datalog.lean` | — | ✅ PROVED (2026-08-26) — hypothesis discharged BY COMPUTATION at every existing call site (`tripleFact_litFree`, `graphFacts_litFree`, `rifTmD_litFree`, `rifAtomD_litFree`, `rifDRules_litFree`, `rifTripleFact_litFree`, `rifGraphFacts_litFree`), so no landed gate theorem weakens in substance | literal-freeness of the program's rules, of the facts, and of the queried atom |
| `owlRlSchema_cardinality_rows` — cls-maxc2, cls-maxc1, cls-maxqc1 and cls-maxqc2 follow from `SatisfiesSchema i owlRlSchema` ALONE, with no appeal to `OwlRlInterpCond`. The shrinkage of the condition bundle, stated as a theorem rather than left in a definition | `Unified/OwlRlSchema.lean` | `OWL/RLSemantics.lean`'s `RlCondClsMaxc2`, `RlNCondClsMaxc1/qc1/qc2` | ✅ PROVED (2026-08-26) — soundness direction (schema → condition), the same direction and strength as every other `cond_*` row | none beyond schema satisfaction |
| `owlRlSchema` + `OwlRlInterpCond` + `owlRlSchema_conditions` — the schema (Horn ∪ guarded families ∪ list-valued families ∪ clash) and the bridge delivering the FULL `RlConditions` / `RlClashConditions` pair, taking the THREE remaining unexpressible rows as an interpretation-class condition | `Unified/OwlRlSchema.lean` | `Unified/Theory.lean`'s `EntailsSchema` bundle slot | ✅ PROVED (2026-08-26) | `OwlRlInterpCond` = cax-dw-comp ∧ cls-maxqc1-comp ∧ minc1-comp (nine conjuncts before 2026-08-26; correction notes 18, 21) |
| `nmAt` / `seqVal` / `seqIs_walk` / `semChain_vals` / `semShares_vals` / `spo2Rule` / `keyRule` / `owlRlSeqSchema` — prp-spo2 and prp-key as per-length Horn families: one rule per collection length, the `rdf:first`/`rdf:rest` walk and the chain (or shared-value) premises flattened into `m+1` body atoms, the last cell resting at `rdf:nil`. Generated names carry their index as a unary tail, so the valuation reads the index off a list length and no numeral injectivity is needed | `Unified/OwlRlSchema.lean` | `OWL/Semantics.lean`'s `SeqIs`; `OWL/RLSemantics.lean`'s `SemChain` / `SemShares` | ✅ PROVED (2026-08-26) — `spo2Rule_wf` / `keyRule_wf` for all lengths; `cond_prpSpo2` / `cond_prpKey` in the soundness direction, the same direction as every other `cond_*` row | — |
| `owlRlSchema_seq_rows` — prp-spo2 and prp-key follow from `SatisfiesSchema i owlRlSchema` ALONE, with no appeal to `OwlRlInterpCond` | `Unified/OwlRlSchema.lean` | `RlCondPrpSpo2`, `RlCondPrpKey` | ✅ PROVED (2026-08-26) — soundness direction | none beyond schema satisfaction |
| `allTrue_satisfies_seq` / `spo2Counter` / `seqSchema_not_everything` — NON-VACUITY for the two families: the all-true interpretation satisfies them at every length, and `spo2Counter` meets every premise of prp-spo2 at chain length 1 while denying its conclusion, so `owlRlSeqSchema` is not the everything-relation | `Unified/OwlRlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| `unified_owlRl_sound` — the stage 4 soundness gate: `OWL.RL.Derives g t` → `EntailsSchema OwlRlInterpCond owlRlSchema [rdfToTheory g] (rdfToTheory [t])` | `Unified/OwlRlAdequacy.lean` | `rl_derives_holds` + `satisfies_rdfToTheory_restrict` | ✅ PROVED (2026-08-26) | `RlReservedFree g`; conclusion is the EXISTENTIAL closure `rdfToTheory [t]` because the comprehension rows mint blank nodes |
| `unified_owlRl_clash_unsat` / `unified_owlRl_clash_entails_all` — a clashing graph has no model in the schema class, so its translation entails everything | `Unified/OwlRlAdequacy.lean` | `rl_clash_holds_false` | ✅ PROVED (2026-08-26) | `AdcMembersIri g`, `OwlRlInterpCond` |
| `OwlRlEntailsMt` + `owlRl_complete_ground` — ground completeness in CONDITION-BUNDLE form: on the Herbrand fragment, a ground triple at a non-reserved predicate entailed under `RlConditions` + `RlClashConditions` is a triple of the saturated closure | `Unified/OwlRlAdequacy.lean` | `rlHerb_conditions`, `rlHerb_clash_conditions`, `rlHerb_triple_decode` | ✅ PROVED (2026-08-26) — condition-bundle form only (correction note 19) | saturation; `RlHerbFrag c`; `¬ Clash c`; triple ground, triple-term-free, non-reserved predicate |
| `allTrue_satisfies_horn` / `allTrue_satisfies_family` / `allTrue_violates_clash` / `allFalse_satisfies_clash` / `allFalse_violates_horn` — SEPARATING models: the all-true interpretation satisfies the Horn and family parts and violates the clash part; the all-false interpretation does the reverse (cls-thing has a premise-free head). Neither half is vacuously satisfied | `Unified/OwlRlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| SCHEMA-RELATIVE GROUND COMPLETENESS NOT PROVED — `unified_owlRl_complete_ground` over `EntailsSchema … owlRlSchema` needs `liftInterp (rlHerb c)` to satisfy every row sentence; `liftInterp` reads a predication as `r.iext p.2 x.2 y.2`, so satisfaction quantifies the PREDICATE position over the whole domain, where `RlCond*` quantifies over `WfIri`. True for `rlHerb c`, but a second pass over all 79 rows — and since 2026-08-26 the pass also has to cover the two per-length families at every length, which is an induction on collection length rather than a finite row walk | — | design doc §4.4 | ⬜ OPEN (recorded gap, correction notes 19, 21) | — |
| THREE ROWS NOT IN THE SCHEMA (was nine before 2026-08-26) — **cax-dw-comp, cls-maxqc1-comp, minc1-comp**: existential heads, excluded by `DRule.definiteB`; costed and DECIDED against in the next row. Carried by `OwlRlInterpCond`, named in the soundness statement. prp-spo2 and prp-key left this residue the same day as per-length families; a ternary reserved helper predicate would also have worked (`DAtom` is n-ary and the helper need never appear in `restrictInterp i` — the earlier "a helper predicate cannot name it" was wrong) but `liftInterp` reads `rel p args` as `False` at every arity other than 2, so a ternary head is false at every model schema-relative completeness needs | `Unified/OwlRlSchema.lean` module header | design doc §4.4 | ⬜ OPEN (recorded boundary, correction notes 18, 21) | — |
| EXISTENTIAL HEADS IN THE SCHEMA — DECIDED, NOT BLOCKED. A `Schema` is a predicate on `CL.Sentence`, so an existentially headed sentence CAN be in one; the decision is not to. Two costs: (i) the head of `RlCondCompDw` is not a conjunction of atoms (`CompProps` carries two universally quantified implications and a five-variable one), so each row is a bespoke CL sentence with a bespoke satisfaction lemma; (ii) an existential head removes the least-model property the completeness direction of the stage-3 class rests on (`datalog_lfp_complete`; the `rdfD1Shape_not_wf` exclusion pins the same boundary at the program layer). If admitted later, it should be a SEPARATE sub-schema so the definite `owlRlSchema` stays available for completeness | `Unified/OwlRlSchema.lean` section header | design doc §4.4 | ⬜ DECISION RECORDED (2026-08-26, correction note 21) | — |
| HERBRAND FRAGMENT NARROWNESS — `RlHerbFrag` clause (a) (every object an IRI or blank node) excludes every graph whose closure carries a cardinality literal. Because the minc1 comprehension row emits `owl:minCardinality "1"` for each `owl:ObjectProperty` declaration, the completeness direction does not reach graphs declaring object properties. **`DTerm.lit` does NOT widen this** (measured 2026-08-26, contrary to the expectation recorded in [#613](https://github.com/danbri/factoidal/issues/613) item 3): clause (a) exists for eq-ref object form, where `rlHerb`'s `iext` reads "the triple is in the graph" and so needs the object to be an `RDF.Subject`, which RDF 1.1 Concepts §3.1 forbids a literal to be. `frag_obj_subject` is consumed at fifteen sites of `rlHerb_conditions`. Widening needs a different `rlHerbIext` for the `owl:sameAs` row, after which `rlHerb_triple_decode` would decode an atom `OWL.RL.Derives` cannot produce | `OWL/RLHerbrand.lean` module header, `Unified/OwlRlAdequacy.lean` module header | design doc §4.4 | ⬜ OPEN (recorded boundary, correction notes 20, 21) | — |

Stage 5 (landed 2026-08-26): OWL 2 Direct Semantics and the tableau
under the unified theory — `Unified/OwlDlDirect.lean` (the name
vocabulary, the class-expression translation, the transport pair and
the transfer lemmas) and `Unified/OwlDlAdequacy.lean` (the gate
theorems). Design-doc correction notes 21-26 record the deviations.
Axiom audit on every row below: `propext`, `Classical.choice`,
`Quot.sound` only (in-source `#print axioms`); `sem_inl` uses
`propext`, `Quot.sound` only.

Scope: the SHIQ fragment of `OWL/Tableau.lean` — class names, `owl:Thing`,
`owl:Nothing`, `ObjectComplementOf`, binary `ObjectIntersectionOf` /
`ObjectUnionOf`, `ObjectAllValuesFrom`, `ObjectSomeValuesFrom`, and
`ObjectMin/MaxCardinality` in both the unqualified and the qualified
form; `ClassAssertion`, `ObjectPropertyAssertion`, binary
`DifferentIndividuals`; a role box of subrole axioms and transitivity
declarations. This is the whole of `OWL.Concept` / `OWL.Assertion` /
`OWL.RoleAxioms`, so no fragment hypothesis appears in any statement.

Equality enters the unified theory here for the first time (stages 1-4
never used `CL.Sentence.eq`): `distinctBlock` is the sentence family
indexed by n carrying pairwise negated equations, and `.diff` translates
to a single negated equation.

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `dlName` / `dlDecode` / `indName` / `className` / `roleName` + `dlName_has_colon`, `dlDecode_dlName`, `dlDecode_dlName_ne`, `dlName_injective` — the colon-carrying injective encoding that separates the tableau's three name spaces from each other and from the colon-free bound-name space of `Unified/RdfEmbed.lean` | `Unified/OwlDlDirect.lean` | `Unified/RdfEmbed.lean`'s `escape` / `unescape` | ✅ PROVED (2026-08-26) — unconditional | none (correction note 21) |
| `bvar` / `bvars` / `OkArg` + `bvar_injective`, `bvar_no_colon`, `bvars_nodup`, `okArg_ne` — the bound-variable space and the argument-position invariant the counting translation threads | `Unified/OwlDlDirect.lean` | — | ✅ PROVED (2026-08-26) | — |
| `conceptFormula` / `assertionSentence` / `subRoleSentence` / `transSentence` / `roleAxiomSentences` / `owlDlDirect` — the Direct-Semantics translation (OWL 2 Direct Semantics Table 5, restricted to the fragment); cardinality as a first-order counting formula | `Unified/OwlDlDirect.lean` | `OWL.Interp.sem` | ✅ DEFINED (2026-08-26) | correction note 22 (the role-axiom sentences are included ONCE, inside `owlDlDirect`) |
| `DLCompat` + `restrictInterpDL` + `dlCompat_restrict` — the restriction half of the transport pair; the domain is PRESERVED (there is no literal operator whose arguments must be recovered from denotations) | `Unified/OwlDlDirect.lean` | `Unified/RdfTransport.lean`'s `restrictInterp` | ✅ PROVED (2026-08-26) — compatibility by `Iff.rfl` | — |
| `inlInterp` + `all_inl` + `card_sum_iff` + `sem_inl` + `liftInterpDL` + `dlCompat_lift` — the lift half. Domain `δ ⊕ String`: the right summand carries predicate identity and both extensions are FALSE on it, so every counting witness lies in the left summand where distinctness is distinctness in `δ` | `Unified/OwlDlDirect.lean` | `OWL.Interp` | ✅ PROVED (2026-08-26) | the `Option String × idom` tag-product of stage 1 is UNSOUND here — correction note 23 |
| `sat_conceptFormula` — THE transfer lemma: a `DLCompat` pair reads every class expression of the fragment the same way, at every `FreshVal` valuation and every `OkArg` argument. Induction over `OWL.Concept`, 12 cases; the four counting cases go through `sat_exBlock_card` | `Unified/OwlDlDirect.lean` | `OWL.Interp.sem`, `OWL.Interp.succWitness` | ✅ PROVED (2026-08-26) — full iff | `FreshVal i ν`, `OkArg k x` (both discharged unconditionally at the top level) |
| `sat_exBlock_card` / `sat_exBlock_card0` / `exists_fun_map` / `exists_override_map` / `sat_distinctBlock` — the counting machinery: an existential over CL VALUATIONS becomes the existential over pairwise-distinct witness LISTS that `succWitness` uses, because every list of the right length is the image of a duplicate-free name list under some valuation | `Unified/OwlDlDirect.lean` | — | ✅ PROVED (2026-08-26) — full iff | `bvars` duplicate-free (proved) |
| `satisfies_assertionSentence` / `satisfies_subRoleSentence` / `satisfies_transSentence` / `satisfiesAll_roleAxiomSentences` / `satisfiesAll_owlDlDirect_iff` — the whole translation transfer, stated ONCE against `DLCompat` and instantiated in both directions (correction note 24) | `Unified/OwlDlDirect.lean` | `OWL.Satisfies`, `OWL.SatAll`, `OWL.RespectsRBox` | ✅ PROVED (2026-08-26) — full iff | — |
| `unified_adequate_dl` — **the stage 5 gate**: `(∃ i : CL.Interp, CL.SatisfiesAll i (owlDlDirect R A)) ↔ OWL.Consistent R A` | `Unified/OwlDlAdequacy.lean` | `OWL.Consistent` (`OWL/Tableau.lean`) | ✅ PROVED (2026-08-26) — FULL iff, NO side conditions | none |
| `refuted_unified_unsat` — **the stage 5 gate, refutation side**: `OWL.Refuted R A` → the translation has no CL model. Covers the whole clash calculus: `clash`, `botClash`, `minMaxClash`, `maxClash`, `disjSplit` (branching), `minMaxClashQ`, `maxClashQ`, `minQMaxClash`, `leqMerge` (the ABox-rewriting ≤-rule) and `exWitness` (the fresh-individual ∃-rule) | `Unified/OwlDlAdequacy.lean` | `OWL.refuted_not_consistent` / `OWL.refuted_sound` | ✅ PROVED (2026-08-26) | `OWL.Refuted R A` only |
| `refuted_unified_entails_all` — explosion: a refuted ABox's translation entails every CL sentence | `Unified/OwlDlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | `OWL.Refuted R A` |
| `unified_sat_not_refuted` / `consistent_unified_sat` — the two directions of the three-valued verdict contract of [#586](https://github.com/danbri/factoidal/issues/586): "inconsistent" ⇒ unified-unsatisfiable, "consistent" (model exhibited) ⇒ unified-satisfiable; "unknown" claims nothing | `Unified/OwlDlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | — |
| `nearClashAbox_consistent` / `clashAbox_refuted` / `diff_flips_satisfiability` — SEPARATING PAIR: two ABoxes differing by ONE `owl:differentFrom` assertion, one unified-satisfiable and one unified-unsatisfiable. `Refuted` therefore holds of something (`refuted_unified_unsat` is not vacuous) and the equality machinery is what carries the verdict | `Unified/OwlDlAdequacy.lean` | `OWL.Refuted.maxClash` | ✅ PROVED (2026-08-26) | non-vacuity guards |
| `empty_unified_sat` / `empty_not_refuted` / `nearClash_not_entails_false` / `conj_entails_component` / `subRole_entails_super` — the calculus does not refute everything; a satisfiable ABox's translation has not collapsed; the translation carries real content on both the concept side and the role-box side | `Unified/OwlDlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| TABLEAU COMPLETENESS NOT PROVED — `¬ OWL.Consistent R A → OWL.Refuted R A`. `OWL/Tableau.lean`'s `Refuted` has no blocking condition and no ⊔-saturation strategy, and `OWL/TableauTheorems.lean` proves soundness only. The gate is soundness plus the satisfiability `↔`, not a decision procedure | — | design doc §4.5 | ⬜ OPEN (recorded gap, correction note 26) | — |
| FRAGMENT BOUNDARY — OWL 2 DL constructs OUTSIDE `OWL.Concept` / `OWL.Assertion`: nominals (`ObjectOneOf`, `ObjectHasValue`), datatypes and data properties (`DataSomeValuesFrom`, `DataAllValuesFrom`, data cardinality, `DatatypeRestriction`), functional and inverse-functional roles, inverse roles, role chains (`ObjectPropertyChain`), reflexive/irreflexive/asymmetric/disjoint role axioms, `Self` restrictions, and every TBox axiom other than the role box (`SubClassOf`, `EquivalentClasses`, `DisjointClasses`). `OWL/Tableau.lean`'s header names the first three as not ported; the rest were never in that datatype | `OWL/Tableau.lean` module header | OWL 2 Direct Semantics Tables 5-7 | ⬜ OPEN (recorded boundary) | — |
| DL-SPECIES GUARD DOES NOT ATTACH — `OWL/SyntaxDL.lean`'s `speciesIsDl` takes five RDF `Graph`s and decides OWL 2 DL membership from triples. The Direct-Semantics route does not factor through graphs (§5.3) and the tree has NO reader from `Graph` to `List OWL.Assertion`, so the guard has no input to guard. The stage 5 fragment guard is structural instead: `OWL.Concept` IS the fragment | `Unified/OwlDlDirect.lean` module header | `OWL/SyntaxDL.lean` | ⬜ OPEN (recorded boundary, correction note 25) | — |
| DIRECT-vs-RDF-BASED CORRESPONDENCE NOT PROVED — the two OWL 2 semantics sit side by side over the same `CL.Interp` (`owlRlSchema` on the graph route, `owlDlDirect` on the structural route). The OWL 2 correspondence theorem (RDF-Based Semantics §7.2) relating them on mapped ontologies is NOT machine-checked here, as §5.3 already states | — | design doc §5.3 | ⬜ OPEN (recorded boundary, unchanged from §5.3) | — |

Stage 6 (landed 2026-08-26): SPARQL 1.x basic graph patterns and the
entailment regimes as satisfaction queries over the unified theory —
`Unified/SparqlQuery.lean` (the definitions, the instantiation bridge,
the regime table) and `Unified/SparqlAdequacy.lean` (the theorems).
Design-doc correction notes 27-32 record the deviations. Axiom audit
on every row below: `propext`, `Classical.choice`, `Quot.sound` only
(21 in-source `#print axioms`).

**Three delimitations carried by every row.** (1) SPARQL 1.1 §18.3.1:
the engine matches a PATTERN BLANK NODE as a constant with that label,
where the specification's pattern instance mapping makes it a
non-distinguished variable that may match any RDF term
([#607](https://github.com/danbri/factoidal/issues/607)). The
narrowing agrees with the Skolem reading, so the gate is a full iff —
but on a pattern containing a blank node it is adequate TO THE ENGINE
AT `evalBgp`, not to the specification. It is no longer a fragment
restriction on what can be CLAIMED: the query path rewrites pattern
blank nodes into non-distinguished variables before evaluation, so
`unified_adequate_bgp_spec` states the gate over the rewritten pattern
with the blank-node guard PROVED (`bgpBnodeFree_rewriteBnodes`) rather
than assumed. It replaces `unified_adequate_bgp_bnodeFree`, whose
guard did no work in the proof.
(2) NO MULTIPLICITY CLAIM (design doc §5.4): `Answers` is a `Prop`,
the evaluator side is MEMBERSHIP, and nothing downstream supplies the
bag either — `SPARQL/AlgebraSpec.lean` keeps the §18.5 set and
cardinality layers apart and the F\* bag-refinement proof is not
ported. (3) `RDF.Term.eqb` is COARSER than syntactic identity
(language-tag case, `rdf:XMLLiteral` canonical XML) and `Graph.mem` is
stated over it, so answers are evaluated under `termEqSchema`.

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `varName` + `varName_no_colon`, `varName_ne_iri`, `varName_ne_bnodeName`, `varName_injective` — the reserved `?`-prefixed colon-free variable spelling, fresh against every well-formed IRI and disjoint from the `_`-initial bound blank-node names | `Unified/SparqlQuery.lean` | `Unified/RdfEmbed.lean`'s `escape` | ✅ PROVED (2026-08-26) — unconditional | — |
| `embedPatternTerm` / `embedPatternSubject` / `patternAtom` / `bgpBody` / `UQuery` / `UQuery.body` / `UQuery.instantiate` / `sparqlBgpToQuery` / `Answers` | `Unified/SparqlQuery.lean` | `SPARQL/Algebra.lean` `Bgp` | ✅ DEFINED (2026-08-26) | `UQuery` carries the PATTERN, not an arbitrary `CL.Sentence` — correction note 28 |
| `patternAtom_eq_tripleAtom` — **the bridge**: `instTriple id μ tp = some t` → `patternAtom μ tp = tripleAtom t`, a syntactic EQUALITY, so the model theory never reasons about pattern syntax | `Unified/SparqlQuery.lean` | `SPARQL.instTriple` (`SPARQL/Update.lean`), `constructPredicate` (`SPARQL/Query.lean`) | ✅ PROVED (2026-08-26) — equation, no hypotheses beyond the instantiation | — |
| `termEqSchema` + `denot_embedTerm_congr_of_schema` — the engine-term-equality schema (one `eq` row per `Term.eqb`-equal pair), and reading it back as denotation equality | `Unified/SparqlQuery.lean` | `RDF.Term.eqb` (`RDF/Core.lean`) | ✅ PROVED (2026-08-26) | delimitation 3; LBase §2.4 axiom-schema mechanism, same device as `dValueSchema` |
| `satisfies_rdfToTheorySk_iff` / `satisfies_rdfToTheorySk_restrict` — the Skolem reading transported: RDF 1.1 Semantics §6, so `HoldsAll` at a FIXED assignment, not `Satisfies` | `Unified/SparqlAdequacy.lean` | `RDF.HoldsAll` (`RDF/Semantics.lean`) | ✅ PROVED (2026-08-26) — full iff | NONE (`FreshVal i i.iName` is trivial) |
| `sat_tripleAtom_eqb` / `sat_tripleAtom_of_graphMem` — a predication about an ENGINE-equal triple transfers, under `termEqSchema` | `Unified/SparqlAdequacy.lean` | `RDF.Graph.mem`, `RDF.Subject.eqb_eq` | ✅ PROVED (2026-08-26) — full iff | `SatisfiesSchema i termEqSchema` |
| `bgp_eval_sound` (via `evalBgpFrom_matches`) — every mapping `evalBgp b g` returns instantiates the WHOLE pattern into the graph: `BgpMatches μ b g` | `Unified/SparqlAdequacy.lean` | `SPARQL.tpMatch_inst`, `instTriple_mono`, `evalBgpFrom_extends` (`SPARQL/BgpRefinement.lean`) | ✅ PROVED (2026-08-26) — UNCONDITIONAL | none |
| `bgp_matches_answers` — the pivot entails the instantiated body | `Unified/SparqlAdequacy.lean` | — | ✅ PROVED (2026-08-26) — UNCONDITIONAL | none |
| `TermQ` / `tq` / `tq_eq_iff` / `herbDenot` / `herbQ` — RDF terms modulo `Term.eqb` (`Quot.mk` for the identification, `Quot.lift` of the `eqb` predicate for the converse) and the term model in which true means "a triple of `g`" | `Unified/SparqlAdequacy.lean` | `RDF.Term.eqb_refl` / `_symm` / `_trans` (`RDF/Core.lean`); replaces `RDF.herbrand`, which separates a language tag by case | ✅ PROVED (2026-08-26) — full iff on the quotient | — |
| `herbQ_satisfiesSchema` / `herbQ_satisfies_sk` — the term model satisfies `termEqSchema` and the graph's Skolem reading | `Unified/SparqlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | `_sk` needs `RDF.GraphTtFree g` |
| `herbDenot_of_eqb` / `eqb_of_herbDenot` — the model identifies exactly what `Term.eqb` identifies | `Unified/SparqlAdequacy.lean` | — | ✅ PROVED (2026-08-26) — both directions | `eqb_of_herbDenot`: `TermTtFree` on both terms |
| `instSubject_of_denot` / `instObject_of_denot` / `constructPredicate_of_denot` / `patternAtom_reflect` — reflection: a satisfied predication forces the pattern to instantiate to a graph triple. The tag component REFUTES an unbound variable, a literal in subject position and a blank node in predicate position | `Unified/SparqlAdequacy.lean` | `SPARQL.instSubject` / `instObject` / `constructPredicate` | ✅ PROVED (2026-08-26) | `PatternSubjectTtFree` / `PatternTermTtFree`; `TermTtFree` on the graph's object |
| `unified_adequate_bgp` — **the stage 6 gate**: `BgpMatches μ b g ↔ Answers condTrue termEqSchema [rdfToTheorySk g] (sparqlBgpToQuery b) μ` | `Unified/SparqlAdequacy.lean` | `SPARQL/Algebra.lean` `evalBgp` (through `bgp_eval_sound`), `RDF.herbrand`'s quarantine discipline | ✅ PROVED (2026-08-26) — FULL iff | → UNCONDITIONAL; ← `RDF.GraphTtFree g` + `BgpTtFree b`. NO domain hypothesis on μ (an unbound variable is refuted, not excluded). Delimitations 1-3 |
| `patternTermBnodeFree_rewrite` / `patternSubjectBnodeFree_rewrite` / `bgpBnodeFree_rewriteBnodes` — the pattern `Query.evalSelect` hands the algebra, `b.map rewriteBnodeTriple`, carries NO blank node | `Unified/SparqlAdequacy.lean` | `SPARQL.rewriteBnodeTriple` (`SPARQL/Query.lean`) | ✅ PROVED (2026-08-26) — equation | `BgpTtFree b` (the one position the rewrite does not descend into is a triple-term SUBJECT, which matches no data subject) |
| `patternTermTtFree_rewrite` / `patternSubjectTtFree_rewrite` / `bgpTtFree_rewriteBnodes` — the rewrite preserves triple-term freeness | `Unified/SparqlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | `BgpTtFree b` |
| `unified_adequate_bgp_spec` — **the §18.3.1 gate with NO blank-node hypothesis**: `BgpMatches μ (b.map rewriteBnodeTriple) g ↔ Answers … (sparqlBgpToQuery (b.map rewriteBnodeTriple)) μ` for EVERY `b`, blank nodes and all. REPLACES `unified_adequate_bgp_bnodeFree`, whose `bgpBnodeFree b = true` hypothesis did no work in the proof and merely marked which instances were specification claims; the guard is now DISCHARGED by `bgpBnodeFree_rewriteBnodes` instead of assumed | `Unified/SparqlAdequacy.lean` | [#607](https://github.com/danbri/factoidal/issues/607) | ✅ PROVED (2026-08-26) — FULL iff | `RDF.GraphTtFree g` + `BgpTtFree b` and nothing else. Delimitations 2-3 still apply |
| `wBbn_rewrite_bnodeFree` / `wBbn_not_bnodeFree` / `unified_bgp_bnode_answer_witness` / `unified_bgp_bnode_no_answer` + two `#guard`s — non-vacuity for the dropped guard: `?s <p> _:z` FAILS `bgpBnodeFree`, its rewrite passes, `bgpMatchesCheck` is FALSE for the raw pattern and TRUE for the rewritten one on the same mapping, and the gate yields both a real answer and a refuted one | `Unified/SparqlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| `BindingCompat` + `tryBindSubject_complete` / `tryBindTerm_complete` / `tpMatch_complete` / `evalBgpFrom_complete` / `bgp_eval_complete` — **evaluator completeness**, the direction `SPARQL/BgpRefinement.lean` does not have: a mapping that instantiates the pattern into the graph has a counterpart the evaluator RETURNS, agreeing on every variable of the pattern up to `Term.eqb` | `Unified/SparqlAdequacy.lean` | `SPARQL.evalBgpFrom`, `Extends` (`SPARQL/BgpRefinement.lean`) | ✅ PROVED (2026-08-26) | `BgpTtFree b`. Conclusion is AGREEMENT, not `μ ∈ evalBgp b g` — correction note 27 |
| `unified_adequate_bgp_engine` / `unified_bgp_answers_returned` — the two chains: engine answer ⇒ unified answer (unconditional); unified answer ⇒ a returned mapping agreeing with it | `Unified/SparqlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | `_returned`: `GraphTtFree g`, `BgpTtFree b` |
| `regimeToSchema` / `regimeDispatchSchema` — the specification table (the four W3C names of `RDF.Regime.ofName?`, `x-rdfscore`, `x-rdfsplus`, the `x-ikl-*` family) and, separately, what `RDFS.entailmentClosureForQueryExt` ACTUALLY selects. A `#guard` pins the disagreement: the ENGINE dispatcher sends `"RDFS"` (and every other unrecognised string) to `OWL.RL.closure` | `Unified/SparqlQuery.lean` | `RDFS/RegimeDispatch.lean` module header | ✅ DEFINED + PINNED (2026-08-26) | correction notes 29, 30 |
| `regime_sound_of_closureHolds` — **the design document's one regime-soundness shape**, stated once: a materialisation-based regime's answers are unified answers over the ORIGINAL graph whenever its closure holds in every model of the graph meeting the regime's schema | `Unified/SparqlAdequacy.lean` | design doc §4.6 | ✅ PROVED (2026-08-26) | the `hclosure` premise is the regime's own content |
| `regime_sound_simple` — regime `simple`: `RDF.Regime.closure .simple = id`, so its answers are answers under the empty schema | `Unified/SparqlAdequacy.lean` | `RDF.Regime.closure` (`RDF/Entailment.lean`) | ✅ PROVED (2026-08-26) — soundness | none |
| `regime_sound_rhoDf` — regime `x-rdfscore` (the ρdf closure): every answer over the closure is an answer over the graph under `rdfsCoreSchema` | `Unified/SparqlAdequacy.lean` | `RDF.rhoDf_derives_holds` (`Unified/RhoDfSchema.lean`), `RDFS.closure_sound` | ✅ PROVED (2026-08-26) — soundness | none |
| `regime_rhoDf_answers_closure_iff` — regime `x-rdfscore`, the materialisation is ANSWER-PRESERVING: under the ρdf schema, answering from the closure's Skolem reading and from the graph's are the SAME relation. The Skolem-level analogue of `RDF.rhoDfEntails_closure_iff` | `Unified/SparqlAdequacy.lean` | `RDF.rhoDfEntails_closure_iff` | ✅ PROVED (2026-08-26) — FULL iff, both directions | none |
| `regime_sound_rdfs` — regime `RDFS` (`RDF.Regime.closure .rdfs`, the full closure) | `Unified/SparqlAdequacy.lean` | `RDF.derivesFull_holds`, `RDF.axiomaticTriples_hold`, `RDFS.fullClosure_sound` | ✅ PROVED (2026-08-26) — soundness | `∀ c ∈ cmps, RDF.IsRdfMemberIri c`; `rdf:XMLLiteral ∈ D` (stage 2 note 10b) |
| `ikl_extend_entailed` + `regime_sound_ikl` — **`x-ikl-*` regime soundness AGAINST THE UNIFIED LAYER'S OWN DATASET READING**: `datasetToTheory ds` entails the whole extended default graph `CL.IklRegime.extendDataset` computes, and an engine answer over that graph is a unified answer from the dataset's embedding. Condition: `CL.IklRespectsThat` alone. RESTATED 2026-08-26 ([#609](https://github.com/danbri/factoidal/issues/609) item 3) — until then both were stated in `Unified/SparqlAdequacy.lean` over `iklPremises`, a reading that asserts EVERY named graph | `Unified/ClBridge.lean` | `CL/IklRegime.lean` `extendDataset`; `Unified/DatasetEmbed.lean` `datasetToTheory` | ✅ PROVED (2026-08-26) — soundness, every suffix, any asserting subject | `datasetBnodeNames ds = []` (the fragment every `ToRdf` output occupies; `#guard` pins it for the witness, not proved for all texts); named subsets deferred to [#581](https://github.com/danbri/factoidal/issues/581) |
| `mergeWhere` + `mergeWhere_entailed` + `mergeAll_entailed` + `iklPremises_extend_entailed` — the SUPERSEDED `iklPremises` statement holds for EVERY selection predicate over the named graphs, the regime's `urn:cl:def:asserts` test and the merge-everything predicate alike, so it certified nothing about the CHOICE of predicate and did not see [#581](https://github.com/danbri/factoidal/issues/581)'s narrowing (a link decoration does not assert). This is the measurement that moved regime soundness onto `datasetToTheory` | `Unified/ClBridge.lean` | `CL/IklRegime.lean` `extendDataset` | ✅ PROVED (2026-08-26) — strength delimitation of the superseded statement | — |
| `wDsMentioned` + `embedding_sees_the_assertion_decoration` (`embedding_entails_content` / `embedding_refutes_mentioned_content` / `premises_entail_mentioned_content`) — **the replacement statement IS predicate-sensitive**: over `datasetToTheory` the proposition's content is entailed on `wDs` and REFUTED on `wDsMentioned` — the same dataset with the assertion decoration deleted — while `iklPremises` entails it on both. `#guard`s pin the executable half (the regime does not merge the mentioned graph; the merge-everything predicate does) | `Unified/ClBridge.lean` | `CL.IklRegime.extendDataset` | ✅ PROVED (2026-08-26) — sensitivity, one refutation witness | separating model `coherentBlind` |
| `premises_entail_content` + `decorationOnly_refutes_content` + `ikl_reading_diverges_from_decoration_only_embedding` — **the two renderings of a proposition inside RDF DISAGREED, over the SUPERSEDED embedding**: on `wDs`, the real `CL.toRdfDataset` output for `((that (Dead OBL)))`, `iklPremises` entails the asserted proposition's content triple and `decorationOnlyToTheory` does not — and does not under `PropAlphaInvariant` either. Separating model `typeBlindInterp`. RESTATED 2026-08-26: these were stated about `datasetToTheory`, which the [#609](https://github.com/danbri/factoidal/issues/609) item-3 repair changed; the statements are FALSE of the repaired reading (`embedding_entails_content`) and are kept about the reading they were evidence against — the `topLevel_exclusion_insufficient_for_tt` pattern of the [#602](https://github.com/danbri/factoidal/issues/602) repair | `Unified/ClBridge.lean` | `CL/ToRdf.lean` translation; `Unified/DatasetEmbed.lean` `decorationOnlyToTheory` | ✅ PROVED (2026-08-26) — refutation witness, [#609](https://github.com/danbri/factoidal/issues/609) item 3 | witness pinned to the parser + translator by `#guard`; premise AND conclusion each shown satisfiable |
| `decorationOnly_refutes_content_ikl` — the divergence survived `CL.IklRespectsThat`, and this row names the defect exactly: coherence constrains a proposition's ZERO-ARY relation extension, and the superseded embedding put the `that`-term in the second argument of `urn:cl:def:names`, where coherence says nothing. The repair moved the `that`-term into the zero-ary position | `Unified/ClBridge.lean` | `CL.IklRespectsThat` (`CL/Semantics.lean`) | ✅ PROVED (2026-08-26) — refutation witness about the superseded reading | separating model `coherentBlind` |
| `pDen` / `pSeq` / `pSat` / `pAll` / `pAny` / `pForall` / `pExists` + `pSat_eq` + `propModel` + `propModel_coherent` — **the first IKL-coherent interpretation in the tree**. Domain `Prop`; a proposition IS a `Prop`; `pSat` writes the model's own satisfaction out as a recursion, which breaks the circularity between `CL.Sat` and `Interp.iProp`. `pSat_eq` proves the recursion agrees with `CL.Sat` clause by clause | `Unified/ClBridge.lean` | `CL.Sat`, `CL.IklRespectsThat` (`CL/Semantics.lean`) | ✅ PROVED (2026-08-26) — satisfiability witness | `propModel_coherent` needs `∀ p, R p [] ↔ p` (zero-ary predication transparent) |
| `embed_asserts_decorated_graphs` + `embedding_entails_content` + `ikl_reading_agrees_with_dataset_embedding` — **the repair, as a DERIVATION**: under `CL.IklRespectsThat` ALONE, an interpretation satisfying `datasetToTheory ds` satisfies the content of every named graph the default graph decorates with `urn:cl:def:asserts`. The regime's encoding commitment (`CL/IklRegime.lean`, "Encoding commitment") is therefore a theorem, not a condition. REMOVED with this landing: `IklAssertionCommitment` (the adopted condition) and `commitment_not_derivable` (its non-derivability), both of which described the superseded embedding | `Unified/ClBridge.lean` | `CL.IklRegime.extendDataset`; `CL.sat_assert_that` | ✅ PROVED (2026-08-26) — derivation, replaces an adopted condition | `datasetBnodeNames ds = []` (the fragment every `ToRdf` output occupies; `#guard` pins it for the witness, not proved for all texts) |
| `objModel` / `objModel_respectsThat` / `ikl_extend_entailed_nonvacuous` / `objModel_not_everything`, `decorationOnly_strictly_weaker`, `divergence_premise_satisfiable` / `_conclusion_satisfiable` — non-vacuity: `objModel` is IKL-coherent, satisfies the REPAIRED embedding of the witness dataset, and refutes a sentence; `coherentBlind` satisfies the superseded reading of the same dataset and refutes the repaired one, so the refinement `datasetToTheory_entails_decorationOnly` is proper | `Unified/ClBridge.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| `regime_sound_ikl` RELATIVE TO `iklPremises` — CLOSED 2026-08-26 by changing the embedding, not the condition. Regime soundness is now stated over `[datasetToTheory ds]` under `CL.IklRespectsThat` and is sensitive to the `urn:cl:def:asserts` test. What is NOT claimed: anything outside `datasetBnodeNames ds = []`, anything about the SUFFIX (all suffixes route to one handler, [#581](https://github.com/danbri/factoidal/issues/581)), and completeness in either direction | `Unified/ClBridge.lean` | [#609](https://github.com/danbri/factoidal/issues/609) item 3 | ✅ CLOSED (2026-08-26, correction note 33) | fragment guard above |
| CL/IKL EXECUTABLE STACK — SATISFACTION HALF NOW PROVED, READER HALF A FRAGMENT STATEMENT. [#609](https://github.com/danbri/factoidal/issues/609) item 1 is closed by `satFin_eq` and item 2 is bounded by `CL/ClifAdequacy.lean`; both are itemised in the block below. Item 3 (`toRdf_adequate`) is the `Unified/ClBridge.lean` rows above | `CL/FiniteSatTheorems.lean`, `CL/ClifAdequacy.lean` | [#609](https://github.com/danbri/factoidal/issues/609) | 🟡 PARTLY CLOSED (2026-08-26) | see the block below |
| `bgpMatches_append` / `satisfies_bgpBody_append` / `answers_bgp_append_iff` — **§18.5's JOIN is the conjunction on the `EntailsSchema` side**: answering the concatenated pattern is answering both parts | `Unified/SparqlAlgebra.lean` | `SPARQL/AlgebraSpec.lean` `InJoin` | ✅ PROVED (2026-08-26) — FULL iff | NONE. Holds for every condition bundle, schema and premise list |
| `unified_adequate_join` / `unified_adequate_join_conj` — **the JOIN gate**: `(BgpMatches μ b₁ g ∧ BgpMatches μ b₂ g) ↔ Answers … (sparqlBgpToQuery (b₁ ++ b₂)) μ` | `Unified/SparqlAlgebra.lean` | [#614](https://github.com/danbri/factoidal/issues/614) | ✅ PROVED (2026-08-26) — FULL iff | `RDF.GraphTtFree g`, `BgpTtFree b₁`, `BgpTtFree b₂` — the stage 6 gate's own guards and no others. No blank-node hypothesis. No multiplicity |
| `bgpMatches_mono` / `extends_of_isMerge_left` / `extends_of_isMerge_right` / `inJoin_bgpMatches` / `unified_join_answers` — **a §18.5 join row over two BGP evaluations is a unified answer**. This is where merge and compatibility do the work: the merged mapping `Extends` both arguments, and `SPARQL.instTriple_mono` carries `BgpMatches` along | `Unified/SparqlAlgebra.lean` | `SPARQL/AlgebraSpec.lean` `merge_extends_left` / `_right`; `SPARQL/BgpRefinement.lean` `instTriple_mono` | ✅ PROVED (2026-08-26) — UNCONDITIONAL | none |
| `unified_join_engine_answers` — a row of the RUNNING `SPARQL.join` is a unified answer | `Unified/SparqlAlgebra.lean` | `SPARQL/JoinRefinement.lean` `join_spec_sound` | ✅ PROVED (2026-08-26) — soundness, hypothesis-carrying | `∀ m₁ ∈ Ω₁, ∀ m₂ ∈ Ω₂, Binding.compatible m₁ m₂ → Compatible m₁ m₂` — `join_spec_sound`'s own hypothesis; `compatible_not_Compatible_of_coarse` is the witness that it cannot be dropped |
| `jCompatible` / `jInJoin` / `unified_join_answer_witness` / `unified_join_no_answer` + four `#guard`s — non-vacuity for JOIN: two real evaluator rows sharing a variable, compatible, merging to a row that matches the concatenated pattern; the reversed mapping is refuted | `Unified/SparqlAlgebra.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| `bgpDisjBody` / `AnswersUnion` / `satisfies_bgpDisjBody_iff` / `answers_union_of_or` — **§18.5's UNION as the disjunction of the two instantiated bodies.** There is no basic graph pattern whose query is a union, so `UQuery` cannot carry one and `AnswersUnion` is entailment of the disjunction | `Unified/SparqlAlgebra.lean` | `SPARQL/AlgebraSpec.lean` `InUnion` | ✅ PROVED (2026-08-26) — `answers_union_of_or` is ONE DIRECTION, unconditional | none |
| `unified_adequate_union` — **the UNION gate**: `(BgpMatches μ b₁ g ∨ BgpMatches μ b₂ g) ↔ AnswersUnion … [rdfToTheorySk g] b₁ b₂ μ` | `Unified/SparqlAlgebra.lean` | [#614](https://github.com/danbri/factoidal/issues/614) | ✅ PROVED (2026-08-26) — FULL iff | `RDF.GraphTtFree g`, `BgpTtFree b₁`, `BgpTtFree b₂`. The ← direction reads one disjunct off `herbQ g`; that step is NOT a general property of `EntailsSchema` — see the row below |
| `entailsSchema_disj_does_not_split` — **the exact strength of that gate**: the premise list `[A ∨ B]` entails `A ∨ B` and NEITHER disjunct, with the two term models as the refutations. So `unified_adequate_union`'s ← direction is a property of the premise list `[rdfToTheorySk g]` (it has a canonical model), not of entailment | `Unified/SparqlAlgebra.lean` | — | ✅ PROVED (2026-08-26) — refutation witness | separating models `herbQ uG1`, `herbQ uG2` |
| `extends_of_smapEq` / `inUnion_bgpMatches` / `unified_union_answers` / `unified_union_engine_answers` — a §18.5 union row, and a row of the RUNNING `SPARQL.union`, are unified answers to the union. Unconditional in both cases: `union` is list append, so there is no compatibility test to be coarse about | `Unified/SparqlAlgebra.lean` | `SPARQL/AlgebraRefinement.lean` `occurs_append` | ✅ PROVED (2026-08-26) — UNCONDITIONAL | none |
| `unified_union_answer_witness` / `unified_union_no_answer` + six `#guard`s — non-vacuity for UNION: a real answer over a graph one branch matches, and a refutation over a graph neither matches | `Unified/SparqlAlgebra.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| `inFilter_answers` / `unified_adequate_filter` — **§18.5's FILTER**: a filter row is a unified answer PLUS its side condition, and the gate is a full iff whose filter conjunct is the SAME on both sides. §18.5 states FILTER parametrically in `FExpr := SMap → Bool`; `f μ` has no reading in an interpretation, and neither theorem gives it one | `Unified/SparqlAlgebra.lean` | `SPARQL/AlgebraSpec.lean` `InFilter` | ✅ PROVED (2026-08-26) — `inFilter_answers` UNCONDITIONAL; `unified_adequate_filter` a full iff under `RDF.GraphTtFree g` + `BgpTtFree b` | the filter conjunct is carried, not interpreted |
| `embedPatternTerm_congr` / `embedPatternSubject_congr` / `patternAtom_congr` / `bgpBody_congr` / `answers_congr_onVars` — **`Answers` reads the solution mapping ONLY through the pattern's own variables**: two mappings agreeing there instantiate the pattern to the SAME sentence (a syntactic equality), hence give the same verdict for every condition bundle, schema and premise list | `Unified/SparqlAlgebra.lean` | — | ✅ PROVED (2026-08-26) — syntactic equality | agreement on `bgpVars b` |
| `filter_not_determined_by_the_query_sentence` — **the FILTER negative result.** For EVERY function `φ` from sentences to sentences, every premise list, every bundle and every schema, the claim "`φ (bgpBody μ b)` is entailed exactly when the filter passes" is FALSE. Witness: two mappings that instantiate the pattern identically, separated by `bound(?z)` on a variable outside the pattern (§17.4.1.1). So the filter conjunct in `unified_adequate_filter` cannot be replaced by an entailment and must stay a side condition on the mapping. `SPARQL/AlgebraRefinement.lean`'s `FExprCongr` is the algebra-layer counterpart, and it assumes congruence up to `SMapEq` — agreement on ALL variables, not on the pattern's | `Unified/SparqlAlgebra.lean` | [#614](https://github.com/danbri/factoidal/issues/614) | ✅ PROVED (2026-08-26) — refutation, universally quantified over `φ` | none — the refutation holds for every `φ`, premise list, bundle and schema |
| FILTER'S CONDITION HAS NO MODEL-THEORETIC READING HERE — §17's effective boolean value is three-valued (an expression may raise an error) and is defined on RDF terms and their lexical/value spaces, not on the denotations of an interpretation. §18.5 itself states FILTER parametrically for that reason, and this stage keeps it parametric. Internalising §17 is a separate stage, not a missing lemma | `Unified/SparqlAlgebra.lean` module header | [#614](https://github.com/danbri/factoidal/issues/614) | ⬜ OPEN (recorded boundary, with `filter_not_determined_by_the_query_sentence` as its proof that the boundary is real) | — |
| UNION CARDINALITY NOT CLAIMED — §18.5's union ADDS multiplicities. `InUnion` is `Occurs` in either operand, a `Prop`, and `AnswersUnion` is a `Prop`. `SPARQL/AlgebraRefinement.lean`'s `union_card` states the cardinality law at the algebra layer; nothing ties it to the unified layer | `Unified/SparqlAlgebra.lean` | design doc §5.4 | ⬜ OPEN (instance of the multiplicity boundary) | — |
| JOIN COMPLETENESS BACK TO THE ENGINE'S `join` LIST NOT PROVED — `bgp_eval_complete` gives, per side, a returned mapping agreeing with μ up to `Term.eqb`; assembling the two into one row of `join` needs the engine's `Binding.compatible` to hold of them, which needs a domain lemma for `evalBgp` the tree does not have, and the conclusion would still be agreement up to `Term.eqb`, not membership (correction note 27) | `Unified/SparqlAlgebra.lean` module footer | [#614](https://github.com/danbri/factoidal/issues/614) | ⬜ OPEN (recorded gap) | — |
| `bgpMatchesCheck` + `bgpMatchesCheck_iff`, `unified_bgp_answer_witness`, `unified_bgp_no_answer`, `termEqSchema_nontrivial` — non-vacuity: the pivot decided with BOTH polarities pinned by `#guard`; a real answer; a REFUTED answer (so the gate is not compatible with `Answers` holding of everything); a schema row that is not an instance of reflexivity | `Unified/SparqlAdequacy.lean` | — | ✅ PROVED (2026-08-26) | non-vacuity guards |
| ENGINE MATCHES PATTERN BLANK NODES AS CONSTANTS **at `evalBgp`** — `tryBindSubject` / `tryBindTerm` require label equality, so every stage 6 row stated over `evalBgp` or over a raw `b` is adequate to that entry point, not to §18.3.1. The QUERY path does not go through a raw `b`: `Query.evalSelect` / `evalAsk` / `evalConstruct` run `QueryPattern.rewriteBnodes` first, and `unified_adequate_bgp_spec` is the gate stated over the rewritten pattern with no blank-node hypothesis. The 2026-08-26 repair extended the rewrite to EXISTS bodies, which it did not reach before | `SPARQL/Algebra.lean` (raw entry point) | [#607](https://github.com/danbri/factoidal/issues/607) | 🟡 NARROWED (2026-08-26, correction note 32 updated) — closed for the query path, open for the raw `evalBgp` entry point and for the F\* tree, whose `substitute_existentials` still leaves EXISTS-body blank nodes as constants | — |
| NO MULTIPLICITY CLAIM, AND NONE AVAILABLE DOWNSTREAM — `Answers` is a `Prop` and the evaluator side is membership. `SPARQL/AlgebraSpec.lean` keeps the §18.5 set layer and the cardinality layer apart, and the F\* bag-refinement proof is not ported, so no downstream theorem ties `evalBgp`'s bag to the specification's | — | design doc §5.4 | ⬜ OPEN (recorded boundary, unchanged from §5.4) | — |
| MEMBERSHIP ON THE NOSE NOT CHARACTERISED — `μ ∈ evalBgp b g` fixes a binding-list ORDER (the evaluator conses subject → predicate → object, left to right) and `tryBindTerm`'s already-bound arm keeps the FIRST term bound to a variable, comparing only by `Term.eqb`. Both are invisible to any semantic condition, so `bgp_eval_complete` concludes AGREEMENT up to `Term.eqb`, not membership | `Unified/SparqlAdequacy.lean` module header | design doc §4.6 | ⬜ OPEN (recorded boundary, correction note 27) | — |
| EVALUATOR COMPLETENESS ONLY ON TRIPLE-TERM-FREE PATTERNS — `tryBindTerm`'s `.tripleTerm` arm recurses through sub-positions with intermediate mappings, which needs the whole `*_complete` family one level down. `BgpTtFree` excludes it. (The MODEL side needs the same guard for the independent reason that the term model gives every triple term one quarantine constant) | `Unified/SparqlAdequacy.lean` | — | ⬜ OPEN (recorded boundary) | — |
| REGIME COMPLETENESS AGAINST THE RUNNING EVALUATOR NOT PROVED — `regime_rhoDf_answers_closure_iff` is answer-preservation of the MATERIALISATION, not "the engine returns every ρdf answer". The latter needs the closure to be SATURATED, which is the `rhoDfClosedCheck` hypothesis the stage 2 decided corollary carries; `x-rdfsplus` has no closure-soundness theorem at all (stage 3 landed the RDFS-Plus Datalog tier at demo-instance strength only) | — | design doc §4.6 | ⬜ OPEN (recorded gap, correction note 30) | — |
| ENGINE REGIME DISPATCH IS NARROWER THAN THE REGIME TABLE — `RDFS.entailmentClosureForQueryExt` recognises `x-rdfscore` and `x-rdfsplus` and routes EVERY other string, `"RDFS"` and `"OWL-RL"` included, to `OWL.RL.closure`. `regime_sound_rdfs` is about `RDF.Regime.closure .rdfs`, which is a DIFFERENT entry point. Splitting the dispatch is engine work, not registry work | `RDFS/RegimeDispatch.lean` module header | — | ⬜ OPEN (recorded divergence, correction note 29) | — |
| `String.toLower` IS KERNEL-OPAQUE — neither `decide` nor `rfl` discharges `RDF.langTagEq "EN" "en" = true`, so `termEqSchema_nontrivial` carries the language-tag fact as a hypothesis and the concrete instance is pinned by `#guard` instead. Not a gap in the theory; a note for the next session that reaches for `decide` on a string-normalising function | `Unified/SparqlAdequacy.lean` | — | ⬜ RECORDED (2026-08-26) | — |

Issue [#609](https://github.com/danbri/factoidal/issues/609) items 1
and 2 (landed 2026-08-26): the host logic's own executable stack
against `CL/Semantics.lean` — `CL/FiniteSatTheorems.lean` (the
satisfaction agreement) and `CL/ClifAdequacy.lean` (what a CLIF
reader-adequacy claim can be here). Design-doc correction notes 35 and
36. Axiom audit on every row below: `propext`, `Classical.choice`,
`Quot.sound` only (in-source `#print axioms`, 16 declarations).

| Theorem | Module | Native anchor | Status | Fragment / hypotheses |
|---|---|---|---|---|
| `satFin_eq` — `sat fi v s = true ↔ CL.Sat fi.toInterp v.ind v.seq s`; `satisfiesFin_eq` the same at sentence level. **The satisfaction half of the pair whose term half is `denotTermFin_eq` / `denotSeqFin_eq`.** One induction on the fuel argument carries all five functions of the satisfaction group; the `Sentence.size` bound `CL/FiniteSat.lean`'s header argued informally is the induction's side condition | `CL/FiniteSatTheorems.lean` | `CL.Sat` / `CL.Satisfies` (`CL/Semantics.lean`), `sat` (`CL/FiniteSat.lean`) | ✅ PROVED (2026-08-26) — FULL iff | THREE, each named in the statement: `[LawfulBEq α]`; `hdom : ∀ x : α, x ∈ fi.domain`; `hns : noSeqQuant s = true`. Free sequence markers are NOT excluded |
| `domain_hypothesis_necessary` / `seqQuant_hypothesis_necessary` / `lawfulBEq_hypothesis_necessary` — each hypothesis shown NOT removable. `FiniteInterp.toInterp` reads neither `domain` nor `maxSeq`, so `partialFin`/`witFin` and `seqFin0`/`seqFin1` are the SAME `Interp` while the checker decides the same sentence differently over them; the `BEq` row uses a two-element domain type whose `==` is constantly `true` | `CL/FiniteSatTheorems.lean` | — | ✅ PROVED (2026-08-26) — separating pairs | concrete witnesses; the `BEq` row is stated at the `sat`/`Sat` level because the unlawful instance changes `toInterp` |
| `sat_atom_iff` / `sat_eq_iff` / `sat_conj_iff` / `sat_disj_iff` / `sat_neg_iff` / `sat_impl_iff` / `sat_iff_iff` / `sat_all_iff` / `sat_ex_iff` / `satAll_*` / `satAny_*` / `satForall_*` / `satExists_*` — one `rw [Sat]`-proved clause lemma per constructor over an ARBITRARY `Interp`. Needed because `CL.Sat` is well-founded-compiled and `simp only [Sat]` cannot fire at `fi.toInterp`: the valuation type-checks against `String → i.dom` only at DEFAULT transparency, `simp` matches at `implicit` | `CL/FiniteSatTheorems.lean` | `CL/Semantics.lean` | ✅ PROVED (2026-08-26) — reusable, unconditional | — |
| `iProp_valuation_independent` / `denotTermFin_that_constant` — the FOURTH condition `CL/FiniteSat.lean`'s header named (valuation-independent `that`-reading) is NOT a hypothesis of `satFin_eq` and cannot be: `toInterp.iProp` is a lookup keyed by canonical CLIF text, so both are `rfl` | `CL/FiniteSatTheorems.lean` | `CL/FiniteSat.lean` header conditions | ✅ PROVED (2026-08-26) — condition reclassified | — |
| `witFin_not_ikl_coherent` — the boundary that condition was really about: the finite reading does NOT meet `CL.IklRespectsThat` in general, so `satFin_eq` is agreement with `fi.toInterp`, not with IKL entailment. `Unified/ClBridge.lean`'s `propModel` is the coherent interpretation the finite reading is not | `CL/FiniteSatTheorems.lean` | `CL.IklRespectsThat` (`CL/Semantics.lean`) | ✅ PROVED (2026-08-26) — refutation witness | concrete `witFin` |
| `witFin` + `wit_sat_boyBill` / `wit_sat_ex` / `wit_sat_neg` / `wit_sat_restricted` / `wit_not_sat_boySue` / `wit_not_sat_allBoy` — non-vacuity: `CL.Examples`' `tiny` over a FINITE domain type, so `hdom` is `decide`-dischargeable; the four `tiny_sat_*` shapes come back through `satisfiesFin_eq` as `Satisfies` theorems and two shapes come back as refutations, so the agreement is not compatible with `Sat` holding of everything | `CL/FiniteSatTheorems.lean` | `CL/Examples.lean` `tiny_sat_*` | ✅ PROVED (2026-08-26) | non-vacuity guards |
| `seqItemsToClif_seqmark` / `bindingToClif_seqmark` — the serialiser guards NAME spellings through `renderName` and writes a SEQUENCE MARKER as the raw `"..." ++ m`. Both `rfl`: what is machine-checked is the ABSENCE of a case split | `CL/ClifAdequacy.lean` | `Sentence.toClif` (`CL/Clif.lean`) | ✅ PROVED (2026-08-26) | — |
| `markerLexable` + `sentMarksLexable` (with `termMarksLexable` / `seqMarksLexable` / `bindMarksLexable` / `sentsMarksLexable`) — the fragment the round trip holds on, found by measuring 38 shapes rather than read off the code | `CL/ClifAdequacy.lean` | `CL/Clif.lean` lexer | ✅ DEFINED (2026-08-26) | — |
| THE CLIF ROUND TRIP IS FALSE IN GENERAL — `.atom (.name "P") [.seqmark "a b"]` serialises to `(P ...a b)` and reads back with TWO argument items. Pinned by `#guard` through argument COUNTS (`Nat` has `DecidableEq`, so the sharpest form uses no comparator). The string-level `#guard`s already in `CL/Clif.lean` cannot see it: the misparse re-serialises to the SAME text, so `stable "(P ...a b)"` is `true` | `CL/ClifAdequacy.lean` | `CL/Clif.lean` | ✅ RECORDED (2026-08-26) — counterexample, `#guard`-pinned | `markSpaceSentence`, `markParenSentence` |
| `clif_roundTrip` — `∀ s, sentMarksLexable s = true → parseClifSentence s.toClif = .ok s` — NOT PROVED. Needs the lexer taken apart: `lexAcc` fuel-monotonicity, a decomposition over `++` with the position counter threaded, the same for `parseSExpr` over token-list concatenation, then `readSentence` inverted | `CL/ClifAdequacy.lean` module header | ISO/IEC 24707 Annex A | ⬜ OPEN (named lemma, correction note 36) | — |
| THE KERNEL CANNOT REDUCE THIS PARSER AT USEFUL SIZES — so INSTANCE-level round-trip theorems (`parseClifSentence s.toClif = .ok s` by `rfl` for a concrete `s`) are unavailable too. Measured 2026-08-26, 16 GB container: `(P a)` and `(P a b)` reduce in 4-6 s; `(P ...a b)` and `(forall (x) (P x))` exhaust memory and are killed after 150-200 s. The cliff is in the string primitives the lexer goes through, not the grammar. `native_decide` is banned. The 38-shape corpus is therefore `#guard` (COMPILED evaluation): tests, not proofs | `CL/ClifAdequacy.lean` module header | — | ⬜ RECORDED (2026-08-26) — measurement, plan input | — |
| `Sentence.structEq` LAWFULNESS NOT PROVED — `DecidableEq` does not derive for the `Term`/`SeqItem`/`Binding`/`Sentence` mutual family (checked 2026-08-26: no deriving handler applies), so the corpus tests compare with a hand-written Bool equality. No theorem relates `structEq a b = true` to `a = b`; it is test harness. The counterexample rows do not depend on it | `CL/ClifAdequacy.lean` | — | ⬜ OPEN (recorded boundary) | — |
| ANNEX A HAS NO INDEPENDENT FORMALISATION HERE — a CLIF text means what the abstract sentence it denotes means, which is clause 6 in `CL/Semantics.lean`. There is no second formal object for the reader to be adequate TO, so "the reader denotes per Annex A" is not statable as an agreement; the round trip against the serialiser is what is available | `CL/ClifAdequacy.lean` module header | ISO/IEC 24707 Annex A | ⬜ RECORDED (2026-08-26) — scope statement | — |


Stage 7 (2026-08-26): no new theorems. The account of what stages 1-6
proved — every gate theorem quoted as landed with its exact strength,
the named gaps, the defects the proof attempts found in shipping code,
and the list of claims NOT made — is
[`docs/designissues/2026-08-26-lbase-account.md`](designissues/2026-08-26-lbase-account.md).
Public version, with the ρdf closure, Finding C-1's separating pair and
an OWL 2 RL row computed live beside the theorems that cover them: hub
post 43, `docs/web/hub/43-one-model-theory-under-all-of-it.md`
(cells pinned by `tests/hub/post43_test.mjs`).
