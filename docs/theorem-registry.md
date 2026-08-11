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
| [ext] | n/a | `cls_maxqc_comp` | N/A | UNATTEMPTED | — | The #236 anchor machinery. **Known sound-but-narrow** (see CLAUDE.md "Known sound-but-narrow rewrites"): drops vacuous-truth individuals and OWL-Full punned class-individuals; the internal-variable LEAK the 2026-07-09 strict runner found is FIXED (task #100, `strip_rewrite_internal_vars`). |
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
| cax-adc | `cax_adc_clash` (union target: `table6_clashes` = `cax_dw_clash \/ cax_adc_clash`) | `all_disjoint_classes` (premise expansion) + `is_inconsistent` check 3, hoisted as `owl_has_disjoint_class_clash` | ✅ PROVED — detection-soundness against `table6_clashes`, **not** `cax_adc_clash` alone (`theorem_cax_adc_cax_dw_detection_sound`, `OWL.RL.Refinement.fst` section 30) | N/A (clash row) | `rdf_type_objects_resource g` (rdf:type objects are IRI/bnode, never literal — see banner) | CLASH-ROW ADJUDICATION (2026-08-06): the engine detects this row in TWO STAGES — `owl_rule_all_disjoint_classes` materialises pairwise `owl:disjointWith` from an `owl:AllDisjointClasses` membership list (premise infra, not itself a clash check), then `is_inconsistent`'s check 3 (now the named top-level `owl_has_disjoint_class_clash`, hoisted out of the anonymous `let`, behavior-identical) looks for two `rdf:type` triples on one subject whose objects are `owl:disjointWith`. That boolean CANNOT tell whether the `disjointWith` triple was asserted directly (cax-dw) or materialised from a list (cax-adc) — a graph with only an asserted cax-dw pair and no AllDisjointClasses node also flips it — so the only TRUE statement it licenses is the row UNION `table6_clashes`, proved here. Completeness (the converse: `table6_clashes g ==> owl_has_disjoint_class_clash g == true`) is PLAUSIBLE for the cax-dw disjunct (single step) but ENGINE-NARROWED for cax-adc: `owl_rule_all_disjoint_classes` uses `decode_chain_list`, an IRI-only `rdf:first`/`rdf:rest` decoder that returns `None` (no-op) on a member list containing a bnode class expression — the same narrowing already documented for `owl_rule_property_chain_n`/prp-key's list machinery — so completeness is NOT claimed for AllDisjointClasses lists with non-IRI members. |
| prp-adp | `prp_adp_clash` (union target: `prp_pdw_clash \/ prp_adp_clash`, both disjuncts of `table4_clashes_complete`) | `all_disjoint_properties` (premise expansion) + `is_inconsistent` check 6, hoisted as `owl_has_pdw_direct_clash` | PARKED — detection-soundness attempted, two-attempt-stop; see Notes | N/A (clash row) | — | CLASH-ROW ADJUDICATION (2026-08-06): SAME shape as cax-adc — `owl_rule_all_disjoint_properties` materialises pairwise `owl:propertyDisjointWith`, then `is_inconsistent` check 6 (hoisted as `owl_has_pdw_direct_clash`/`owl_is_pdw_pair`, `OWL.Closure.fsti`, behavior-identical) looks for two triples sharing subject AND object through a disjoint property pair — cannot attribute to prp-pdw (asserted) vs prp-adp (materialised), so the provable statement is the row union, same reasoning as cax-adc. PARKED, not proved: unlike cax-adc's `t1.o`/`t2.o` (rdf:type objects, provably IRI/bnode via `rdf_type_objects_resource`), check 6's shared object `t1.o == t2.o` (`rdf_term_eq t1.o t2.o`, required TRUE by the check) ranges over ARBITRARY property values, which legitimately include literals in real OWL RL data (`New-Feature-DisjointDataProperties-*`). `rdf_term_eq` on two literals is RDF-1.1 VALUE equality (case-insensitive lang tag, XMLLiteral c14n, #337) while `prp_pdw_clash`/`prp_adp_clash` need SYNTACTIC `==`; a graph with `t1.o = "V"@EN`, `t2.o = "V"@en` flips the check without giving a `==`-exact witness. Closing this needs either (a) a graph-level "literals `rdf_term_eq`-related implies `==`-equal" hypothesis (true for realistic non-adversarial data, mirrors prp-key's `cond_literal_term_eq_respecting` weakening pattern already accepted in this ledger), or (b) restating literal-value-aware `prp_pdw_clash`/`prp_adp_clash` variants in `OWL.RL.Spec.fst` using `rdf_term_eq`/`literal_value_eq` instead of `==` (the cls-hv2/prp-key WEAKENED-ROW precedent). Recipe otherwise identical to cax-adc's proved lemma; the hoisted `owl_has_pdw_direct_clash`/`owl_is_pdw_pair` are ready for whichever fix lands. Completeness note: same ENGINE-NARROWED `decode_chain_list` (IRI-only) caveat as cax-adc. |
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
| Bucket lookup completeness — the other FIVE buckets | `RDF.Indexed.Completeness.fst` stage 6 (2026-08-06) | ✅ PROVED | `lemma_build_indexed_complete_subj` / `_sp` (total keys, no side condition) and `_obj` / `_po` / `_so` (option keys — conditional on `bucket_key_X t == Some k`, because `build_bucket` files a literal-object or triple-term-object triple in NO binding). Each is the generic stage-5 lemma at one more `key_of`. Removes the first half of finding BR-4. |
| Dedup-key injectivity (literal arm, #348 fix) | `RDF.Indexed.KeyInjectivity.fst` | ✅ PROVED (e137b5d) | `term_to_key_total`/`triple_to_key` full injectivity across all four term shapes under separator-free side conditions; `lemma_graph_full_sep_free_no_dup_keys`. Engine fix: literal keys now unit_sep-joined (extraction re-gate pending). |
| Closure-step no-repeats (Gap B) | `RDF.Entailment.RDFS.FixedPoint.fst` | ✅ PROVED (e137b5d) — UNCONDITIONAL | `lemma_rdfs_closure_step_no_repeats`; the noeq-vs-`sortWith_sorted` blocker fell to the Completeness module's eqtype-free sortedness proof. `lemma_len_eq_saturated_gapB` left only Gap A — CLOSED same day: `lemma_len_eq_saturated_sep_free` (Gap A landing) makes the termination test faithful for separator-free, tt-object-free, repeat-free inputs. NO open gaps on the termination path. |
| Row-level separator-freedom | `RDF.Entailment.RDFS.SepFree.fst` | ✅ PROVED — per-row conclusion cleanliness for rdfD2 and rdfs1-13 (checked directly: `lemma_rdfsN_sep_free` per row) | Feeds `ChainWf`. |
| Closure well-formedness chain | `RDF.Entailment.RDFS.ChainWf.fst` | ✅ PROVED — `graph_sep_free g ==> closure_chain_wf g`, empty + non-empty instances machine-checked | Makes `rdfs_closure_entails` apply to concrete graphs (hypothesis discharged non-vacuously). |
| Closure step extensivity + fixed-point | `RDF.Entailment.RDFS.FixedPoint.fst` | 🟡 LANDED WITH ADJUDICATION (commit `1aa4e71`) | Length-test fixed-point theorem holds under two explicit hypotheses (`no_dup_keys` on the pre-dedup intermediate graph), not unconditionally — the unconditional form is FALSE. Third finding from this landing: `term_to_key_total` literal keys use plain `"^^"` not `unit_sep`, a wider dedup-collision surface than #338 described (#348). |
| String ordering axioms | `RDF.Indexed.StringOrder.fsti` | ⚠️ 3 TRUSTED AXIOMS (#347) | See Trust surface. |

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

## 6. G4: response-path theorems (2026-08-09, wave 1)

| Stage | Theorem | Status | Notes |
|---|---|---|---|
| ORDER BY | `theorem_sort_solutions_permutation` | ✅ PROVED | Multiset-level, hand-derived (stdlib `sortWith_permutation` needs `eqtype`; noeq `rdf_term` fails it — reusable finding). Sortedness NOT claimed: comparator ties break antisymmetry; wave 2. |
| LIMIT/OFFSET | `theorem_slice_solutions_window` / `_length` | ✅ PROVED | Contiguous index-shifted window, all None/Some combinations. |
| DISTINCT | `theorem_distinct_complete` | ✅ PROVED | Representative-level, needs `noRepeats` domains hypothesis. |
| DISTINCT card | `theorem_sr3_distinct_card_spec_false` | ❌ SPEC FALSE | FINDING SR-3 (#359): dedup case-insensitive lang tags vs count exact — third strike of the SR-1/SR-2 equality gap. |
| SRJ (tree layer) | `lemma_json_val_of_{term,row,vars,rows,response,bool}_roundtrip` | ✅ PROVED | Exact equality, IRI+literal fragment (no bnodes/triple terms/dir literals yet), SPARQL.Protocol.RoundTrip.fst. |
| SRJ (text layer) | `Parser.FastString.Axioms.fsti` (8 facts / 9 vals, DO-NOT-WIDEN, justified line-by-line vs the OCaml realisation) + `lemma_byte_at_after_prefix` | ✅ PROVED, off trust surface (Step 4, 2026-08-10 — see "FastString migration Step 4" below; was 🟡 UNBLOCKED-as-axioms as of wave 1/2, now real theorems in `Parser.FastString.Axioms.fst`) | `fs_byte_length "ab" == 2` provable; all 8 facts now machine-verified true of the real definitions, not merely assumed. parse_json↔serialise text bridge still separately blocked by `FStar.String.sub`/`concat` gaps — see `docs/designissues/2026-08-10-string-foundation-decision.md`. |

**G4 wave 2b/2c (2026-08-09)**: ORDER BY sortedness —
`lemma_sortWith_sorted_by` (sorted-under-preorder for stdlib
quicksort; totality must be IF-form, OR-form refuted by 2-element
counterexample, in-file) + `theorem_sort_solutions_sorted`
(hypotheses carried; IRI fragment discharges via StringOrder axioms;
numeric fragment REFUTED — FINDING SR-4 #362, unparseable literal
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
collapse), both stated as divergence lemmas with witnesses, #365.
Text-bridge: BLOCKED pending owner decision on FastString candidate
axioms 7-8 (value-level facts, documented in-file with OCaml
justification); tree-level remains the proved boundary meanwhile.

**G4 wave 4 (2026-08-09/10)**: EXISTS-cycle RESOLVED — `eval_exists_fwd`
assume val RETIRED via real mutual recursion (`pattern_size`/`expr_size`
metric + `lemma_substitute_pattern_preserves_size`, phase+size decreases
per the MathML.Present precedent; z3 cost 1.4-1.6x baseline, under the
3x gate; glue patch 62 down to 2 symbols). Full W3C on the branch:
SPARQL 631 pass, 0 fail (out of 631); RDF 1031 pass, 0 fail (out of
1031) — the 4 RIF failures of #367 do NOT reproduce (stale-binary
measurement artifact suspected; see issue). RIF enters the theorems
zone — `RIF.Core.Refinement.fst`: `rif_fixpoint_extensive`/
`rif_one_round_extensive`/`rif_fire_rule_extensive` (UNCONDITIONAL —
finding E-1: no dedup-pass hypothesis needed, unlike rho-df),
`rif_derives` declarative spec + `fire_rule_licensed`/
`one_round_licensed`/`fixpoint_licensed` (two-graph snapshot idiom
forced by intra-round order-dependence). FINDING F-1 (#367 candidate
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
value-content axioms beyond the approved 8 (extends #358) OR a
specified reimplementation of the fast path; and triple-line
injectivity is FALSE without a content-safety restriction (IRI
containing quote-gt-space forges line boundaries) — the
`iri_print_safe` predicate family is the required guard, aligning with
the M1 parser plan's same move.

**G4 wave 5b (2026-08-10)**: FastString axioms 7-8 PROMOTED
(owner-approved, #358) — set now 8, DO-NOT-WIDEN. New proved lexing
lemmas: `build_string` length/byte facts (induction over facts 1-4+7)
and `lemma_quoted_content_byte_sub` — the quoted-string read-back step
of the SRJ text bridge. FULL text bridge still blocked by a THIRD
string-spec wall: `FStar.String.concat` has ZERO lemmas in ulib
(checked; both parser and serializer sit on it). Candidate rule
documented in-file, owner-gated. Three walls, one pattern — feeds the
re-found-the-fast-path decision on #358.

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
consolidated with the #358 string-foundation decision.

**FastString migration steps 2+3 MERGED (2026-08-10)**: six primitives
are REAL Spec-backed F* definitions (assume vals retired; sole
survivor unsafe_char_of_d7ff in CharBoundary); patch 89 → 1 symbol;
fast OCaml now an experimental_ocaml_glue SPEED patch (rule 11(b)).
Gates: 233/234 verify (1 = pre-existing #327); extract/compile clean,
29 binaries; W3C SPARQL 631 pass 0 fail (of 631) + RDF 1031 pass 0
fail (of 1031), exact match (OWL DL suite not run, stated);
benchmarks ALL within the 10% gate vs frozen baselines (1M parse rows
FASTER: nt -8.0%, turtle -3.1%); equivalence 401/401 on valid UTF-8.
WALL (documented in the plan doc's Step 2/3 results): Spec's
utf8_bytes mixes two decoders that disagree on INVALID UTF-8 (665
divergences + one crash path) — the deletability promise holds for
valid input only until the Spec is re-founded on a single WHATWG
decoder; repair scheduled before step 4's axiom discharge.

**FastString #374 repair (2026-08-10)**: Spec re-founded — the "second
decoder" was ulib's own list_of_string, which returns NEGATIVE
codepoints on invalid UTF-8 (measured -1670; a genuine F* stdlib bug,
upstream-reportable). Guards added in utf8_enc_char +
utf8_decode_all_aux (verified first-try; two new lemmas). Equivalence
corpus now COMPLETES CLEAN: 93,846 pass, 0 unexpected fail, 962
documented expected-fail rows (the necessity-forced byte_sub boundary
domain), no crash. Deletability contract now holds on ALL input. W3C
regression: RDF 1031/0 exact; SPARQL 627/4 with the 4 = the known
intermittent RIF quartet (#367's environmental pattern). Residual:
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
(`utf8_decode_all_utf8_bytes_identity`) this file's own #374-repair
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
quartet #367) + RDF 1031 pass 0 fail (of 1031), benchmark every row
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
byte-level single-decoder round-trip, #374). PROVED: the split
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
