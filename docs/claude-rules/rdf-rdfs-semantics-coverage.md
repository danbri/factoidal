# Core RDF/RDFS semantics coverage — survey 2026-08-05

Agent survey of the RDF/RDFS entailment verticals against the RDF 1.1
Semantics REC structure. Companion to
[`owl-rule-shape-matrix.md`](owl-rule-shape-matrix.md). Full detail
lives in the modules' own banners; this records the coverage verdicts
and the ranked gap list driving the core-semantics push.

## Verdicts by area

- **Simple entailment (§5)**: the INTERPOLATION LEMMA is proved as a
  full iff on the RDF-1.2-triple-term-free fragment
  (`Simple.ModelTheory.interpolation_lemma`, Herbrand construction at
  `herbrand`), composed end-to-end with the shipping search
  (`simple_entails_iff_model_theory`, plus the `graph_exact`
  soundness boundary with its machine-checked SE-1 witness). The
  spec-text instance-subgraph form has one unproved converse
  (choice-based image construction). The MERGING lemma is absent.
  Label-independence at the parser boundary is proved
  (`Boundary.entails_ntriples_boundary`).
- **RDF entailment (§8)**: rdfD2 licensed + true at rule and closure
  level; rdfD1 unimplemented (mints bnodes — Skolem
  family); axiomatic tables transcribed, `rdf:_n` as a schema
  predicate; `rdf_closed` defined; NO completeness theorem at this
  rung.
- **RDFS entailment (§9)**: all thirteen rows have spec predicates;
  eleven have engine rules with BOTH licensing and truth proved
  (rdfs6/rdfs10 via the regime-split reflexivity axioms, RS-1 fixed;
  rdfs12 via the finite CMP slice); rdfs1-2004 unimplemented
  (bnode-minting). The composite `rdfs_licensed_true`, step/closure
  soundness, and `rdfs_closure_entails` (hypothesis now discharged
  non-vacuously via ChainWf) all landed. **NO COMPLETENESS THEOREM
  EXISTS at this rung** — the rho-df fragment is named and predicated
  (`rho_df_graph` etc.) but the theorem is unlanded; unrestricted
  completeness is FALSE (axiomatic tables unseeded), not merely
  unproven.
- **D-entailment**: `datatype_set` parametric machinery + the
  `d_minimal` engine set only. NO literal value spaces, no IL
  conditions, no ill-typed-literal clause; the SE-1 divergence
  (lang-tag folding legal at the RDF rung, illegal at simple) is
  banner prose, not a rung-level theorem.
- **Interpretation conditions**: 17-conjunct `rdfs_conditions`
  bundle covers every implemented row; missing by design/absence:
  IL/value-space conditions, Hayes §7 container-structure conditions,
  the lg/gg literal-generalization machinery, first-class IP/IC sets
  (recovered via icext — the documented enlarging convention).
- **Generalized-RDF deltas**: every GR/GP-restricted spec row has an
  exactly matching engine guard — refinement proved EXACT (RS-3),
  not merely sound.

## Ranked gaps (the dispatch queue)

1. **rho-df completeness** — ⚠️ the statement first written here,
   "`rdfs_entails d_minimal g e <==>` closure-then-simple-entailment,
   for `rho_df_graph` g, e", is **FALSE**; see the 2026-08-06 entry
   below. The corrected, landed statement is over the SIX rho-df
   semantic conditions (`RDF.Entailment.RDFS.Completeness.
   rho_df_saturation_iff`); Herbrand technique from the simple rung
   reuses, as predicted.
2. **Index completeness** — `lemma_build_indexed_complete_pred`:
   every triple with predicate p IS in the pred bucket (converse of
   wf). Named prerequisite; design doc calls it "not hard".
3. **Faithful fixed-point** — replace/justify `rdfs_closure`'s
   length-equality test with a genuine no-more-derivations predicate
   (per-row `_monotone`/`_complete` lemmas already pin element sets).
4. **General sp_key injectivity statement** — lift the ChainWf-scoped
   discharges to the fully general U+001F-free theorem, closing
   HypothesisWitness §4c-4d entirely.
5. **Literal value spaces / IL conditions** — a VL map +
   `cond_langString_value`, making the SE-1/D3 divergence a provable
   rung-level entailment fact. Least existing infrastructure.

Status tracking (updated 2026-08-05 late):

- **Gap 2 BLOCKED on #347**: `FStar.String.compare` ships with no
  ordering specification in ulib (interface-only native primitive),
  so tree-lookup completeness cannot link positional splits to key
  comparisons. The sortWith completeness companions landed (4a0e6dd);
  the axiom-module decision is #347.
- **Gap 3 LANDED with adjudication** (1aa4e71,
  `RDF.Entailment.RDFS.FixedPoint.fst`): `step_saturated`, per-row
  extensivity, `lemma_saturated_stable`, and the length-test theorem
  under TWO explicit hypotheses — the unconditional form is FALSE
  (no_dup_keys needed on the pre-dedup intermediate graph; no_repeats
  blocked by noeq triple vs stdlib sortWith_sorted). Third finding:
  `term_to_key_total` literal keys use plain `"^^"` not `unit_sep` —
  #348, a wider dedup-collision surface than #338 described.
- **Gap 1 (rho-df completeness)** now sits behind #347 and #348 —
  both on the same dedup/lookup faithfulness path. Herbrand-side
  machinery is unaffected; dispatch once either unblocks.
- Gaps 4-5 queued.

Status update 2026-08-06 — **gap 1 PARTLY LANDED, and its statement
corrected** (`formal/fstar/RDF.Entailment.RDFS.Completeness.fst`, 829
lines, verifies under `make verify-rdf-mt`, now 21 modules):

- ❌ **The gap-1 statement above was false.** Pairing
  `rdfs_entails d_minimal` with closure-then-simple-entailment cannot
  be an iff, and no fragment predicate on g and e repairs it. Two
  witnesses, both inside `rho_df_graph`. **W1**: `[X sc Y]`
  RDFS-entails `[X sc X]` (`cond_subClassOf_ic` +
  `cond_subClassOf_refl`), which `rdfs_closure` never derives. Both
  halves are now machine-checked —
  `rho_df_entailment_strictly_stronger`. **W2**: `cond_resource` makes
  `[Z rdf:type rdfs:Resource]` entailed by every graph, for EVERY IRI
  Z, including IRIs absent from g; no finite closure can list that.
  W2 is structural, not a missing rule.
- ✅ **The corrected theorem is landed.** `rho_df_conditions` keeps
  the six semantic conditions the six rho-df rows rest on and drops
  the reflexivity / IC-IP / resource / datatype / axiomatic
  conditions — the same reduction the published rho-df result makes.
  `rho_df_closed_iff`: on a rho-df-closed fragment graph, rho-df
  entailment IS simple entailment. `rho_df_saturation_iff`: any
  extensive, rho-df-sound, rho-df-closed saturation of g decides
  rho-df entailment of fragment graphs by simple entailment.
- ⚠️ **The shipping closure gets the completeness half only**
  (`rdfs_closure_rho_df_complete`) — the missing half, so this is the
  gap's payload. The converse is NOT available and must not be
  claimed: the twelve-rule step also runs rdfs1 / rdfs4a / rdfs4b /
  rdfs8 / rdfs13 / container membership, whose conclusions are not
  rho-df-entailed. A six-rule rho-df closure operator would close the
  iff end to end; the tree does not expose one.
- 🔴 **Hypotheses carried, not discharged** (M2's): `rho_df_closed
  (rdfs_closure g fuel)` needs `_complete` lemmas for the six
  index-driven rows (only the five RS-2 rows have them);
  `is_subgraph g (rdfs_closure g fuel)` needs iterated extensivity;
  `rho_df_frag_graph (rdfs_closure g fuel)` needs a per-row fragment-
  preservation argument.
- ⚠️ **Fragment restriction, stated**: the proof's fragment is
  literal-free and triple-term-free in object position, and requires
  IRI objects on `rdfs:subPropertyOf` triples. Literal-freeness is the
  generalized-RDF delta D5 biting the canonical model — `p rdfs:range
  c` plus `a p "lit"` demands ICEXT membership for a literal, and
  `RDF.Term.subject` has no literal case. Real restriction, not a
  formality.
