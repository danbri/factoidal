# 2026-05-07 — OWL 2 RL: next steps + scoping

Last refreshed: 2026-05-07 (OWL profile-RL and entailment scores re-measured against live runners).

## Status

Design + scoping. Doc-only. No code in this commit.

Tracking issue: https://github.com/danbri/factoidal/issues/207
("Epic: OWL 2 RL profile — current 15/30 → 30/30").

The user wrote "OWL 1.1 — rl"; OWL 1.1 was never standardised. The
intended target is the **OWL 2 RL profile** (W3C Recommendation, 2012),
which is what `formal/fstar/RDF.Graph.Executable.fst` already
implements partially via `owl_rl_closure_step` and friends. OWL 1.x is
addressed only insofar as OWL 2 RL/RDF subsumes it for the rules we
need; there is no separate "OWL 1.1 compatibility" track.

## Where we are

- **W3C OWL 2 PositiveEntailmentTest, profile-RL.rdf:** 15 pass,
  15 fail (out of 30) per `bin/linux-x86_64/owl_runner` (re-measured
  2026-05-07; `docs/test-results/latest.json` still records the
  earlier 13/17 split).
- **W3C SPARQL 1.1 entailment suite:** 69 pass, 1 fail (out of 70)
  per `bin/linux-x86_64/w3c_runner entailment` (re-measured
  2026-05-07). The single fail is `parent query with (hasChild max 1
  Female) restriction` and lives in the same OWL DL cardinality area
  as the RL gaps.
- **F\* modules in scope:**
  - `formal/fstar/OWL.QueryRewrite.fst` — query-side CE expansion
    (intersectionOf / unionOf / restrictions in BGPs).
  - `formal/fstar/OWL.QueryEval.fst` — wiring layer that composes
    `rewrite_query` with the SPARQL evaluators.
  - `formal/fstar/RDF.Graph.Executable.fst` — graph-side OWL-RL
    closure (`owl_rl_closure_step`, ~30 named rules), the bulk of
    the actual RL inference logic.
- **Runner:** `formal/fstar/ocaml-output/owl_runner.ml` is I/O glue
  only (CLAUDE.md rule #11) — manifest parsing + entity expansion +
  per-test outcome printing. The reasoning calls F\*-extracted
  `owl_rl_closure_with_reflexivity g fuel`.
- **Existing design docs:** `2026-04-24-owl-rl-posent-triage.md`
  (Zeta's per-test root-cause analysis) and
  `2026-04-25-owl-rl-residual-fails-diagnosis.md` (Wave 8 / Omega
  delta from 11/30 to 13/30) cover the same territory at a finer
  grain. This doc consolidates them into a **forward-looking
  next-steps plan** anchored to the current 13/30 baseline.

## Scope: OWL 2 RL profile

The OWL 2 RL profile (https://www.w3.org/TR/owl2-profiles/#OWL_2_RL)
is the rule-language profile of OWL 2 — designed so that all
sound consequences are derivable by a polynomial-time forward-chaining
rule engine. It is a partial entailment regime for OWL DL (sound but
incomplete); the canonical rule table sits at
https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules.

Rule families relevant to this project, with current status:

| RL rule family | Examples | F\* status |
|---|---|---|
| Class assertion / equivalence | cls-eqc1/2, scm-eqc1, scm-eqc2 | Implemented (cls-eqc1/2; scm-eqc2 added 2026-04-24) |
| Class disjointness (positive) | cax-dw | Partial — cax-dw is consistency-only; positive-entailment via complementOf bnode synthesis is unimplemented (out of scope, mode (c)) |
| Class hierarchy | scm-sco, cax-sco | Implemented via RDFS closure |
| Property hierarchy | prp-spo1, scm-spo, scm-eqp1 | Implemented (RDFS-side prp-spo1; scm-eqp2 added 2026-04-24) |
| Property characteristics | prp-symp, prp-trp, prp-fp, prp-ifp, prp-rfl, prp-asyp, prp-irp | prp-symp / trp / fp / ifp / rfl implemented; asyp / irp produce inconsistency only |
| Inverse properties | prp-inv1/2 | Implemented |
| Property chains | prp-spo2 (n=2) | Implemented for n=2 (`owl_rule_property_chain_2`); n>=3 not implemented |
| Domain / range | prp-dom, prp-rng, scm-dom2, scm-rng2 | Implemented (scm-dom2 / scm-rng2 added 2026-04-25) |
| Cardinality (qualified) | cls-minqc1, cls-maxqc1, cls-exactqc1 | Implemented for n=1 (the RL profile cap) |
| Cardinality (unqualified) | cls-minc1, cls-maxc1, cls-exactc1 | cls-minc1 implemented as a "bridge"; cls-maxc2 implemented |
| someValuesFrom / allValuesFrom | cls-svf1/2, cls-avf1/2 | cls-svf2-qual + cls-avf1 implemented; cls-svf2 existential witness has a partial skolemised form |
| Keys | prp-key | Not implemented (1 RL test depends) |
| sameAs propagation | eq-sym, eq-trans, eq-rep-s/p/o | Implemented |
| differentFrom | eq-diff1 (consistency), eq-diff-sym | eq-diff-sym implemented; eq-diff1 produces consistency, not positive differentFrom triples |
| AllDifferent | eq-diff2/3 | Not implemented (1 RL test depends) |
| XSD datatype hierarchy | (axiomatic) | Implemented (`owl_rule_xsd_datatype_axioms` + core axioms) |
| Vocabulary axioms | owl:Thing / owl:Nothing | Implemented (`owl_thing_axioms`) |

The "out of scope" rows below correspond exactly to the modes Zeta's
2026-04-24 triage labelled (c) non-monotonic, (f) DL-grade fresh
existential witness, and (e) datatype-facet semantics — none of which
the OWL 2 RL profile is designed to cover.

## Failure analysis: the 17 RL test failures

Bucketed from `formal/fstar/ocaml-output/owl_profile_rl_results.log`
(13/30) cross-referenced with Zeta's per-test triage. Each bucket =
one chunk of next-step work; "RL-feasible" means the cluster is
entailable by some sound monotonic rule the RL profile sanctions,
"out-of-RL" means it requires non-monotonic / DL-grade reasoning
that the profile explicitly excludes.

| Failure cluster | Tests | Root cause | RL-feasible? | Target F\* fix |
|---|---:|---|---|---|
| **A. Property chains, n>=3 + annotated** | 1 | `prp-spo2` is implemented for n=2 only. `New-Feature-ObjectPropertyChain-BJP-002` reports "no-premise" — the annotated propertyChainAxiom isn't surviving the parser. | Yes (parser + n-ary chain) | Generalise `owl_rule_property_chain_2` to `owl_rule_property_chain_n` in `RDF.Graph.Executable.fst`; investigate RDF/XML annotated-axiom parse path |
| **B. Keys (prp-key)** | 1 | Not implemented at all. Walks the owl:hasKey RDF list, then for each pair of individuals matching all key values emits owl:sameAs. | Yes | New `owl_rule_prp_key` in `RDF.Graph.Executable.fst` (~80 LoC; needs RDF list walk, already factored elsewhere) |
| **C. Qualified-card on existing data** | 1 (RL) + **1 (SPARQL)** | `New-Feature-ObjectQCR-002` needs `_:b a owl:Class` synthesised from a qualified-cardinality restriction in the premise — short scm-cls completion. The SPARQL fail `(hasChild max 1 Female)` is the **same area**: the OWL.QueryRewrite cardinality-restriction expansion is producing 311 rows where 1 is expected — over-yielding because `cls-maxqc1` rule fires but the rewrite doesn't constrain the filler-typed children. | Yes for the RL test; the SPARQL fail is in cls-maxqc1 + query-side filler binding, also RL-feasible | Extend `owl_rule_scm_cls_restriction` to also cover non-bnode restrictions; audit `OWL.QueryRewrite.expand_ce_subject` for the QCR-with-named-filler case |
| **D. DisjointObjectProperties / DataProperties (positive)** | 3 | Conclusions assert `owl:differentFrom` (or AllDifferent) from `(x P y), (x Q y), DisjointProperties(P,Q)`. This is **prp-pdw / prp-adp contrapositive on a shared object** — non-monotonic in the RL/RDF table (yields consistency, not differentFrom). | **No** — out-of-RL | Mark out of scope; document in failure log |
| **E. DisjointClasses (positive complementOf)** | 2 | `Stewie a Boy + Boy disjointWith Girl ⊨ Stewie a _:b ; _:b owl:complementOf Girl`. Requires fabricating a fresh complementOf bnode (existential witness). | **No** — out-of-RL (mode f) | Out of scope |
| **F. fp/ifp differentFrom** | 2 | `Y2 fp X2 + Y1 fp X1 + X1 differentFrom X2 ⊨ Y1 differentFrom Y2`. Contrapositive of prp-fp; non-monotonic. | **No** — out-of-RL | Out of scope |
| **G. WebOnt-I5.5-005 (unionOf bnode synthesis)** | 1 | Conclusion synthesises a bnode plus `owl:unionOf` list from a class declaration; comprehension principle. | **No** — out-of-RL (mode f) | Out of scope; documented in 2026-04-25 residual diagnosis |
| **H. WebOnt-I5.26-010 (someValuesFrom witness)** | 1 | Conclusion has `_:n owl:onProperty :p` synthesised from a someValuesFrom premise — fresh restriction bnode. | **No** — out-of-RL | Out of scope |
| **I. WebOnt-I4.6-005-Direct + equivalentClass-008-Direct (annotation propagation)** | 2 | Annotation property must propagate from `c1` to `c2` via `owl:equivalentClass`. Standard RL does this only for sameAs — not equivalentClass on named classes. | Yes (Proposed extension) | New rule `owl_rule_namedClass_equivalentClass_to_sameAs` in `RDF.Graph.Executable.fst`; chains with existing `eq_rep_s` |
| **J. WebOnt-I4.6-003 (sameAs of named classes)** | 1 | `(C1 sameAs C2) ∧ (C1 a owl:Class) ∧ (C2 a owl:Class) ⊨ (C1 owl:equivalentClass C2)`. Status="Proposed" in catalog; sound. | Yes | Same rule as cluster I (it produces the equivalentClass needed for I as a side effect) |
| **K. WebOnt-imports-011 (parser issue)** | 1 | Bnode-vs-IRI artefact for empty xml:base on `owl:Ontology`. Not a closure rule problem. | Yes (parser) | Investigate `Parser.RDFXML.fst` empty-base path; +1 if fixed |
| **L. XSD facet intersection** | 2 | `(p range xsd:nonNeg) + (p range xsd:nonPos) ⊨ (p range xsd:short)`. Needs value-space intersection / facet semantics — explicitly not in the RL profile. | **No** — out-of-RL (mode e, facets) | Out of scope; documented in 2026-04-25 residual diagnosis |

Bucket sizes: A=1, B=1, C=1+1, D=3, E=2, F=2, G=1, H=1, I=2, J=1,
K=1, L=2. Total RL-positive-entailment rows = 17. Plus the 1 SPARQL
fail under cluster C.

### RL-feasible vs out-of-RL

- **RL-feasible (will pass with verified F\* additions):** A, B, C, I,
  J, K. Total = **8 RL tests + 1 SPARQL test = 9 wins**.
- **Out-of-RL profile (will not pass without leaving the rule profile):**
  D, E, F, G, H, L. Total = **9 RL tests** that the OWL 2 RL profile
  itself does not sanction monotonically.

This puts a **realistic ceiling at 22/30 (73%)** for pure OWL 2 RL
work. Pushing beyond 22/30 requires opening one of:

- A tableau / DL reasoner for clusters E, F, G, H (existential
  witnesses + non-monotonic reasoning). Stage (a) of a DL tableau is
  scaffolded already (`Tableau.fst`, see
  `docs/designissues/2026-04-19-tableau-owl-plan.md`) — currently
  returns `None` for everything non-trivial.
- A facet semantics module for cluster L. This mixes value-space and
  RDF-graph reasoning; treat as a separate research track.
- Treating the catalog assertions in clusters D, F as
  consistency-checking tests rather than positive-entailment tests
  (catalog mis-classification — see Zeta's "Surprises" note).

## Sequenced next steps

Cheapest first; each step should land as one commit per anti-pattern
#23. Rebuild the runner after each step (`./build-ocaml.sh` from
`formal/fstar`) to confirm the score delta.

### Step 1 — Cluster I + J (sameAs of named classes -> equivalentClass + propagation)

- **F\* module:** `RDF.Graph.Executable.fst`
- **New rules:**
  - `owl_rule_named_class_sameAs_to_equivClass`: `(c1 owl:sameAs c2) ∧
    (c1 a owl:Class) ∧ (c2 a owl:Class) → (c1 owl:equivalentClass c2)`.
  - `owl_rule_named_class_equivClass_to_sameAs`: dual; gates the
    annotation-property propagation pattern via existing
    `eq_rep_s/p/o`.
- **LoC:** ~40-60 (mirror the existing `owl_rule_named_sameAs_to_equivClass`
  pattern at line 3238 of `RDF.Graph.Executable.fst`; one direction may
  already exist — confirm before rewriting).
- **Tests unblocked:** `WebOnt-I4.6-003`, `WebOnt-I4.6-005-Direct`,
  `WebOnt-equivalentClass-008-Direct`.
- **Score delta:** +3 RL tests. **13/30 -> 16/30**.

### Step 2 — Cluster C (cardinality completion + the SPARQL fail)

- **F\* modules:** `RDF.Graph.Executable.fst` + `OWL.QueryRewrite.fst`.
- **Graph-side fix:** extend `owl_rule_scm_cls_restriction` to emit
  `?r a owl:Class` for non-bnode owl:Restriction subjects too (one
  extra fold over the graph; already-factored helper). Unblocks
  `New-Feature-ObjectQCR-002`.
- **Query-side fix:** audit `OWL.QueryRewrite.expand_ce_subject` for
  the **maxQualifiedCardinality 1 with a named filler class** case.
  Current symptom: `(hasChild max 1 Female)` returns 311 rows where
  the W3C expects 1; the rewrite must intersect against the filler
  type, not just count edges. Look at the `MaxQC` arm of
  `ce_combinator` (line 554 onward of OWL.QueryRewrite.fst); the
  child-filter on `?c a Female` is being dropped or wrongly
  positioned in the `wrap_distinct_over_ggp` path.
- **LoC:** scm-cls extension ~15 LoC; query-rewrite fix ~30-50 LoC
  (depending on whether the bug is in marker collection or in
  `expand_consumer_for_intersection`).
- **Tests unblocked:** `New-Feature-ObjectQCR-002` (RL), and the
  single non-RIF SPARQL entailment fail.
- **Score delta:** +1 RL test, +1 SPARQL test. **16/30 RL, +0
  net but the SPARQL board flips to 626/626 non-RIF.**

### Step 3 — Cluster A (property chain n>=3, plus annotated parser fix)

- **F\* module:** `RDF.Graph.Executable.fst`.
- **Generalise `owl_rule_property_chain_2`** at line 3236 to
  `owl_rule_property_chain_n` for n in 2..k (small bound — k=4 covers
  every published OWL 2 test). Either iterate manually for n=2,3,4
  (verbose but trivially decreasing) or factor through the existing
  RDF-list-walk helper used by `owl_rule_inverse_of`.
- **Parser audit:** investigate why
  `New-Feature-ObjectPropertyChain-BJP-002` reports `no-premise` —
  RDF/XML annotated-axiom (`owl:Axiom` reification?) wrapper might
  be hiding the propertyChainAxiom from the parser. Confirm with a
  one-off `parse_rdfxml_with_base` invocation against the test's
  premise lexical form.
- **LoC:** chain-n extension ~50-80 LoC; parser fix unknown until
  diagnosed.
- **Tests unblocked:** `New-Feature-ObjectPropertyChain-BJP-002` (if
  the parser issue is real). Plus latent unblock when `chain2trans1`
  next regresses.
- **Score delta:** +1 RL test. **17/30**.

### Step 4 — Cluster B (prp-key)

- **F\* module:** `RDF.Graph.Executable.fst`.
- **New rule** `owl_rule_prp_key`: walk the owl:hasKey list, then
  for each pair of individuals (x, y) matching every key
  (P_i x v_i) ∧ (P_i y v_i), emit (x owl:sameAs y).
- **LoC:** ~80-120 (RDF-list walk + n-ary join + sameAs emit).
- **Tests unblocked:** `New-Feature-Keys-003`.
- **Score delta:** +1 RL test. **18/30**.

### Step 5 — Cluster K (parser empty-base bnode artefact)

- **F\* module:** `Parser.RDFXML.fst` (likely).
- **Diagnose:** `WebOnt-imports-011` conclusion has `_:b0 rdf:type
  owl:Ontology` where the premise has a named owl:Ontology with
  empty xml:base. The bnode in the conclusion is from the
  *conclusion graph* parse, not the premise — the parser is
  inventing a bnode for the implicit ontology IRI when xml:base is
  empty. The owl_runner relaxed bnode match should accept any bnode
  in the closure that has the same predicate-object skeleton, but
  evidently no such triple exists.
- **LoC:** unknown until diagnosed.
- **Tests unblocked:** `WebOnt-imports-011` if root cause is
  parser-side as suspected.
- **Score delta:** +1 RL test (uncertain). **19/30 if it lands.**

### Step 6 — Done criteria (within RL ceiling)

- Update `owl_runner` to print a **per-cluster pass rate** rather
  than just the total — useful for the dashboard. (I/O glue change
  only; no F\* edits.)
- Roll the per-cluster score onto the
  `docs/test-results/latest.json` schema as
  `owl_rl_positive_entailment.by_cluster`.
- Document the 22/30 ceiling and the four out-of-RL clusters
  (D, E, F, G, H, L) on the project README so that the qualifier in
  CLAUDE.md rule #11 stays accurate.

### Beyond the RL ceiling — separate tracks (not in this epic)

- **DL tableau (clusters E, F, G, H):** `Tableau.fst` + the
  2026-04-19 plan. Stage (b)+(c) is the plan; stage (a) returns
  None. Track separately under issue #58.
- **XSD facet semantics (cluster L):** value-space intersection
  module; out of OWL 2 RL profile.
- **Cluster D revisit:** if the catalog admits a
  consistency-checking interpretation, the runner can score it as
  pass on a separate "RL-with-consistency" knob.

## Done criteria

For this epic, "done" means:

- **17/30 -> 22/30** OWL 2 RL PositiveEntailmentTests passing.
- **The 1 non-RIF SPARQL fail flips to pass** — confirmed in cluster C
  above; same family.
- All new F\* rules verify under z3 4.13.3 with no `--lax`,
  `--admit_smt_queries`, or other escape-hatch flags (rule #10).
- `owl_runner` prints per-cluster pass rates; the dashboard exposes
  an OWL 2 RL panel.
- The 22/30 ceiling is documented (README qualifier + CLAUDE.md rule
  #11 expansion + this doc's "Beyond the RL ceiling" section).
- Each of the 8 RL-feasible clusters (A, B, C, I, J, K) has either
  flipped to PASS or has its parser-side blocker captured as a
  follow-up issue.

The unconditional 30/30 target requires opening separate tracks
(tableau / facet) and is **not** in scope for this epic.

## Out of scope

- **OWL 2 EL profile.** Separate RL/RDF rule subset; no test
  pressure on the F\* side currently.
- **OWL 2 QL profile.** Same as EL.
- **OWL DL full reasoner.** Out of scope per the README qualifier
  ("parser and algebra spec verified in F\*; on-disk backend has
  unverified OCaml-side optimization layers being migrated back to
  F\*"). DL clusters (E, F, G, H) belong on the tableau track.
- **OWL 1.x compatibility shim.** OWL 2 RL/RDF subsumes OWL 1 Lite
  for every rule we need. No separate work.
- **RIF entailment.** Two W3C SPARQL entailment tests use RIF Core;
  tracked separately (see `2026-05-07-rif-fstar-investigation.md`).
- **AllDifferent positive entailment** (cluster D). RL profile does
  not sanction it monotonically; see `Out-of-RL` ceiling note.

## Open questions

1. **Ceiling vs floor.** Is 22/30 (73%) a satisfactory headline
   number for the README, with the 8 out-of-RL tests carved out as a
   tableau-track epic, or does the dashboard need 30/30 before we
   declare OWL 2 RL "done"?
2. **Cluster D and F catalog interpretation.** Should the runner
   allow a `--regime=RL-with-consistency` mode that scores positive
   AllDifferent / fp-differentFrom as pass when the closure derives
   inconsistency for the negated goal? This would lift the ceiling
   to 27/30 but adds an interpretation knob.
3. **Cluster K (parser).** Is the empty-xml:base bnode synthesis a
   `Parser.RDFXML.fst` bug or a runner relaxed-match bug? Decision
   gate: a 5-line repro against `parse_rdfxml_with_base` on the
   conclusion lexical form, before any rule work.
4. **Step ordering vs SPARQL board.** The SPARQL fail is in cluster
   C. Do we want to fast-track step 2 (1+1 wins) ahead of step 1
   (3 wins) so the SPARQL non-RIF board reads 626/626?
5. **Per-cluster scoring schema.** Does the `latest.json` schema
   need a stable per-cluster shape (cluster id + pass/fail counts)
   so the dashboard can render an OWL 2 RL panel without
   string-matching test names?
6. **DL tableau coupling.** When clusters E / F / G / H eventually
   move (under #58), does the OWL.QueryEval module need to call
   `owl_tableau_entails` as a fallback after the RL closure misses,
   or do we keep tableau on a separate evaluation pipeline?

## References

- W3C OWL 2 RL profile: https://www.w3.org/TR/owl2-profiles/#OWL_2_RL
- W3C OWL 2 RL Reasoning rules table:
  https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules
- W3C OWL 2 Test Cases:
  https://www.w3.org/TR/owl2-test/
- Test catalog: `third_party/testing/owl/profile-RL.rdf` (1896
  triples, 91 cases, 30 PositiveEntailmentTests).
- Per-test triage (2026-04-24, Zeta):
  `docs/designissues/2026-04-24-owl-rl-posent-triage.md`.
- Wave-8 residual diagnosis (2026-04-25, Omega):
  `docs/designissues/2026-04-25-owl-rl-residual-fails-diagnosis.md`.
- Tableau plan (2026-04-19):
  `docs/designissues/2026-04-19-tableau-owl-plan.md`.
- Tier-2 OWL-RL rules plan (2026-04-24):
  `docs/designissues/2026-04-24-tier2-owl-rl-rules.md`.
- Closure entry point:
  `formal/fstar/RDF.Graph.Executable.fst:3183` (`owl_rl_closure_step`)
  and `:3379` (`owl_rl_closure_with_reflexivity`).
- Query-side rewriter:
  `formal/fstar/OWL.QueryRewrite.fst` (1715 lines; CE marker dispatch
  at line 554; expand_ce_subject at line 1018).
- Runner I/O glue:
  `formal/fstar/ocaml-output/owl_runner.ml` (504 lines; rule-#11
  compliant — no semantic logic).
- Existing OWL DL umbrella issue: #58.
