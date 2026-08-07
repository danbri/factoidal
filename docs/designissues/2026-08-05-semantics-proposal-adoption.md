# Adoption assessment: the model-theoretic verification proposal

Assesses the owner-supplied draft
[`../semantics_proposal.md`](../semantics_proposal.md) (saved verbatim
2026-08-05) against the tree as of 2026-08-05. Companion coverage
survey:
[`../claude-rules/rdf-rdfs-semantics-coverage.md`](../claude-rules/rdf-rdfs-semantics-coverage.md).

**Verdict in one line:** the proposal's Track A (semantic soundness)
and most of its Track B (executable correspondence) are ALREADY
IMPLEMENTED — the 2026-07 entailment verticals plus the 2026-08-04/05
proof program landed the interpretation structures, satisfaction,
entailment, rule-level soundness (including all four milestone rules),
index lemmas, and closure soundness the proposal asks for, under
different module names. Six elements are genuinely new; they are
adopted into the queue below. The proposal's seven open questions all
now have answers from landed experience.

## Element-by-element map (proposal → tree)

| Proposal element | Status | Landed artifact |
|---|---|---|
| Interpretation structure (semantic universe, denotation) | ✅ landed | `OWL.Semantics.fst` `interp` record (relational encoding; IR/IP/IC recovered via `icext` — the documented enlarging convention) |
| Term/subject interpretation, triple + graph satisfaction | ✅ landed | `triple_holds`, `holds_all`, `satisfies` in `OWL.Semantics.fst`; simple rung has its own in `Simple.ModelTheory` |
| Simple entailment, model-theoretic | ✅ landed, STRONGER than asked | `Simple.ModelTheory.interpolation_lemma` — full iff (Herbrand construction) on the triple-term-free fragment, composed with the shipping search as `simple_entails_iff_model_theory`. The proposal's longer-term "complete simple entailment characterization" is therefore already done. |
| RDF interpretations + axiomatic conditions | 🟡 partial | rdfD2 licensed + true; axiomatic tables transcribed; `rdf:_n` as a syntactic schema predicate (exactly the proposal's recommendation); no completeness at this rung (known, recorded) |
| RDFS interpretations (subproperty/domain/range/subclass/transitivity conditions) | ✅ landed | `rdfs_conditions` bundle (17+ conjuncts) covering every implemented row |
| `rdfs_entails` | ✅ landed | `rdfs_entails` + `rdfs_closure_entails` (hypothesis discharged non-vacuously via ChainWf) |
| Rule-level soundness (`rdfs_rule_domain_sound` form) | ✅ landed | `OWL.Semantics.Soundness.fst` — the interpretation-exposing form the proposal prefers is exactly the form used. All thirteen RDFS rows have spec predicates; eleven engine rules have BOTH licensing and truth proved. |
| Initial milestone: rdfs2, rdfs3, rdfs7, rdfs9 | ✅ complete | All four proved (licensing + truth) before the proposal arrived |
| Inflationary / preservation lemmas | ✅ landed | Per-row `_monotone` lemmas; the two-case proof pattern the proposal sketches is the shipped skeleton (see `skills/proof-factory/SKILL.md`) |
| `bucket_lookup_sound` (index soundness) | ✅ landed | Five-bucket well-formedness family: `ig_wf_pred`, `ig_wf_sp`, `ig_wf_subj`, `ig_wf_obj`, `ig_wf_po` — discharged in `RDF.Indexed.KeyInjectivity.fst` (#338) |
| `bucket_lookup_complete` (index completeness) | 🟡 in flight | Gap #2 of the coverage survey; agent dispatched 2026-08-05 (`lemma_build_indexed_complete_pred`) |
| `build_indexed_preserves_graph` | ✅ landed (as convention) | Index-reading proofs take `ig.ig_triples == g` as hypothesis — the relational `index_represents` alternative the proposal offers |
| Closure step + fuel soundness | ✅ landed | `rdfs_closure_step_sound`, `rdfs_closure_sound`; the fixed-point faithfulness refinement is gap #3, agent in flight |
| Declarative rule layer (positive_rule AST + evaluator) | 🟡 equivalent exists; AST form NOT adopted now | The `<row>_derives` spec predicates (`OWL.RL.Spec.fst`) + licensing lemmas (`OWL.RL.Refinement.fst`) already give Track B: "output = input ∪ one W3C-row application" is proved per rule, relationally instead of via an AST interpreter. The AST evaluator adds a third artifact to keep in sync for no new theorem strength; deferred (see Q6). |
| Blank-node handling (term-preserving vs fresh-term split) | ✅ matches landed practice | Exactly the split the program discovered: term-preserving rules all proved; fresh-bnode rules (`transitive_to_chain`, `cls_svf_thing_materialize`, `cls_hasself2_synth`) are IMPOSSIBLE under the fixed-assignment shape, bannered with degenerate-model evidence. The proposal's "extended assignment" is the future Skolem/model-extension lemma shape already queued. |
| Axiomatic-triple predicates + finite-table soundness | 🟡 partial | Tables transcribed, `rdf:_n` recognizer landed; the explicit `finite_rdf_axioms_sound` bridging lemma is worth adding (adopted, A5) |
| Datatype phasing (abstract first, value spaces later) | ✅ matches | Phase 1 is the current state (`datatype_set` parametric machinery, `d_minimal`); phase 2 is gap #5 of the coverage survey |
| Proof engineering strategy | ✅ matches | `skills/proof-factory/SKILL.md` is this section plus the war stories (closure-identity law, guard depth ≤3) the proposal could not know about |
| RDFS rule completeness (longer-term) | 🟡 scoped | Gap #1: rho-df completeness, behind gaps 2-3 (both in flight). Unrestricted completeness is FALSE (axiomatic tables unseeded), not merely unproven. |
| OWL 2 RL/RDF soundness (longer-term) | 🟡 in progress | This IS the current program: ~40 lemmas landed against the 84-row ledger |
| SPARQL entailment regimes, extracted-code correspondence | queued | Future; extraction boundary already has the hash-witness pattern (`2026-05-07-io-verification-and-third-party.md`) |

## Adopted: the genuinely new items

- **A1 — `verify-rdf-mt` make target** (adopted in the same landing as
  this doc): one grouped phony target in `formal/fstar/Makefile` that
  checks the semantic-layer modules, so CI and humans can gate the
  model-theoretic layer by name.
- **A2 — generated property tests + soundness boundary tests**: per
  proved rule, an executable premise→conclusion template plus the
  proposal's boundary list (literal subjects under rdfs3, duplicate
  premises, ordering independence). Tests exercise extraction and
  boundaries the pure theorem does not cover. Queue.
- **A3 — per-theorem registry**: extend the `OWL.RL.Spec.fst` foot
  ledger with the proposal's fields (W3C id, engine function, fragment
  restrictions, assumptions, proof status, linked tests). The ledger
  already has id/function/status; restrictions + tests are the delta.
  Queue.
- **A4 — claims language**: the proposal's calibrated wording ("proved
  sound with respect to an independent F\* formalization … under the
  stated fragment restrictions", never "complete formally verified
  implementation of RDF semantics") is adopted for READMEs, demo
  pages, and talks — same discipline as the iron-rule-#11 qualifier.
- **A5 — `finite_rdf_axioms_sound` + merging lemma +
  `graph_bnodes_complete`**: three small semantic-layer lemmas the
  survey also flagged (merging lemma absent; finite-table-to-semantic
  bridge implicit). Queue, after gaps 1-3.
- **A6 — declarative-rule AST evaluator (Track B extension)**:
  DEFERRED, not rejected. Revisit if a rule-exchange format (e.g.
  emitting the rule table as machine-readable data for external
  audit) becomes a goal; the derives-predicates give the same theorem
  content today.

## The seven open questions, answered from landed experience

1. **W3C-notation vs relational encoding?** Relational won. The
   `interp` record is relational; IR/IP/IEXT-style sets are recovered
   as derived notions (`icext`, the enlarging convention). Proofs
   never missed the literal W3C shape.
2. **RDF 1.2 triple terms?** Exclude from the first fragment. The
   interpolation lemma's `graph_tt_free` side condition is the
   precedent; the fragment predicate makes the exclusion a checked
   hypothesis, not prose.
3. **Assignments over all identifiers or finite?** Total assignments,
   with the documented enlarging convention for fresh identifiers.
   Finite-domain refinement only becomes necessary for completeness
   arguments (gap #1 will decide its exact form).
4. **Lists, sets, or multisets?** Lists compared by `memP` — all
   licensing invariants quantify `forall t. memP t out ==> …`, and
   set-equivalence where needed is two `memP` inclusions. No multiset
   reasoning has ever been required.
5. **Which index invariants exist?** Answered concretely: all five
   buckets have discharged well-formedness (#338); completeness
   (`bucket_lookup_complete` direction) is the one genuinely new
   obligation, in flight as gap #2.
6. **Declarative rules first or direct proofs first?** Direct proofs
   first, definitively: the `_derives` relational layer emerged as
   the licensing target and cost no separate evaluator. An AST layer
   first would have doubled the closure-identity debugging surface.
7. **Axiomatic triples: tables vs generated families?** Both, split
   exactly as the proposal suggests: finite tables for the finite
   part, a syntactic recognizer for `rdf:_n`. Completeness of a
   finite table against the infinite family is not claimed anywhere.

## Adopted goals (owner approval 2026-08-05: "go for it")

Two explicit goals now govern this work, refining the proposal's aims:

**G1 — A reviewable core that provably governs the implementation.**
A W3C-domain expert must be able to review Factoidal's semantics
without reading F\* proofs, and KNOW the reviewed definitions are not
overridden by implementation detail. Deliverables:

1. **Theorem registry** (first deliverable — LANDED 2026-08-05):
   [`../theorem-registry.md`](../theorem-registry.md) — one table per
   area: W3C rule id → spec predicate → engine function → hypotheses
   / fragment restrictions → proof status → notes, plus the
   trust-surface section (G1.3's seed). 84 OWL RL rows, 13 RDFS rows,
   10 simple/RDF-rung theorems, 6 infrastructure lemmas. Carries its
   own count-convention audit (the 23-of-34 vs 24 inverse_of
   ambiguity, flagged for a ledger-comment settlement).
2. **Review kernel**: the spec-layer definitions (`*_derives` rows,
   `cond_*` conditions, interpretation records) curated as a small,
   separated, table-notation-close surface; the proofs' job is the
   "not overridden" guarantee, checked by `make verify-rdf-mt` — no
   proof reading required.
3. **Trust-surface manifest**: the complete enumeration of what is
   trusted rather than proved — `assume val` realisations (rule #11),
   interface axioms (#347's StringOrder module is the model: one
   module, one banner, DO-NOT-WIDEN), the extraction step, and the
   test gates that bound it.
4. **Calibrated claims language** (A4): the guarantee holds up to the
   stated hypotheses and the trust surface; the binding to the
   running binary goes through extraction, mitigated by suites and
   the hash-witness pattern. Stated plainly wherever the work is
   presented.

**G2 — A tighter, more usable core for developers, APIs, and AI
users.** A different axis: G1 serves readers of definitions, G2
serves callers of code. Maps to the module-stratification roadmap
(`fstar-module-style`), the .fsti policy, a bounded public API
surface per binding (native/JS/npm) with a quickstart each, and — for
AI users — the `skills/` system as the machine-facing operating
manual. Sequenced after G1's registry exists, since the registry
also names the modules the stratification must keep public.

## G3 — e2e deep proofs (owner-adopted 2026-08-06)

For the rho-df fragment (type / subClassOf / subPropertyOf / domain /
range — the working core of RDFS), the F\* theorems establish the
FULL chain: model theory ⟷ entailment ⟷ closure ⟷ termination test ⟷
index ⟷ query answers. Concretely: `rdfs_closure g` computes exactly
the entailed fragment triples (soundness done; COMPLETENESS is the
missing half), the shipping termination test is proved faithful (not
hypothesized), and SPARQL ASK/SELECT under the RDFS regime provably
returns the regime-defined answers on that fragment. Includes
completing and integrating the in-progress OWL RL work.

Milestones, dependency order:

1. **M1 — rho-df completeness** (coverage gap 1): closure =
   entailment on the fragment. Herbrand technique from the simple
   rung (`interpolation_lemma` is the existing completeness-grade
   precedent); prerequisite index completeness landed 90e2801.
   **AMENDED 2026-08-06 by finding C-1** (machine-checked,
   `RDF.Entailment.RDFS.Completeness.fst`): the goal sentence
   "`rdfs_closure g` computes exactly the entailed fragment triples"
   is unattainable against FULL RDFS entailment — reflexivity
   (`[X sc Y]` entails `[X sc X]`) and universality
   (`cond_resource` entails `[Z type Resource]` for every IRI Z)
   witnesses are both proved. The correct and landed form is the
   published rho-df move: entailment over the SIX rho-df semantic
   conditions. Under that class: `rho_df_saturation_iff` (full iff
   for any rho-df-closed saturation) + `rdfs_closure_rho_df_complete`
   (the shipping closure derives everything rho-df-entailed — the
   half that was missing). **M1b**: a six-rule rho-df closure
   operator in F\* closes the iff for an ENGINE (the theorem accepts
   it with no new proof); the shipping twelve-rule closure
   deliberately derives more than the rho-df class licenses.
2. **M2 — faithful termination**: fix #348 (`term_to_key_total`
   literal-arm separator), extend `RDF.Indexed.KeyInjectivity` to the
   literal arm, discharge the two explicit hypotheses
   `lemma_len_eq_saturated` carries — "saturation, full stop" for
   separator-free graphs.
3. **M3 — the query rung**: `evaluate(q, closure(g))` equals the
   RDFS-regime answer set for ASK/SELECT on the fragment. Design doc
   before dispatch — the genuinely new frontier.
4. **M4 — OWL RL parity**: finish the licensing/truth sweep and the
   closure-level composite. End-state is "implements the profile's
   rule set exactly", NOT completeness — the RL profile is
   deliberately incomplete for OWL semantics.
5. **M5 — extraction bridge stays test-backed**: generated per-rule
   tests + hash-witness pattern, in the calibrated claims language.

## What the proposal got right that we had to learn the hard way

Written independently, the proposal converges on several rules this
repo paid for in agent-days: interpretation-exposing lemma forms over
entailment-oriented forms; inflationary lemmas as a separate cheap
layer; term-preserving vs fresh-term rule split; "avoid unfolding the
indexed graph implementation in semantic proofs"; soundness before
completeness. Convergence from two directions is evidence the
architecture is right. What the proposal could not know: the
closure-identity law and the guard-depth ≤3 rule (engine-side naming
requirements that make the proofs POSSIBLE at all) — see
`skills/proof-factory/SKILL.md`.
