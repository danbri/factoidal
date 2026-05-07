# 2026-05-07 — Tableau.fst audit + next-steps

Last refreshed: 2026-05-07 (entailment-suite numbers updated to live runner output).

## Status

Audit. Doc-only. No F\* / OCaml code edits in this PR-equivalent.

The user flagged "Tableau is incomplete." This audit confirms that
characterisation — but with an important caveat: **Tableau.fst is
live, sound, partially-functional production code**, not dead
scaffolding. The "incompleteness" is principled (returns `None`
rather than guessing) and is consistent with the staged plan in
`docs/designissues/2026-04-19-tableau-owl-plan.md`. The next-steps
recommendation below is **complete** (continue the Phase 1+ roadmap),
not retire.

## What's there

`formal/fstar/Tableau.fst`:

- **LoC:** 1167 lines (1 module, ~46 KB).
- **`assume val` count:** 0. (Iron-rule-3 clean — no acknowledged
  gaps via assumption; all gaps surface as `None` in the option-bool
  contract instead.)
- **`--lax` / `--admit_smt_queries` usage:** 0. Iron-rule-10 clean.
- **TODO / XXX / FIXME comments:** 0 literal occurrences. The
  module does, however, carry an extensive header block (lines 3-49)
  that *names every deferred stage explicitly* — see "Completeness
  assessment" below — and per-case soundness notes throughout. So
  "TODO" is structured, not ad-hoc.
- **Verifies cleanly under z3 4.13.3?** **Yes.** Reproduced locally:

  ```
  $ eval $(opam env --switch=fstar)
  $ cd formal/fstar
  $ fstar.exe --z3version 4.13.3 --use_hints --hint_dir hints \
      --include . Tableau.fst
  ...
  Verified module: Tableau
  All verification conditions discharged successfully
  ```

  (Run from `formal/fstar/`. The non-error warnings are from
  `RDF.Graph.Executable` re-checking, not from Tableau.)

### Top-level surface (excerpt — full enumeration in §References)

OWL vocabulary constants (lines 58-127): 17 `wf_iri` constants
(`owl_intersectionOf`, `owl_unionOf`, `owl_complementOf`,
`owl_disjointWith`, `owl_Restriction`, `owl_onProperty`,
`owl_someValuesFrom`, `owl_allValuesFrom`, `owl_hasValue`,
`owl_cardinality`, `owl_minCardinality`, `owl_maxCardinality`,
`owl_qualifiedCardinality`, `owl_minQualifiedCardinality`,
`owl_maxQualifiedCardinality`, `owl_onClass`, plus `rdf_first` /
`rdf_rest` / `rdf_nil`).

Class-expression AST (lines 139-166): `class_expr` with 12
constructors covering `CE_Named`, `CE_SomeValuesFrom`,
`CE_AllValuesFrom`, `CE_HasValue`, `CE_IntersectionOf`,
`CE_UnionOf`, `CE_ComplementOf`, `CE_MinCard`, `CE_MaxCard`,
`CE_ExactCard`, `CE_MinQualCard`, `CE_MaxQualCard`,
`CE_ExactQualCard`, `CE_Unknown`.

Parser + helpers (lines 173-326): `find_first_object`,
`term_as_subject`, `walk_rdf_list`, `cardinality_literal_to_nat`,
`cardinality_value`, mutually-recursive
`parse_class_expr` / `parse_class_expr_list` (fuel-bounded).

Membership decision procedure (lines 349-617):
- `has_type`, `find_P_successors`
- `any_disjoint_witness_in` / `any_disjoint_witness_sym` /
  `has_disjoint_witness` (the disjointWith → complementOf bridge)
- `is_member` (the main entry, mutually-recursive with
  `any_is_member`, `all_is_member`, `is_intersection_member`,
  `is_union_member`, `count_qual_successors`).

Legacy stage-(a) tableau-state types (lines 623-685):
`tab_link`, `tab_individual`, `tab_node`, `tab_status`,
`tab_branch`, `tab_obligation`, `tableau_state`,
`init_tableau_state`, `triple_in_graph`, `tableau_step`. The
`tableau_step` helper is a **no-op stub** — it returns
`(st, Unknown)` regardless of state. This is the only piece that
matches the colloquial "incomplete tableau" reading.

Top-level entailment entry (lines 705-735):
`owl_tableau_entails` (regime, dataset, schema, goal) →
`option bool`, plus the `_graph` convenience wrapper.

Materialisation pipeline (lines 746-1036):
- `is_class_expression_subject`, `collect_ce_bnodes`,
  `collect_candidate_individuals`
- `materialise_for_pair`, `materialise_for_ce`, `materialise_all`
- `emit_intersection_subclasses_via_eqc` and
  `emit_union_subclasses_via_eqc` (cls-int / cls-uni unfoldings)
- `materialise_eqc_expansion`
- `existential_obligation`, `witness_bnode_id`,
  `already_has_witness`, `witnesses_for_ce_bnode`,
  `witnesses_for_all`, `tableau_introduce_witnesses`
- **Public entries actually called from the runner:**
  `tableau_materialise` (the orchestrator) and
  `owl_tableau_entails` / `owl_tableau_entails_graph`.

In-file sanity matrix (lines 1043-1167): a `_tableau_sanity_matrix`
let-binding gated on `if false` so F\* type-checks the assertions
(min1, min2, max0, qualified-min, existential-obligation
extraction) without running them.

## What it's used by

### Internal F\* consumers

- `formal/fstar/RDF.Graph.Executable.fst` — references Tableau in
  comments and notes the bridge symmetry (Tableau is downstream of
  Executable, not upstream — duplication in QueryRewrite is to avoid
  a cycle, see lines 76-80 of `OWL.QueryRewrite.fst`).
- `formal/fstar/OWL.QueryRewrite.fst` (7 hits) — does NOT
  `open Tableau`. It deliberately re-declares OWL constants locally
  to dodge the cycle (`Tableau` depends on `RDF.Graph.Executable`;
  `OWL.QueryRewrite` would land Executable in a cycle if it took
  Tableau as a dependency). It does, however, **mirror**
  Tableau's `has_disjoint_witness` bridge inline. That mirroring
  is technical-debt earmarked for resolution by the F\*-only
  recovery plan (see `2026-05-07-query-planning-fstar-recovery.md`).
- `formal/fstar/OWL.QueryEval.fst` — does NOT consume Tableau
  directly; it composes `OWL.QueryRewrite.rewrite_query` with the
  SPARQL11 evaluators. Tableau is engaged earlier in the pipeline
  (closure side, runner side), not at query-rewrite time.

### OCaml-side consumers (extracted)

`formal/fstar/ocaml-output/w3c_runner.ml`:

- Line 705-715: the **`OWL-Direct` regime** runs
  `Tableau.tableau_materialise` between two OWL-RL closure passes
  on the default graph. This is the live integration point that
  every OWL-Direct test in the W3C entailment suite actually goes
  through.
- Line 728-735: same wrapper applied to **named-graph data** under
  OWL-Direct.
- Line 436-445: in-file comment block describing the dispatch
  (entailment regime IRI → "OWL-Direct" string label → tableau
  materialisation step).

### Build pipeline

- `formal/fstar/Makefile` line 6: `MODULES = RDF.Graph.Executable
  SPARQL11.Algebra Tableau SPARQL.ServiceDescription
  SPARQL.GraphStore`. Tableau is a verify-target.
- `formal/fstar/build-ocaml.sh` lines 208-209, 222, 323, 623:
  Tableau is in the extract for-loop (`Tableau.fst → Tableau.ml`)
  and in `COMMON_MODULES` for the OCaml link line.

### Test-runner exposure

The runner exercises Tableau **on every OWL-Direct test** (§"What
this gets you" in the entailment audit). The current SPARQL 1.1
entailment suite score is **69 pass, 1 fail (out of 70)** (verified
2026-05-07 against `bin/linux-x86_64/w3c_runner entailment`);
the +2 attributable to stage-(b) class-expression satisfiability and
the +0 from stage-(c) cardinality (commits `3f80014`, `eac72ae`) are
reflected in that score. The single remaining entailment failure
corresponds to a deferred-stage case below; the historical RIF tests
that previously contributed to the gap are out of scope (they need a
RIF rule engine, not OWL-DL).

## What it appears to do

The module implements a **hybrid forward-materialising
description-logic decision procedure** rather than a textbook
backtracking tableau. Specifically:

- Class expressions parse out of bnode-encoded RDF — the canonical
  W3C representation: `[a owl:Restriction; owl:onProperty :p;
  owl:someValuesFrom :C ]` etc.
- The decision procedure is a 3-valued (Some true / Some false /
  None) member-of-class-expression check that **only emits
  `Some true` from a direct model-theoretic justification**. Where
  a textbook tableau would branch on disjunction or skolemise, this
  module either (a) checks the literal RDF for an existing witness,
  (b) folds in a `tableau_introduce_witnesses` pass that mints a
  deterministic witness bnode for `∃P.C` / `MinCard 1`, or (c)
  bottoms out as `None` and lets the OWL-RL Datalog closure
  retry post-materialisation.
- DL fragment reachable from the AST: roughly **ALCN(D)** with
  qualified cardinality (so closer to ALCQ) — but only the
  positive fragment of the decision procedure is implemented.
  Negation is partial: `CE_ComplementOf` flips a definite answer
  from a sub-call, plus the disjointWith bridge synthesises
  positive complement-membership when an asserted disjoint type
  lines up with a known `rdf:type`.
- **Termination story:** every recursive entry takes a `nat fuel`
  parameter with a lexicographic `decreases` measure; the materialiser
  is graph-decreasing. The default fuel is 32 for parsing and 64 for
  membership in the public entry. This is verified, not just claimed.
- **Blocking story:** none. There is no anywhere/equality blocking
  because there is no full-tableau search loop. The
  witness-introduction pass is **one-shot** (line 1024-1037 comment);
  the closure caller can re-run the Datalog closure once over the
  augmented graph and stops there. In particular, this is **not**
  a complete decision procedure for any DL — it is a sound
  *semi-*decision procedure that defers to OWL-RL on hard cases.

So the contract is: "if the answer is provable from the asserted
ABox + a single round of existential witnesses + the OWL-RL
closure, we materialise it. Anything beyond that is `None`."

## Completeness assessment

**Concrete gaps**, mapped to the staged plan in
`2026-04-19-tableau-owl-plan.md` and the per-test breakdown in
`2026-04-25-owl-dl-tableau-paper-q3-parent-min-max-plan.md`:

### Stage gaps (per the original roadmap)

- **Stage (a) skeleton** — DONE (`tableau_state`,
  `init_tableau_state`, `tableau_step`). The `tableau_step` itself
  is a no-op stub that always returns `Unknown`; it is preserved as
  scaffolding, not actively used by any consumer. **This is the
  most likely source of "Tableau is incomplete" if a reader greps
  for a tableau search loop.**
- **Stage (b) class-expression satisfiability** — DONE (commit
  `3f80014`, `+2` entailment passes). All AST constructors except
  the cardinality variants have a soundness-bounded `is_member`
  case.
- **Stage (c) cardinality** — DONE for the AST + parse + decision
  cases that Datalog can't reach (commit `eac72ae`, `+0` passes
  on its own — it's scaffolding for stages (d)/(e); see the
  scoping note in `2026-04-24-tableau-stage-c.md`).
- **Stage (d) full classical-negation dual-branch search** —
  **MISSING.** The `CE_ComplementOf` case at lines 484-495 only
  flips a definite answer; there is no second branch. The
  `disjointWith` bridge at lines 377-404 is a partial substitute
  but only fires when an explicit disjoint axiom + an explicit
  type-of-the-disjoint-class are both present.
- **Stage (e) fresh-individual skolemisation for ∃** — **PARTIAL
  ("Phase 1") but not iterated.** `tableau_introduce_witnesses`
  (lines 1016-1019) does mint witness bnodes for
  `CE_SomeValuesFrom p c` / `CE_MinCard 1 p` / `CE_MinQualCard 1 p c`,
  but it is one-shot, fuel-uncapped at the iteration level (no
  outer fixpoint), and does not chain witnesses through nested
  someValuesFrom (e.g. `simple8`'s `p some (p some B)`).
- **Stage (f) max/exact cardinality refutation over k≥1** —
  **MISSING.** Lines 505-516 and 523-531 only return `Some true`
  for `k = 0` and zero known successors; for k≥1, they return
  `None`. The `2026-04-25-owl-dl-tableau-paper-q3-parent-min-max-plan.md`
  flags `parent7` (max-1) explicitly as "deferred to Phase 2",
  with the note that the real bug is closure-side
  (`cls-maxqc1`-skolem explosion — 973 spurious rows), not
  tableau-side. So this gap is co-owned with `RDF.Graph.Executable`.
- **`sameAs` / `differentFrom` UNA tracking** — declared in the AST
  (`tab_node.tn_same_as`) but not propagated. Required for true
  max-N refutation.
- **Back-jumping / absorption / blocking** — out of scope per
  every prior design note.

### Proof artefacts

- **Soundness:** the per-case header comments are model-theoretic
  arguments, not Coq-style theorems. There are **no `lemma`s** in
  the file. The verified content is purely the type system + total
  termination + the embedded sanity matrix.
- **Completeness:** explicitly disclaimed by the module header (the
  return value `None` means "unknown — caller falls back to
  Datalog"). The contract is "sound semi-decision", not
  "complete".
- **Termination:** discharged by F\*'s `decreases` clause on every
  recursive function. No `assume`, no `admit`.

### Live-codepath check

Tableau **is** on the live codepath. Specifically:
- Every test under the **`OWL-Direct`** entailment regime in the
  W3C suite calls `Tableau.tableau_materialise` (twice: once on
  the default graph, once on each named graph), see
  `formal/fstar/ocaml-output/w3c_runner.ml:705-735`.
- `Tableau.owl_tableau_entails` / `…_entails_graph` are exported but
  **not** currently called by the runner — the materialisation
  pipeline approach (mint type-triples, re-close) was preferred
  per Lamed's Phase 1 plan because it composes with OWL-RL more
  cleanly than a per-goal entailment check. So that entry point is
  defined but currently unconsumed; not dead, just dormant.
- The `tableau_step` no-op stub is **not** consumed anywhere.

## Next steps

Three options.

### Option 1 — Retire (NOT RECOMMENDED)

Tableau is on the OWL-Direct codepath. Removing it loses the +2
entailment passes from stage (b) and the witness-introduction
work from Phase 1. It would also force `OWL.QueryRewrite` to
re-import the disjointWith bridge from somewhere — currently
duplicated specifically because Tableau owns the canonical version.

If retire were chosen, the following would have to move:
- `tableau_materialise` → either inlined into
  `RDF.Graph.Executable.fst`'s `owl_rl_closure` or moved to a
  new `OWL.Closure.Materialise.fst`.
- `is_member` decision procedure → similar relocation.
- `OWL.QueryRewrite`'s "mirror" comment lifts from "TODO unify"
  to "TODO re-host".

Verdict: **net-negative.** Skip.

### Option 2 — Complete the staged roadmap (RECOMMENDED)

Continue along the existing tracks, in this order:

1. **Phase 2 — iterate witness introduction to a fixpoint**
   (~50 LoC F\*). Currently `tableau_materialise` runs
   `introduce_witnesses` once. Wrapping the
   introduce_witnesses → owl_rl_closure → materialise pipeline in
   a fuel-bounded fixpoint loop unlocks `simple8`-style chained
   existentials (`p some (p some B)`). Already scoped in
   `2026-04-25-owl-dl-tableau-paper-q3-parent-min-max-plan.md`
   §"Phase 2".
2. **Stage (d) — disjointness propagation in QueryRewrite + Tableau**
   (~150 LoC F\*). The disjointWith bridge already exists in
   `Tableau.fst:377-404` and is mirrored in `OWL.QueryRewrite.fst`.
   Strengthening it to fire transitively (across rdfs:subClassOf
   chains) would unlock paper-sparqldl-Q3 alongside the witness
   introduction. Cross-reference: closure-side disjointness rules
   may be the cleaner home — design call.
3. **Stage (f) — closure-side guard on `cls-maxqc1` skolem
   emission** (lives in `RDF.Graph.Executable.fst`, not Tableau).
   Fixes the parent7 973-row regression. **Not a Tableau edit
   per se**, but must be done in lockstep with stage (f) of the
   tableau plan.
4. **(Optional) classical-negation dual-branch search** in a new
   `Tableau.Branch.fst` companion module. Big lift, exponential
   in worst case, only justified if (1)-(3) leave hard tests
   unaddressed. Defer until needed.
5. **Wire `owl_tableau_entails` into the runner** as a per-goal
   ASK pathway (currently only `tableau_materialise` is consumed).
   The function exists but no consumer. ~20 LoC OCaml-side glue
   in `bin/w3c_runner/` (boundary-correct per Iron Rule 11) plus
   ~30 LoC F\* for the wiring helper.

Tighten the F\*-vs-mirror duplication issue with `OWL.QueryRewrite`
by promoting the OWL constants to a shared `OWL.Vocabulary.fst`
module — Tableau opens it, QueryRewrite opens it, no cycle. ~80
LoC mechanical refactor; needed before stage (d) can land cleanly.

Anticipated pass delta: see
`2026-04-19-tableau-owl-plan.md` §"Anticipated pass delta" and the
2026-04-25 plan's Phase 1/2 estimates. Roughly +3 to +6 entailment
passes from (1)+(2), depending on how parent4 and Q3 land.

### Option 3 — Park as scaffolding

Add a top-of-file banner explicitly stating the staged plan,
freeze the surface area, and treat Tableau as a known-incomplete
decision procedure for the W3C OWL-Direct regime only. Useful if
the project decides to redirect engineering effort entirely (e.g.
focus on COTTAS / Roaring / SPARQL-Update completeness) before
revisiting OWL DL.

The work-in-progress comments at the top of the file
(`STAGE (c) SOUNDNESS NOTES`, `WHAT REMAINS DEFERRED TO LATER
STAGES`) *already* function as that banner; making the park
official just means linking issue #58 and this audit doc from
the file header.

### Recommendation

**Option 2 (complete).** Rationale:

- Tableau is sound, verifies cleanly, and is the live OWL-Direct
  codepath — not dead code.
- The staged plan is tractable: each phase is ~150-200 LoC of
  F\* with a pre-existing scoping doc.
- The remaining gaps map onto specific failing W3C entailment
  tests (parent4, parent7, paper-sparqldl-Q3, simple8) — concrete
  signal, not speculative work.
- Issue #58 ("OWL DL entailment: 28 tests need OWL reasoner") is
  open and specifically asks for this; the audit doc closes the
  scoping question of *what* the reasoner is and *where* the
  unfinished edges are.

If the project is currently bandwidth-limited, Option 3 (park) is
acceptable as a stopgap — but it should **not** be retired.

## Open questions

1. **Should the F\*-only recovery roadmap subsume Tableau, or
   should Tableau remain a sibling module?** The recovery doc
   (`2026-05-07-query-planning-fstar-recovery.md`) lists OCaml
   shadow-logic targets (Yod6/Tet3/Lamed3/...) but doesn't
   explicitly schedule Tableau-completion work. Owner needs to
   confirm whether Phase 9 of the recovery includes the Phase 2
   witness-fixpoint loop or not.
2. **Is `owl_tableau_entails` worth wiring into the runner**, or is
   `tableau_materialise` sufficient on its own forever? Right now
   it's a defined-but-unconsumed export — a small wart.
3. **Is the OCaml-side `cls-maxqc1` skolem explosion** (parent7,
   973 rows) properly tracked as a closure-side bug rather than
   a Tableau-side bug? It blocks parent7 / parent8, but the
   ownership is `RDF.Graph.Executable.fst`. Confirm scope.
4. **Should the OWL constants be promoted to a shared
   `OWL.Vocabulary.fst`** before further Tableau work, to undo
   the explicit duplication in `OWL.QueryRewrite.fst`?
5. **Are RIF tests (rif01, rif03) in or out of scope?** The
   2026-04-19 plan flags them as "not OWL"; the OWL DL issue #58
   currently lumps them in. Disambiguate so the denominator
   reporting (Iron Rule / anti-pattern #25) is honest.

## References

- The module file itself: `formal/fstar/Tableau.fst`.
- Original scoping (Apr 19): `docs/designissues/2026-04-19-tableau-owl-plan.md`.
- Stage (c) scoping (Apr 24): `docs/designissues/2026-04-24-tableau-stage-c.md`.
- Phase 1+2 plan (Apr 25): `docs/designissues/2026-04-25-owl-dl-tableau-paper-q3-parent-min-max-plan.md`.
- Existing OWL DL tracking issue: danbri/factoidal#58
  ("OWL DL entailment: 28 tests need OWL reasoner").
- W3C standard reference for the targeted DL fragment:
  - OWL 2 Web Ontology Language Direct Semantics
    (https://www.w3.org/TR/owl2-direct-semantics/)
  - OWL 2 Web Ontology Language Profiles (RL profile baseline:
    https://www.w3.org/TR/owl2-profiles/#OWL_2_RL)
  - SPARQL 1.1 Entailment Regimes
    (https://www.w3.org/TR/sparql11-entailment/)
- DL textbook reference: Baader, Calvanese, McGuinness, Nardi,
  Patel-Schneider, *The Description Logic Handbook* (2nd ed.,
  2007), chapter 8 (tableau algorithms for ALC and extensions).
