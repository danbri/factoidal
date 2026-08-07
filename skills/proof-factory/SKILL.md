---
name: proof-factory
description: Run the rule-by-rule F* proof program at scale — the method that took the OWL/RDFS licensing + truth-preservation effort from 0 to ~40 landed lemmas in two session-days (2026-08-04/05). Use when proving engine rules against the W3C tables (licensing, truth-preservation, or extension lemmas), when dispatching proof subagents, when a step obligation fails undischargeably, when deciding model tier for a proof task, or when a proof agent goes silent. Carries the closure-identity law, the guard-depth ≤3 rule, the brief anatomy that gets first-attempt passes, the spray-and-verify economics, the harvest pattern for stalled agents, and the findings discipline that caught six ledger drifts and one engine completeness gap.
---

# The proof factory

How to produce machine-checked rule-by-rule proofs about the shipping
engine at scale, with subagents doing the typing and the F\* checker
as the quality gate. Every rule below was paid for in this repo;
dates and costs are named so the rules stick.

## The three lemma kinds (the program's shape)

Each engine rule (`owl_rule_*`, `rdfs_rule_*`) owes up to three
statements, tracked against the engine ledger at the foot of
`OWL.RL.Spec.fst`:

1. **Licensing** (syntactic): every output triple is an input triple
   or ONE application of the W3C row the ledger claims —
   `OWL.RL.Refinement.fst`, invariant shape
   `forall t. memP t out ==> memP t g \/ <row>_derives g t`.
2. **Truth-preservation** (semantic): every emission is true in every
   interpretation satisfying the row's semantic conditions —
   `OWL.Semantics.Soundness.fst`, `holds_all` invariants under
   `cond_*` hypotheses stated in the weakest table-implied form.
3. **Extension justification**: `[ext]` ledger entries (no W3C row)
   get their banner claim made a theorem — a `cond_*` capturing the
   cited table condition plus a soundness lemma.

An IMPOSSIBILITY with named evidence is a first-class outcome for
kind 2: rules minting fresh bnodes (`transitive_to_chain`,
`cls_svf_thing_materialize`, `cls_hasself2_synth`) cannot be proved
under the fixed-assignment shape because no RDF-Based table asserts
the existence facts their emissions need — a degenerate model
witnesses the failure. Banner it (Soundness Rules 12/14/15 are the
form); the fix is a future Skolem/model-extension lemma shape, not a
stronger hypothesis (that would break the interpretations-superset
invariant).

## The two laws of discharge (learned the hard way)

1. **CLOSURE IDENTITY.** Anonymous lambdas in a rule's step body
   (guards, inner folds, emitters) are distinct SMT tokens per
   spelling site — a proof-side re-spelling can NEVER transfer facts
   to the engine's instance, at any budget (z3rlimit 1500 tested).
   Engine fix: name the helper top-level (`term_is_iri`, the
   `*_emit` family) and have BOTH the engine and the proof reference
   the same symbol — first-order congruence then does the work.
   Cost of not knowing: two days, one 318k-token agent, four failed
   structural variants (task #36 history). Every new engine rule
   MUST use named helpers (the PROOF-FRIENDLY GUARD RULE comments in
   OWL.Closure.fsti).
2. **GUARD DEPTH ≤ 3.** A step lambda whose no-op branch sits behind
   4+ sequential decision points (if / match / if / if) defeats the
   `fold_left_inv` step obligation resource-independently (z3rlimit
   1200, ifuel 12 tested — 72a965c). Flatten sequential booleans
   into one `&&` guard (behavior-identical rewrites only). Depth ≤3
   discharges everywhere it has been tried.

The two laws are INDEPENDENT obstructions, and a single rule can have
both (measured 2026-08-05, the cls-int1/cls-uni wave): cls-int1 fell
to lambda-lifting alone; cls-uni needed lambda-lifting at EVERY fold
nesting level (including a pairwise double fold) AND a 4→3 guard
flatten (two option matches collapsed into one decode helper) —
seven prior attempts that fixed only one of the two kept failing at
the other's signature site. When a proof still fails after one
treatment, check for the other before raising budgets.

DEPTH COROLLARY (2026-08-06, the wave 3 relift — cls-hv1, cls-avf,
prp-spo2 n=2). Do not read "sections 15-17 proved this shape with
anonymous lambdas" as evidence that YOUR rule can. Those precedents
were TWO-level folds. At three levels (cls-hv1, prp-spo2) and four
(cls-avf) the anonymous-lambda proof stops discharging, and the
failure does NOT point at the lambdas: all three parked with Error 19
on the innermost `eliminate ... returns <row>_derives g new_t`, which
reads as a missing witness, not as a closure-identity problem. Four
attempts on cls-hv1 (two agent-side, two orchestrator-side, including
an intro-lemma taking all four witnesses as arguments) were spent
before the engine was touched. The treatment that worked, applied as
ONE change, first attempt green on all three rules:

  (a) lambda-lift EVERY fold level in the engine to a named
      top-level helper parameterized by exactly what its lambda
      closed over (`owl_cls_hv1_outer`/`_mid`/`_emit`,
      `owl_cls_avf1_outer`/`_prop`/`_member`/`_emit`,
      `owl_chain2_outer`/`_mid`/`_emit`) — behavior-identical, and it
      also deletes the closing `assert_norm`, since the engine
      function now unfolds to the fold by delta; and
  (b) give each proof level its OWN standalone lemma taking the level
      above's witnesses as ARGUMENTS, so the row's existential is
      assembled in one flat context (`lemma_cls_hv1_row_intro`,
      `lemma_cls_avf_row_intro`) instead of across N nested
      `introduce` scopes.

Rule of thumb: at ≥3 fold levels, do (a) and (b) FIRST. They are
cheap, mechanical and behavior-preserving; the diagnosis they replace
is not.

BRIDGE-LEMMA COROLLARY, same landing: when a bridge reads TWO buckets
at ONE node (rdf:first + rdf:rest), spell the provenance in FOUR
steps per hop — served-object map equation, `memP` in the bucket,
`ig_wf_sp`-pinned `memP _ ig.ig_triples /\ .s /\ .p`, then the
record-literal `memP _ g` the spec's cons case wants verbatim. The
parked `lemma_decode_chain_pair_licensed` collapsed those into one
assert per triple and produced four Error-19s; the intermediate
bucket-`memP` assert is what lets Z3 e-match `ig_wf_sp` for both
buckets at once. `lemma_decode_iri_list_licensed` (Refinement section
18) and `decode_chain_pair_sound` (Soundness Rule 11) both already
carry the four-step spelling — copy one of them rather than
compressing.

Corollaries: `assert_norm (rule g ig == fold_left step ...)` reduces
only through zeta-unfoldable LOCAL step lambdas spelled VERBATIM from
the engine text (top-level proof-side copies fail; pair-match vs
nested-match spellings differ in normal form). `String.concat` (list
form) is an opaque val — strings needing injectivity/decomposition
proofs must be built with `^` (see sp_key's do-not-simplify-back
comment).

Cross-module corollary (2026-08-06, the BGP-refinement landing, four
dead attempts): an equation whose right-hand side is a bare lambda
cannot cross a module boundary in the SMT encoding — a lambda in the
engine module gets a different opaque symbol from a syntactically
identical lambda written in the proof module, with no congruence
between them. Fix: NAME the continuation in the proof module, state
the defining equation with the engine's guard and match transcribed
verbatim, and close it with `norm [delta_only ...; zeta; iota;
primops; unascribe; unmeta]` + `trefl` (a TACTIC, not SMT). Related:
the normalizer will not simplify symbolic `n + 1 - 1` to `n` — spell
the fuel that way in the equation and let SMT finish at the use
site. Closed-over-term variant (same day, RhoDFClosure): two lambdas
closing over propositionally-equal RECORDS are still distinct
tokens; work with the original binder directly (`decl`, whose field
equations are in context) instead of a reconstructed record literal,
or share one let-bound `inner_of q` symbol across every fold site.

## Foundations to reuse, never rebuild

- **Index serving contracts**: all five buckets have discharged
  well-formedness — `ig_wf_pred`, `ig_wf_sp` (separator-free side
  condition), `ig_wf_subj`, `ig_wf_obj`, `ig_wf_po` (predicates in
  OWL.Semantics, weak forms in MemLemmas, discharges in
  RDF.Indexed.KeyInjectivity). Index-reading proofs take the wf they
  need plus `ig.ig_triples == g`.
- **Pipelines**: `lemma_sameas_pairs_provenance` (licensing) /
  `lemma_sameas_pairs_hold` (semantic) for the #262 pair machinery;
  `lemma_decode_iri_list_licensed` / `decode_iri_list_sound` for
  rdf:List walks; `decode_chain_pair_sound` for two-hop chains.
- **Bridges**: `lemma_subj_term_agree`,
  `lemma_term_to_subject_subj_term`, vocabulary-agreement `()`
  lemmas per constant pair, `lemma_rdf_term_eq_pins_iri`,
  `memP_existsb` + `memP_map_elim` for existsb/map witness chains.
- **Skeleton**: local verbatim step lambda → `introduce forall`
  step-preservation (case-split replaying the engine's guards,
  bridge calls, targeted asserts naming the row's conclusion form) →
  `fold_left_inv` → closing `assert_norm` → per-triple corollary.
  Nested folds: inner introduce + inner `fold_left_inv` as the
  branch's LAST expression (`rdfs_rule_domain_sound` shape); two
  sequential inner folds compose with three `fold_left_inv` calls
  (Refinement section 17).

## Brief anatomy (what gets first-attempt passes)

Ship the full sketch, not the goal: exact lemma signatures, the
witness chain spelled out, the template section named, engine text
location, known soft spots ranked, and a TWO-ATTEMPT STOP RULE with
exact-error reporting ("a precise failure report is a valued
deliverable"). Mandatory lines: Edit/Write only, never a python
heredoc; `(* *)` comments NEST — `//` only; no admit/--lax; bounded
`#push-options` allowed; restore the checked-cache branch snapshot
before verifying (cold worktree chains cost hours); activate the
opam switch, exporting the six variables by hand if the eval form is
rejected. Pin the exact `val` — agents cannot then weaken the
statement, only fail loudly. Agents deliver SECTIONS; the
orchestrator owns the file (renumber at graft, re-verify in MAIN
before committing, always).

## Economics (measured 2026-08-04/05)

- Sonnet on a recipe with a good brief: ~100-200k tokens, mostly
  first-attempt. Frontier-shaped tasks (new fold shapes, alignment
  analyses) run 2-4x that and may STOP — still profitable via
  findings.
- Haiku: good on mechanical enumeration and recipe work WITH stop
  rules (the TupRepro ladder; the allDifferent stop that caught
  ledger drift #4); poor on open-ended proof surgery (undersized
  timeouts, muddled reports).
- A checked proof is correct regardless of who wrote it; the only
  cheap-model risk is a WEAKENED statement, which the pinned `val`
  prevents. Polish (shorter proofs, lower budgets, dropped
  hypotheses) is mechanical post-hoc work against a green baseline.
- Toys lie: three separate times a minimal reproducer passed where
  the real proof failed. Never document a cause from toy evidence;
  bisect the REAL failing file (shrink until the error vanishes).
  A plausible mechanism with two data points is a hypothesis to
  refute cheaply, not a documented cause.

## Operating the fleet

- Worktree per agent (~1.2GB each — watch `df`; reclaim on landing;
  the checked-cache snapshot makes worktree verifies fast).
- Agents may end "waiting for the monitor" mid-verify: that is not a
  report. Check the worktree (file written? `fstar.exe` alive?). A
  verify silent for HOURS is a wedged z3, not progress: kill it,
  graft the section into main, and run a BOUNDED verify yourself —
  pass lands it, fail parks it with the exact error (the harvest
  pattern; three landings recovered this way).
- STOP treatment for undischargeable sections: keep the verified
  pieces, remove the failing proof (never admit), banner the exact
  error and attempts in-file, park the WIP text in the scratchpad,
  record next steps in the task list. Main stays green at all times.
- Findings discipline: every proof attempt adjudicates the ledger's
  claim. Six ledger drifts and one engine completeness gap (cls-int1
  unimplemented) came from proofs that "failed" to match the claimed
  row — proving against what the function ACTUALLY computes and
  correcting the ledger beats forcing a false theorem. Engine-vs-row
  narrowings (guards emitting less than the row licenses) are safe:
  record them in-file.
- Redundancy check before dispatch: grep for the lemma first — one
  agent run was spent re-verifying a proof that already existed.

## What this skill does NOT cover

- The measurement discipline for perf/inference claims —
  `measuring-inference`.
- General subagent prompting (paths, post-conditions, commit-first)
  — `subagent-prompting`.
- F\* syntax/extraction traps and the full proof-shape trap list —
  `fstar-module-style` (its trap #3 is the long-form history of the
  closure-identity law).
- The per-shape dispatch map — `docs/claude-rules/owl-rule-shape-matrix.md`.
