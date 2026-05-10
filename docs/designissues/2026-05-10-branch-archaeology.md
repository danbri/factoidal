# Branch archaeology report — 2026-05-10

**Verdict**: No useful finds. Every non-`claude/main` branch is either fully landed via merged PRs, a stale precursor superseded by later main work, or docs-only. None contains F\* code, lemma proofs, or `assume val` realisations not already on `claude/main`.

## Survey scope

- **Total non-main refs surveyed**: 81 unique branches (43 active `claude/*` + 38 worktree-agent scratch + 1 `readability-refactor` + 1 deleted `codex-ballyhoo-baseline` alias)
- **Date range**: 2026-03-06 → 2026-05-10
- **Branches with any F\* diff vs `claude/main`**: 37
- **Branches with novel cherry-pickable commits vs `claude/main`**: 30
- **Branches whose F\* content is unique-and-new (not just behind main)**: **0**

The 30 branches with novel commits all turn out to be either:
1. Un-rebased work whose substance has since landed via a PR with a different commit hash, or
2. WIP that's been *passed* by main, so the branch is now behind.

## Categorically distinct branches checked

| Branch | Tip | Status |
|---|---|---|
| `claude/research-rdf-datasets-tvQYj` | 2026-05-10 | Docs-only (RDF dataset survey) |
| `claude/fstar-roaring-bitmap-D3f23` | 2026-05-07 | Landed (#177) |
| `claude/roaring-phase-d5-promotion-lemmas` | 2026-05-07 | Landed (`b27e6d9` on main) |
| `claude/fstar-2025-12-15-drift-fix` | 2026-05-07 | Landed (#228) |
| `claude/heth3-retirement` | 2026-05-07 | Landed (#211) |
| `claude/eval-timebudget-limits` | 2026-05-07 | Landed (#205) |
| `claude/shacl-skeleton` | 2026-05-07 | Landed (#181 stub on main) |
| `claude/rif-phase-4-test-runner` | 2026-05-07 | Landed (#225); behind main (lacks `parse_rif_imports`) |
| `claude/rif-import-resolution` | 2026-05-07 | Landed (#232) |
| `claude/rdfc10-phase2-hndq-permutations` | 2026-05-07 | Landed (`596c077` on main) |
| `claude/owl-rl-cluster-c-maxqc-fix` | 2026-05-07 | Landed; behind main (lacks parent7 anchor fix) |
| `claude/template-prefix-fstar` | 2026-05-07 | Landed (#159) |
| `claude/http-buffer-helpers-fstar` | 2026-05-07 | Landed (#156) |
| `readability-refactor` | 2026-04-24 | Orphan history (no merge base with `claude/main`); contains the original KaRaMeL C-extraction pilot (`9bf1bd5`, 1710 lines of C from `RDF.Graph.Executable.fst`) |

## Mechanical-diff sample for sanity

For every branch `B`, `git diff <B>:<file> claude/main:<file>` shows the branch is *strictly older or equal* to main on every modified F\* file:

- `claude/rif-phase-4-test-runner:RIF.Core.Tests.fst` lacks `parse_rif_imports` that exists on `claude/main` (Phase 5, #232).
- `claude/owl-rl-cluster-c-maxqc-fix:OWL.QueryRewrite.fst` lacks the `parent7 anchor` `_mxqc1_anchor_` binding that exists on `claude/main`.
- `claude/shacl-skeleton:SHACL.Validation.fst` is byte-identical to `claude/main`'s.
- `claude/bet7-loader:SPARQL.Plan.Loader.fst` is byte-identical to `claude/main`'s.
- `claude/lamed3-offset-index:{RDF.Store.Columnar.OffsetIndex,SPARQL.Plan.AccessPath}.fst` byte-identical.
- `claude/roaring-phase-d5-promotion-lemmas:formal/roaring/src/Container.fst` 2-dot diff = empty.

## The only "novel" content anywhere

`readability-refactor` (orphan, 2026-04-24) carries:
- `formal/fstar/corespecs/{RDF.CoreSpec, RDF.Vocabulary, RDF.ModelTheory, RDF.Formats, RDFS.Vocabulary, XSD.Vocabulary, OWL.Vocabulary, OWL.ProfileSpec, SPARQL.QuerySpec}.fst`
- `formal/fstar/midzone/{Entailment.Policy, JSONLD.Policy, RDF.GreyArea}.fst`
- `formal/fstar/practical/{RDF.IndexedMemory, RDF.Pragmatic}.fst`

Per the commit message, this is a "passive readability layer" — math-spec-style restatements of types like `iri`, `triple`, `graph` as predicates over collections. Not implementation; would not close any #200 stub. The same branch also still has the old `assume val utf8_of_codepoint` from before today's `1d2b669`, so its `SPARQL11.Parser.fst` is strictly behind main.

## #200 cross-reference

| #200 outstanding item | Anything reusable from branches? |
|---|---|
| **#64** `process_string_escapes` | No. No branch has an F\* implementation. |
| **#65** BASE IRI threading (~70 callsites) | No. Every branch's `SPARQL11.Algebra.fst` is behind main. |
| **#68** NTriples residual (`FStar.Char.char_code`) | No. Tonight's `b781175 patch: shrink #68 — Turtle half is dead code, NTriples half remains` is on main; no branch carries an upstream-Char or codepoint-type workaround. |
| **#118** cottas_ondisk_runtime perf parity | No. Phase 2.5a foundation `7c6f594` is already on main; no branch carries further progress. |
| **#253** ballyhoo_hdt_runtime retirement | No. No branch contains stalled retirement work. |
| **#254** Bet7 lazy-populate retirement | No. `claude/bet7-loader` is identical to main. |
| **DictWriter / PresenceWriter / OffsetsWriter / CompoundPresenceWriter cons-case lemmas** | **No.** These files don't exist on any other branch — they were added to main in tonight's `1b5e255`, `3e2d72d`, `071a88a`. The `admit ()` cons-cases on main are the only versions anywhere in the repo. |
| **G2/G3 C-build pilot demos** | Only `readability-refactor`'s ancestor `9bf1bd5` (1710 lines of pre-Low\* C extraction, March 6); but those artifacts are already preserved in `junk/do_not_use/c-output/` on `claude/main`, with the README explaining why they were retired. Not a useful starting point. |
| **Recovery-plan precursor work** | `claude/fstar-only-query-planning-recovery` (May 7) = docs-only (the recovery plan + I/O verification annex), already on main. |

## Recommendation

**No cherry-pick candidates.** The #200 outstanding work has to be done fresh on `claude/main`. There is no half-finished proof, no `assume val` realisation, no novel F\* module, and no C-extraction pilot anywhere in the branch graph that isn't already on `claude/main` (in `formal/fstar/`) or memorialised under `junk/do_not_use/`.

The only piece of mild archival interest is `readability-refactor`'s `formal/fstar/{corespecs, midzone, practical}/*.fst` (April 24, orphan history). These are math-style "spec-shape" restatements rather than implementation. If you ever want a normative-spec-style reading layer parallel to the executable modules, those files are findable at `2e0753b`. They will not help close #200.

## Suggested cleanup

The cluster of May 6-7 branches whose work has landed is taking up `git branch -a` real estate and showing up in any future archaeology grep. Consider deleting:

```bash
# Candidate deletions — branches whose F* content is fully on claude/main:
for br in \
  claude/backend-info-helpers-fstar claude/backend-source-string-fstar \
  claude/backend-source-string-fstar-stacked claude/bet7-loader \
  claude/bgps-in-query-fstar claude/bound-status-fstar \
  claude/dump-nq-rdf-format-fstar claude/error-response-bodies-fstar \
  claude/eval-timebudget-limits claude/fstar-2025-12-15-drift-fix \
  claude/heth3-retirement claude/http-buffer-helpers-fstar \
  claude/lamed3-offset-index claude/nquads-serialize-fstar \
  claude/owl-cls-maxqc1-parent7-fix claude/owl-cluster-a-property-chain-n3 \
  claude/owl-cluster-b-prp-key claude/owl-cluster-k-rdfxml-empty-base-bnode \
  claude/owl-progress-equivclass-sameas-named claude/owl-querywrite-parent7-rewriter-fix \
  claude/owl-rl-cluster-c-maxqc-fix claude/parser-nquads-z3rlimit-bump \
  claude/pe5-plan-explain claude/qof3-diagnostics-fstar \
  claude/rdf-format-fstar-migration claude/rdf-pretty-fstar-migration \
  claude/rdfc10-hash-patch-extraction-format-fix claude/rdfc10-phase2-hndq-permutations \
  claude/recent-query-json-fstar claude/render-headers-fstar \
  claude/rif-core-phase-1 claude/rif-core-phase-2-eval \
  claude/rif-core-phase-3-rifxml-parser claude/rif-eval-tail-rec-and-exact-smoke \
  claude/rif-import-resolution claude/rif-phase-4-test-runner \
  claude/roaring-phase-d claude/roaring-phase-d5-promotion-lemmas \
  claude/select-vars-and-cors-cleanup claude/shacl-skeleton \
  claude/sparql-plan-pruning-estimate claude/static-files-fstar \
  claude/template-prefix-fstar claude/timing-formatters-fstar \
  claude/track1-bs-json-tp-explain claude/track1-rdfc10-escape-delegate \
  claude/track1-rdfc10-nquads-delegate claude/track1-test-manifest-helpers \
  claude/update-has-load-fstar
do
  git branch -D "$br"
  git push origin --delete "$br" 2>/dev/null || true
done
```

(NOT run by the archaeology subagent or by this commit — listed for the user's review.)
