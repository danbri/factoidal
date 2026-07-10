# Worklog checkpoint — 2026-07-10 ~14:20 UTC (Fable session, time-limited)

Per anti-pattern #18: in-flight plan dump so ANY successor session can
land the running work. Read with docs/claude-rules/2026-07-10-reset-
recovery-and-parser-proof-recipe.md (environment restore traps).

## Seven agents in flight (worktrees under .claude/worktrees/)

Each was briefed: ONE commit on its worktree branch, labelled scores,
fast loop, obsolescence sweep, zero main-checkout footprint, no Claude
attribution. When one reports, LAND IT (recipe below). Agent → goal:

1. OWL syntax-dl — OWL2.SyntaxDL.fst species checker (DL vs FULL) over
   the 646-case syntax-dl.rdf catalog; owl_runner + dashboard row;
   fixes stale "tableau wiring in flight" ledger note.
2. ShEx negativeSyntax + tree-sitter — scores the ~100 ShExC
   grammar-reject tests with Parser.ShExC (new row); vendors
   ericprud/tree-sitter-shexc (MIT) as comparison probe; grammar audit
   doc. Floors: ShExC↔ShExJ differential 433/433; shex 1181/1.
3. CSVW finish — burns down the enumerated 52 (ledger CSVW row = work
   list); FIRST re-examines the 11 "PARKED protocol" discovery tests.
4. XSLT completion — six clusters per docs/designissues/2026-07-10-
   xslt-grddl-completion-scoping.md; namespace-node model is the big
   rock. Cross-consumer floor: GRDDL passes must not DECREASE.
5. QUDT Layer A — vendors v3.4.0 (CC BY 4.0 + PROVENANCE), QUDT's own
   SHACL rulesets through our validator, new dashboard family, perf
   timing recorded.
6. RIF burndown — the 4 fails + 12 skips, fixed or dispositioned per
   skills/test-suites taxonomy.
7. compile-target tooling — ./build-ocaml.sh compile <binary> filter +
   measured timings. (Stalled twice on untracked waits; if silent,
   SendMessage-nudge or check its worktree build logs.)

## Landing recipe (per agent report)

1. git cherry-pick <sha> on claude/main. Conflicts: generated
   artifacts resolve by OWNERSHIP (later-landed features keep theirs);
   .extract-state/depend*.make → theirs + git add -f; generate-report
   structural conflicts → main's tree layout + agent's row additions.
2. Re-run the agent's headline suite ON MAIN + its named floors.
   Scores must reproduce exactly.
3. cd formal/fstar && ./generate-report.sh (outputs land at repo-root
   docs/test-results/); commit + push. CI races push "ci: refresh
   dashboard" — on rebase conflict over docs/test-results/*, keep OUR
   regenerated files (checkout --theirs during rebase) and continue.
4. git worktree remove --force <path>; delete branch; df check.
5. TaskUpdate the matching task; ledger row if the agent missed it.

## Queue after landings (in order)

- OWL tableau refutation (#98) — AFTER syntax-dl (same modules). The
  deepest remaining work: clash detection, disjunction branching,
  existential witnesses, cardinality merges, nominals. Target:
  inconsistency 36/81 of 117.
- GRDDL Tracks 2+3 — AFTER XSLT; re-measure the 8 fails first.
  Scoping: 2026-07-10-xslt-grddl-completion-scoping.md.
- GeoSPARQL map fix + fullscreen (#105) — post 21 has no basemap (CSP
  blocks tile hosts BY DESIGN) + broken default marker icon. Prefer a
  vendored GeoJSON vector basemap; verify via headless harness.
  Owner-reported with screenshot 2026-07-10.
- OWL tails + DL dashboard rows (#99, #100); QUDT Layer B (after
  refutation dispatch); JSON-LD frame + html; SPARQL protocol
  wire-replay harness (sparql11-protocol.yaml remaining).

## Cautions

- DISK: allowance exhausted once today (7 worktrees + builds); freed
  by deleting stale scratchpad build dirs. Remove landed worktrees
  PROMPTLY; df before dispatching.
- z3 must be 4.13.3; fresh containers ship 4.16 first on PATH — see
  session-restore skill for the symlink fix.
- Push after EVERY landing (container resets lose only unpushed work —
  proven twice today).
- tools/obsolescence-sweep.sh is MANDATORY after each landing.
