# Provenance: leanprover/skills (vendored, unmodified)

- Source: https://github.com/leanprover/skills
- Commit: 7d3da0282e7b724b07620e45cf212f2e05e19334 (branch main, fetched 2026-09-02)
- Licence: Apache-2.0 (LICENSE alongside this file)
- Files: skills/lean-proof/SKILL.md, skills/lean-mwe/SKILL.md, copied byte for
  byte with `gh api ... -H 'Accept: application/vnd.github.raw'`.
- Why these two: `lean-proof` is the upstream one-step-at-a-time proof
  method (error priority, hardest case first, cleanup, dependent-type
  rewriting), which matches how this repository's proof subagents work;
  `lean-mwe` is the minimal-example recipe for reporting a Lean or Lake
  bug upstream. The seven other upstream skills (setup, bisect, PR
  conventions, Mathlib build/PR/review, nightly testing) target Mathlib or
  the lean4 repository and are not vendored; `factoidal-lean-basics`
  covers this repository's setup.
- Local policy on top of `lean-proof`: `sorry` is a working placeholder
  only; nothing with `sorry`, a user axiom or `native_decide` is committed
  (CLAUDE.md, `factoidal-lean-basics`). Do not edit the vendored files;
  refresh by re-fetching and updating the commit here.
