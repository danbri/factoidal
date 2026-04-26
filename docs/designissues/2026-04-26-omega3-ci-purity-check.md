# Omega3 — Phase 2.8 Layer 3 CI purity check

**Subagent:** Omega3. **Date:** 2026-04-26. **Branch:** `claude/main`.
**Scope:** add `.github/workflows/check-fstar-purity.yml` (rule #11
recurrence guard, soft-mode for now) and `.github/workflows/ukparliament-bench.yml`
(demo-query-shape regression gate per "Companion concern B" in the unwind doc).
The purity workflow grandfathers in the existing patches under
`formal/fstar/experimental_ocaml_glue/` (drift baseline as of this commit)
and only flags **net-new** semantic-shaped definitions added in PR diffs:
`+let cottas_ondisk_*`, new `+module Cottas_*` blocks, and patterns matching
`if /\* ... rdfs ... \*/ then`. Soft-mode means it logs `::warning::` and
posts a PR comment annotation but exits 0 — the env var `FSTAR_PURITY_HARD`
flips it to a hard failure. The bench workflow boots the daemon (best-effort,
since CI doesn't yet have a baseline parliament corpus wired in), runs
`tools/bench_ukpar_modern.py`, and compares its `--summary` output to a
baseline JSON. Both workflows are intentionally narrow: configuration only,
no semantic logic, per rules #11 and #15.
