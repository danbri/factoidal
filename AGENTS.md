# Factoidal agent instructions

Read [`CLAUDE.md`](CLAUDE.md) and the relevant `skills/<topic>/SKILL.md` before
working in that area. These instructions apply to every coding agent, not only
Claude.

## Lean 4 working directory

`formal/lean4/` is a self-contained Lake project. Every `lake build`, `lake
exe`, or `lake env` command **must** use `formal/lean4/` as its explicit
working directory. Never run a `lake` command from the repository root,
including after a separate earlier command which happened to `cd` there. Run
repository Git commands from the repository root.

Do not write a combined command that assumes a prior `cd` remains active. Use
separate commands (or set the tool's working directory explicitly) for Lean
and Git work. Before each Lean command, check the tool call's `workdir`, not
the previous transcript. This repeated failure caused root-level Lake errors
and misleading test results on 2026-08-31.

## Worktree discipline

Preserve unrelated working-tree changes. Stage only the files needed for the
current coherent change. Record substantive design and implementation progress
in dated `docs/YYYYMMDD-*.md` worknotes.
