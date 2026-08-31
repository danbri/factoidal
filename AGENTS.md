# Factoidal agent instructions

Read [`CLAUDE.md`](CLAUDE.md) and the relevant `skills/<topic>/SKILL.md` before
working in that area. These instructions apply to every coding agent, not only
Claude.

## Lean 4 working directory

`formal/lean4/` is a self-contained Lake project. Every `lake build`, `lake
exe`, or `lake env` command **must** use `formal/lean4/` as its explicit
working directory. Run repository Git commands from the repository root.

Do not write a combined command that assumes a prior `cd` remains active. Use
separate commands (or set the tool's working directory explicitly) for Lean
and Git work. This prevents accidental root-level Lake failures and misleading
test results.

## Worktree discipline

Preserve unrelated working-tree changes. Stage only the files needed for the
current coherent change. Record substantive design and implementation progress
in dated `docs/YYYYMMDD-*.md` worknotes.
