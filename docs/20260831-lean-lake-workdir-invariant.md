# Lean Lake working-directory invariant

`formal/lean4/` is a self-contained Lake project. All `lake build`,
`lake exe`, and `lake env` invocations for Factoidal must use that directory
as their explicit working directory. Git status, commit, fetch, merge, and
push remain repository-root operations. Do not combine the two scopes in a
single shell command which relies on a preceding `cd`.

This rule is recorded in `skills/factoidal-lean-basics/SKILL.md` and
`CLAUDE.md` after repeated root-directory build invocations obscured the
actual Lean build boundary.
