---
name: lean4-env
description: Set up and work on the Lean 4 port (formal/lean4/, the L4Factoidal library) — toolchain install (elan/lake), the pinned version, the build-is-the-test-run contract (#guard), the no-sorry/no-axiom policy and how to audit it, the lean-lsp-mcp server for interactive goal states, and the lemma-search services (loogle, leansearch). Use when building or editing anything under formal/lean4/, when a Lean proof fails and you need the goal state, when hunting for a stdlib lemma name, or when bootstrapping Lean on a fresh machine/container.
---

# Lean 4 environment and working method (L4Factoidal)

## Toolchain

- Installer: `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y`
  then ensure `~/.elan/bin` is on PATH. `elan` is Lean's rustup:
  it reads `formal/lean4/lean-toolchain` and fetches the pinned
  version automatically on first `lake` invocation in that directory.
- Pinned toolchain: see `formal/lean4/lean-toolchain`
  (Lean 4.33.1 at port creation, 2026-08-22). Bump deliberately, in
  its own commit, with a clean `lake build`.
- Build: `cd formal/lean4 && lake build`. No dependencies — no
  mathlib, no batteries; keep it that way as long as possible (a
  mathlib dependency costs a multi-GB download or a `lake exe cache
  get` step on every fresh machine).

## The contract: a green build IS the test run and the proof check

- `L4Factoidal/Tests.lean` uses `#guard` — evaluated during
  elaboration, so a wrong answer is a BUILD ERROR. Add executable
  behaviour checks there, not in a separate runner.
- Proof policy (from the port brief, stricter than the F\* tree's):
  **no `sorry`, no user `axiom`, no `native_decide`**
  (`native_decide` smuggles in the `Lean.ofReduceBool` trust of the
  compiled evaluator). Audit with `#print axioms <theorem>`: the
  acceptable base is exactly `propext`, `Classical.choice`,
  `Quot.sound`. Tests.lean keeps `#print axioms` lines on the
  headline theorems so the audit is in every build log.
- Well-formedness witnesses for string constants (`WfIri`) are `rfl`
  — the kernel evaluates the check. If `rfl` times out on a long
  string, use `by decide`; never `native_decide`.

## Interactive proof work: lean-lsp-mcp

`.mcp.json` registers `lean-lsp` (PyPI `lean-lsp-mcp`, run via
`uvx`). It is the Lean analogue of the repo's `fstar` MCP: instead of
re-running `lake build` to chase one error, ask for
- file diagnostics (errors/warnings with ranges),
- the **goal state** at a line/column (the thing you need when a
  tactic fails),
- hover docs / declaration lookup for any identifier,
- and its built-in lemma search bridges.
Needs `uv` (`curl -LsSf https://astral.sh/uv/install.sh | sh`).
First call is slow (it boots the Lean server on the lake project).

## Finding lemma names (the #1 Lean friction)

- **loogle** — search by type shape: https://loogle.lean-lang.org/
  (e.g. `List.filter, List.mem` or `?a ++ ?b = ?b ++ ?a`).
- **leansearch** — natural-language search: https://leansearch.net/.
- In-repo: `exact?`/`apply?` tactics ask Lean itself; `simp?` shows
  which simp lemmas closed a goal (then pin them explicitly).
- Core-vs-mathlib trap: this project uses CORE Lean only. Lemma names
  found on loogle/leansearch are often mathlib-only — check the
  `Init.*`/`Std.*` namespaces in results before using.

## Style rules carried over from the port

- Every definition cites the W3C spec section it implements; module
  headers explain what is and is NOT ported and why (see
  `formal/lean4/PORT_NOTES.md` for the correspondence table and the
  assumption report against the F\* originals).
- Spec/engine split: `formal/lean4` holds the SPECIFICATION evaluator
  (list scans, nested-loop join). Do not port the F\* tree's index
  seam / planner / hash join / fuel bounds — those are performance
  machinery whose semantics is exactly the spec evaluator.
- Derived `BEq` is lawless: for types that need `==` inside proofs,
  derive `DecidableEq` and let Lean's `instBEqOfDecidableEq` provide
  a lawful `==` (2026-08-22: a derived `BEq` on `TextDirection` made
  `l.direction == l.direction` unprovable by simp; dropping the
  derivation fixed every downstream proof).
- Names: `Binding.lookup_merge`-style theorem names stating the
  observational content; `@[simp]` only on true simplification laws.

## W3C-suite harness (next stage, not yet built)

The port's compliance story will follow the F\* tree's iron rule #6:
a small Lean executable reading the SAME W3C manifests as
`bin/w3c-runner`, so Lean-engine scores come from the real test
files. Until that exists, do not quote conformance numbers for the
Lean side at all.
