---
name: lean4-proof-patterns
description: Prove properties of this repository's fuel-bounded, match-heavy Lean 4 definitions (parsers, codecs, evaluators) without Mathlib — which tactics exist here, how to split nested matches without a case explosion, why `split`/`generalize` on large Nat literals never returns, the `rename_i` order after `split`, `omega` after `List.length_cons`, timed per-theorem compiles to bisect a hang, and the `#print axioms` gate. Use when a proof stalls, when `lake build` sits on one theorem for minutes, or before dispatching a proof subagent against `L4Factoidal`. Layers on the vendored `lean-proof` method; does not repeat it.
---

# Lean 4 proof patterns for L4Factoidal (no Mathlib)

Read [`lean-proof`](../../third_party/skills/leanprover-skills/lean-proof/SKILL.md)
first: one tactic then `done`, error priority, hardest case first, cleanup.
Review a finished diff with
[`lean-review`](../../third_party/skills/lean-agent-skills/lean-review/SKILL.md).
This file carries what those two assume and this tree needs. Every rule
below names the proof that paid for it.

## 1. What is available here

- Core Lean 4 only (`formal/lean4/lakefile`, no Mathlib, no Batteries):
  `cases`, `induction`, `split`, `simp`, `simp only`, `dsimp only`,
  `decide`, `omega`, `rfl`, `exact`, `rw`, `generalize`, `rename_i`,
  `obtain`, `rcases`, `subst`, `first`, `all_goals`, `<;>`.
- Not available: `ring`, `linarith`, `norm_num`, `positivity`, `aesop`,
  `convert` (the `lean-proof` "motive is not type correct" recipe uses
  `convert`; here use `generalize` and `subst` instead).
- Lemma names: `List.length_cons`, `List.length_eq_zero_iff`,
  `List.cons.inj`, `Except.ok.injEq`, `Prod.mk.injEq`, `Nat.lt_succ_self`,
  `Nat.lt_of_le_of_lt`. Check with `lean_local_search` (lean-lsp-mcp)
  before guessing.

## 2. Fuel-bounded loops: the theorem shape

A loop `f : Nat → ... → List Char → ...` with `| 0, ... => stop | fuel+1,
... => step` that consumes at least one character per step is the same
function for every fuel above the remaining length. State it as

```lean
theorem f_fuel_indep : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (f1 f2 ...), cs.length < f1 → cs.length < f2 → f f1 ... cs ... = f f2 ... cs ...
```

induct on the bound `n`, `cases f1` / `cases f2` to expose `succ`, `cases cs`,
then `simp only [f]` and `split`. The corollary "constant fuel equals the
per-token specification fuel" is one application with `Nat.lt_succ_self`.
Landed example: `L4Factoidal/Syntax/TurtleFuelTheorems.lean` (2026-09-02),
which made `parseTurtle` linear (20,019 lines: 6.16 s to 0.74 s) with the
specification forms kept as the meaning.

## 3. `split` on nested matches: one scrutinee at a time

`unfold f at h; split at h; all_goals try (split at h)` looks harmless and
hung for over seven minutes on `decodeEscape` (2026-09-02): the second
`split` hit an eight-discriminant match (`hexVal h0, ..., hexVal h7`),
which `split` handles by case analysis over the product. Instead:

```lean
generalize hexVal h0 = v0 at h   -- one per discriminant
...
cases v0 with
| none => simp at h              -- the fallback arm closes the goal
| some d0 =>
cases v1 with ...                -- nested, so 8 goals, not 256
```

`cases v0 <;> cases v1 <;> ... <;> simp at h` also works (256 goals, 2 s)
but the nested form is what reads well and scales.

## 4. Large Nat literals: never let `split` or `generalize` see them

`split at h` and `generalize e = x at h` compare candidate subterms by
definitional unfolding. On `d0 * 268435456 + ...` that unfolds `Nat.mul` on
a unary-recursive literal and does not return (the same tactic on
`d0 * 4096 + ...` returned in one second, which is how it was found). Fix
at the definition, not the proof: give the step its own function with the
number as a parameter (`escapeResult (cp pos k : Nat) ...` in
`Syntax/Turtle.lean`) and prove a lemma about that function with `cp` a
variable. `exact escapeResult_ok h` then assigns `cp := <the arithmetic>`
by unification without unfolding. Cost of not knowing this: two stalled
proof subagents and an evening.

## 5. `rename_i` order after `split`

After `split` on `match c :: rest with ...` the inaccessible names are, in
order: the pattern variables of the arm, then one hypothesis per earlier
arm that did not match, then `heq` if the scrutinee was not a variable.
`rename_i` names from the END. So for the last arm of a five-arm match
with pattern `c' :: rest'`: `rename_i cs' c' rest' hx1 hx2 hx3 heq`. When
the scrutinee IS a variable, `split` substitutes it and there is no `heq`;
a variable you named earlier may then be stale while the live one is
`rest✝` (seen 2026-09-02 in `readNumericLiteralWith_fuel_indep`: the
`rw` pattern named the stale variable and "did not find an occurrence").
When unsure, pass `_` for the list argument and let unification pick it.

## 6. `omega` does not know `List.length`

`omega` sees `(c :: rest).length` as an opaque atom. Rewrite first:
`simp only [List.length_cons] at h1 h2 ⊢; omega`. Inside a term argument
that is `(by (try simp only [List.length_cons] at *); omega)`; the `try`
because `simp only` fails with "no progress" when nothing matches.

## 7. Equality of two `match`es on the same scrutinee

`unfold f; split` on a goal `match cs with ... = match cs with ...`
substitutes the scrutinee, so both sides reduce and each arm closes with
`rfl` or with the loop theorem. Do not `unfold` both sides separately or
`simp` the whole goal; `split` alone is enough.

## 8. Bisect a hang with timed single-theorem compiles

`lake build` prints nothing while one theorem spins, and lean-lsp-mcp
requests get moved to the background. Put each theorem in its own file
(`import L4Factoidal.Syntax.Turtle`, `set_option maxHeartbeats 200000`),
compile with `timeout 180 lake env lean FILE` from `formal/lean4/`, in
parallel, and read the seconds. A theorem that reports "unsolved goals" in
one second is fine; one that hits the timeout is the target. Then cut that
proof at `done` after each tactic until the slow one shows. The scratch
wrapper used on 2026-09-02 was ten lines of shell; write it again rather
than guessing.

## 9. Gate before commit

- `#print axioms <thm>` at the end of the module: only `propext`,
  `Classical.choice`, `Quot.sound`.
- No `sorry`, no user `axiom`, no `native_decide`, no new `partial`
  (`lean-review` registry, rows 2 to 5).
- The module is imported from `L4Factoidal.lean`; an unimported theorems
  file is not built by CI and proves nothing for the tree.
- If the definition changed to make the proof possible (sections 2, 4), the
  W3C suites for that syntax are the behaviour gate, and the WASM mirrors
  are rebuilt.
