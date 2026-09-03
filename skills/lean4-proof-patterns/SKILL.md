---
name: lean4-proof-patterns
description: Prove properties of this repository's fuel-bounded, match-heavy Lean 4 definitions (parsers, codecs, evaluators) without Mathlib — which tactics exist here, how to split nested matches without a case explosion, why `split`/`generalize` on large Nat literals never returns, the `rename_i` order after `split`, `omega` after `List.length_cons`, timed per-theorem compiles to bisect a hang, and the `#print axioms` gate. Use when a proof stalls, when `lake build` sits on one theorem for minutes, when retiring a `partial def`, or before dispatching a proof subagent against `L4Factoidal`. Layers on the vendored `lean-proof` method; does not repeat it.
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

## 9. Retiring a `partial def`: five techniques, cheapest first

Measured on 2026-09-03/04 over ShEx (50 `partial def`) and RIF (15).
Result: RIF 15 to 0, ShEx 50 to 21, with both suites byte-identical.
Count with `grep -c "partial def" <file>` per file, before and after.

**Do the technique-1 sweep across EVERY declaration of an area first**,
and only then spend time on one hard declaration. `sed -i '' 's/^partial
def /def /'` a whole file, `lake build` it, and read the "fail to show
termination for" list. 27 of the 65 declarations needed nothing else.

1. **Drop the marker.** Many are defensive. RIF/Engine went 8 to 0 this
   way; ShEx/SchemaEq 8 to 0.

2. **Match the CONSTRUCTOR, not the field accessor; write the list
   recursion out.** `ShEx/Schema.lean` declares `Shape`, `Group` and
   `TripleConstraint` as single-constructor `inductive`s inside a
   `mutual` block, NOT as `structure`s. So `sh.expression` is a match
   the equation compiler cannot see through, and `es.findSome? f` /
   `g.expressions.flatMap f` hide the decrease inside a higher-order
   argument. `findTeInShapeExpr` failed as
   `| .shape sh => sh.expression.bind (findTeInTripleExpr id)` and
   succeeded as
   `| .shape (.mk _ _ expr _ _ _) => match expr with | some te => ...`,
   with `findSome?` replaced by an explicit `List` companion in the same
   `mutual` block. Four ShEx declarations retired this way. Note that
   `flatMap` DOES work when its list argument comes straight from the
   constructor pattern (`ShEx.directExtends`), which is why the failure
   looks inconsistent until you check where the list came from.

3. **`termination_by s.size - i` for an index walk over an `Array`.**
   One theorem serves a whole module:

   ```lean
   theorem charAt_lt {s : Chars} {i : Nat} {c : Char}
       (h : charAt s i = some c) : i < s.size := by
     rcases Nat.lt_or_ge i s.size with hlt | hge
     . exact hlt
     . rw [charAt, Array.getElem?_eq_none hge] at h
       simp at h
   ```

   `by_contra` does not exist here (no Mathlib); `rcases Nat.lt_or_ge`
   is the replacement. `Option.noConfusion h` fails on `none = some c`;
   use `simp at h`.

   The scrutinee MUST be bound for the hypothesis to reach
   `decreasing_by`: write `match h : charAt s j with`, not
   `match charAt s j with`. Then

   ```lean
   termination_by s.size - j
   decreasing_by all_goals (have hlt := charAt_lt h; omega)
   ```

   This works on a `let rec` inside a `def` — put the two clauses after
   the `let rec` body and before the code that calls it. Six ShEx/Compact
   scanners retired this way. It costs one `unusedVariables` warning per
   arm where `h` is not needed; that is expected, not a defect.

4. **When the walker restarts where a HELPER stopped, put the bound in
   the helper's RETURN TYPE.** `skipTrivia` calls `skipTrivia s (toEol
   (i+1))`, so its measure needs `i + 1 <= toEol s (i+1)` — a fact about
   `toEol`, which would need functional induction over `toEol`. Cheaper:
   lift the helper to a top-level `def` returning `{ k : Nat // j <= k }`
   and build the proof as you build the value.

   ```lean
   def skipToEol (s : Chars) (j : Nat) : { k : Nat // j <= k } :=
     match h : charAt s (j) with
     | none => ⟨j, Nat.le_refl j⟩
     | some d =>
         if d == '\n' then ⟨j + 1, Nat.le_succ j⟩
         else
           let r := skipToEol s (j + 1)
           ⟨r.1, Nat.le_trans (Nat.le_succ j) r.2⟩
     termination_by s.size - j
     decreasing_by (have hlt := charAt_lt h; omega)
   ```

   The caller then writes `skipTrivia s (skipToEol s (i + 1)).1` and
   `decreasing_by` uses `(skipToEol s (i + 1)).2`. Where the helper is a
   separate `def` already (`Compact.readEscape`), prove the bound
   instead:

   ```lean
   unfold readEscape at h
   split at h
   . simp at h
   . repeat' split at h
     all_goals simp_all
     all_goals omega
   ```

   `repeat' split at h` handles a ten-arm `if`/`else if` chain that a
   single `split` cannot.

5. **Fuel, last.** For recursive descent over a token list the remainder
   is not visibly shorter, and nothing above helps. Give each recursive
   group a `Nat` fuel as its FIRST match discriminant, keep the public
   name as a wrapper that supplies `3 * ts.length + 3`, and make
   exhaustion an error that NAMES the construct. RIF/Ps went 7 to 0 this
   way. Justify the constant in the module text: every step of the group
   either consumes a token or hands control to the one function of the
   group that consumes a token before it recurses, so the group descends
   at most two levels per token.

   The gate for a fuel conversion is a BYTE-IDENTICAL runner output, not
   a matching score line. `diff` the whole run against the baseline you
   captured before touching the file.

### What blocks the rest

Four shapes resist all five techniques, and each is a design question
rather than a proof question. Recognise them and stop early.

- **A remainder returned by a mutual group** (ShEx/Compact's 10-def
  shape and triple-expression parser). Fuel would work; the group is
  large enough that the conversion is its own commit.
- **Termination on a VISITED set** (ShEx `flattenSE`, `resolveExtends`,
  `reachesLabel`). The measure is the schema's label count minus the
  visited count, which is not an argument of the function.
- **Recursion through a caller-supplied function** (ShEx `matchStates`,
  `tripleConstraintsWith` recurse through `lookupTe`). An inclusion
  cycle does not terminate at all, so no measure exists.
- **Recursion into sub-documents through an untyped selector** (ShEx
  `FromJson.shapeExprOf` recurses through `arr` and `fld?`, which carry
  no size bound on the result).

## 10. Gate before commit

- `#print axioms <thm>` at the end of the module: only `propext`,
  `Classical.choice`, `Quot.sound`.
- No `sorry`, no user `axiom`, no `native_decide`, no new `partial`
  (`lean-review` registry, rows 2 to 5).
- The module is imported from `L4Factoidal.lean`; an unimported theorems
  file is not built by CI and proves nothing for the tree.
- If the definition changed to make the proof possible (sections 2, 4), the
  W3C suites for that syntax are the behaviour gate, and the WASM mirrors
  are rebuilt.
