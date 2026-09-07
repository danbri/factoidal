# Lean 4 parity for the "Think of a Number" (TOAN) module family

Date: 2026-09-07. Status: landed on `wt/lean-cov-toan`, not pushed.

TOAN is the small computer-algebra layer that Factoidal grew for
MathML: an expression tree with EXACT rationals, symbolic
substitution, differentiation, a canonical normaliser, finite
summation and product, and a serializer to Presentation and Content
MathML. The owner's name for it, 2026-09-06: "a module inspired by
popular Python tools, named here 'Think of a Number'".

Scope note carried from the owner: MathML and XForms are BACKENDS —
content evaluation and models. There is no presentation UI in scope.
The Presentation MathML serializer is in scope because TOAN renders
its results, and a rendered result is an output of the backend.

## The two trees

| Function | F* | Lean 4 |
| --- | --- | --- |
| Expression tree, exact rationals, evaluation | `Math.Expr.fst` | `L4Factoidal/MathML/Core.lean` |
| Substitution | `Math.Subst.fst` | `Math/Subst.lean` |
| Normaliser | `Math.Simplify.fst` | `Math/Simplify.lean` |
| Differentiation | `Math.Diff.fst` | `Math/Diff.lean` |
| Summation / finite product | `Math.Series.fst` | `Math/Series.lean` |
| Matrices | `Math.Matrix.fst` | `Math/Matrix.lean` |
| Sigmoid | `Math.Sigmoid.fst` | `Math/Sigmoid.lean` |
| Content MathML decoding | `MathML.Content.fst` | `MathML/FromXml.lean` |
| Presentation + Content SERIALIZATION | `MathML.Present.fst` | `MathML/Present.lean` |
| JSON expression argument shape | `expr_of_json` in `bin/npm-entry/entry_jsoo.ml` | `MathML/FromJson.lean` |
| The five ABI operations | `entry_jsoo.ml` line 2548 | `Wasm/Ops/Toan.lean` |

## The battery

`tests/unit/toan_tests.ml` is the F*-side consumer test. It is 465
lines and most of its checks run inside loops, so the number of CHECKS
is not the number of call sites. Expanding every loop gives **110
checks** in
thirteen categories. The task brief that opened this work quoted 69;
that figure comes from an earlier revision of the file and is wrong
for the file as it stands. The expansion, per category, is what
`lake exe l4toan` prints.

`L4Factoidal/Math/ToanCases.lean` transcribes all 110, each citing its
`tests/unit/toan_tests.ml` line, and adds four checks that are NOT
transcriptions (see below), for 114. `Harness/ToanRun.lean` runs them
(`lake exe l4toan`, no arguments) and prints a labelled score.

A check whose F* function has no Lean counterpart prints `MISSING`
with the Lean function named, and counts as a FAILURE. It is not
skipped. A suite that skips its unported functions reports a score
about the suite rather than about the port (anti-pattern 28).

## Status, 2026-09-07

| Gate | Before | After |
| --- | --- | --- |
| `lake exe l4toan` | 32 pass, 78 fail (out of 110) | **114 pass, 0 fail (out of 114)** |
| `lake exe l4mathml` | 81 pass, 0 fail (out of 81) | 81 pass, 0 fail (out of 81) |
| `Wasm/native-smoke.sh` | 108 pass, 0 fail (out of 108) | 120 pass, 0 fail (out of 120) |
| `tools/lean-hygiene-audit.py` | clean, `partial def` 172 | clean, `partial def` 172 |

The denominator moved from 110 to 114 for a reason recorded below, not
by a suite growing on its own.

### The first score

    TOAN (Lean): 32 pass, 78 fail (out of 110)

| Category | Pass | Fail | Out of |
| --- | ---: | ---: | ---: |
| motivating-summation | 1 | 0 | 1 |
| motivating-product | 1 | 0 | 1 |
| empty-range | 4 | 0 | 4 |
| coeff-merge | 8 | 0 | 8 |
| coeff-merge-soundness | 3 | 0 | 3 |
| simplify-idempotence | 9 | 0 | 9 |
| simplify-soundness | 6 | 0 | 6 |
| present-wellformed | 0 | 18 | 18 |
| present-parens | 0 | 5 | 5 |
| content-roundtrip | 0 | 17 | 17 |
| present-new-ops | 0 | 20 | 20 |
| present-new-ops-wellformed | 0 | 14 | 14 |
| content-new-ops | 0 | 4 | 4 |

All 78 failures were one gap and said so by name: `MathML.Present.fst`
had no Lean counterpart, so every check that SERIALIZES an expression
reported `MISSING L4Factoidal.MathML.toPresentationMathML` or
`... toContentMathML`. The 32 passes were the summation, product,
normaliser and evaluation checks, whose Lean counterparts were already
present and agreed with F* on every one.

### The serializer

`L4Factoidal/MathML/Present.lean` closes all 78. It adds two things
the F* module does not have, because the Lean `Expr` carries §4.4.10
literals and `Math.Expr.expr` does not: a `<matrix>` renders as a
fenced `<mtable>` and a `<vector>` as a fenced one-column `<mtable>`
(MathML 3 §3.5.1), and the content form emits
`<matrix>`/`<matrixrow>`/`<vector>`, which `FromXml.lean` reads back,
so both round-trip like every other node.

No new `partial def`. Structural recursion was rejected for the nested
`List Expr`, so both mutual blocks carry a `termination_by` measure:
the presentation block a lexicographic `(sizeOf, tag)` pair matching
the F* `%[size; tag]`, the content block a plain `sizeOf`. The generic
function-application fallback is hoisted to a thunk BEFORE `args` is
destructured -- written inside an inner match, the checker can no
longer relate the reconstructed list to `args` and the measure stops
being provable.

### Four checks the F* battery does not contain

`110 pass, 0 fail` on the first run of a fresh port is a claim about
the battery before it is a claim about the port, so the battery was
perturbed to see whether it discriminates.

  * Changing the factorial token and the `merror` text: 104 pass, 6
    fail. It discriminates.
  * Changing the invisible-times separator from `&#x2062;` to
    `&#x22C5;`: **110 pass, 0 fail**. It did not notice. No
    `check_pres` case in `tests/unit/toan_tests.ml` renders a `times`,
    a `divide`, a `power`, a `root` or an n-ary function application
    with an exact expected string, so a wrong token in any of them was
    invisible to the transcribed checks.

Four checks were added for exactly those tokens, read off
`MathML.Present.fst` directly rather than transcribed, and they carry
the `.fst` line instead of an `.ml` line (category
`present-fstar-tokens`). The same perturbation now scores 113 pass, 1
fail. That is where 110 became 114.

### The dispatch ABI

`Wasm/Ops/Toan.lean` serves five operations, registered in
`Wasm/Dispatch.lean` and reported by the `ops` reflection:

| Op | Arity | Answer |
| --- | --- | --- |
| `toanSummation(bodyJson, idx, lo, hi)` | 4 | `{"ok":true,"mathml":…}` |
| `toanProduct(bodyJson, idx, lo, hi)` | 4 | same |
| `toanSimplify(exprJson)` | 1 | same |
| `toanDiff(exprJson, var)` | 2 | same |
| `toanSubst(exprJson, var, valueJson)` | 3 | same |

Five, not the six or seven the brief named.
`bin/npm-entry/entry_jsoo.ml` line 2548 registers exactly these;
`toanExprToMathML` and `toanEval` exist nowhere in the F* entry.

The `mathml` member carries CONTENT MathML (`toan_mathml_result`, line
2159), not Presentation. Both forms begin `<math`, so each smoke
assertion names a content element -- `<apply>`, `<plus/>`, `<cn>` --
and one asserts `<mi>` is absent.

`L4Factoidal/MathML/FromJson.lean` reads the argument shape of
`expr_of_json` (line 2125) member for member, and adds `mat` and
`vec`. Those two have no F* counterpart because `Math.Expr.expr` has
no matrix or vector constructor; a JSON shape that could not express
them would make the two engines differ in what they ACCEPT rather than
in what they answer.

No new `partial def` there either. The recursion cannot be structural
-- a member is reached by a LOOKUP, so the checker cannot see that the
value found is smaller than the object it came from. It is structural
on a fuel, and the fuel is the length of the value's own
serialisation: every nesting level writes at least one bracket, so the
bound is never reached by a document the arms would otherwise accept.
`sizeOf` would be the natural measure and is not usable -- it has no
compiled implementation for `Json`, which makes any definition using
it noncomputable. 15 build-time `#guard`s cover the round trip on
every constructor, the two bare forms the F* entry accepts, absent
`args` as the empty list, and two refusals.

### The linear-algebra de-duplication

`L4Factoidal/MathML/Matrix.lean` was a second copy of the algebra in
`L4Factoidal/Math/Matrix.lean`, the port of `Math.Matrix.fst` that
carries the shape theorems. The copy is deleted and
`MathML.Core.linAlg` routes §4.4.10 through `Math.Matrix`. The import
arrow reversed to allow it: `Math/Matrix.lean` now imports
`MathML.Rat`, which is all it ever used, and `MathML.Core` imports
`Math.Matrix`.

Two things stayed where they were, each for a reason:

  * Vector `plus` and `minus` stay elementwise in Core.
    `Math.Matrix.dynAdd` has no vector case and answers
    `add-type-mismatch`; that is the F* module's behaviour, and
    §4.4.10 wanting vector addition is not a reason to change the port
    from the MathML side.
  * The shape CHECKS stay in Core. MathML decides which shapes have a
    value; `Math.Matrix` computes what the value is.

### Registry

  * `formal/lean4/lakefile.lean` — the `l4toan` executable and
    `Wasm.Ops.Toan` in the `l4wasm` library roots.
  * `formal/lean4/L4Factoidal.lean` — `MathML.Present`,
    `MathML.FromJson`, `Math.ToanCases`.
  * `docs/20260903-internal-test-inventory.md` — a `lean-probe-l4toan`
    row, the probe count 30 to 31, and the native-smoke count
    re-measured at 120.

## Open items

1. The npm package and the hub are UNTOUCHED. `npm/factoidal/test/toan.test.js`
   and `tests/hub/post28_test.mjs` still run against the F* bundle;
   pointing them at the Lean module needs a wasm rebuild, which this
   session deliberately did not do.
2. Nothing in the TOAN layer is PROVED. The battery is a differential
   test against F*, not a theorem. The obvious first statements are the
   ones `Math/Simplify.lean`'s header already claims in prose:
   `simplify` is idempotent, and `eval env (simplify e) = eval env e`.
   The probe checks both on 15 expressions; neither is a theorem in
   either tree.
3. `Math/Simplify.lean`, `Math/Subst.lean`, `Math/Diff.lean` and
   `MathML/Core.lean`'s `eval` are still `partial def`, inherited from
   before this work. `Present.lean` and `FromJson.lean` show both
   repairs -- a lexicographic size measure and a serialisation-length
   fuel -- so the pattern for retiring them exists.
4. The four `present-fstar-tokens` checks close the gap the
   perturbation found in the PRESENTATION serializer. The equivalent
   audit was not run on the CONTENT serializer: `content` has no
   exact-string check for `<cn type="rational">`, `<csymbol>` or the
   `<matrix>`/`<matrixrow>` nesting, only `contains` checks for four
   empty elements. The round-trip checks constrain it, but a
   round-trip cannot see an error the decoder makes symmetrically.
