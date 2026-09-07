# Lean 4 parity for the "Think of a Number" (TOAN) module family

Date: 2026-09-07. Status: in progress.

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
| Presentation + Content SERIALIZATION | `MathML.Present.fst` | (see status) |

## The battery

`tests/unit/toan_tests.ml` is the F*-side consumer test. It is 465
lines and most of its checks run inside loops, so the number of CHECKS
the number of call sites. Expanding every loop gives **110 checks** in
thirteen categories. The task brief that opened this work quoted 69;
that figure comes from an earlier revision of the file and is wrong
for the file as it stands. The expansion, per category, is what
`lake exe l4toan` prints.

`L4Factoidal/Math/ToanCases.lean` transcribes all 110, each citing its
`tests/unit/toan_tests.ml` line. `Harness/ToanRun.lean` runs them
(`lake exe l4toan`, no arguments) and prints a labelled score.

A check whose F* function has no Lean counterpart prints `MISSING`
with the Lean function named, and counts as a FAILURE. It is not
skipped. A suite that skips its unported functions reports a score
about the suite rather than about the port (anti-pattern 28).

## Status, 2026-09-07

FIRST SCORE, measured, before any change to the serializer:

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

All 78 failures are one gap and they say so by name: `MathML.Present.fst`
has no Lean counterpart, so every check that SERIALIZES an expression
reports `MISSING L4Factoidal.MathML.toPresentationMathML` or
`... toContentMathML`. The 32 passes are the summation, product,
normaliser and evaluation checks, whose Lean counterparts are present
and agree with F* on every one.

An earlier revision of this note carried 32/78 as a PREDICTION made by
reading the two trees while the disk floor blocked a build. The run
matched it. That is worth exactly one sentence: the prediction was
cheap because the gap is a whole missing module, and a prediction that
matches is still not a measurement.

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

`lake exe l4mathml`: 81 pass, 0 fail (out of 81), unchanged.

## Open items

1. Land `Present.lean`, flip the five hook functions in
   `ToanCases.lean` (`presCheck`, `presContains`, `presWellFormed`,
   `contentContains`, `contentRoundTrip`) from `chkMissing` to the
   real comparison, and record the before and after scores.
2. The dispatch ABI operations. The brief named
   `toanExprToMathML`, `toanEval`, `toanSummation`, `toanProduct`,
   `toanDiff` and `toanSimplify`. The F* npm entry
   (`bin/npm-entry/entry_jsoo.ml` line 2548) registers five and they
   are not that set: `toanSummation`, `toanProduct`, `toanSimplify`,
   `toanDiff`, `toanSubst`. There is no `toanExprToMathML` and no
   `toanEval`. Port the five that exist -- matching the npm entry op
   for op is the whole point of the dispatch table -- and do not
   invent the two that do not.
3. All five operations return `{"ok":true,"mathml":...}` carrying
   CONTENT MathML, not Presentation (`toan_mathml_result`, line
   2159). A Lean port that returned Presentation would pass a
   `contains "<math"` test and be wrong.
4. `lakefile.lean` entry, the `L4Factoidal.lean` import and the
   design record are done; the `docs/20260903-internal-test-inventory.md`
   row is not. That document's `lean-probe-*` row counts 30 zero-arg
   probes; `l4toan` makes 31.
