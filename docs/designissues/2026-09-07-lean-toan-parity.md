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

**No score has been measured.** The session was stopped by the disk
floor before anything could be built or run. What is recorded here is
therefore a transcription and a predicted score, both labelled as
such.

The environment: `/System/Volumes/Data` had about 10 GB free at the
start, shared with three other agents. A cold `lake build` in this
worktree reached target 529 of 602 -- the per-module `:c.o` compiles
that the executables link against -- and the volume fell to 2.0 GB.
The build was killed to keep the volume from filling; it recovered to
2.7 GB, still under the 3 GB floor this session was given, so no
further build was attempted. This worktree's own `.lake` is 460 MB,
so it is not what filled the volume.

PREDICTED first score, from reading the two trees rather than running
them. It is a prediction and must be replaced by a run:

    TOAN (Lean): 32 pass, 78 fail (out of 110)

The 78 predicted failures are all one gap: `MathML.Present.fst` has
no Lean counterpart, so every check that serializes an expression --
`present-wellformed` 18, `present-parens` 5, `content-roundtrip` 17,
`present-new-ops` 20, `present-new-ops-wellformed` 14,
`content-new-ops` 4 -- reports MISSING. The 32 predicted passes are
the summation, product, normaliser and evaluation checks, whose Lean
counterparts are all present.

## What is committed

| Path | State |
| --- | --- |
| `formal/lean4/L4Factoidal/Math/ToanCases.lean` | the 110 cases, each citing its `.ml` line; NEVER COMPILED |
| `formal/lean4/Harness/ToanRun.lean` | `lake exe l4toan`, zero-argument; NEVER COMPILED |
| `formal/lean4/lakefile.lean` | the `l4toan` executable entry |
| `formal/lean4/L4Factoidal.lean` | the `ToanCases` import |
| `formal/lean4/L4Factoidal/MathML/Present.lean` | DRAFT port of `MathML.Present.fst`; NEVER COMPILED, not imported by anything |
| `formal/lean4/L4Factoidal/MathML/FromJson.lean` | DRAFT reading of `expr_of_json`; NEVER COMPILED, not imported by anything |

Nothing in that table has been through `lake build`. Two specific
risks are unresolved because of it:

1. `Present.lean` and `FromJson.lean` use MUTUAL STRUCTURAL RECURSION
   over `Expr`, whose `app` constructor nests a `List Expr`. Every
   existing recursion over `Expr` in this tree (`Core.render`,
   `Simplify.simplify`, `Diff.diff`, `Subst.subst`) is a `partial
   def`. Whether Lean accepts the structural form here is untested.
   If it does not, the alternative is `termination_by` on a size
   measure -- NOT a new `partial def`, which the hygiene baseline of
   172 forbids.
2. `ToanCases.lean` computes its outcomes eagerly at module level
   through `partial def`s (`simplify`, `summation`). Whether that
   elaborates without a `#eval` wrapper is untested, and it is the
   reason the guards asked for in step 4 were not written: `#guard`
   cannot reduce a `partial def`.

## Open items

1. Build and run: `lake build`, `lake exe l4toan`, record the real
   first score here, and replace the prediction above.
2. Land `Present.lean`, flip the five hook functions in
   `ToanCases.lean` (`presCheck`, `presContains`, `presWellFormed`,
   `contentContains`, `contentRoundTrip`) from `chkMissing` to the
   real comparison, and record the before and after scores.
3. The dispatch ABI operations. The brief named
   `toanExprToMathML`, `toanEval`, `toanSummation`, `toanProduct`,
   `toanDiff` and `toanSimplify`. The F* npm entry
   (`bin/npm-entry/entry_jsoo.ml` line 2548) registers five and they
   are not that set: `toanSummation`, `toanProduct`, `toanSimplify`,
   `toanDiff`, `toanSubst`. There is no `toanExprToMathML` and no
   `toanEval`. Port the five that exist -- matching the npm entry op
   for op is the whole point of the dispatch table -- and do not
   invent the two that do not.
4. All five operations return `{"ok":true,"mathml":...}` carrying
   CONTENT MathML, not Presentation (`toan_mathml_result`, line
   2159). A Lean port that returned Presentation would pass a
   `contains "<math"` test and be wrong.
5. `lakefile.lean` entry, the `L4Factoidal.lean` import and the
   design record are done; the `docs/20260903-internal-test-inventory.md`
   row is not. That document's `lean-probe-*` row counts 30 zero-arg
   probes; `l4toan` makes 31.
