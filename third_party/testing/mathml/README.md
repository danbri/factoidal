# Content MathML evaluation corpus (REC-cited)

This directory holds two manifests, both scored by
`bin/mathml-runner/mathml_runner.ml` against
`formal/fstar/MathML.Content.fst`:

- `manifest.json` — scalar Content MathML (arithmetic, relations, `cn`
  literals) evaluated over exact rationals via `Math.Expr`.
- `matrix-manifest.json` — Content MathML **linear algebra**
  (MathML3 §4.4.10: `<matrix>`/`<matrixrow>`/`<vector>` and the
  `linalg1`/`linalg2` operators `determinant`, `transpose`,
  `scalarproduct`, `vectorproduct`, `outerproduct`, `selector`, plus
  matrix/scalar `plus`/`minus`/`times`) evaluated via `Math.Matrix`.
  Matrices print as `[[a,b],[c,d]]`, vectors as `[a,b,c]`; shape
  violations (non-square determinant, inner-dimension mismatch,
  ragged add, out-of-range selector) print as `undef`.

The default `mathml_runner` invocation scores both manifests and reports
a combined labelled total.

## Provenance

These are **not** vendored from a third-party test suite. No public,
machine-checkable Content-MathML *numeric-evaluation* corpus exists:
the W3C MathML test suites and the browser-hosted MathML test suite are
overwhelmingly **Presentation/rendering** tests (they check visual
layout, not the value a `<apply>` tree computes). A probe for
`w3c/mathml-testsuite` on 2026-07-07 found no accessible evaluation
suite; `w3c/mathml` is the specification source repository, not an
evaluation harness.

Following the project's endorsed pattern for domains that lack a
machine-checkable vendored corpus (see
`docs/designissues/2026-07-05-xforms-model-program-plan.md`, Stage-1
"Test suite"), each test is **authored from the MathML 3.0 (2nd Edition)
Recommendation, Chapter 4 "Content Markup"**
(https://www.w3.org/TR/MathML3/), and its OpenMath Content Dictionaries
(`arith1`, `relation1`, `integer1`, `minmax1`). Every test's `spec`
field cites the section / operator it exercises. The `<apply>`
constructions mirror the worked forms in the REC; the expected values
are the exact mathematical results.

This is REC-example-derived with citations, **not** synthetic tests
dressed up as conformance (iron rule #6 / anti-pattern #25). It is
labelled as authored, not as a W3C conformance pass.

## Format

```json
{
  "provenance": "...",
  "tests": [
    { "name": "...", "spec": "MathML3 §... / OpenMath CD",
      "input": "<math>...</math>",
      "expectedValue": "<canonical value string>",
      "env": { "x": "41" }          // optional variable bindings
    }
  ]
}
```

`expectedValue` is compared against `MathML_Content.value_to_string` of
the computed value:

- integers print as `n` (e.g. `42`, `-17`);
- non-integer rationals print reduced as `num/den` (e.g. `3/4`,
  `157/50`) — the denominator is always positive and the fraction is in
  lowest terms;
- booleans print as `true` / `false`;
- anything not exactly evaluable (unsupported operator, non-integer
  power, inexact root, division by zero, unbound variable, type error)
  prints as the single token `undef`.

`env` binds `<ci>` variables to numeric strings, parsed to exact
rationals by the F* side before evaluation.

## Why exact (no floating-point tolerance)

`MathML.Content.fst` models every value as an **exact rational**
(reduced `int/int` with positive denominator). Reals such as `3.14`
are parsed exactly (`314/100 = 157/50`); e-notation is exact because
`10^k` is rational. Comparison is therefore exact canonical-string
equality — no tolerance is needed and none is applied. Genuinely
irrational operators (`exp`, `ln`, `log`, trigonometric functions,
non-integer `power`, inexact `root`) are **refused** with `undef`
rather than approximated, which is why the corpus scores them as
`undef` expectations.
