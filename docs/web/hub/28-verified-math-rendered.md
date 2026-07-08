---
title: "Verified math, rendered: MathML, TOAN, and linear algebra"
description: "MathML evaluation returning an exact rational (and a clean undef instead of NaN on division by zero), an exact-arithmetic CAS producing Content MathML for a summation, and matrix/vector algebra over exact rationals — the verified semantic form and a small honest Presentation-MathML renderer shown side by side."
layout: hub.njk
series: docs-hub
series_order: 28
vocab: none
status: published
tests: tests/hub/post28_test.mjs
---

Three engines here share one number type: an exact rational, never a
float. `Math.Expr.fst` defines it (`E_Rat` of a numerator and a
denominator, both arbitrary precision); `MathML.Content.fst` evaluates a
**Content MathML** expression to one; `Math.Series`/`Math.Simplify`/
`Math.Diff`/`Math.Subst` (the "TOAN" exact CAS) build and rewrite
expressions and emit them back out as Content MathML; `Math.Matrix.fst`
runs determinants and vector products over the same type.

**Content MathML is the form these engines actually speak and the form
this page verifies against** — `<apply><plus/><cn>2</cn><cn>3</cn></apply>`,
one element per operator, unambiguous, made for a machine to evaluate.
Browsers don't render it: what a browser draws natively is **Presentation
MathML** (`<mrow><mn>2</mn><mo>+</mo><mn>3</mn></mrow>`), a different
vocabulary for layout, not meaning. Below, every result is shown twice
where it matters: the verified Content MathML the engine actually
produced (read that as the source of truth), and, for the TOAN results, a
Presentation-MathML rendering built by a small converter written directly
in the cell, purely so the browser can typeset it — a display convenience
layered on top of the verified value, not a replacement for it.

## Evaluating: exact rationals, and a clean undef

```observable-js
abi = await Factoidal.loadNpmEntry()
```

```observable-js
formatMathValue = (v) => {
  if (v.kind === "rat") return `${v.num}/${v.den}`;
  if (v.kind === "bool") return String(v.value);
  return `undef (${v.reason})`;
}
```

```observable-js
mathmlDemo = {
  const two = JSON.parse(abi.mathmlEval("<apply><plus/><cn>2</cn><cn>3</cn></apply>", "{}"));
  const zero = JSON.parse(abi.mathmlEval("<apply><divide/><cn>1</cn><cn>0</cn></apply>", "{}"));
  if (!two.ok || !zero.ok) throw new Error(two.error || zero.error);
  return [
    { contentMathml: "<apply><plus/><cn>2</cn><cn>3</cn></apply>", value: formatMathValue(two.value) },
    { contentMathml: "<apply><divide/><cn>1</cn><cn>0</cn></apply>", value: formatMathValue(zero.value) },
  ];
}
```

```observable-js
return pretty(mathmlDemo);
```

`2 + 3` evaluates to `5/1` — a rational, kept as numerator over
denominator rather than collapsed to the integer `5`, because the engine
never assumes the next operation won't need the denominator. `1 / 0` is
`undef (division-by-zero)`: `MathML.Content.fst`'s `mvalue` type has a
constructor for "this has no value", so division by zero is a value the
evaluator returns, not an exception it throws or a `NaN` it fabricates.

## TOAN: an exact CAS that speaks Content MathML

`toanSummation(bodyExpr, indexVar, lo, hi)` expands a finite sum and
returns the **verified** Content MathML result — the actual output
`Math.Series.fst`'s `summation` produces, before any display step:

```observable-js
summationMathml = {
  const bodyExpr = { app: "plus", args: [{ sym: "x" }, { app: "times", args: [{ sym: "i" }, { sym: "y" }] }] };
  const raw = JSON.parse(abi.toanSummation(JSON.stringify(bodyExpr), "i", "1", "4"));
  if (!raw.ok) throw new Error(raw.error);
  return raw.mathml;
}
```

That's the sum, for `i` from 1 to 4, of `(x + i*y)` — four terms, `x`
repeated four times and `i` summed to `1+2+3+4=10` against `y`, so the
engine folds it to `4x + 10y`. The string above is the verified answer; the browser can't
draw it as written, so the next cell converts it to Presentation MathML
for display only — a small, honest converter covering exactly the
operators these demos use (`ci`, `cn`, and `apply` of `plus`/`times`/
`power`/`minus`), nothing more:

```observable-js
summationPresentation = {
  function parseContentMathml(mathmlText) {
    const inner = mathmlText.replace(/^<math[^>]*>/, "").replace(/<\/math>$/, "");
    let i = 0;
    function parseNode() {
      if (inner.startsWith("<ci>", i)) {
        const end = inner.indexOf("</ci>", i);
        const text = inner.slice(i + 4, end);
        i = end + 5;
        return { tag: "ci", text };
      }
      if (inner.startsWith("<cn", i)) {
        const gt = inner.indexOf(">", i);
        const end = inner.indexOf("</cn>", gt);
        const text = inner.slice(gt + 1, end);
        i = end + 5;
        return { tag: "cn", text };
      }
      if (inner.startsWith("<apply>", i)) {
        i += 7;
        const opMatch = /^<([a-zA-Z]+)\/>/.exec(inner.slice(i));
        const op = opMatch[1];
        i += opMatch[0].length;
        const args = [];
        while (!inner.startsWith("</apply>", i)) args.push(parseNode());
        i += 8;
        return { tag: "apply", op, args };
      }
      throw new Error("unsupported Content MathML at: " + inner.slice(i, i + 30));
    }
    return parseNode();
  }

  function toPresentation(node) {
    if (node.tag === "ci") return `<mi>${node.text}</mi>`;
    if (node.tag === "cn") return `<mn>${node.text}</mn>`;
    const args = node.args.map(toPresentation);
    if (node.op === "plus") return `<mrow>${args.join("<mo>+</mo>")}</mrow>`;
    if (node.op === "minus") {
      return args.length === 1
        ? `<mrow><mo>-</mo>${args[0]}</mrow>`
        : `<mrow>${args.join("<mo>-</mo>")}</mrow>`;
    }
    if (node.op === "times") return `<mrow>${args.join("<mo>&#8290;</mo>")}</mrow>`;
    if (node.op === "power") return `<msup>${args[0]}${args[1]}</msup>`;
    throw new Error("unsupported operator for presentation: " + node.op);
  }

  const presentation = toPresentation(parseContentMathml(summationMathml));
  return html`<math display="block">${presentation}</math>`;
}
```

That renders as real, browser-typeset math — not an image, not a LaTeX
library, a `<math>` element the browser's own MathML renderer draws from
the markup the cell built. It exists purely so this page is readable;
`summationMathml` above it is the value that was actually verified.

## Matrices: determinants over exact rationals

`matrixDeterminant` takes a matrix of cells, each either a plain integer
or an exact `[numerator, denominator]` pair, and returns the determinant
the same way — exactly, never as a rounded float:

```observable-js
determinantPlain = {
  const raw = JSON.parse(abi.matrixDeterminant(JSON.stringify([[1, 2], [3, 4]])));
  if (!raw.ok) throw new Error(raw.error);
  return raw.result;
}
```

`-2`, for the 2x2 matrix `[[1, 2], [3, 4]]` — `1*4 - 2*3`. Feed it
fractional cells instead of integers and the exactness carries through
the whole computation, not just the inputs:

```observable-js
determinantExact = {
  const raw = JSON.parse(abi.matrixDeterminant(JSON.stringify([[[1, 2], 0], [0, [1, 2]]])));
  if (!raw.ok) throw new Error(raw.error);
  return raw.result;
}
```

`1/4`, for the diagonal matrix `[[1/2, 0], [0, 1/2]]` — the product of the
diagonal, kept as a fraction rather than the floating-point `0.25` a
double-precision determinant routine would produce. `matrixScalarProduct`,
`matrixVectorProduct`, and `matrixOuterProduct` (`Math.Matrix.fst`, same
module) follow the same `{result, reason}` shape for the other three
operations.

Every live cell above is pinned in
[`tests/hub/post28_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post28_test.mjs),
including the Content-to-Presentation converter's exact output string —
not just that the cell runs, but that the markup it hands the browser is
the one this page describes.
