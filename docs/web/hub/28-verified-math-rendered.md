---
title: "Verified math, rendered: MathML, TOAN, linear algebra, and a bounded-rational sigmoid"
description: "MathML evaluation returning an exact rational (and a clean undef instead of NaN on division by zero), an exact-arithmetic CAS producing Content MathML for a summation, matrix/vector algebra over exact rationals, and a bounded-rational exp() approximation (argument reduction, truncated Taylor, repeated squaring, documented error bound) driving an engine-serialized MathML formula and an interactive sigmoid plot."
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
formatMathValue = (v) => {
  if (v.kind === "rat") return `${v.num}/${v.den}`;
  if (v.kind === "bool") return String(v.value);
  return `undef (${v.reason})`;
}
```

```observable-js
mathmlDemo = {
  const two = await fn.mathmlEval("<apply><plus/><cn>2</cn><cn>3</cn></apply>");
  const zero = await fn.mathmlEval("<apply><divide/><cn>1</cn><cn>0</cn></apply>");
  return [
    { contentMathml: "<apply><plus/><cn>2</cn><cn>3</cn></apply>", value: formatMathValue(two) },
    { contentMathml: "<apply><divide/><cn>1</cn><cn>0</cn></apply>", value: formatMathValue(zero) },
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
  return await fn.toanSummation(bodyExpr, "i", 1, 4);
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
  const raw = await fn.matrixDeterminant([[1, 2], [3, 4]]);
  return raw.result;
}
```

`-2`, for the 2x2 matrix `[[1, 2], [3, 4]]` — `1*4 - 2*3`. Feed it
fractional cells instead of integers and the exactness carries through
the whole computation, not just the inputs:

```observable-js
determinantExact = {
  const raw = await fn.matrixDeterminant([[[1, 2], 0], [0, [1, 2]]]);
  return raw.result;
}
```

`1/4`, for the diagonal matrix `[[1/2, 0], [0, 1/2]]` — the product of the
diagonal, kept as a fraction rather than the floating-point `0.25` a
double-precision determinant routine would produce. `matrixScalarProduct`,
`matrixVectorProduct`, and `matrixOuterProduct` (`Math.Matrix.fst`, same
module) follow the same `{result, reason}` shape for the other three
operations.

## The sigmoid: a bounded-rational `exp`, never a float

Everything above evaluates or rewrites an expression a caller supplies.
`Math.Sigmoid.fst` goes one step further: it *approximates* — `exp` is
transcendental, so no finite expression computes it exactly — and an
approximation needs a stated error bound or it is just a guess wearing a
number. The whole computation stays scaled-integer, fixed-point
arithmetic (never a float): argument reduction divides the input by
`2^10`, a degree-12 Taylor polynomial approximates `exp` on that
now-small value at a fixed 24-digit internal precision, and
repeated squaring raises the result back to the `2^10` power. Every
multiply/divide along the way truncates back to that fixed precision
— deliberately: an earlier version of this module carried the
computation as exact, arbitrary-precision rationals instead, and the
ten repeated-squaring steps made the exact denominator's digit count
explode (roughly doubling per squaring), so a single 25-point sample
call didn't return in several CPU-minutes. Fixed-point arithmetic
keeps every intermediate value's size constant regardless of how many
multiplications are chained. `Math.Sigmoid.fst`'s header derives the
combined error bound term by term — Taylor truncation, the fixed-point
rounding at each of the roughly 180 internal operations, squaring
amplification, and the final rounding to the 9-digit output — and it
comes out to `< 10^-9` over the practical sigmoid range, dominated
entirely by that last, deliberate rounding step.

`sigmoidFormulaMathml` asks the engine to typeset its own formula —
`MathML.Present.to_presentation_mathml` walks a `Math.Expr.expr` AST for
`L / (1 + exp(-k*(x - x0)))` and emits real Presentation MathML, the
browser-native vocabulary (unlike the hand-written Content-to-
Presentation converter two sections up, this one is entirely engine
output, nothing assembled in the cell):

```observable-js
sigmoidFormulaMathml = await fn.sigmoidFormulaMathml();
```

```observable-js
sigmoidFormulaDisplay = html`${sigmoidFormulaMathml}`;
```

`sigmoidPoints(k, x0, l, xmin, xmax, n)` samples that formula at `n+1`
evenly spaced `x` values — the samples themselves, and every `exp`
inside them, computed by `Math.Sigmoid.sigmoid_points`, never by this
page's JavaScript:

```observable-js
sigmoidParams = ({ k: "1", x0: "0", l: "1", xmin: "-6", xmax: "6", n: 24 })
```

```observable-js
sigmoidSamples = await fn.sigmoidPoints(sigmoidParams);
```

Each sample is `{x, y}`, and each of `x`/`y` is the engine's `scaled`
value verbatim — `{mantissa, scale, decimal}`, the same (mantissa,
scale) pair `SPARQL11.Algebra.parse_to_scaled` produces for an
`xsd:decimal` literal, plus `decimal` (that pair formatted back to a
string by the same verified formatter) for convenience. The plot below
only ever reads `.decimal` — it positions pixels, it does not compute
sigmoid values:

```observable-js
sigmoidPlot = {
  const width = 480, height = 220, pad = 24;
  const xmin = Number(sigmoidParams.xmin);
  const xmax = Number(sigmoidParams.xmax);
  const l = Number(sigmoidParams.l);
  const coords = sigmoidSamples.map((p) => {
    const px = Number(p.x.decimal);
    const py = Number(p.y.decimal);
    const xFrac = (px - xmin) / (xmax - xmin);
    const yFrac = l > 0 ? py / l : 0;
    const sx = pad + xFrac * (width - 2 * pad);
    const sy = height - pad - yFrac * (height - 2 * pad);
    return sx.toFixed(2) + "," + sy.toFixed(2);
  });
  return (
    '<svg viewBox="0 0 ' + width + ' ' + height + '" width="' + width + '" height="' + height + '">' +
    '<polyline points="' + coords.join(" ") + '" fill="none" stroke="currentColor" stroke-width="2"></polyline>' +
    '</svg>'
  );
}
```

```observable-js
sigmoidPlotDisplay = html`${sigmoidPlot}`;
```

That's a fixed set of parameters. The last cell wires three range
sliders (`k`, `x0`, `L`) to the same `fn.sigmoidPoints` call — every
drag re-runs the F\*-verified sampler and redraws the curve; the slider
values, converted to strings, are the only thing JavaScript hands the
engine:

```observable-js
sigmoidInteractive = {
  const container = document.createElement("div");
  container.className = "hub-sigmoid-demo";

  const width = 480, height = 220, pad = 24;
  const xmin = -6, xmax = 6, n = 24;

  function makeSlider(label, min, max, step, value) {
    const wrap = document.createElement("label");
    wrap.textContent = label + " ";
    const input = document.createElement("input");
    input.type = "range";
    input.min = String(min);
    input.max = String(max);
    input.step = String(step);
    input.value = String(value);
    wrap.appendChild(input);
    container.appendChild(wrap);
    return input;
  }

  const kInput = makeSlider("k", 0.2, 5, 0.1, 1);
  const x0Input = makeSlider("x0", -4, 4, 0.5, 0);
  const lInput = makeSlider("L", 0.5, 3, 0.5, 1);

  const svg = document.createElement("svg");
  svg.setAttribute("viewBox", "0 0 " + width + " " + height);
  svg.setAttribute("width", String(width));
  svg.setAttribute("height", String(height));
  container.appendChild(svg);

  function toPixel(px, py, l) {
    const xFrac = (px - xmin) / (xmax - xmin);
    const yFrac = l > 0 ? py / l : 0;
    const sx = pad + xFrac * (width - 2 * pad);
    const sy = height - pad - yFrac * (height - 2 * pad);
    return sx.toFixed(2) + "," + sy.toFixed(2);
  }

  async function render() {
    const l = Number(lInput.value);
    const points = await fn.sigmoidPoints({
      k: kInput.value, x0: x0Input.value, l: lInput.value, xmin, xmax, n,
    });
    const coords = points.map((p) => toPixel(Number(p.x.decimal), Number(p.y.decimal), l));
    svg.innerHTML = '<polyline points="' + coords.join(" ") + '" fill="none" stroke="currentColor" stroke-width="2"></polyline>';
    return svg.innerHTML;
  }

  kInput.addEventListener("input", render);
  x0Input.addEventListener("input", render);
  lInput.addEventListener("input", render);

  await render();
  return container;
}
```

Every live cell above is pinned in
[`tests/hub/post28_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post28_test.mjs),
including the Content-to-Presentation converter's exact output string —
not just that the cell runs, but that the markup it hands the browser is
the one this page describes.
