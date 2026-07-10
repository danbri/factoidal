# Arbitrary-expression MathML rendering: XML/XPath/XSLT/MathML program

Date: 2026-07-10. Status: PLAN (written during a network outage;
re-check the sigmoid post-28 landing state before Wave 1 — that agent
was mid-pipeline at the 2026-07-10 evening rollback and its exp-approx
+ serializer-"exp" work may need re-landing first).

Owner goal (2026-07-10 `/goal`): XML, XSLT, XPath, MathML — enough to
display ARBITRARY expressions using browser rendering.

## What exists (verified in-tree today)

- `Math.Expr.fst` — symbolic expression core: rationals, variables,
  `E_App` nodes for "power", "root", "sin", "ln", … (heads are open
  strings; numeric eval is exact-rational and refuses inexactness).
- TOAN expr -> Presentation-MathML serializer (landed with task #72,
  summation/product included; exact current coverage needs a
  head-by-head audit — Wave 0 below).
- `MathML.Content.fst` — Content-MathML -> Math.Expr decoder +
  exact evaluator (plus/minus/times/divide/power/root/matrix/…,
  min/max/gcd/factorial/abs/rem/quotient, eq/neq/lt/…, vectors,
  determinant/transpose/scalarproduct/…).
- `Math.Diff.fst`, `Math.Series.fst`, `Math.Simplify.fst`,
  `Math.Subst.fst`, `Math.Matrix.fst` — producers of expressions that
  all need faithful rendering.
- XML parser with DTD Stage A, XPath 1.0 (axes, PI nodes, doc-order
  union), XSLT 1.0 at 62/88 OASIS (in-flight cluster work aims
  higher), Schematron, XForms recalc. Hub post 25/27/28/29 demonstrate
  them; post 28 is the rendered-math showcase.
- Browsers render Presentation MathML natively (Chromium 109+,
  Firefox, Safari) — no JS math-typesetting library, keeping the
  no-CDN/no-third-party-code hub rule intact.

## Definition of "arbitrary expression displayed"

Any `Math.Expr.expr` the engine can construct — including every
`E_App` head any Math.* module emits, matrices/vectors, summation/
product with bound variables and limits, derivatives from Math.Diff,
relations (eq/lt/…), and intervals — serializes to Presentation MathML
that a stock browser renders correctly, AND a user-typed input path
exists in the hub so "arbitrary" includes expressions we didn't
hard-code. Round-trip: Content MathML in -> expr -> Presentation out
must cover the full evaluable vocabulary of `MathML.Content.fst`.

## Waves

- **Wave 0 (audit, cheap)**: table of every `E_App` head emitted
  anywhere in Math.*/MathML.* vs the serializer's cases vs the
  Content-MathML decoder's vocabulary. Output: the actual gap list.
  (Planning honesty: everything below adjusts to this table.)
- **Wave 1 (serializer completeness)**: Presentation-MathML cases for
  every gap head: trig/exp/ln (with the sigmoid landing's "exp" case
  re-used or re-landed), n-ary plus/times flattening with correct
  parenthesization by precedence, unary minus, fractions vs division
  by context, msub/msup/msubsup for indexed vars and powers,
  munderover for sum/product (exists — verify limits), sqrt vs mroot,
  matrices via mtable, relations, intervals, derivative notation
  (d/dx upright, partials if Math.Diff emits them). Property-style
  unit tests: serializer output for each head parses as well-formed
  XML via OUR XML parser (self-test), and spot-render assertions in
  the post-28 browser harness.
- **Wave 2 (input path)**: user-typed expressions in the hub.
  Content MathML textarea is already honest (decoder exists). Add the
  TOAN textual grammar (already used in npm toan* tests — confirm
  exposure) as the friendlier input; parse -> expr -> render live.
  npm API: `fn.exprToMathML(input, {from: "toan"|"content-mathml"})
  -> string` plus `fn.mathmlRender` alias if naming consistency
  demands. Typed, unit-tested (including a fuzz loop over generated
  expressions: serialize -> reparse XML -> well-formed).
- **Wave 3 (XSLT bridge, the standards flex)**: a vendored-in-repo
  XSLT stylesheet transforming Content MathML -> Presentation MathML
  EXECUTED BY OUR OWN XSLT ENGINE, demonstrated in a hub cell next to
  the F* serializer's output on the same input. This exercises
  XML+XPath+XSLT+MathML together — the goal's four letters in one
  cell — and doubles as a differential test of the serializer.
  (Scope: the corpus of heads from Wave 0, not the whole MathML 3
  spec; label accordingly.)
- **Wave 4 (post 28 as the showcase)**: restructure post 28 around
  "type an expression, watch the engine parse, simplify, evaluate,
  differentiate, and render it" — reactive cells chaining
  fn.toanSimplify/fn.mathDiff (confirm names in Wave 0) into
  fn.exprToMathML, with the sigmoid sliders section (in-flight) as the
  applied example. Browser-harness test asserts each cell's <math>
  output. Anti-pattern #28: bundle rebuild + forced npm-entry each
  landing.

## Constraints

- All serialization/parsing in F* (iron rules #1/#2/#4); JS cells are
  presentation-only. No MathJax/KaTeX — native rendering only.
- Obsolescence sweep each wave (post 28 prose, mathml.yaml
  `remaining`, Math module headers).
- Floors: MathML suite, XSLT 62/88-or-current, XML conformance,
  units, plus standard SPARQL/RDF floors on any binary rebuild.
