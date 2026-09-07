/-
L4Factoidal.Math.ToanCases — the "Think of a Number" (TOAN) parity
battery, transcribed from the F* consumer test
`tests/unit/toan_tests.ml` (465 lines).

Every case below cites the `.ml` line it comes from. The F* file runs
most of its checks inside loops, so the number of CHECKS is not the
number of call sites. Expanding every loop gives 110 checks:

    motivating-summation           1
    motivating-product             1
    empty-range                    4
    coeff-merge                    8
    coeff-merge-soundness          3
    simplify-idempotence           9
    simplify-soundness             6
    present-wellformed            18
    present-parens                 5
    content-roundtrip             17   (8 in section 6, 9 in 7c)
    present-new-ops               20
    present-new-ops-wellformed    14
    content-new-ops                4
                                 ---
                                 110

`lake exe l4toan` prints the same table from this list, so the count
is derived from the tree rather than from this comment. The task brief
that opened this work quoted 69; that figure belongs to an earlier
revision of the `.ml` file.

A case whose F* function has no Lean counterpart reports `missing`
with the function named. It is never skipped: a missing function is a
failure, and a suite that hides one reports a score about itself
rather than about the port.
-/
import L4Factoidal.Math.Series
import L4Factoidal.Math.Diff
import L4Factoidal.MathML.FromXml
import L4Factoidal.XML.Parser

namespace L4Factoidal.Math.Toan

open L4Factoidal.MathML
open L4Factoidal.Math

/-! ## Case records -/

/-- The result of one check. `missing` names the Lean function that
    does not exist yet, so the score line says what is absent. -/
inductive Outcome where
  | pass
  | fail (detail : String)
  | missing (fn : String)
deriving Repr, DecidableEq, Inhabited

structure Case where
  /-- The category, matching the F* `~cat` label. -/
  cat : String
  /-- The check name, matching the F* `~name`. -/
  name : String
  /-- The line in `tests/unit/toan_tests.ml` this case comes from. -/
  ml : Nat
  outcome : Outcome
deriving Repr, Inhabited

def Case.ok (c : Case) : Bool := c.outcome == Outcome.pass

/-! ## Check constructors -/

def chkTrue (cat name : String) (ml : Nat) (b : Bool) : Case :=
  { cat, name, ml, outcome := if b then .pass else .fail "expected true, got false" }

def chkEq (cat name : String) (ml : Nat) (expected actual : String) : Case :=
  { cat, name, ml,
    outcome := if expected == actual then .pass
               else .fail s!"expected {repr expected} got {repr actual}" }

def chkMissing (cat name : String) (ml : Nat) (fn : String) : Case :=
  { cat, name, ml, outcome := .missing fn }

/-! ## Expression builders (mirroring the `.ml` builders, lines 57-70) -/

def ei (n : Int) : Expr := .int n
def erat (n d : Int) : Expr := .rat n d
def sy (s : String) : Expr := .sym s
def ap (fn : String) (args : List Expr) : Expr := .app fn args
def eadd (a b : Expr) : Expr := ap "plus" [a, b]
def eaddn (xs : List Expr) : Expr := ap "plus" xs
def emul (a b : Expr) : Expr := ap "times" [a, b]
def emuln (xs : List Expr) : Expr := ap "times" xs
def epow (a b : Expr) : Expr := ap "power" [a, b]
def ediv (a b : Expr) : Expr := ap "divide" [a, b]
def eminus (a b : Expr) : Expr := ap "minus" [a, b]
def fapp1 (fn : String) (a : Expr) : Expr := ap fn [a]
def erel (fn : String) (a b : Expr) : Expr := ap fn [a, b]

def ex : Expr := sy "x"
def ey : Expr := sy "y"
def ez : Expr := sy "z"

/-- The body of the two motivating examples: `x + i*y` (`.ml` line 79). -/
def body : Expr := eadd ex (emul (sy "i") ey)

def key (e : Expr) : String := exprKey e
def keq (a b : Expr) : Bool := key a == key b

/-- `.ml` line 86: compare `simplify actual` to `simplify expected`
    through the canonical key, so operand order does not matter. -/
def chkSimpl (cat name : String) (ml : Nat) (actual expected : Expr) : Case :=
  chkTrue cat name ml (keq (simplify actual) (simplify expected))

/-- The F* `value_to_string` (`Math.Expr.fst` line 499). -/
def valueToString : Option Value → String
  | none               => "undef"
  | some (.bool b)     => if b then "true" else "false"
  | some (.num (n, d)) => if d == 1 then toString n else toString n ++ "/" ++ toString d

/-- An environment as an association list, the way the `.ml` writes it. -/
def envOf (ps : List (String × (Int × Int))) : String → Option (Int × Int) :=
  fun s => (ps.find? (fun p => p.1 == s)).map (·.2)

def evalAt (env : List (String × (Int × Int))) (e : Expr) : Option Value :=
  eval (envOf env) e

/-! ## The serializer hooks

`MathML.Present.fst` has no Lean counterpart yet. Each hook below
reports the missing function by name; when the port lands, the body
becomes the real comparison and the expected data above it does not
move. -/

/-- Presentation MathML, exact expected document (`.ml` line 332). -/
def presCheck (cat name : String) (ml : Nat) (_e : Expr) (_expectedInner : String) : Case :=
  chkMissing cat name ml "L4Factoidal.MathML.toPresentationMathML"

/-- Presentation MathML, `contains` predicate over the rendered string. -/
def presContains (cat name : String) (ml : Nat) (_e : Expr)
    (_needle : String) (_want : Bool) : Case :=
  chkMissing cat name ml "L4Factoidal.MathML.toPresentationMathML"

/-- Presentation MathML is well-formed XML by our own parser. -/
def presWellFormed (cat name : String) (ml : Nat) (_e : Expr) (_startsWithMath : Bool) : Case :=
  chkMissing cat name ml "L4Factoidal.MathML.toPresentationMathML"

/-- Content MathML, `contains` predicate over the rendered string. -/
def contentContains (cat name : String) (ml : Nat) (_e : Expr) (_needle : String) : Case :=
  chkMissing cat name ml "L4Factoidal.MathML.toContentMathML"

/-- `key (simplify (parse (content e))) = key (simplify e)` (`.ml` 293). -/
def contentRoundTrip (cat name : String) (ml : Nat) (_e : Expr) : Case :=
  chkMissing cat name ml "L4Factoidal.MathML.toContentMathML"

/-! ## 1. The two motivating examples (`.ml` 92-124) -/

def motivating : List Case :=
  [ chkTrue "motivating-summation" "summation(x + i*y, i, 1, 4) = 4*x + 10*y" 99
      (keq (summation body "i" 1 4)
           (simplify (eadd (emul (ei 4) ex) (emul (ei 10) ey))))
  , chkTrue "motivating-product"
      "product(x + i*y, i, 0, 5) = x*(x+y)*(x+2y)*(x+3y)*(x+4y)*(x+5y)" 115
      (keq (finiteProduct body "i" 0 5)
           (simplify (emuln [ ex
                            , eadd ex ey
                            , eadd ex (emul (ei 2) ey)
                            , eadd ex (emul (ei 3) ey)
                            , eadd ex (emul (ei 4) ey)
                            , eadd ex (emul (ei 5) ey) ])))
  ]

/-! ## 2. Empty-range identities (`.ml` 126-141) -/

def emptyRange : List Case :=
  [ chkTrue "empty-range" "summation over empty range (5..1) = 0" 126
      (keq (summation body "i" 5 1) (ei 0))
  , chkTrue "empty-range" "product over empty range (5..1) = 1" 130
      (keq (finiteProduct body "i" 5 1) (ei 1))
  , chkTrue "empty-range" "summation over single point (2..2) = x + 2*y" 134
      (keq (summation body "i" 2 2) (simplify (eadd ex (emul (ei 2) ey))))
  , chkTrue "empty-range" "product over single point (3..3) = x + 3*y" 139
      (keq (finiteProduct body "i" 3 3) (simplify (eadd ex (emul (ei 3) ey))))
  ]

/-! ## 3. Coefficient-carrying like-term merge (`.ml` 149-187) -/

def coeffMerge : List Case :=
  [ chkSimpl "coeff-merge" "simplify(2*y + 3*y) = 5*y" 149
      (eadd (emul (ei 2) ey) (emul (ei 3) ey)) (emul (ei 5) ey)
  , chkSimpl "coeff-merge" "simplify(y + 2*y + 3*y + 4*y) = 10*y" 151
      (eaddn [ey, emul (ei 2) ey, emul (ei 3) ey, emul (ei 4) ey]) (emul (ei 10) ey)
  , chkSimpl "coeff-merge" "simplify(3*x + x) = 4*x" 153
      (eadd (emul (ei 3) ex) ex) (emul (ei 4) ex)
  , chkSimpl "coeff-merge" "simplify(x + 2*y + 3*y) = x + 5*y" 155
      (eaddn [ex, emul (ei 2) ey, emul (ei 3) ey]) (eadd ex (emul (ei 5) ey))
  , chkSimpl "coeff-merge" "simplify(2*x + 3*x + 4) = 5*x + 4" 157
      (eaddn [emul (ei 2) ex, emul (ei 3) ex, ei 4]) (eadd (emul (ei 5) ex) (ei 4))
  , chkSimpl "coeff-merge" "simplify((1/2)*y + (1/2)*y) = y" 160
      (eadd (emul (erat 1 2) ey) (emul (erat 1 2) ey)) ey
  , chkSimpl "coeff-merge" "simplify(2*y + (-2)*y) = 0" 163
      (eadd (emul (ei 2) ey) (emul (ei (-2)) ey)) (ei 0)
  , chkSimpl "coeff-merge" "simplify(2*x*y + 3*x*y) = 5*x*y" 166
      (eadd (emuln [ei 2, ex, ey]) (emuln [ei 3, ex, ey])) (emuln [ei 5, ex, ey])
  ]

def coeffMergeSoundness : List Case :=
  let unlike := eadd (emul (ei 2) ex) (emul (ei 3) ey)
  let env : List (String × (Int × Int)) := [("x", (5, 1)), ("y", (7, 1))]
  [ chkTrue "coeff-merge-soundness"
      "simplify(2*x + 3*y) keeps two distinct terms (no merge)" 170
      (match simplify unlike with
       | .app "plus" [_, _] => true
       | _                  => false)
  , chkTrue "coeff-merge-soundness"
      "simplify(2*x + 3*x^2) keeps distinct cores x vs x^2" 175
      (match simplify (eadd (emul (ei 2) ex) (emul (ei 3) (epow ex (ei 2)))) with
       | .app "plus" [_, _] => true
       | _                  => false)
  , chkEq "coeff-merge-soundness"
      "eval(simplify(2*x+3*y)) = eval(2*x+3*y) at x=5,y=7" 183
      (valueToString (evalAt env unlike))
      (valueToString (evalAt env (simplify unlike)))
  ]

/-! ## 4. simplify idempotence (`.ml` 192-209) -/

def idempotenceCases : List (String × Expr) :=
  [ ("2*y + 3*y",        eadd (emul (ei 2) ey) (emul (ei 3) ey))
  , ("y + 2y + 3y + 4y", eaddn [ey, emul (ei 2) ey, emul (ei 3) ey, emul (ei 4) ey])
  , ("x + 2y + 3y",      eaddn [ex, emul (ei 2) ey, emul (ei 3) ey])
  , ("2*x*y + 3*x*y",    eadd (emuln [ei 2, ex, ey]) (emuln [ei 3, ex, ey]))
  , ("2y + (-2)y",       eadd (emul (ei 2) ey) (emul (ei (-2)) ey))
  , ("summation(1..4)",  summation body "i" 1 4)
  , ("summation(0..6)",  summation body "i" 0 6)
  , ("product(0..5)",    finiteProduct body "i" 0 5)
  , ("product(1..4)",    finiteProduct body "i" 1 4)
  ]

def idempotence : List Case :=
  idempotenceCases.map (fun (nm, e) =>
    let s1 := simplify e
    chkEq "simplify-idempotence" ("idempotent: " ++ nm) 192 (key s1) (key (simplify s1)))

/-! ## 5. simplify value-preservation (`.ml` 215-232) -/

def soundnessCases : List (String × Expr) :=
  [ ("2y + 3y",          eadd (emul (ei 2) ey) (emul (ei 3) ey))
  , ("y + 2y + 3y + 4y", eaddn [ey, emul (ei 2) ey, emul (ei 3) ey, emul (ei 4) ey])
  , ("x + 2y + 3y",      eaddn [ex, emul (ei 2) ey, emul (ei 3) ey])
  , ("2*x*y + 3*x*y",    eadd (emuln [ei 2, ex, ey]) (emuln [ei 3, ex, ey]))
  , ("summation(1..4)",  summation body "i" 1 4)
  , ("product(1..4)",    finiteProduct body "i" 1 4)
  ]

def simplifySoundness : List Case :=
  let env : List (String × (Int × Int)) := [("x", (3, 1)), ("y", (5, 2))]
  soundnessCases.map (fun (nm, f) =>
    chkEq "simplify-soundness" s!"eval(simplify {nm}) = eval({nm})" 215
      (valueToString (evalAt env f)) (valueToString (evalAt env (simplify f))))

/-! ## 6. Presentation shape, parenthesization, content round-trip
    (`.ml` 249-317) -/

def presentShapes : List (String × Expr) :=
  [ ("x",             ex)
  , ("4*x + 10*y",    eadd (emul (ei 4) ex) (emul (ei 10) ey))
  , ("(x+y)*z",       emul (eadd ex ey) ez)
  , ("x^2 * y",       emul (epow ex (ei 2)) ey)
  , ("(x+y)^2",       epow (eadd ex ey) (ei 2))
  , ("1/2",           erat 1 2)
  , ("x/(x^2+1)",     ediv ex (eadd (epow ex (ei 2)) (ei 1)))
  , ("sin(x^2)",      fapp1 "sin" (epow ex (ei 2)))
  , ("product(0..5)", finiteProduct body "i" 0 5)
  ]

def presentWellFormed : List Case :=
  presentShapes.flatMap (fun (nm, e) =>
    [ presWellFormed "present-wellformed" s!"to_presentation_mathml({nm}) starts with <math" 263 e true
    , presWellFormed "present-wellformed" s!"Parser.XML accepts to_presentation_mathml({nm})" 266 e false
    ])

def presentParens : List Case :=
  [ presContains "present-parens" "(x+y)*z fences the sum" 272
      (emul (eadd ex ey) ez) "<mo>(</mo>" true
  , presContains "present-parens" "x^2 * y does NOT parenthesize the power" 276
      (emul (epow ex (ei 2)) ey) "<mo>(</mo>" false
  , presContains "present-parens" "(x+y)^2 fences the base" 280
      (epow (eadd ex ey) (ei 2)) "<mo>(</mo>" true
  , presContains "present-parens" "x + y is not parenthesized" 284
      (eadd ex ey) "<mo>(</mo>" false
  , presContains "present-parens" "(x/y)*z does not fence the fraction" 288
      (emul (ediv ex ey) ez) "<mo>(</mo>" false
  ]

def roundTripShapes : List (String × Expr) :=
  [ ("x^2 + 1",         eadd (epow ex (ei 2)) (ei 1))
  , ("2*x + 3*y",       eadd (emul (ei 2) ex) (emul (ei 3) ey))
  , ("x*(x+y)",         emul ex (eadd ex ey))
  , ("5/2",             erat 5 2)
  , ("x/(x^2+1)",       ediv ex (eadd (epow ex (ei 2)) (ei 1)))
  , ("4*x + 10*y",      eadd (emul (ei 4) ex) (emul (ei 10) ey))
  , ("summation(1..4)", summation body "i" 1 4)
  , ("product(0..5)",   finiteProduct body "i" 0 5)
  ]

def contentRoundTrips : List Case :=
  roundTripShapes.map (fun (nm, e) =>
    contentRoundTrip "content-roundtrip" ("content round-trip: " ++ nm) 308 e)

/-! ## 7. Relations, abs, factorial, exp, the diff sentinel (`.ml` 332-390) -/

def mathmlDoc (s : String) : String :=
  "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">" ++ s ++ "</math>"

def newOps : List Case :=
  [ presCheck "present-new-ops" "eq(x,y)" 337
      (erel "eq" ex ey) "<mi>x</mi><mo>=</mo><mi>y</mi>"
  , presCheck "present-new-ops" "neq(x,y)" 339
      (erel "neq" ex ey) "<mi>x</mi><mo>&#x2260;</mo><mi>y</mi>"
  , presCheck "present-new-ops" "lt(x,y)" 341
      (erel "lt" ex ey) "<mi>x</mi><mo>&lt;</mo><mi>y</mi>"
  , presCheck "present-new-ops" "gt(x,y)" 343
      (erel "gt" ex ey) "<mi>x</mi><mo>&gt;</mo><mi>y</mi>"
  , presCheck "present-new-ops" "leq(x,y)" 345
      (erel "leq" ex ey) "<mi>x</mi><mo>&#x2264;</mo><mi>y</mi>"
  , presCheck "present-new-ops" "geq(x,y)" 347
      (erel "geq" ex ey) "<mi>x</mi><mo>&#x2265;</mo><mi>y</mi>"
  , presCheck "present-new-ops" "eq(x, plus(y,1))" 350
      (erel "eq" ex (eadd ey (ei 1)))
      "<mi>x</mi><mo>=</mo><mi>y</mi><mo>+</mo><mn>1</mn>"
  , presCheck "present-new-ops" "geq(eq(x,y), z) fences the nested relation" 353
      (erel "geq" (erel "eq" ex ey) ez)
      "<mrow><mo>(</mo><mi>x</mi><mo>=</mo><mi>y</mi><mo>)</mo></mrow><mo>&#x2265;</mo><mi>z</mi>"
  , presCheck "present-new-ops" "lt(plus(x,y), z) does not fence the sum" 357
      (erel "lt" (eadd ex ey) ez)
      "<mi>x</mi><mo>+</mo><mi>y</mi><mo>&lt;</mo><mi>z</mi>"
  , presCheck "present-new-ops" "abs(x)" 361
      (fapp1 "abs" ex) "<mrow><mo>|</mo><mi>x</mi><mo>|</mo></mrow>"
  , presCheck "present-new-ops" "abs(plus(x,y)) does not fence the sum inside the bars" 363
      (fapp1 "abs" (eadd ex ey))
      "<mrow><mo>|</mo><mi>x</mi><mo>+</mo><mi>y</mi><mo>|</mo></mrow>"
  , presCheck "present-new-ops" "abs(-3) carries the sign inside the bars unfenced" 365
      (fapp1 "abs" (ei (-3))) "<mrow><mo>|</mo><mn>-3</mn><mo>|</mo></mrow>"
  , presCheck "present-new-ops" "factorial(n)" 369
      (fapp1 "factorial" (sy "n")) "<mi>n</mi><mo>!</mo>"
  , presCheck "present-new-ops" "factorial(plus(x,y)) fences the sum" 371
      (fapp1 "factorial" (eadd ex ey))
      "<mrow><mo>(</mo><mi>x</mi><mo>+</mo><mi>y</mi><mo>)</mo></mrow><mo>!</mo>"
  , presCheck "present-new-ops"
      "factorial(abs(x)) does not re-fence an already-atomic operand" 373
      (fapp1 "factorial" (fapp1 "abs" ex))
      "<mrow><mo>|</mo><mi>x</mi><mo>|</mo></mrow><mo>!</mo>"
  , presCheck "present-new-ops" "exp(x)" 377
      (fapp1 "exp" ex) "<msup><mi>e</mi><mrow><mi>x</mi></mrow></msup>"
  , presCheck "present-new-ops" "exp(plus(x,y)) puts the sum in the exponent unfenced" 379
      (fapp1 "exp" (eadd ex ey))
      "<msup><mi>e</mi><mrow><mi>x</mi><mo>+</mo><mi>y</mi></mrow></msup>"
  , presCheck "present-new-ops" "diff_unsupported(x) direct construction" 384
      (ap "diff_unsupported" [ex]) "<merror><mtext>unsupported derivative</mtext></merror>"
  , presCheck "present-new-ops"
      "diff x (coth x) has no rule -> diff_unsupported -> merror" 386
      (diff "x" (fapp1 "coth" ex))
      "<merror><mtext>unsupported derivative</mtext></merror>"
  , presCheck "present-new-ops"
      "plus(x, diff_unsupported(y)) embeds the error box atomically" 388
      (eadd ex (ap "diff_unsupported" [ey]))
      "<mi>x</mi><mo>+</mo><merror><mtext>unsupported derivative</mtext></merror>"
  ]

/-! ## 7b. Well-formedness for the new cases (`.ml` 398-416) -/

def newShapes : List (String × Expr) :=
  [ ("eq(x,y)",              erel "eq" ex ey)
  , ("geq(eq(x,y), z)",      erel "geq" (erel "eq" ex ey) ez)
  , ("abs(minus(x,y))",      fapp1 "abs" (eminus ex ey))
  , ("factorial(plus(x,1))", fapp1 "factorial" (eadd ex (ei 1)))
  , ("exp(power(x,2))",      fapp1 "exp" (epow ex (ei 2)))
  , ("diff_unsupported(x)",  ap "diff_unsupported" [ex])
  , ("eq(x, abs(y))",        erel "eq" ex (fapp1 "abs" ey))
  ]

def newOpsWellFormed : List Case :=
  newShapes.flatMap (fun (nm, e) =>
    [ presWellFormed "present-new-ops-wellformed"
        s!"to_presentation_mathml({nm}) starts with <math" 410 e true
    , presWellFormed "present-new-ops-wellformed"
        s!"Parser.XML accepts to_presentation_mathml({nm})" 413 e false
    ])

/-! ## 7c. Content round-trip and element names for the new ops
    (`.ml` 424-450) -/

def newOpsRoundTripShapes : List (String × Expr) :=
  [ ("eq(x,y)",      erel "eq" ex ey)
  , ("neq(x,y)",     erel "neq" ex ey)
  , ("lt(x,y)",      erel "lt" ex ey)
  , ("gt(x,y)",      erel "gt" ex ey)
  , ("leq(x,y)",     erel "leq" ex ey)
  , ("geq(x,y)",     erel "geq" ex ey)
  , ("abs(x)",       fapp1 "abs" ex)
  , ("factorial(n)", fapp1 "factorial" (sy "n"))
  , ("exp(x)",       fapp1 "exp" ex)
  ]

def newOpsRoundTrips : List Case :=
  newOpsRoundTripShapes.map (fun (nm, e) =>
    contentRoundTrip "content-roundtrip" ("content round-trip: " ++ nm) 426 e)

def contentNewOps : List Case :=
  [ contentContains "content-new-ops"
      "to_content_mathml(exp(x)) uses <exp/> not <csymbol>" 440 (fapp1 "exp" ex) "<exp/>"
  , contentContains "content-new-ops"
      "to_content_mathml(abs(x)) uses <abs/>" 443 (fapp1 "abs" ex) "<abs/>"
  , contentContains "content-new-ops"
      "to_content_mathml(factorial(n)) uses <factorial/>" 446
      (fapp1 "factorial" (sy "n")) "<factorial/>"
  , contentContains "content-new-ops"
      "to_content_mathml(eq(x,y)) uses <eq/>" 449 (erel "eq" ex ey) "<eq/>"
  ]

/-! ## The whole battery -/

def allCases : List Case :=
  motivating ++ emptyRange ++ coeffMerge ++ coeffMergeSoundness ++
  idempotence ++ simplifySoundness ++ presentWellFormed ++ presentParens ++
  contentRoundTrips ++ newOps ++ newOpsWellFormed ++ newOpsRoundTrips ++
  contentNewOps

def caseCount : Nat := allCases.length
def passCount : Nat := (allCases.filter Case.ok).length
def failCount : Nat := caseCount - passCount

end L4Factoidal.Math.Toan
