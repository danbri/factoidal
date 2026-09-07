/-
Wasm.Ops.Toan — the "Think of a Number" computer-algebra operations.

Envelopes match `bin/npm-entry/entry_jsoo.ml` op for op (registered
there at line 2548), so the same JavaScript argument drives either
engine:

  toanSummation(bodyJson, idx, lo, hi) -> {"ok":true,"mathml":"…"}
  toanProduct(bodyJson, idx, lo, hi)   -> {"ok":true,"mathml":"…"}
  toanSimplify(exprJson)               -> {"ok":true,"mathml":"…"}
  toanDiff(exprJson, var)              -> {"ok":true,"mathml":"…"}
  toanSubst(exprJson, var, valueJson)  -> {"ok":true,"mathml":"…"}

and `{"ok":false,"error":"…"}` on a refusal.

Five operations, not six or seven. The brief that asked for this work
named `toanExprToMathML` and `toanEval`; the F* entry registers
neither, and inventing an op here would put the two engines out of
step, which is the one thing this table exists to prevent.

The `mathml` member carries CONTENT MathML — `to_content_mathml` in
the F* entry's `toan_mathml_result` (line 2159), not the Presentation
form. Both start with `<math`, so a test that only looks for that
would score a Presentation answer as correct.

The argument JSON shape is read by `L4Factoidal.MathML.exprOfJson`,
which follows `expr_of_json` (line 2125) member for member.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.MathML.FromJson
import L4Factoidal.MathML.Present
import L4Factoidal.Math.Series
import L4Factoidal.Math.Diff

namespace L4Wasm.Ops

open L4Factoidal.MathML
open L4Factoidal.Math
open L4Factoidal.JSON

/-- The shared result: the expression as Content MathML. -/
private def mathmlResult (e : Expr) : String :=
  okWith [("mathml", .string (toContentMathML e))]

/-- Read one expression argument, or name which argument was wrong.
    `who` is the op name, matching the F* entry's `failwith` text. -/
private def readExpr (who : String) (src : String) : Except String Expr :=
  match exprOfJsonString src with
  | some e => .ok e
  | none   =>
      .error (who ++ ": expr object needs one of int / rat / bool / sym / app")

/-- A decimal bound. The F* entry passes these through `Z.of_string`,
    which REFUSES a non-numeral rather than defaulting to zero. -/
private def readInt (who what : String) (s : String) : Except String Int :=
  match s.toInt? with
  | some n => .ok n
  | none   => .error (who ++ ": " ++ what ++ " must be a decimal integer")

def toanSummation (bodyJson idx lo hi : String) : String :=
  match readExpr "toanSummation" bodyJson with
  | .error e => errJson e
  | .ok body =>
    match readInt "toanSummation" "lo" lo, readInt "toanSummation" "hi" hi with
    | .ok l, .ok h => mathmlResult (summation body idx l h)
    | .error e, _  => errJson e
    | _, .error e  => errJson e

def toanProduct (bodyJson idx lo hi : String) : String :=
  match readExpr "toanProduct" bodyJson with
  | .error e => errJson e
  | .ok body =>
    match readInt "toanProduct" "lo" lo, readInt "toanProduct" "hi" hi with
    | .ok l, .ok h => mathmlResult (finiteProduct body idx l h)
    | .error e, _  => errJson e
    | _, .error e  => errJson e

def toanSimplify (exprJson : String) : String :=
  match readExpr "toanSimplify" exprJson with
  | .error e => errJson e
  | .ok x    => mathmlResult (simplify x)

def toanDiff (exprJson var : String) : String :=
  match readExpr "toanDiff" exprJson with
  | .error e => errJson e
  | .ok x    => mathmlResult (diff var x)

def toanSubst (exprJson var valueJson : String) : String :=
  match readExpr "toanSubst" exprJson with
  | .error e => errJson e
  | .ok x =>
    match readExpr "toanSubst (value)" valueJson with
    | .error e  => errJson e
    | .ok value => mathmlResult (subst var value x)

end L4Wasm.Ops
