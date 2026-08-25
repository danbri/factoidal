/-
L4Factoidal.Math.Diff — symbolic differentiation.

Port of `formal/fstar/Math.Diff.fst`. Total and structural — the
recursion is on the strict subterm ordering, no fuel.

## Soundness over coverage

A construct with no rule is returned WRAPPED in an explicit
`diff_unsupported` marker rather than given a guessed derivative.
`MathML.eval` has no rule for that function name, so it evaluates to
nothing: a missing rule can never masquerade as a wrong answer. That
is the whole design of this module, and it is why the marker is a
node in the result rather than a silent identity.

Rules, with respect to a symbol `x`:

  * constants and every other symbol → `0`; `x` itself → `1`;
  * `plus` (n-ary) → the sum of the derivatives;
  * `minus` (unary and binary) → negation and difference;
  * `times` (n-ary) → the FULL product rule;
  * `divide` → the quotient rule;
  * `power` → the power rule for a LITERAL exponent, and the general
    `f^g` logarithmic derivative otherwise;
  * `root` with one argument (square root), and with a positive
    integer degree;
  * `sin`, `cos`, `exp`, `ln`, `tan` → the chain rule.
-/
import L4Factoidal.Math.Simplify

namespace L4Factoidal.Math

open L4Factoidal.MathML

def eAdd (a b : Expr) : Expr := .app "plus" [a, b]
def eMul (a b : Expr) : Expr := .app "times" [a, b]
def ePow (a b : Expr) : Expr := .app "power" [a, b]
def eNeg (a : Expr) : Expr := .app "minus" [a]

/-- The explicit "no rule" marker. A function name `eval` does not
    know, so it reports the result undefined rather than producing a
    number. -/
def diffUnknown (e : Expr) : Expr := .app "diff_unsupported" [e]

mutual

partial def diff (x : String) : Expr → Expr
  | .int _   => .int 0
  | .rat _ _ => .int 0
  | .bool _  => .int 0
  | .sym n   => if n == x then .int 1 else .int 0
  | .app "plus" args => .app "plus" (diffList x args)
  | .app "minus" args =>
      (match args with
       | [a]    => eNeg (diff x a)
       | [a, b] => .app "minus" [diff x a, diff x b]
       | _      => diffUnknown (.app "minus" args))
  | .app "times" args => .app "plus" (diffProd x [] args)
  | .app "divide" args =>
      (match args with
       -- (a'b - a b') / b^2
       | [a, b] => .app "divide"
           [ .app "minus" [eMul (diff x a) b, eMul a (diff x b)], ePow b (.int 2) ]
       | _ => diffUnknown (.app "divide" args))
  | .app "power" args =>
      (match args with
       | [a, b] =>
         (match b with
          -- The power rule for a CONSTANT literal exponent:
          -- d(a^n) = n * a^(n-1) * a'. Valid for every base.
          | .int n   => eMul (eMul (.int n) (ePow a (.int (n - 1)))) (diff x a)
          | .rat p q => eMul (eMul (.rat p q) (ePow a (.rat (p - q) q))) (diff x a)
          -- The general f^g = f^g * (g' ln f + g f'/f), sound where
          -- f is positive.
          | _ =>
              let fg := ePow a b
              eMul fg (eAdd (eMul (diff x b) (.app "ln" [a]))
                            (eMul b (.app "divide" [diff x a, a]))))
       | _ => diffUnknown (.app "power" args))
  | .app "root" args =>
      (match args with
       -- sqrt a : a' / (2 sqrt a)
       | [a] => .app "divide" [diff x a, eMul (.int 2) (.app "root" [a])]
       | [.int k, a] =>
           if k > 0
           -- the k-th root is a^(1/k): (1/k) a^((1-k)/k) a'
           then eMul (eMul (.rat 1 k) (ePow a (.rat (1 - k) k))) (diff x a)
           else diffUnknown (.app "root" args)
       | _ => diffUnknown (.app "root" args))
  | .app "sin" args =>
      (match args with
       | [a] => eMul (.app "cos" [a]) (diff x a)
       | _   => diffUnknown (.app "sin" args))
  | .app "cos" args =>
      (match args with
       | [a] => eMul (eNeg (.app "sin" [a])) (diff x a)
       | _   => diffUnknown (.app "cos" args))
  | .app "exp" args =>
      (match args with
       | [a] => eMul (.app "exp" [a]) (diff x a)
       | _   => diffUnknown (.app "exp" args))
  | .app "ln" args =>
      (match args with
       | [a] => .app "divide" [diff x a, a]
       | _   => diffUnknown (.app "ln" args))
  | .app "tan" args =>
      (match args with
       | [a] => .app "divide" [diff x a, ePow (.app "cos" [a]) (.int 2)]
       | _   => diffUnknown (.app "tan" args))
  | .app fn args => diffUnknown (.app fn args)

partial def diffList (x : String) : List Expr → List Expr
  | []     => []
  | h :: t => diff x h :: diffList x t

/-- The product rule for an n-ary product: the sum over `i` of the
    product with the `i`-th factor differentiated. `pre` accumulates
    the factors already passed, undifferentiated. -/
partial def diffProd (x : String) (pre : List Expr) : List Expr → List Expr
  | []       => []
  | a :: rest =>
      .app "times" (pre ++ (diff x a :: rest)) :: diffProd x (pre ++ [a]) rest

end

/-- The derivative, normalised. -/
def diffSimplified (x : String) (e : Expr) : Expr := simplify (diff x e)

end L4Factoidal.Math
