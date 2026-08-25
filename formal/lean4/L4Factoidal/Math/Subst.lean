/-
L4Factoidal.Math.Subst — symbolic substitution over a Content MathML
expression.

Port of `formal/fstar/Math.Subst.fst`. The building block the rest of
the CAS layer (`Diff`, `Simplify`, `Series`) rests on: replace every
occurrence of a symbol by an expression. Structural, total, no fuel —
the recursion is on the strict subterm ordering.
-/
import L4Factoidal.MathML.Core

namespace L4Factoidal.Math

open L4Factoidal.MathML

mutual

/-- `subst x v e` is `e` with every `sym x` replaced by `v`. -/
partial def subst (x : String) (v : Expr) : Expr → Expr
  | .int n     => .int n
  | .rat n d   => .rat n d
  | .bool b    => .bool b
  | .sym name  => if name == x then v else .sym name
  | .app fn as => .app fn (substList x v as)

partial def substList (x : String) (v : Expr) : List Expr → List Expr
  | []      => []
  | h :: t  => subst x v h :: substList x v t

end

end L4Factoidal.Math
