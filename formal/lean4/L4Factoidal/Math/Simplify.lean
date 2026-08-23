/-
L4Factoidal.Math.Simplify — a canonical normaliser for Content MathML
expressions.

Port of `formal/fstar/Math.Simplify.fst`. Bottom-up: children are
normalised first, then a shallow combining pass normalises the node.

## The sound subset, and what is deliberately left out

Normalised:

  * CONSTANT FOLDING — an application whose arguments are all numeric
    literals is folded through `MathML.eval`, so `2+3` is `5` and
    `2^3` is `8`. A fold that would be undefined (division by zero,
    an inexact root) is left SYMBOLIC, never faked.
  * `plus` — flatten nested sums, drop `+0`, sum the literals into one
    constant, and merge LIKE TERMS by summing their rational
    coefficients over a canonical core key, so `x + x` is `2*x` and
    `y + 2*y + 3*y + 4*y` is `10*y`.
  * `times` — flatten, annihilate on a literal `0`, drop `*1`,
    multiply the literals into one constant, and combine equal bases
    with integer exponents, so `x*x` is `x^2`.
  * the always-sound identities `a^1 = a`, `a/1 = a`, `a-0 = a`.

NOT normalised, each sound to omit and unsound to add:

  * distributing a product over a sum — that is a separate `expand`,
    and no factoring either;
  * `a^0 = 1` for a SYMBOLIC base, which is wrong at `a = 0`, or any
    other rule that changes the domain of definition;
  * trigonometric and logarithmic identities.

## Commutative operands are ordered by a canonical key

`plus` and `times` are commutative, so their operands must be put in
a fixed order for the result to be a normal form at all. The key is a
string serialisation of the subtree, and the sort is by that key —
which makes `simplify` idempotent, the property the whole notion of a
normal form rests on.
-/
import L4Factoidal.Math.Subst

namespace L4Factoidal.Math

open L4Factoidal.MathML

/-! ## The canonical ordering key -/

mutual

partial def exprKey : Expr → String
  | .int n     => "0i:" ++ toString n
  | .rat n d   => "1r:" ++ toString n ++ "/" ++ toString d
  | .bool b    => "2b:" ++ (if b then "t" else "f")
  | .sym s     => "3s:" ++ s
  | .app fn as => "4a:" ++ fn ++ "(" ++ exprKeyList as ++ ")"

partial def exprKeyList : List Expr → String
  | []     => ""
  | h :: t => exprKey h ++ "," ++ exprKeyList t

end

def exprLe (a b : Expr) : Bool := exprKey a ≤ exprKey b

/-- Insertion sort by the canonical key. -/
def insertSorted (x : Expr) : List Expr → List Expr
  | []     => [x]
  | h :: t => if exprLe x h then x :: h :: t else h :: insertSorted x t

def sortExprs : List Expr → List Expr
  | []     => []
  | h :: t => insertSorted h (sortExprs t)

/-! ## Numeric literals

A value is `Option (Int × Int)`: `none` is UNDEFINED, and an
undefined constant is left symbolic rather than folded. -/

abbrev MVal := Option (Int × Int)

def isNumLit : Expr → Bool
  | .int _ | .rat _ _ => true
  | _                 => false

def litValue : Expr → MVal
  | .int n   => some (n, 1)
  | .rat n d => if d == 0 then none else some (normRat n d)
  | _        => none

def isZeroLit : Expr → Bool
  | .int n   => n == 0
  | .rat n _ => n == 0
  | _        => false

def mAdd (a b : MVal) : MVal := do let x ← a; let y ← b; some (addRat x y)
def mMul (a b : MVal) : MVal := do let x ← a; let y ← b; some (mulRat x y)

def valueToLit (v : Int × Int) : Expr :=
  if v.2 == 1 then .int v.1 else .rat v.1 v.2

/-! ## Flattening an associative operator

The children are already normalised, hence internally flat, so one
splice is enough. -/

def flattenOp (fn : String) : List Expr → List Expr
  | []     => []
  | h :: t =>
      let rest := flattenOp fn t
      match h with
      | .app fn2 inner => if fn2 == fn then inner ++ rest else h :: rest
      | _              => h :: rest

/-! ## Base and exponent -/

def baseExp : Expr → Expr × Int
  | .app "power" [b, .int n] => (b, n)
  | e                        => (e, 1)

def bumpExp (b : Expr) (n : Int) : List (Expr × Int) → List (Expr × Int)
  | []             => [(b, n)]
  | (hb, hn) :: r  =>
      if exprKey hb == exprKey b then (hb, hn + n) :: r else (hb, hn) :: bumpExp b n r

def combinePowers : List (Expr × Int) → List (Expr × Int) → List (Expr × Int)
  | [],            acc => acc
  | (b, n) :: t,   acc => combinePowers t (bumpExp b n acc)

/-! ## Splitting an argument list into a constant and the rest -/

def splitSum : List Expr → MVal → List Expr → MVal × List Expr
  | [],     c, ts => (c, ts)
  | h :: t, c, ts =>
      if isNumLit h then splitSum t (mAdd c (litValue h)) ts
      else splitSum t c (ts ++ [h])

def splitProd : List Expr → MVal → List Expr → MVal × List Expr
  | [],     c, fs => (c, fs)
  | h :: t, c, fs =>
      if isNumLit h then splitProd t (mMul c (litValue h)) fs
      else splitProd t c (fs ++ [h])

/-! ## Like-term merging for a sum

Each non-numeric summand splits into a rational COEFFICIENT and a
CORE — its non-numeric factors, already sorted because the child was
normalised. Summands whose cores share a key have their coefficients
summed. Only genuinely like terms merge: distinct cores have distinct
keys, so unlike terms are never combined. -/

def splitCoeff : Expr → MVal × List Expr
  | .app "times" fs => splitProd fs (some (1, 1)) []
  | e               => (some (1, 1), [e])

/-- The key of a core factor list. The EMPTY core denotes a pure
    number, which is folded into the additive constant instead of
    forming a group. -/
def coreKey : List Expr → String
  | []  => ""
  | [f] => exprKey f
  | cf  => exprKey (.app "times" cf)

def bumpCore (k : String) (cf : List Expr) (c : MVal)
    : List (String × List Expr × MVal) → List (String × List Expr × MVal)
  | []                 => [(k, cf, c)]
  | (hk, hcf, hc) :: r =>
      if hk == k then (hk, hcf, mAdd hc c) :: r else (hk, hcf, hc) :: bumpCore k cf c r

def collectCoeffs : List Expr → MVal → List (String × List Expr × MVal)
    → MVal × List (String × List Expr × MVal)
  | [],     c, acc => (c, acc)
  | t :: r, c, acc =>
      let (co, cf) := splitCoeff t
      match cf with
      | [] => collectCoeffs r (mAdd c co) acc
      | _  => collectCoeffs r c (bumpCore (coreKey cf) cf co acc)

/-- Rebuild one summand. Coefficient 0 ANNIHILATES; coefficient 1
    drops to the bare core; otherwise a flat `times` node with the
    coefficient in front, so that re-normalising is stable. -/
def mergedTerm (cf : List Expr) (c : MVal) : List Expr :=
  match c with
  | some (0, 1) => []
  | some (1, 1) => [ match cf with | [f] => f | _ => .app "times" cf ]
  | some v      => [ .app "times" (valueToLit v :: cf) ]
  | none        => [ match cf with | [f] => f | _ => .app "times" cf ]

def emitMerged : List (String × List Expr × MVal) → List Expr
  | []                => []
  | (_, cf, c) :: r   => mergedTerm cf c ++ emitMerged r

def emitFactors : List (Expr × Int) → List Expr
  | []            => []
  | (b, n) :: r =>
      if n == 0 then emitFactors r
      else (if n == 1 then b else .app "power" [b, .int n]) :: emitFactors r

/-! ## The shallow normalisers -/

def simplifyPlus (args : List Expr) : Expr :=
  let flat := flattenOp "plus" args
  let (c0, terms) := splitSum flat (some (0, 1)) []
  let (c, groups) := collectCoeffs terms c0 []
  let summands := sortExprs (emitMerged groups)
  let constLit := match c with
    | some (0, 1) => []
    | some v      => [valueToLit v]
    | none        => []
  match summands ++ constLit with
  | []  => .int 0
  | [x] => x
  | all => .app "plus" all

def simplifyTimes (args : List Expr) : Expr :=
  let flat := flattenOp "times" args
  if flat.any isZeroLit then .int 0
  else
    let (c, factors) := splitProd flat (some (1, 1)) []
    let pairs := combinePowers (factors.map baseExp) []
    let facs := sortExprs (emitFactors pairs)
    let constLit := match c with
      | some (1, 1) => []
      | some v      => [valueToLit v]
      | none        => []
    match constLit ++ facs with
    | []  => .int 1
    | [x] => x
    | all => .app "times" all

/-- A node that is neither `plus` nor `times`, whose arguments are
    already normalised: fold it when every argument is a literal AND
    the fold is defined, then try the cheap always-sound identities,
    then rebuild. -/
def simplifyOther (fn : String) (args : List Expr) : Expr :=
  if args.all isNumLit then
    match eval (fun _ => none) (.app fn args) with
    | some (.num v)  => valueToLit v
    | some (.bool b) => .bool b
    | none           => .app fn args      -- undefined: stays symbolic
  else
    match fn, args with
    | "power",  [a, .int 1] => a
    | "divide", [a, .int 1] => a
    | "minus",  [a, .int 0] => a
    | _, _                  => .app fn args

def simplifyApp (fn : String) (args : List Expr) : Expr :=
  if fn == "plus" then simplifyPlus args
  else if fn == "times" then simplifyTimes args
  else simplifyOther fn args

mutual

/-- Normalise an expression: children first, then the node. -/
partial def simplify : Expr → Expr
  | .int n     => .int n
  | .rat n d   => .rat n d
  | .bool b    => .bool b
  | .sym s     => .sym s
  | .app fn as => simplifyApp fn (simplifyList as)

partial def simplifyList : List Expr → List Expr
  | []     => []
  | h :: t => simplify h :: simplifyList t

end

end L4Factoidal.Math
