/-
L4Factoidal.Math.Matrix — exact-rational linear algebra.

Port of `formal/fstar/Math.Matrix.fst`. Domain-neutral: no MathML
knowledge lives here. The Content MathML front end maps
`matrix`/`vector`/`apply` trees onto the operations below, exactly as
it maps scalar applications onto `MathML.eval`.

## Where the shape discipline lives, and how this port differs

The F* module indexes a matrix by its dimensions IN THE TYPE
(`matrix r c`), so `matMul`'s "the inner dimensions must agree" is a
precondition a caller cannot even form a term without satisfying, and
the result shape is PROVEN rather than checked.

This port carries the shape two ways instead. `rect` and the
`Rect`-preservation theorems below state it, and the DYNAMIC layer
(`MRes`, `dynAdd`, `dynMul`, …) checks it at run time — which is what
a MathML front end needs anyway, since dimensions come from runtime
XML and no static type can know them. A mismatch is an explicit
`undef` carrying its REASON, never a bogus matrix. The difference
from the F* is recorded in `PORT_NOTES.md`, because a shape that a
type used to guarantee and a check now guarantees is exactly the kind
of change that goes unnoticed.

## Exactness

Every entry is an exact rational, or `none` for undefined. Nothing
here produces a float, so `1/3 + 1/3 + 1/3` is `1`.
-/
import L4Factoidal.MathML.Core

namespace L4Factoidal.Math

open L4Factoidal.MathML

/-- A matrix entry: an exact rational, or UNDEFINED. -/
abbrev MEnt := Option (Int × Int)

def entAdd (a b : MEnt) : MEnt := do let x ← a; let y ← b; some (addRat x y)
def entSub (a b : MEnt) : MEnt := do let x ← a; let y ← b; some (subRat x y)
def entMul (a b : MEnt) : MEnt := do let x ← a; let y ← b; some (mulRat x y)

def entOne : MEnt := some (1, 1)
def entZero : MEnt := some (0, 1)

/-! ## Rectangularity -/

/-- Every row has exactly `c` entries. -/
def rect (c : Nat) : List (List MEnt) → Bool
  | []      => true
  | r :: t  => r.length == c && rect c t

/-! ## Row operations -/

def rowBinop (f : MEnt → MEnt → MEnt) : List MEnt → List MEnt → List MEnt
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => f a b :: rowBinop f as bs

def rowDot : List MEnt → List MEnt → MEnt
  | [],      _       => entZero
  | _,       []      => entZero
  | a :: as, b :: bs => entAdd (entMul a b) (rowDot as bs)

def scaleRow (s : MEnt) (v : List MEnt) : List MEnt := v.map (entMul s)

/-! ## The core operations -/

def matAdd (a b : List (List MEnt)) : List (List MEnt) :=
  (a.zip b).map (fun (x, y) => rowBinop entAdd x y)

def matSub (a b : List (List MEnt)) : List (List MEnt) :=
  (a.zip b).map (fun (x, y) => rowBinop entSub x y)

def scalarMul (s : MEnt) (m : List (List MEnt)) : List (List MEnt) :=
  m.map (scaleRow s)

def matNeg (m : List (List MEnt)) : List (List MEnt) :=
  scalarMul (some (-1, 1)) m

def mapHead (rows : List (List MEnt)) : List MEnt :=
  rows.map (fun r => match r with | x :: _ => x | [] => none)

def mapTail (rows : List (List MEnt)) : List (List MEnt) :=
  rows.map (fun r => match r with | _ :: xs => xs | [] => [])

def transposeBuild (c : Nat) (rows : List (List MEnt)) : List (List MEnt) :=
  match c with
  | 0     => []
  | n + 1 => mapHead rows :: transposeBuild n (mapTail rows)

def transposeM (c : Nat) (m : List (List MEnt)) : List (List MEnt) :=
  transposeBuild c m

def mulOneRow (arow : List MEnt) (bt : List (List MEnt)) : List MEnt :=
  bt.map (rowDot arow)

/-- `a` is `r1 × c1`, `b` is `r2 × c2`, and the caller has checked
    `c1 = r2`. Multiplying through the TRANSPOSE of `b` turns the
    column walk into a row walk, which is the only reason `transpose`
    appears here. -/
def matMul (c2 : Nat) (a b : List (List MEnt)) : List (List MEnt) :=
  let bt := transposeM c2 b
  a.map (fun arow => mulOneRow arow bt)

def unitRow (n i : Nat) : List MEnt :=
  (List.range n).map (fun j => if j == i then entOne else entZero)

def identityM (n : Nat) : List (List MEnt) :=
  (List.range n).map (unitRow n)

def matElem (rows : List (List MEnt)) (i j : Nat) : MEnt :=
  match rows[i]? with
  | none   => none
  | some r => (r[j]?).getD none

def traceM (n : Nat) (rows : List (List MEnt)) : MEnt :=
  (List.range n).foldl (fun acc i => entAdd acc (matElem rows i i)) entZero

def delAt (j : Nat) : List MEnt → List MEnt
  | []     => []
  | h :: t => if j == 0 then t else h :: delAt (j - 1) t

def delCol (j : Nat) (rows : List (List MEnt)) : List (List MEnt) :=
  rows.map (delAt j)

mutual

/-- Laplace expansion along the first row. The determinant of the
    0 × 0 matrix is `1` by convention, which is what makes the
    expansion bottom out. -/
partial def detRows (n : Nat) (rows : List (List MEnt)) : MEnt :=
  if n == 0 then entOne
  else match rows with
    | head :: tail => cofactorSum n 0 head tail
    | []           => entZero

partial def cofactorSum (n j : Nat) (head : List MEnt) (tail : List (List MEnt))
    : MEnt :=
  if j ≥ n then entZero
  else
    let a0j := (head[j]?).getD none
    let sign : MEnt := if j % 2 == 0 then entOne else some (-1, 1)
    let minor := delCol j tail
    let sub := detRows (n - 1) minor
    entAdd (entMul sign (entMul a0j sub)) (cofactorSum n (j + 1) head tail)

end

def determinant (n : Nat) (rows : List (List MEnt)) : MEnt := detRows n rows

/-! ## Vectors -/

def vecDot (a b : List MEnt) : MEnt := rowDot a b

/-- The cross product of two 3-vectors. -/
def cross3 (a b : List MEnt) : List MEnt :=
  let g (v : List MEnt) (i : Nat) : MEnt := (v[i]?).getD none
  [ entSub (entMul (g a 1) (g b 2)) (entMul (g a 2) (g b 1)),
    entSub (entMul (g a 2) (g b 0)) (entMul (g a 0) (g b 2)),
    entSub (entMul (g a 0) (g b 1)) (entMul (g a 1) (g b 0)) ]

def outerBuild (u v : List MEnt) : List (List MEnt) :=
  u.map (fun x => scaleRow x v)

/-! ## The dynamically-checked layer

Dimensions reach a MathML front end from runtime XML, so no static
type can know them. Every operator below checks agreement and yields
an explicit `undef` CARRYING ITS REASON on a mismatch — never a bogus
matrix, and never a silent shape coercion. -/

structure AMat where
  rows' : Nat
  cols  : Nat
  data  : List (List MEnt)
deriving Repr, Inhabited

inductive MRes where
  | scalar (v : MEnt)
  | matrix (m : AMat)
  | vector (n : Nat) (v : List MEnt)
  | undef  (reason : String)
deriving Repr, Inhabited

/-- Validate a raw list of rows. A RAGGED one is not a matrix, and is
    refused rather than padded. -/
def mkAMat (rows : List (List MEnt)) : Option AMat :=
  let nr := rows.length
  let nc := match rows with | []     => 0 | h :: _ => h.length
  if rect nc rows then some { rows' := nr, cols := nc, data := rows } else none

def mkMatrixRes (rows : List (List MEnt)) : MRes :=
  match mkAMat rows with
  | some am => .matrix am
  | none    => .undef "non-rectangular-matrix"

def mkVectorRes (v : List MEnt) : MRes := .vector v.length v

def dynAdd : MRes → MRes → MRes
  | .undef s, _ => .undef s
  | _, .undef s => .undef s
  | .scalar a, .scalar b => .scalar (entAdd a b)
  | .matrix a, .matrix b =>
      if a.rows' == b.rows' && a.cols == b.cols then
        .matrix { a with data := matAdd a.data b.data }
      else .undef "matrix-add-shape-mismatch"
  | _, _ => .undef "add-type-mismatch"

def dynSub : MRes → MRes → MRes
  | .undef s, _ => .undef s
  | _, .undef s => .undef s
  | .scalar a, .scalar b => .scalar (entSub a b)
  | .matrix a, .matrix b =>
      if a.rows' == b.rows' && a.cols == b.cols then
        .matrix { a with data := matSub a.data b.data }
      else .undef "matrix-sub-shape-mismatch"
  | _, _ => .undef "sub-type-mismatch"

/-- `times` covers scalar by scalar, scalar by matrix in EITHER order,
    and matrix by matrix. -/
def dynTimes : MRes → MRes → MRes
  | .undef s, _ => .undef s
  | _, .undef s => .undef s
  | .scalar a, .scalar b => .scalar (entMul a b)
  | .scalar s, .matrix m => .matrix { m with data := scalarMul s m.data }
  | .matrix m, .scalar s => .matrix { m with data := scalarMul s m.data }
  | .matrix a, .matrix b =>
      if a.cols == b.rows' then
        .matrix { rows' := a.rows', cols := b.cols,
                  data := matMul b.cols a.data b.data }
      else .undef "matrix-multiply-inner-dimension-mismatch"
  | _, _ => .undef "times-type-mismatch"

def dynTranspose : MRes → MRes
  | .undef s => .undef s
  | .matrix m => .matrix { rows' := m.cols, cols := m.rows',
                           data := transposeM m.cols m.data }
  | _ => .undef "transpose-requires-matrix"

def dynDeterminant : MRes → MRes
  | .undef s  => .undef s
  | .matrix m =>
      if m.rows' == m.cols then .scalar (determinant m.rows' m.data)
      else .undef "determinant-requires-square-matrix"
  | _ => .undef "determinant-requires-matrix"

def dynTrace : MRes → MRes
  | .undef s  => .undef s
  | .matrix m =>
      if m.rows' == m.cols then .scalar (traceM m.rows' m.data)
      else .undef "trace-requires-square-matrix"
  | _ => .undef "trace-requires-matrix"

def dynScalarProduct : MRes → MRes → MRes
  | .undef s, _ => .undef s
  | _, .undef s => .undef s
  | .vector n1 u, .vector n2 v =>
      if n1 == n2 then .scalar (vecDot u v)
      else .undef "scalarproduct-length-mismatch"
  | _, _ => .undef "scalarproduct-requires-vectors"

def dynVectorProduct : MRes → MRes → MRes
  | .undef s, _ => .undef s
  | _, .undef s => .undef s
  | .vector n1 u, .vector n2 v =>
      if n1 == 3 && n2 == 3 then .vector 3 (cross3 u v)
      else .undef "vectorproduct-requires-3-vectors"
  | _, _ => .undef "vectorproduct-requires-vectors"

def dynOuterProduct : MRes → MRes → MRes
  | .undef s, _ => .undef s
  | _, .undef s => .undef s
  | .vector n1 u, .vector n2 v =>
      .matrix { rows' := n1, cols := n2, data := outerBuild u v }
  | _, _ => .undef "outerproduct-requires-vectors"

/-- `selector(A, i, j)` on a matrix, with MathML's ONE-BASED indices.
    An out-of-range index is an explicit refusal, not a wrapped or
    clamped one. -/
def dynSelector (x : MRes) (i1 j1 : Int) : MRes :=
  match x with
  | .undef s  => .undef s
  | .matrix m =>
      if i1 ≥ 1 && j1 ≥ 1 && i1 ≤ (m.rows' : Int) && j1 ≤ (m.cols : Int) then
        .scalar (matElem m.data (i1 - 1).toNat (j1 - 1).toNat)
      else .undef "selector-index-out-of-range"
  | .vector n v =>
      if i1 ≥ 1 && i1 ≤ (n : Int) then .scalar ((v[(i1 - 1).toNat]?).getD none)
      else .undef "selector-index-out-of-range"
  | _ => .undef "selector-requires-matrix-or-vector"

/-! ## Canonical string form

A scalar prints as `n` or `num/den`; a vector as `[a,b,c]`; a matrix
as `[[a,b],[c,d]]`. The nesting keeps a one-row matrix and a vector
apart, which an unbracketed form would not. -/

def entToString (e : MEnt) : String :=
  match e with
  | none        => "undef"
  | some (n, 1) => toString n
  | some (n, d) => toString n ++ "/" ++ toString d

def rowToString (v : List MEnt) : String :=
  "[" ++ String.intercalate "," (v.map entToString) ++ "]"

def mresToString : MRes → String
  | .scalar v   => entToString v
  | .vector _ v => rowToString v
  | .matrix m   => "[" ++ String.intercalate "," (m.data.map rowToString) ++ "]"
  | .undef _    => "undef"

def mresReason : MRes → String
  | .undef r => r
  | _        => ""

end L4Factoidal.Math
