/-
L4Factoidal.MathML.Matrix — exact linear algebra over the rationals
for Content MathML §4.4.10.

Spec: MathML 3.0 (2nd Edition) §4.4.10 (Linear Algebra) and the
OpenMath Content Dictionaries it references, `linalg1` and `linalg2`:
`matrix`, `matrixrow`, `vector`, `determinant`, `transpose`,
`scalarproduct`, `vectorproduct`, `outerproduct`, `selector`.

## Every operation is PARTIAL, and the partiality is the point

A shape that does not admit an operation has no value: adding a 2x2
to a 2x3, multiplying when the inner dimensions disagree, taking the
determinant of a non-square matrix, dotting vectors of different
lengths, indexing outside the bounds. Each of those returns `none`.

Returning a number for any of them would be wrong in the direction
hardest to notice — an answer of the right TYPE and the wrong value,
which a test suite scores as decided. Five of the corpus's 25 linear
algebra cases expect exactly this absence, and they are scored like
any other case rather than skipped.

## No floating point anywhere

Entries are exact rationals `(num, den)` in lowest terms with a
positive denominator, the same representation `MathML.Core` uses for
a scalar. A determinant is computed by Laplace expansion over those
rationals, so `determinant-3x3` is exactly -306 and not -305.9999.

## Recursion is bounded by a fuel argument

`determinant` recurses on minors. The fuel is the matrix order, which
strictly decreases, so the definition is structurally recursive on
`Nat` and needs no `partial def`.
-/
import L4Factoidal.MathML.Rat

namespace L4Factoidal.MathML

/-- A matrix as a list of rows, each a list of exact rationals. -/
abbrev Mat := List (List (Int × Int))

/-- A vector as a list of exact rationals. -/
abbrev Vec := List (Int × Int)

/-- `true` when every row has the same length as the first, and there
    is at least one row. A ragged `<matrix>` is not a matrix. -/
def rectangular (m : Mat) : Bool :=
  match m with
  | []      => false
  | r :: rs => rs.all (fun s => s.length == r.length)

def rows (m : Mat) : Nat := m.length
def cols (m : Mat) : Nat := (m.head?.map List.length).getD 0

/-- Same shape, entry by entry. -/
def sameShape (a b : Mat) : Bool :=
  rectangular a && rectangular b && rows a == rows b && cols a == cols b

/-- Elementwise combination; `none` when the shapes disagree. -/
def zipWithMat (f : (Int × Int) → (Int × Int) → (Int × Int)) (a b : Mat)
    : Option Mat :=
  if !sameShape a b then none
  else some ((a.zip b).map (fun (ra, rb) => (ra.zip rb).map (fun (x, y) => f x y)))

def addMat (a b : Mat) : Option Mat := zipWithMat addRat a b
def subMat (a b : Mat) : Option Mat := zipWithMat subRat a b

/-- A scalar scales every entry. -/
def scaleMat (k : Int × Int) (a : Mat) : Mat := a.map (fun r => r.map (mulRat k))

def transposeMat (m : Mat) : Option Mat :=
  if !rectangular m then none
  else
    some ((List.range (cols m)).map (fun j =>
      m.map (fun r => (r[j]?).getD (0, 1))))

/-- The exact dot product of two equal-length vectors. -/
def dot (u v : Vec) : Option (Int × Int) :=
  if u.length != v.length then none
  else some ((u.zip v).foldl (fun acc (x, y) => addRat acc (mulRat x y)) (0, 1))

/-- Matrix product. `none` unless both are rectangular and the inner
    dimensions agree. -/
def mulMat (a b : Mat) : Option Mat := do
  if !rectangular a || !rectangular b then none
  else if cols a != rows b then none
  else
    let bt ← transposeMat b
    some (a.map (fun r => bt.map (fun c => (dot r c).getD (0, 1))))

/-- Drop column `j` from every row. -/
def dropCol (j : Nat) (m : Mat) : Mat :=
  m.map (fun r => r.take j ++ r.drop (j + 1))

/-- Laplace expansion along the first row. `fuel` is the order of the
    matrix and strictly decreases with each minor. -/
def detFuel : Nat → Mat → Option (Int × Int)
  | _, []       => none
  | _, [[a]]    => some a
  | 0, _        => none
  | n + 1, r0 :: rest =>
      if !rectangular (r0 :: rest) then none
      else if r0.length != (rest.length + 1) then none
      else
        (List.range r0.length).foldl (fun acc j =>
          match acc with
          | none     => none
          | some sum =>
              match detFuel n (dropCol j rest), r0[j]? with
              | some minor, some a =>
                  let term := mulRat a minor
                  some (if j % 2 == 0 then addRat sum term else subRat sum term)
              | _, _ => none) (some (0, 1))

/-- The determinant of a SQUARE matrix; `none` for any other shape. -/
def determinant (m : Mat) : Option (Int × Int) :=
  if !rectangular m || rows m != cols m then none else detFuel (rows m) m

/-- The three-dimensional cross product (linalg1 `vectorproduct`).
    Defined for 3-vectors only. -/
def cross (u v : Vec) : Option Vec :=
  match u, v with
  | [a1, a2, a3], [b1, b2, b3] =>
      some [ subRat (mulRat a2 b3) (mulRat a3 b2)
           , subRat (mulRat a3 b1) (mulRat a1 b3)
           , subRat (mulRat a1 b2) (mulRat a2 b1) ]
  | _, _ => none

/-- The outer product `u (x) v`: entry (i, j) is `u_i * v_j`. -/
def outer (u v : Vec) : Mat := u.map (fun x => v.map (fun y => mulRat x y))

/-- `selector` indexes from ONE, per §4.4.10. Index zero and any index
    past the end are out of range, and out of range is `none`. -/
def nth1? (i : Int) (l : List α) : Option α :=
  if i < 1 then none else l[i.toNat - 1]?

/-! ## Writing a value the way the corpus writes it -/

def showRat (r : Int × Int) : String :=
  if r.2 == 1 then toString r.1 else toString r.1 ++ "/" ++ toString r.2

def showVec (v : Vec) : String := "[" ++ String.intercalate "," (v.map showRat) ++ "]"

def showMat (m : Mat) : String :=
  "[" ++ String.intercalate "," (m.map showVec) ++ "]"

end L4Factoidal.MathML
