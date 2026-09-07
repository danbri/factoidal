/-
L4Factoidal.MathML.Core — Content MathML expressions, evaluation and
Presentation rendering, ported from `formal/fstar/MathML.Content.fst`
and `MathML.Present.fst`.

Spec: MathML 3 (https://www.w3.org/TR/MathML3/) — Content markup
(§4) for the expression tree, Presentation markup (§3) for the
rendered form.

Rationals are EXACT (`numerator / denominator` in lowest terms), not
floats: MathML content markup means the mathematical value, and
`1/3 + 1/3 + 1/3` must be `1`.
-/

-- The linear algebra lives in `L4Factoidal.Math.Matrix` — the port of
-- `formal/fstar/Math.Matrix.fst`, which carries the shape theorems.
-- `MathML/Matrix.lean` was a second copy of the same algebra and is
-- gone; §4.4.10 evaluation below routes through the one that is
-- proved.
import L4Factoidal.Math.Matrix

namespace L4Factoidal.MathML

open L4Factoidal.Math (MEnt matAdd matSub scalarMul transposeM matMul
  determinant rowDot cross3 outerBuild)

/-! ## Matrix and vector VALUES

The evaluated form: every entry is a defined exact rational, because
an entry that failed to evaluate leaves the whole literal without a
value (see `eval`'s `.mat` / `.vec` cases). `Math.Matrix` works over
`MEnt = Option (Int × Int)`, so the two lifts below move between the
representations and `lower*` REFUSES a result carrying an undefined
entry rather than substituting a zero. -/

/-- A matrix of exact rationals, as rows. -/
abbrev Mat := List (List (Int × Int))

/-- A vector of exact rationals. -/
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

/-- `selector` indexes from ONE, per §4.4.10. Index zero and any index
    past the end are out of range, and out of range is `none`. -/
def nth1? (i : Int) (l : List α) : Option α :=
  if i < 1 then none else l[i.toNat - 1]?

def liftMat (m : Mat) : List (List MEnt) := m.map (fun r => r.map some)
def liftVec (v : Vec) : List MEnt := v.map some

def lowerMat (m : List (List MEnt)) : Option Mat := m.mapM (fun r => r.mapM id)
def lowerVec (v : List MEnt) : Option Vec := v.mapM id

/-! ## Writing a value the way the corpus writes it -/

def showRat (r : Int × Int) : String :=
  if r.2 == 1 then toString r.1 else toString r.1 ++ "/" ++ toString r.2

def showVec (v : Vec) : String := "[" ++ String.intercalate "," (v.map showRat) ++ "]"

def showMat (m : Mat) : String :=
  "[" ++ String.intercalate "," (m.map showVec) ++ "]"

/-- A Content MathML expression. -/
inductive Expr where
  | int  (n : Int)
  | rat  (num : Int) (den : Int)
  | bool (b : Bool)
  | sym  (name : String)
  | app  (fn : String) (args : List Expr)
  /-- `<matrix>` of `<matrixrow>`s, §4.4.10.2. Rows of expressions,
      not of values: an entry may itself be an `<apply>`. -/
  | mat  (rows : List (List Expr))
  /-- `<vector>`, §4.4.10.1. -/
  | vec  (xs : List Expr)
deriving Repr, Inhabited

/-! ## Evaluation -/

/-- A value: an exact rational or a boolean. -/
inductive Value where
  | num  (r : Int × Int)
  | bool (b : Bool)
  /-- A vector of exact rationals (§4.4.10.1). -/
  | vecv (v : Vec)
  /-- A matrix of exact rationals (§4.4.10.2). -/
  | matv (m : Mat)
deriving Repr, DecidableEq, Inhabited

private def relResult (fn : String) (o : Ordering) : Option Bool :=
  if fn == "eq"  then some (o == .eq)
  else if fn == "neq" then some (o != .eq)
  else if fn == "lt"  then some (o == .lt)
  else if fn == "gt"  then some (o == .gt)
  else if fn == "leq" then some (o != .gt)
  else if fn == "geq" then some (o != .lt)
  else none

def isRelation (fn : String) : Bool :=
  ["eq", "neq", "lt", "gt", "leq", "geq"].contains fn

/-! ### The arithmetic the corpus exercises beyond the four operations

Each of these is exact or it REFUSES. `root` of 2 is not a rational,
so it is `none` rather than an approximation; MathML content markup
denotes a value, and returning a nearby float would state something
the expression does not. -/

/-- Integer `n`th power, `n ≥ 0`. -/
def powNat (x : Int × Int) : Nat → Int × Int
  | 0     => (1, 1)
  | n + 1 => mulRat x (powNat x n)

/-- The exact `n`th root of a NON-NEGATIVE integer, or `none`. Found by
    a bounded search rather than a floating-point guess, so it is
    exact by construction. -/
def exactRootNat (n : Nat) (v : Nat) : Option Nat :=
  if n == 0 then none
  else
    let rec go : Nat → Option Nat
      | 0     => if (powNat ((0 : Int), 1) n).1 == (v : Int) then some 0 else none
      | k + 1 =>
          let p := powNat (((k + 1 : Nat) : Int), 1) n
          if p.1 == (v : Int) then some (k + 1)
          else if p.1 > (v : Int) then go k
          else none
    if v == 0 then some 0 else go v

/-- The exact `n`th root of a rational: both numerator and denominator
    must be perfect `n`th powers. A negative radicand is refused —
    MathML's `root` is the principal one, and an even root of a
    negative has no real value. -/
def exactRootRat (n : Nat) (a : Int × Int) : Option (Int × Int) :=
  if a.1 < 0 then none
  else match exactRootNat n a.1.natAbs, exactRootNat n a.2.natAbs with
    | some p, some q => some (normRat (p : Int) (q : Int))
    | _, _ => none

/-- `factorial`, on a non-negative integer. -/
def factorialInt (n : Nat) : Int :=
  (List.range n).foldl (fun (acc : Int) (k : Nat) => acc * ((k : Int) + 1)) (1 : Int)

private partial def gcdInt (a b : Int) : Int :=
  if b == 0 then (if a < 0 then -a else a) else gcdInt b (a % b)

/-- Is this rational an integer? The n-ary integer operators refuse a
    fractional argument rather than truncating it. -/
def asInt (a : Int × Int) : Option Int := if a.2 == 1 then some a.1 else none

/-- The linear-algebra operators of §4.4.10, over already-evaluated
    arguments.

    `none` means "this is not a linear-algebra application" AND "this
    application has no value" — the two collapse safely, because the
    scalar path that `eval` falls through to also has no value for an
    argument that is a matrix or a vector. So a shape mismatch stays
    undefined rather than being answered with a number.

    `plus`, `minus` and `times` are shared with the scalar evaluator:
    they reach here only when an argument is a matrix or a vector. -/
def linAlg (fn : String) (vs : List Value) : Option Value :=
  -- Each arm CHECKS the shape here and then calls `Math.Matrix` for
  -- the arithmetic. The check stays on this side because MathML says
  -- which shapes have a value; the algebra lives on that side because
  -- that is where it is proved.
  match fn, vs with
  | "plus",  [.matv a, .matv b] =>
      if !sameShape a b then none
      else (lowerMat (matAdd (liftMat a) (liftMat b))).map Value.matv
  | "minus", [.matv a, .matv b] =>
      if !sameShape a b then none
      else (lowerMat (matSub (liftMat a) (liftMat b))).map Value.matv
  -- Vector addition is NOT routed through `Math.Matrix.dynAdd`: the F*
  -- module it ports has no vector case for `add` and answers
  -- "add-type-mismatch", which is its behaviour and not a gap to patch
  -- from here. §4.4.10 does add vectors, so the two-line elementwise
  -- form stays.
  | "plus",  [.vecv a, .vecv b] =>
      if a.length != b.length then none
      else some (.vecv ((a.zip b).map (fun (x, y) => addRat x y)))
  | "minus", [.vecv a, .vecv b] =>
      if a.length != b.length then none
      else some (.vecv ((a.zip b).map (fun (x, y) => subRat x y)))
  | "times", [.num k, .matv a] => (lowerMat (scalarMul (some k) (liftMat a))).map Value.matv
  | "times", [.matv a, .num k] => (lowerMat (scalarMul (some k) (liftMat a))).map Value.matv
  | "times", [.num k, .vecv a] => some (.vecv (a.map (mulRat k)))
  | "times", [.vecv a, .num k] => some (.vecv (a.map (mulRat k)))
  | "times", [.matv a, .matv b] =>
      if !rectangular a || !rectangular b || cols a != rows b then none
      else (lowerMat (matMul (cols b) (liftMat a) (liftMat b))).map Value.matv
  | "determinant", [.matv a] =>
      if !rectangular a || rows a != cols a then none
      else (determinant (rows a) (liftMat a)).map Value.num
  | "transpose", [.matv a] =>
      if !rectangular a then none
      else (lowerMat (transposeM (cols a) (liftMat a))).map Value.matv
  | "scalarproduct", [.vecv u, .vecv v] =>
      if u.length != v.length then none
      else (rowDot (liftVec u) (liftVec v)).map Value.num
  | "vectorproduct", [.vecv u, .vecv v] =>
      -- `cross3` is defined for 3-vectors; any other length has no
      -- cross product, so the length is checked before the call.
      if u.length != 3 || v.length != 3 then none
      else (lowerVec (cross3 (liftVec u) (liftVec v))).map Value.vecv
  | "outerproduct",  [.vecv u, .vecv v] =>
      (lowerMat (outerBuild (liftVec u) (liftVec v))).map Value.matv
  -- `selector` indexes from ONE: (row, column) into a matrix, or a
  -- single index into a vector. Out of range has no value.
  | "selector", [.matv a, .num i, .num j] =>
      if i.2 != 1 || j.2 != 1 then none
      else (nth1? i.1 a).bind (fun r => (nth1? j.1 r).map Value.num)
  | "selector", [.matv a, .num i] =>
      if i.2 != 1 then none else (nth1? i.1 a).map Value.vecv
  | "selector", [.vecv v, .num i] =>
      if i.2 != 1 then none else (nth1? i.1 v).map Value.num
  | _, _ => none

/-- Evaluate against a symbol environment. `none` is a REFUSAL — an
    unbound symbol, an unknown operator, or a division by zero — never
    a default value. -/
partial def eval (env : String → Option (Int × Int)) : Expr → Option Value
  | .int n     => some (.num (n, 1))
  | .rat n d   => if d == 0 then none else some (.num (normRat n d))
  | .bool b    => some (.bool b)
  | .sym s     => (env s).map .num
  -- A `<matrix>`/`<vector>` literal may hold any expression, so each
  -- entry is evaluated; an entry that is not a scalar, or a ragged
  -- row shape, leaves the whole literal without a value.
  | .mat rws =>
      match rws.mapM (fun r => r.mapM (fun e => match eval env e with
                                | some (.num x) => some x
                                | _             => none)) with
      | some m => if rectangular m then some (.matv m) else none
      | none   => none
  | .vec xs =>
      (xs.mapM (fun e => match eval env e with
        | some (.num x) => some x
        | _             => none)).map Value.vecv
  | .app fn args =>
      match args.mapM (eval env) with
      | none => none
      | some vs =>
      match linAlg fn vs with
      | some r => some r
      | none =>
      let nums := vs.mapM (fun v => match v with
        | .num r => some r
        | _      => none)
      match nums with
      | none => none
      | some rs =>
          if fn == "plus" then some (.num (rs.foldl addRat (0, 1)))
          else if fn == "times" then some (.num (rs.foldl mulRat (1, 1)))
          else if fn == "minus" then
            match rs with
            | [x]    => some (.num (negRat x))
            | x :: t => some (.num (t.foldl subRat x))
            | []     => none
          else if fn == "divide" then
            match rs with
            | [x, y] => (divRat x y).map Value.num
            | _      => none
          else if fn == "power" then
            match rs with
            | [x, y] =>
                -- A NON-INTEGER exponent is refused (it is not a
                -- rational power in general); a NEGATIVE one is the
                -- reciprocal, which is exact.
                if y.2 != 1 then none
                else if y.1 ≥ 0 then some (.num (powNat x y.1.toNat))
                else (divRat (1, 1) (powNat x y.1.natAbs)).map Value.num
            | _ => none
          else if fn == "root" then
            -- `root` takes an optional DEGREE, which the front end
            -- passes as the first argument; with one argument the
            -- degree is 2.
            (match rs with
             | [x]    => (exactRootRat 2 x).map Value.num
             | [d, x] =>
                 match asInt d with
                 | some n => if n ≤ 0 then none else (exactRootRat n.toNat x).map Value.num
                 | none   => none
             | _ => none)
          else if fn == "abs" then
            (match rs with
             | [x] => some (.num (if x.1 < 0 then negRat x else x))
             | _   => none)
          else if fn == "quotient" then
            (match rs with
             | [x, y] =>
                 match asInt x, asInt y with
                 | some a, some b => if b == 0 then none else some (.num (a / b, 1))
                 | _, _ => none
             | _ => none)
          else if fn == "rem" then
            (match rs with
             | [x, y] =>
                 match asInt x, asInt y with
                 | some a, some b => if b == 0 then none else some (.num (a % b, 1))
                 | _, _ => none
             | _ => none)
          else if fn == "factorial" then
            (match rs with
             | [x] =>
                 match asInt x with
                 | some a => if a < 0 then none else some (.num (factorialInt a.toNat, 1))
                 | none   => none
             | _ => none)
          else if fn == "gcd" then
            (match rs.mapM asInt with
             | some (a :: t) => some (.num (t.foldl gcdInt a, 1))
             | _ => none)
          else if fn == "max" then
            (match rs with
             | x :: t => some (.num (t.foldl (fun a b => if cmpRat a b == .lt then b else a) x))
             | []     => none)
          else if fn == "min" then
            (match rs with
             | x :: t => some (.num (t.foldl (fun a b => if cmpRat a b == .gt then b else a) x))
             | []     => none)
          else if isRelation fn then
            -- Relations CHAIN: `eq` of three values holds when every
            -- adjacent pair does, which is what MathML's n-ary
            -- relations mean. Reading only the first two would call
            -- `2 = 2 = 3` true.
            (match rs with
             | _ :: _ :: _ =>
                 let pairs := rs.zip (rs.drop 1)
                 match pairs.mapM (fun (a, b) => relResult fn (cmpRat a b)) with
                 | some (bs : List Bool) => some (Value.bool (bs.all id))
                 | none => none
             | _ => none)
          else none

/-! ## Presentation rendering -/

/-- Operator precedence, matching the F* table: relations bind
    loosest, then plus/n-ary minus, then times/unary minus, then
    power, with atoms and divide tightest. A NEGATIVE literal gets
    the loose precedence of a `minus`, so `2^-3` renders fenced. -/
def prec : Expr → Int
  -- A matrix or vector literal is an ATOM: it carries its own
  -- brackets, so it never needs fencing.
  | .mat _   => 4
  | .vec _   => 4
  | .int n   => if n < 0 then 1 else 4
  | .rat n _ => if n < 0 then 1 else 4
  | .bool _  => 4
  | .sym _   => 4
  | .app fn args =>
      if fn == "plus" then 1
      else if fn == "minus" then (match args with | [_] => 2 | _ => 1)
      else if fn == "times" then 2
      else if fn == "power" then 3
      else if fn == "divide" then 4
      else if isRelation fn then 0
      else 4

def escapeXml (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if c == '&' then "&amp;" else if c == '<' then "&lt;"
            else if c == '>' then "&gt;" else String.mk [c])) ""

def fence (s : String) : String := "<mrow><mo>(</mo>" ++ s ++ "<mo>)</mo></mrow>"

def relationToken (fn : String) : String :=
  if fn == "eq" then "<mo>=</mo>"
  else if fn == "neq" then "<mo>&#x2260;</mo>"
  else if fn == "lt" then "<mo>&lt;</mo>"
  else if fn == "gt" then "<mo>&gt;</mo>"
  else if fn == "leq" then "<mo>&#x2264;</mo>"
  else "<mo>&#x2265;</mo>"

/-- Render to Presentation MathML, fencing a child whose precedence
    is looser than its parent's. -/
partial def render (e : Expr) : String :=
  let sub (parent : Int) (child : Expr) : String :=
    let s := render child
    if prec child < parent then fence s else s
  match e with
  -- Presentation output for a matrix or vector is NOT modelled: this
  -- module is a Content MathML backend (decoding and exact
  -- evaluation), not a presentation renderer, so it names the
  -- construct rather than inventing a layout for it.
  | .mat _   => "<mi>matrix</mi>"
  | .vec _   => "<mi>vector</mi>"
  | .int n   => "<mn>" ++ toString n ++ "</mn>"
  | .rat n d => "<mfrac><mn>" ++ toString n ++ "</mn><mn>" ++ toString d ++ "</mn></mfrac>"
  | .bool b  => "<mi>" ++ (if b then "true" else "false") ++ "</mi>"
  | .sym s   => "<mi>" ++ escapeXml s ++ "</mi>"
  | .app fn args =>
      if fn == "plus" then
        "<mrow>" ++ String.intercalate "<mo>+</mo>" (args.map (sub 1)) ++ "</mrow>"
      else if fn == "times" then
        "<mrow>" ++ String.intercalate "<mo>&#x22C5;</mo>" (args.map (sub 2)) ++ "</mrow>"
      else if fn == "minus" then
        match args with
        | [x]  => "<mrow><mo>-</mo>" ++ sub 2 x ++ "</mrow>"
        | args => "<mrow>" ++ String.intercalate "<mo>-</mo>" (args.map (sub 1)) ++ "</mrow>"
      else if fn == "divide" then
        match args with
        | [x, y] => "<mfrac>" ++ render x ++ render y ++ "</mfrac>"
        | _      => "<mrow/>"
      else if fn == "power" then
        match args with
        | [x, y] => "<msup>" ++ sub 4 x ++ render y ++ "</msup>"
        | _      => "<mrow/>"
      else if isRelation fn then
        match args with
        | [x, y] => "<mrow>" ++ sub 1 x ++ relationToken fn ++ sub 1 y ++ "</mrow>"
        | _      => "<mrow/>"
      else
        "<mrow><mi>" ++ escapeXml fn ++ "</mi><mo>(</mo>" ++
        String.intercalate "<mo>,</mo>" (args.map render) ++ "<mo>)</mo></mrow>"

/-! ## Content vs Presentation detection -/

inductive Kind where
  | content | presentation | unknown
deriving Repr, DecidableEq, Inhabited

def contentVocab (ln : String) : Bool :=
  ["apply", "cn", "ci", "csymbol", "bind", "bvar", "cbytes", "cs",
   "cerror", "share"].contains ln

def presentationVocab (ln : String) : Bool :=
  ["mi", "mo", "mn", "mrow", "mfrac", "msqrt", "mroot", "msup", "msub",
   "msubsup", "mtable", "mtr", "mtd", "mtext", "mspace", "mover",
   "munder", "munderover", "mfenced", "mpadded", "mstyle"].contains ln

/-- Classify by the element names present. CONTENT wins when both
    appear, matching the F* order: a document mixing the two is
    processed as content markup, since that is what carries meaning. -/
def kindOf (names : List String) : Kind :=
  if names.any contentVocab then .content
  else if names.any presentationVocab then .presentation
  else .unknown

end L4Factoidal.MathML
