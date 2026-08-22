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

namespace L4Factoidal.MathML

/-- A Content MathML expression. -/
inductive Expr where
  | int  (n : Int)
  | rat  (num : Int) (den : Int)
  | bool (b : Bool)
  | sym  (name : String)
  | app  (fn : String) (args : List Expr)
deriving Repr, Inhabited

/-! ## Exact rational arithmetic -/

private partial def gcdNat (a b : Nat) : Nat := if b == 0 then a else gcdNat b (a % b)

/-- Normalise to lowest terms with a positive denominator. A zero
    denominator collapses to `0/1` rather than propagating — Content
    MathML has no infinity, so the F* module treats it as absent
    rather than inventing a value. -/
def normRat (n d : Int) : Int × Int :=
  if d == 0 then (0, 1)
  else
    let s : Int := if d < 0 then -1 else 1
    let n := n * s
    let d := d * s
    let g : Int := gcdNat n.natAbs d.natAbs
    if g == 0 then (0, 1) else (n / g, d / g)

def addRat (a b : Int × Int) : Int × Int :=
  normRat (a.1 * b.2 + b.1 * a.2) (a.2 * b.2)

def mulRat (a b : Int × Int) : Int × Int := normRat (a.1 * b.1) (a.2 * b.2)
def negRat (a : Int × Int) : Int × Int := (-a.1, a.2)
def subRat (a b : Int × Int) : Int × Int := addRat a (negRat b)

/-- Division. A zero divisor yields `none` — MathML has no infinity,
    so this refuses rather than inventing one. -/
def divRat (a b : Int × Int) : Option (Int × Int) :=
  if b.1 == 0 then none else some (normRat (a.1 * b.2) (a.2 * b.1))

def cmpRat (a b : Int × Int) : Ordering := compare (a.1 * b.2) (b.1 * a.2)

/-! ## Evaluation -/

/-- A value: an exact rational or a boolean. -/
inductive Value where
  | num  (r : Int × Int)
  | bool (b : Bool)
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

/-- Evaluate against a symbol environment. `none` is a REFUSAL — an
    unbound symbol, an unknown operator, or a division by zero — never
    a default value. -/
partial def eval (env : String → Option (Int × Int)) : Expr → Option Value
  | .int n     => some (.num (n, 1))
  | .rat n d   => if d == 0 then none else some (.num (normRat n d))
  | .bool b    => some (.bool b)
  | .sym s     => (env s).map .num
  | .app fn args =>
      let nums := args.mapM (fun a => match eval env a with
        | some (.num r) => some r
        | _ => none)
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
                if y.2 != 1 || y.1 < 0 then none      -- only natural powers
                else some (.num ((List.replicate y.1.toNat x).foldl mulRat (1, 1)))
            | _ => none
          else if isRelation fn then
            match rs with
            | [x, y] => (relResult fn (cmpRat x y)).map Value.bool
            | _      => none
          else none

/-! ## Presentation rendering -/

/-- Operator precedence, matching the F* table: relations bind
    loosest, then plus/n-ary minus, then times/unary minus, then
    power, with atoms and divide tightest. A NEGATIVE literal gets
    the loose precedence of a `minus`, so `2^-3` renders fenced. -/
def prec : Expr → Int
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
