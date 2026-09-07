/-
L4Factoidal.MathML.Present — expression into MathML markup, the
reverse of `MathML/FromXml.lean`.

Port of `formal/fstar/MathML.Present.fst`. Two outputs:

  * `toPresentationMathML` — Presentation MathML (MathML 3 §3), so a
    browser typesets the expression. Operator precedence drives
    MINIMAL parenthesization: a subexpression is fenced only when its
    top operator binds looser than the position it sits in, so
    `(x+y)*z` fences the sum and `x^2*y` does not fence the power. A
    fraction, a power and a function box are visually atomic and are
    never fenced.

  * `toContentMathML` — Content MathML (MathML 3 §4) mirroring the
    tree one-to-one. It round-trips with `MathML/FromXml.lean`:
    parsing it back and normalising recovers the original up to
    `simplify`.

Total and structurally recursive, no fuel and no `partial def`. The
recursion is on the strict subterm ordering: `presJoin` and
`presApplyArgs` walk the argument list, which is a component of the
node they came from.

Two facts recorded here rather than re-derived, carried over from the
F* module's own header:

  (a) `Math/Series.lean`'s `summation` and `finiteProduct` are
      EVALUATE-ONLY — they fold into a flat `plus` / `times` node. No
      symbolic sum or product head ever reaches this serializer, so
      there is nothing here to render for sum or product notation.
  (b) `<matrix>` and `<vector>` never reach `Expr` at all; the matrix
      path in the decoder produces `Math/Matrix.lean`'s own result
      type. There is no `app "matrix"` node to serialize.
-/
import L4Factoidal.MathML.Core

namespace L4Factoidal.MathML

/-! ## XML escaping

The F* `escape_char` escapes all five predefined entities, including
the two quote characters. `Core.escapeXml` escapes only the three
that matter in element content; this one is used for the names that
can also land in attribute position. -/

def escapeXmlFull (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if c == '&' then "&amp;"
            else if c == '<' then "&lt;"
            else if c == '>' then "&gt;"
            else if c == '"' then "&quot;"
            else if c == '\'' then "&apos;"
            else String.mk [c])) ""

/-! ## Number rendering -/

/-- An integer as `<mn>`; a negative sign is carried inside the token. -/
def renderInt (n : Int) : String := "<mn>" ++ toString n ++ "</mn>"

/-- A rational as a fraction box; the sign lives in the numerator. -/
def renderRat (n d : Int) : String :=
  "<mfrac><mn>" ++ toString n ++ "</mn><mn>" ++ toString d ++ "</mn></mfrac>"

/-- Fence an already-rendered operand when its operator binds looser
    than the position it sits in. -/
def fenced (minp p : Int) (s : String) : String := if p < minp then fence s else s

/-! ## Presentation MathML -/

mutual

/-- Render one node. The caller decides fencing from `prec`. -/
def pres : Expr → String
  | .int n   => renderInt n
  | .rat n d => renderRat n d
  | .bool b  => "<mi>" ++ (if b then "true" else "false") ++ "</mi>"
  | .sym s   => "<mi>" ++ escapeXmlFull s ++ "</mi>"
  -- §4.4.10 literals. They are not in `MathML.Present.fst`, whose
  -- header records that no `<matrix>` or `<vector>` node could reach
  -- it; the Lean `Expr` DOES carry them, so they are rendered rather
  -- than dropped. A matrix is a fenced `<mtable>`, a vector a fenced
  -- one-column `<mtable>`, which is the Presentation form §3.5.1
  -- gives for both.
  | .mat rws =>
      "<mrow><mo>(</mo><mtable>" ++ presRows rws ++ "</mtable><mo>)</mo></mrow>"
  | .vec xs =>
      "<mrow><mo>(</mo><mtable>" ++ presCells xs ++ "</mtable><mo>)</mo></mrow>"
  | .app fn args =>
      -- The generic function-application rendering, as a thunk. It is
      -- the fallback of every arm below, and it must be written once
      -- HERE, before `args` is destructured: inside an inner match the
      -- termination checker can no longer relate the reconstructed
      -- list to `args`, and the measure `sizeOf args < sizeOf (.app fn
      -- args)` stops being provable.
      let fallback : Unit → String := fun _ => presApply fn args
      if fn == "plus" then
        match args with
        | []       => renderInt 0
        | a :: rest => fenced 1 (prec a) (pres a) ++ presJoin "<mo>+</mo>" 1 rest
      else if fn == "minus" then
        match args with
        | [a]    => "<mo>-</mo>" ++ fenced 2 (prec a) (pres a)
        | [a, b] => fenced 1 (prec a) (pres a) ++ "<mo>-</mo>" ++ fenced 2 (prec b) (pres b)
        | _      => fallback ()
      else if fn == "times" then
        match args with
        | []        => renderInt 1
        | a :: rest => fenced 2 (prec a) (pres a) ++ presJoin "<mo>&#x2062;</mo>" 2 rest
      else if fn == "divide" then
        match args with
        | [a, b] => "<mfrac><mrow>" ++ pres a ++ "</mrow><mrow>" ++ pres b ++ "</mrow></mfrac>"
        | _      => fallback ()
      else if fn == "power" then
        match args with
        | [a, b] =>
            "<msup><mrow>" ++ fenced 4 (prec a) (pres a) ++ "</mrow><mrow>" ++
            pres b ++ "</mrow></msup>"
        | _ => fallback ()
      else if fn == "root" then
        match args with
        | [a]    => "<msqrt><mrow>" ++ pres a ++ "</mrow></msqrt>"
        | [d, a] => "<mroot><mrow>" ++ pres a ++ "</mrow><mrow>" ++ pres d ++ "</mrow></mroot>"
        | _      => fallback ()
      else if isRelation fn then
        -- An infix chain. An operand is fenced only when it is itself
        -- a relation, whose precedence 0 is below the 1 required here.
        match args with
        | a :: rest => fenced 1 (prec a) (pres a) ++ presJoin (relationToken fn) 1 rest
        | []        => fallback ()
      else if fn == "abs" then
        -- |x| : atomic, no internal fencing — the bars delimit it.
        match args with
        | [a] => "<mrow><mo>|</mo>" ++ pres a ++ "<mo>|</mo></mrow>"
        | _   => fallback ()
      else if fn == "factorial" then
        -- n! : atomic; the operand is fenced if it binds looser.
        match args with
        | [a] => fenced 4 (prec a) (pres a) ++ "<mo>!</mo>"
        | _   => fallback ()
      else if fn == "exp" then
        -- e^x as a superscript, matching power's visual form.
        match args with
        | [a] => "<msup><mi>e</mi><mrow>" ++ pres a ++ "</mrow></msup>"
        | _   => fallback ()
      else if fn == "diff_unsupported" then
        -- `Math/Diff.lean`'s explicit "no rule" marker. It surfaces as
        -- a visible error box rather than leaking as a generic
        -- function application that reads like a real derivative.
        "<merror><mtext>unsupported derivative</mtext></merror>"
      else fallback ()
termination_by e => (sizeOf e, 0)

/-- The remaining operands of an infix operator, each preceded by the
    operator token and fenced against `minp`. -/
def presJoin (tok : String) (minp : Int) : List Expr → String
  | []        => ""
  | a :: rest => tok ++ fenced minp (prec a) (pres a) ++ presJoin tok minp rest
termination_by es => (sizeOf es, 1)

/-- `f(a, b, ..)`: atomic, arguments comma-separated. -/
def presApply (fn : String) (args : List Expr) : String :=
  "<mrow><mi>" ++ escapeXmlFull fn ++ "</mi><mo>&#x2061;</mo><mo>(</mo>" ++
  presApplyArgs args ++ "<mo>)</mo></mrow>"
termination_by (sizeOf args, 2)

def presApplyArgs : List Expr → String
  | []        => ""
  | [a]       => pres a
  | a :: rest => pres a ++ "<mo>,</mo>" ++ presApplyArgs rest
termination_by es => (sizeOf es, 1)

/-- One `<mtr>` per row of a matrix literal. -/
def presRows : List (List Expr) → String
  | []        => ""
  | r :: rest => "<mtr>" ++ presCells r ++ "</mtr>" ++ presRows rest
termination_by rws => (sizeOf rws, 1)

/-- One `<mtd>` per entry. A vector literal is one entry per ROW, so
    the cells are wrapped a row at a time there. -/
def presCells : List Expr → String
  | []        => ""
  | a :: rest => "<mtd>" ++ pres a ++ "</mtd>" ++ presCells rest
termination_by es => (sizeOf es, 1)

end

def mathDoc (inner : String) : String :=
  "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">" ++ inner ++ "</math>"

def toPresentationMathML (e : Expr) : String := mathDoc (pres e)

/-! ## Content MathML -/

/-- The operators Content MathML names with an empty element. Any
    other function name is carried as `<csymbol>` text, which
    `FromXml.lean` reads back. -/
def knownContentOp (fn : String) : Bool :=
  ["plus", "times", "minus", "divide", "power", "root", "abs",
   "quotient", "rem", "factorial", "gcd", "max", "min",
   "eq", "neq", "lt", "gt", "leq", "geq", "exp"].contains fn

def contentOp (fn : String) : String :=
  if knownContentOp fn then "<" ++ fn ++ "/>"
  else "<csymbol>" ++ escapeXmlFull fn ++ "</csymbol>"

mutual

def content : Expr → String
  | .int n   => "<cn type=\"integer\">" ++ toString n ++ "</cn>"
  | .rat n d => "<cn type=\"rational\">" ++ toString n ++ "<sep/>" ++ toString d ++ "</cn>"
  | .bool b  => if b then "<true/>" else "<false/>"
  | .sym s   => "<ci>" ++ escapeXmlFull s ++ "</ci>"
  | .app fn args => "<apply>" ++ contentOp fn ++ contentArgs args ++ "</apply>"
  -- §4.4.10.2 and §4.4.10.1. `FromXml.lean` reads both back, so these
  -- round-trip like every other node.
  | .mat rws => "<matrix>" ++ contentRows rws ++ "</matrix>"
  | .vec xs  => "<vector>" ++ contentArgs xs ++ "</vector>"
termination_by e => sizeOf e

def contentArgs : List Expr → String
  | []        => ""
  | a :: rest => content a ++ contentArgs rest
termination_by es => sizeOf es

def contentRows : List (List Expr) → String
  | []        => ""
  | r :: rest => "<matrixrow>" ++ contentArgs r ++ "</matrixrow>" ++ contentRows rest
termination_by rws => sizeOf rws

end

def toContentMathML (e : Expr) : String := mathDoc (content e)

end L4Factoidal.MathML
