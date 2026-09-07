/-
L4Factoidal.MathML.FromJson — a Content MathML expression written as
JSON, the shape the TOAN operations take over the dispatch ABI.

This is the Lean reading of `expr_of_json` in
`bin/npm-entry/entry_jsoo.ml` (line 2125). The shape is not invented
here; it is matched member for member so the SAME JavaScript argument
drives either engine:

    {"int": 3}                    an integer
    {"rat": [5, 2]}               an exact rational, numerator first
    {"bool": true}                a boolean
    {"sym": "x"}                  a symbol
    {"app": "plus",
     "args": [ …exprs… ]}         an application; "args" absent is []
    {"mat": [[…], […]]}           a <matrix>, rows of expressions
    {"vec": [ …exprs… ]}          a <vector>
    3                             a bare number is the integer
    "x"                           a bare string is the symbol

The members are tried in that order, which is what the F* entry does:
an object carrying more than one of them is read by the first, not
refused.

`mat` and `vec` have no F* counterpart: `Math.Expr.expr` has no matrix
or vector constructor, so the F* entry could not carry one. The Lean
`Expr` does (MathML 3 §4.4.10), and a JSON shape that could not
express it would make the two engines differ in what they ACCEPT
rather than in what they answer. The five members the F* entry does
read are byte-identical in behaviour.

A shape with none of the five members is a REFUSAL (`none`), which
the caller reports as an error envelope. It is never read as a
default expression: an argument the caller mistyped must come back as
an error, not as a number nobody asked for.
-/
import L4Factoidal.MathML.Core
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.MathML

open L4Factoidal.JSON

private def member? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun m => m.1 == k)).map (·.2)
  | _          => none

/-- A JSON number as an `Int`. The JSON grammar allows a fraction and
    an exponent, which an integer position does not; such a number is
    refused rather than truncated. -/
private def intOf : Json → Option Int
  | .number s => s.toInt?
  | _         => none

/-! ## Fuel, and why it cannot refuse a document it should accept

A member is reached by a LOOKUP (`member?`), not by destructuring, so
the termination checker cannot see that the value found is smaller
than the object it came from. Rather than a `partial def` -- which the
hygiene baseline forbids and which would make this reader the only
untrusted step in the chain -- the recursion is structural on a fuel
argument, and `exprOfJson` supplies `sizeOf j`.

The fuel is the LENGTH OF THE SERIALISED VALUE. That bound is never
reached by a document this should accept: each recursive call descends
one nesting level and spends one fuel, and every nesting level writes
at least one bracket, so the serialised length strictly exceeds the
nesting depth. The fuel running out therefore means the input was
malformed in a way the arms already refuse, not that a legitimate
document was cut off.

(`sizeOf` would be the natural measure and is not usable: it has no
compiled implementation for `Json`, so a definition using it is
noncomputable.) -/

mutual

/-- Read one expression. `none` names a shape this does not accept. -/
def exprOfJsonFuel : Nat → Json → Option Expr
  | _, .number s => (s.toInt?).map Expr.int
  | _, .string s => some (.sym s)
  | fuel + 1, j@(.object _) =>
      match member? "int" j with
      | some n => (intOf n).map Expr.int
      | none =>
        match member? "rat" j with
        | some (.array [a, b]) =>
            match intOf a, intOf b with
            | some n, some d => some (.rat n d)
            | _, _           => none
        | some _ => none
        | none =>
          match member? "bool" j with
          | some (.bool b) => some (.bool b)
          | some _         => none
          | none =>
            match member? "sym" j with
            | some (.string s) => some (.sym s)
            | some _           => none
            | none =>
              match member? "app" j with
              | some (.string fn) =>
                  match member? "args" j with
                  | some (.array items) => (exprsOfJsonFuel fuel items).map (Expr.app fn)
                  -- an absent "args", or one that is not an array, is
                  -- an empty argument list in the F* entry too.
                  | _                   => some (.app fn [])
              | _ =>
                match member? "mat" j with
                | some (.array rws) => (rowsOfJsonFuel fuel rws).map Expr.mat
                | some _            => none
                | none =>
                  match member? "vec" j with
                  | some (.array items) => (exprsOfJsonFuel fuel items).map Expr.vec
                  | _                   => none
  | _, _ => none
termination_by fuel _ => (fuel, 0, 0)

def exprsOfJsonFuel : Nat → List Json → Option (List Expr)
  | _,    []     => some []
  | fuel, j :: t =>
      match exprOfJsonFuel fuel j, exprsOfJsonFuel fuel t with
      | some e, some es => some (e :: es)
      | _, _            => none
termination_by fuel js => (fuel, 1, sizeOf js)

def rowsOfJsonFuel : Nat → List Json → Option (List (List Expr))
  | _,    []     => some []
  | fuel, j :: t =>
      match j with
      | .array items =>
          (match exprsOfJsonFuel fuel items, rowsOfJsonFuel fuel t with
           | some r, some rs => some (r :: rs)
           | _, _            => none)
      | _ => none
termination_by fuel js => (fuel, 1, sizeOf js)

end

/-- The fuel a value is read with: the length of its serialisation. -/
def jsonFuel (j : Json) : Nat := (toStringCompact j).length

/-- Read one expression, with the fuel taken from the value itself. -/
def exprOfJson (j : Json) : Option Expr := exprOfJsonFuel (jsonFuel j) j

def exprsOfJson (js : List Json) : Option (List Expr) :=
  exprsOfJsonFuel (jsonFuel (.array js)) js

/-- Parse the JSON text and read the expression. -/
def exprOfJsonString (src : String) : Option Expr :=
  match parseJson? src with
  | none   => none
  | some j => exprOfJson j

/-! ## Writing an expression back as JSON

The inverse of `exprOfJson`, used by the round-trip guards. It emits
the canonical member for each constructor, so
`exprOfJson (exprToJson e) = some e` for every `e`. -/

mutual

def exprToJson : Expr → Json
  | .int n   => .object [("int", .number (toString n))]
  | .rat n d => .object [("rat", .array [.number (toString n), .number (toString d)])]
  | .bool b  => .object [("bool", .bool b)]
  | .sym s   => .object [("sym", .string s)]
  | .app fn args => .object [("app", .string fn), ("args", .array (exprsToJson args))]
  | .mat rws     => .object [("mat", .array (rowsToJson rws))]
  | .vec xs      => .object [("vec", .array (exprsToJson xs))]
termination_by e => sizeOf e

def exprsToJson : List Expr → List Json
  | []      => []
  | e :: t  => exprToJson e :: exprsToJson t
termination_by es => sizeOf es

def rowsToJson : List (List Expr) → List Json
  | []      => []
  | r :: t  => Json.array (exprsToJson r) :: rowsToJson t
termination_by rs => sizeOf rs

end

/-! ## Round-trip guards

`exprOfJson (exprToJson e) = some e` on every constructor, including
the two the F* entry has no shape for. These run at build time. -/

private def rt (e : Expr) : Bool :=
  match exprOfJson (exprToJson e) with
  | some e2 => exprToJson e2 == exprToJson e
  | none    => false

#guard rt (.int 3)
#guard rt (.int (-7))
#guard rt (.rat 5 2)
#guard rt (.bool true)
#guard rt (.sym "x")
#guard rt (.app "plus" [.sym "x", .app "times" [.int 2, .sym "y"]])
#guard rt (.app "nullary" [])
#guard rt (.mat [[.int 1, .int 2], [.sym "x", .app "plus" [.int 1, .sym "y"]]])
#guard rt (.vec [.int 1, .rat 1 2, .sym "z"])

/-! The bare forms the F* entry accepts alongside the object forms
(`expr_of_json` lines 2155 and 2156): a number is the integer, a
string is the symbol. -/

private def reads (j : Json) (e : Expr) : Bool :=
  match exprOfJson j with
  | some e2 => exprToJson e2 == exprToJson e
  | none    => false

#guard reads (.number "42") (.int 42)
#guard reads (.string "x") (.sym "x")

/-! An object with none of the members is a REFUSAL, not a default. -/

#guard (exprOfJson (.object [("nope", .number "1")])).isNone
#guard (exprOfJson .null).isNone

/-! `args` absent is the empty argument list, which is what the F*
entry does (line 2149). -/

#guard reads (.object [("app", .string "pi")]) (.app "pi" [])

end L4Factoidal.MathML
