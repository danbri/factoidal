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
    3                             a bare number is the integer
    "x"                           a bare string is the symbol

The members are tried in that order, which is what the F* entry does:
an object carrying more than one of them is read by the first, not
refused.

A shape with none of the five members is a REFUSAL (`none`), which
the caller reports as an error envelope. It is never read as a
default expression: an argument the caller mistyped must come back as
an error, not as a number nobody asked for.
-/
import L4Factoidal.MathML.Core
import L4Factoidal.JSON.Parser

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

mutual

/-- Read one expression. `none` names a shape this does not accept. -/
def exprOfJson : Json → Option Expr
  | .number s => (s.toInt?).map Expr.int
  | .string s => some (.sym s)
  | j@(.object _) =>
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
                  | some (.array items) => (exprsOfJson items).map (Expr.app fn)
                  -- an absent "args", or one that is not an array, is
                  -- an empty argument list in the F* entry too.
                  | _                   => some (.app fn [])
              | _ => none
  | _ => none

def exprsOfJson : List Json → Option (List Expr)
  | []      => some []
  | j :: t  =>
      match exprOfJson j, exprsOfJson t with
      | some e, some es => some (e :: es)
      | _, _            => none

end

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

def exprsToJson : List Expr → List Json
  | []      => []
  | e :: t  => exprToJson e :: exprsToJson t

end

end L4Factoidal.MathML
