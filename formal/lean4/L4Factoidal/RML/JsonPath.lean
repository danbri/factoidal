/-
L4Factoidal.RML.JsonPath — the JSONPath SUBSET an RML `rml:iterator`
and `rml:reference` need, over `JSON.Json`.

## The subset, stated in full

    Path ::= '$' Step*
    Step ::= '.' Name | '[' '*' ']' | '[' Digits ']' | "['" Name "']"

`Name` is a run of characters that is not `.` or `[`.

ANYTHING ELSE fails to parse, and `evalPath` on an unparsed path
yields NOTHING rather than guessing. That distinction carries: a
mapping whose reference this module cannot read produces no term,
which is what RML says an unresolved reference does — not an empty
string, and not a silent match.

The RML-Core corpus writes `$.students[*]`, `$.ID`, `$[*]` and one
`$.students[*]]`, which is malformed and is a negative test. Nothing
in it needs a filter, a slice, or a recursive descent, and adding
those untested would be code nobody has measured.
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.RML

open L4Factoidal.JSON

inductive JStep where
  | field    (name : String)
  | wildcard
  | index    (i : Nat)
deriving Repr, DecidableEq, Inhabited

private def isNameChar (c : Char) : Bool := c != '.' && c != '['

/-- Parse a path. `none` for anything outside the subset. -/
def parseJsonPath (p : String) : Option (List JStep) :=
  let rec go (acc : List JStep) : Nat → List Char → Option (List JStep)
    | 0,      _  => none
    | _,      [] => some acc
    | fuel + 1, '.' :: rest =>
        let name := rest.takeWhile isNameChar
        if name.isEmpty then none
        else go (acc ++ [.field (String.ofList name)]) fuel (rest.dropWhile isNameChar)
    | fuel + 1, '[' :: rest =>
        (match rest with
         | '*' :: ']' :: tl => go (acc ++ [.wildcard]) fuel tl
         | '\'' :: tl =>
             let name := tl.takeWhile (· != '\'')
             (match tl.dropWhile (· != '\'') with
              | '\'' :: ']' :: tl2 => go (acc ++ [.field (String.ofList name)]) fuel tl2
              | _ => none)
         | _ =>
             let ds := rest.takeWhile (fun c => '0' ≤ c && c ≤ '9')
             (match rest.dropWhile (fun c => '0' ≤ c && c ≤ '9') with
              | ']' :: tl =>
                  if ds.isEmpty then none
                  else go (acc ++ [.index ((String.ofList ds).toNat!)]) fuel tl
              | _ => none))
    | _ + 1,  _  => none
  match p.toList with
  | '$' :: rest => go [] (rest.length + 1) rest
  | _           => none

/-- Every value a path selects, in document order. -/
def evalSteps : List JStep → Json → List Json
  | [],           j => [j]
  | step :: rest, j =>
      let here : List Json := match step, j with
        | .field n,  .object ms => (ms.filter (fun (k, _) => k == n)).map (·.2)
        | .wildcard, .array vs  => vs
        | .wildcard, .object ms => ms.map (·.2)
        | .index i,  .array vs  => (vs[i]?).toList
        | _, _ => []
      here.flatMap (evalSteps rest)

/-- A path applied to a document. An UNPARSED path selects nothing. -/
def evalPath (p : String) (j : Json) : List Json :=
  match parseJsonPath p with
  | none       => []
  | some steps => evalSteps steps j

end L4Factoidal.RML
