/-
L4Factoidal.JSONSchema.Validate — JSON Schema validation, ported from
`formal/fstar/JSONSchema.Validate.fst`.

Spec: JSON Schema draft 2020-12 core + validation vocabularies.

TWO DESIGN POINTS carried from the F* module, both of which decide
whether the validator is honest:

1. **The result is THREE-valued**: pass, fail, or UNSUPPORTED. A
   keyword outside the ported slice makes the verdict undetermined
   rather than passing. `vand` lets a definite failure dominate an
   unsupported sibling (a schema that definitely fails still fails);
   `vor` lets a definite pass dominate one (one satisfied branch is
   enough). Both directions matter: collapsing unsupported into pass
   inflates the score, collapsing it into fail deflates it, and
   neither is the truth.

2. **Numbers are EXACT RATIONALS parsed from the JSON lexeme**, never
   floats. A `JNumber` carries its verbatim RFC 8259 text; it reduces
   to `(numerator, denominator)` with a power-of-ten denominator, so
   `multipleOf` and the range keywords are exact.
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.JSONSchema

open L4Factoidal.JSON

/-- Pass, fail, or outside the ported slice. -/
inductive VResult where
  | pass | fail | unsupported
deriving Repr, DecidableEq, Inhabited

/-- Conjunction: a definite failure dominates; otherwise any
    unsupported keyword makes the verdict undetermined. -/
def vand : VResult → VResult → VResult
  | .fail, _ | _, .fail => .fail
  | .unsupported, _ | _, .unsupported => .unsupported
  | _, _ => .pass

/-- Disjunction: a definite pass dominates; otherwise undetermined if
    any branch was unsupported. -/
def vor : VResult → VResult → VResult
  | .pass, _ | _, .pass => .pass
  | .unsupported, _ | _, .unsupported => .unsupported
  | _, _ => .fail

def vall (rs : List VResult) : VResult := rs.foldl vand .pass
def vany (rs : List VResult) : VResult := rs.foldl vor .fail

/-! ## Exact rationals from JSON number lexemes -/

/-- A number as `num / den`, `den` a positive power of ten. -/
abbrev Rat := Int × Nat

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def pow10 : Nat → Nat
  | 0     => 1
  | n + 1 => 10 * pow10 n

/-- Parse a JSON number lexeme to an exact rational. Handles sign,
    fraction and exponent; returns `none` on anything else. -/
def parseRat (s : String) : Option Rat :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _        => (false, cs)
  let ip := cs.takeWhile isDigit
  let rest := cs.dropWhile isDigit
  if ip.isEmpty then none else
  let (fp, rest) := match rest with
    | '.' :: r => (r.takeWhile isDigit, r.dropWhile isDigit)
    | _        => ([], rest)
  let (expNeg, expDigits, rest) := match rest with
    | 'e' :: r | 'E' :: r =>
        match r with
        | '-' :: r2 => (true, r2.takeWhile isDigit, r2.dropWhile isDigit)
        | '+' :: r2 => (false, r2.takeWhile isDigit, r2.dropWhile isDigit)
        | _         => (false, r.takeWhile isDigit, r.dropWhile isDigit)
    | _ => (false, [], rest)
  if !rest.isEmpty then none else
  let digits := ip ++ fp
  let mantissa : Int := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat : Int)) 0
  let e : Nat := expDigits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  let scale := fp.length
  let num := if neg then -mantissa else mantissa
  if expNeg then some (num, pow10 (scale + e))
  else
    -- Multiplying by 10^e can cancel the existing scale.
    if e ≥ scale then some (num * (pow10 (e - scale) : Int), 1)
    else some (num, pow10 (scale - e))

def ratLt (a b : Rat) : Bool := a.1 * (b.2 : Int) < b.1 * (a.2 : Int)
def ratLe (a b : Rat) : Bool := a.1 * (b.2 : Int) ≤ b.1 * (a.2 : Int)
def ratEq (a b : Rat) : Bool := a.1 * (b.2 : Int) == b.1 * (a.2 : Int)

/-- Is `v` an exact integer multiple of `d`? Done on the cross
    product, so no division and no float rounding. -/
def isMultiple (v d : Rat) : Bool :=
  if d.1 == 0 then false
  else
    let n := v.1 * (d.2 : Int)
    let m := d.1 * (v.2 : Int)
    m != 0 && n % m == 0

/-- Is the rational an integer? -/
def isIntegral (r : Rat) : Bool := r.1 % (r.2 : Int) == 0

/-! ## Instance inspection -/

def typeName : Json → String
  | .null     => "null"
  | .bool _   => "boolean"
  | .string _ => "string"
  | .number _ => "number"
  | .array _  => "array"
  | .object _ => "object"

def instRat (v : Json) : Option Rat :=
  match v with
  | .number lex => parseRat lex
  | _           => none

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

/-- JSON equality for `const`/`enum`: numbers compare by VALUE, so
    `1.0` equals `1`, while everything else compares structurally. -/
partial def jsonEq (a b : Json) : Bool :=
  match a, b with
  | .number x, .number y =>
      match parseRat x, parseRat y with
      | some p, some q => ratEq p q
      | _, _ => x == y
  | .null, .null => true
  | .bool x, .bool y => x == y
  | .string x, .string y => x == y
  | .array xs, .array ys =>
      xs.length == ys.length && (xs.zip ys).all (fun (x, y) => jsonEq x y)
  | .object xs, .object ys =>
      xs.length == ys.length &&
      xs.all (fun (k, v) => match (ys.find? (fun (k2, _) => k2 == k)).map (·.2) with
                            | some w => jsonEq v w
                            | none   => false)
  | _, _ => false

/-! ## Keyword validation -/

/-- `type`, accepting a single name or an array of names. The
    `integer` type accepts a number whose VALUE is integral, so `1.0`
    is an integer — a rule that a float-based port gets wrong in the
    other direction. -/
def checkType (spec : Json) (inst : Json) : VResult :=
  let matchOne (n : String) : Bool :=
    if n == "integer" then
      match instRat inst with
      | some r => isIntegral r
      | none   => false
    else n == typeName inst
  match spec with
  | .string n  => if matchOne n then .pass else .fail
  | .array ns  => if ns.any (fun s => match s with
                              | .string n => matchOne n
                              | _ => false) then .pass else .fail
  | _ => .unsupported

private def ratKeyword (spec : Json) (inst : Json) (ok : Rat → Rat → Bool) : VResult :=
  match instRat inst with
  | none => .pass                     -- non-numbers ignore numeric keywords
  | some v =>
      match instRat spec with
      | none   => .unsupported
      | some b => if ok v b then .pass else .fail

/-- Validate one instance against one schema. `true`/`false` schemas
    are the boolean forms from draft 2019-09 onward. -/
partial def validate (schema inst : Json) : VResult :=
  match schema with
  | .bool true  => .pass
  | .bool false => .fail
  | .object ms =>
      vall (ms.map (fun (k, v) =>
        if k == "type" then checkType v inst
        else if k == "const" then (if jsonEq v inst then .pass else .fail)
        else if k == "enum" then
          (match v with
           | .array vs => if vs.any (fun c => jsonEq c inst) then .pass else .fail
           | _         => .unsupported)
        else if k == "minimum" then ratKeyword v inst (fun x b => ratLe b x)
        else if k == "maximum" then ratKeyword v inst (fun x b => ratLe x b)
        else if k == "exclusiveMinimum" then ratKeyword v inst (fun x b => ratLt b x)
        else if k == "exclusiveMaximum" then ratKeyword v inst (fun x b => ratLt x b)
        else if k == "multipleOf" then ratKeyword v inst isMultiple
        else if k == "minLength" then
          (match inst, instRat v with
           | .string s, some (n, 1) => if (s.toList.length : Int) ≥ n then .pass else .fail
           | .string _, _ => .unsupported
           | _, _ => .pass)
        else if k == "maxLength" then
          (match inst, instRat v with
           | .string s, some (n, 1) => if (s.toList.length : Int) ≤ n then .pass else .fail
           | .string _, _ => .unsupported
           | _, _ => .pass)
        else if k == "minItems" then
          (match inst, instRat v with
           | .array a, some (n, 1) => if (a.length : Int) ≥ n then .pass else .fail
           | .array _, _ => .unsupported
           | _, _ => .pass)
        else if k == "maxItems" then
          (match inst, instRat v with
           | .array a, some (n, 1) => if (a.length : Int) ≤ n then .pass else .fail
           | .array _, _ => .unsupported
           | _, _ => .pass)
        else if k == "items" then
          (match inst with
           | .array a => vall (a.map (fun e => validate v e))
           | _        => .pass)
        else if k == "required" then
          (match inst, v with
           | .object _, .array names =>
               vall (names.map (fun n => match n with
                 | .string nm => if (field? nm inst).isSome then .pass else .fail
                 | _          => .unsupported))
           | _, _ => .pass)
        else if k == "properties" then
          (match inst, v with
           | .object _, .object props =>
               vall (props.map (fun (nm, sub) =>
                 match field? nm inst with
                 | some got => validate sub got
                 | none     => .pass))
           | _, _ => .pass)
        else if k == "allOf" then
          (match v with
           | .array ss => vall (ss.map (fun s => validate s inst))
           | _         => .unsupported)
        else if k == "anyOf" then
          (match v with
           | .array ss => vany (ss.map (fun s => validate s inst))
           | _         => .unsupported)
        else if k == "not" then
          (match validate v inst with
           | .pass => .fail
           | .fail => .pass
           | .unsupported => .unsupported)
        -- Annotation-only keywords never affect the verdict.
        else if ["title", "description", "default", "$comment", "examples",
                 "$schema", "$id"].contains k then .pass
        else .unsupported))
  | _ => .unsupported

end L4Factoidal.JSONSchema
