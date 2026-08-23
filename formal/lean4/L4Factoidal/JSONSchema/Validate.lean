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
import L4Factoidal.Regex.XPath

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

/-! ## `$ref` resolution

A `$ref` is a JSON POINTER into the schema DOCUMENT, so the validator
carries the document root alongside the sub-schema being applied. A
REMOTE ref (one naming another document) is `unsupported` rather than
ignored: pretending a remote schema imposes nothing would pass every
instance against it.

`fuel` bounds the recursion. `$ref` makes a schema a graph, and a
recursive schema (`{"$ref": "#"}` applied to a nested instance) walks
it as deep as the instance is; a cycle with no instance to consume
would otherwise not terminate. Running out of fuel is `unsupported` —
no verdict — never a pass. -/

/-- Split a JSON pointer into its unescaped tokens. `~1` is `/` and
    `~0` is `~`, in that order (RFC 6901 §3); unescaping them the other
    way round turns `~01` into `/` instead of `~1`. -/
def pointerTokens (p : String) : List String :=
  let unesc := fun (t : String) =>
    String.intercalate "~" ((String.intercalate "/" (t.splitOn "~1")).splitOn "~0")
  match p.splitOn "/" with
  | _ :: rest => rest.map unesc
  | []        => []

def resolvePointer (root : Json) (toks : List String) : Option Json :=
  toks.foldl (fun acc t =>
    acc.bind (fun j => match j with
      | .object ms => (ms.find? (fun (k, _) => k == t)).map (·.2)
      | .array vs  => t.toNat?.bind (fun i => vs[i]?)
      | _          => none)) (some root)

/-- Percent-decode a pointer fragment. A `$ref` is a URI, so its
    fragment is URI-escaped BEFORE it is a JSON pointer:
    `#/definitions/foo%22bar` names the member `foo"bar`. Tokenising
    without decoding looks for a member spelled with the escape and
    finds nothing. -/
def percentDecode (s : String) : String :=
  let hex := fun (c : Char) =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go : Nat → List Char → List Char
    | 0,        cs => cs
    | fuel + 1, cs =>
        match cs with
        | '%' :: a :: b :: rest =>
            (match hex a, hex b with
             | some x, some y => Char.ofNat (x * 16 + y) :: go fuel rest
             | _, _           => '%' :: go fuel (a :: b :: rest))
        | c :: rest => c :: go fuel rest
        | []        => []
  String.ofList (go s.length s.toList)

/-- The registry a `$ref` to ANOTHER document resolves against: an
    absolute URI (without its fragment) to that document's root. -/
abbrev Registry := List (String × Json)

/-- Resolve a `$ref`. `#` is the root itself; `#/a/b` is a pointer into
    it; an absolute URI is looked up in the registry and then
    pointed into. -/
def resolveRefIn (reg : Registry) (root : Json) (r : String) : Option Json :=
  let r := percentDecode r
  if r == "#" then some root
  else if r.startsWith "#/" then resolvePointer root (pointerTokens r)
  else
    -- Split the URI from its fragment, then find the document.
    let (base, frag) := match r.splitOn "#" with
      | [b]       => (b, "")
      | b :: rest => (b, "#" ++ String.intercalate "#" rest)
      | []        => (r, "")
    match (reg.find? (fun (u, _) => u == base)).map (·.2) with
    | none => none
    | some doc =>
        if frag == "" || frag == "#" then some doc
        else if frag.startsWith "#/" then resolvePointer doc (pointerTokens frag)
        else none

def resolveRef (root : Json) (r : String) : Option Json :=
  resolveRefIn [] root r

/-- Draft-07 keywords that carry no assertion: annotations, and the
    `definitions` container whose members are only reached through a
    `$ref`. Listing them explicitly is what keeps `unsupported`
    meaning "not implemented" rather than "not an assertion". -/
def annotationKeywords : List String :=
  ["title", "description", "default", "$comment", "examples", "$schema",
   "$id", "definitions", "readOnly", "writeOnly", "contentMediaType",
   "contentEncoding", "format"]

/-- Validate one instance against one schema, in the context of the
    document `root`. `true`/`false` schemas are the boolean forms from
    draft 2019-09 onward. -/
partial def validateIn (reg : Registry) (root : Json) (fuel : Nat)
    (schema inst : Json) : VResult :=
  match fuel with
  | 0 => .unsupported
  | fuel + 1 =>
  let rec' := validateIn reg root fuel
  match schema with
  | .bool true  => .pass
  | .bool false => .fail
  | .object ms =>
      -- `additionalProperties` and `additionalItems` are defined
      -- RELATIVE to their siblings, so they need the whole object.
      let props : List String := match field? "properties" schema with
        | some (.object ps) => ps.map (fun (k, _) => k)
        | _ => []
      let patProps : List String := match field? "patternProperties" schema with
        | some (.object ps) => ps.map (fun (k, _) => k)
        | _ => []
      let itemsIsTuple := match field? "items" schema with
        | some (.array _) => true
        | _ => false
      let tupleLen := match field? "items" schema with
        | some (.array ss) => ss.length
        | _ => 0
      -- Draft-07 §8.3: when `$ref` is present, EVERY other keyword in
      -- the same schema object is IGNORED. Applying them alongside
      -- the referenced schema makes a document stricter than it says
      -- it is, and the suite's `ref.json` measures exactly that.
      let hasRef := (field? "$ref" schema).isSome
      vall (ms.map (fun (k, v) =>
        if hasRef && k != "$ref" then .pass
        else if k == "$ref" then
          (match v with
           | .string r =>
               (match resolveRefIn reg root r with
                | some sub => rec' sub inst
                | none     => .unsupported)
           | _ => .unsupported)
        else if k == "type" then checkType v inst
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
        else if k == "pattern" then
          (match inst, v with
           | .string s, .string pat =>
               -- UNANCHORED, per draft-07: the pattern must match
               -- SOMEWHERE in the string, not the whole of it.
               if L4Factoidal.Regex.regexMatch s pat "" then .pass else .fail
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
        else if k == "uniqueItems" then
          (match inst, v with
           | .array a, .bool true =>
               if (a.zipIdx).all (fun (x, i) =>
                    (a.zipIdx).all (fun (y, j) => i == j || !(jsonEq x y)))
               then .pass else .fail
           | .array _, .bool false => .pass
           | .array _, _ => .unsupported
           | _, _ => .pass)
        else if k == "contains" then
          (match inst with
           | .array a =>
               if a.any (fun e => rec' v e == .pass) then .pass
               else if a.any (fun e => rec' v e == .unsupported) then .unsupported
               else .fail
           | _ => .pass)
        else if k == "items" then
          (match inst, v with
           -- The TUPLE form: schema i applies to item i, and any item
           -- past the tuple is left to `additionalItems`.
           | .array a, .array ss =>
               vall ((a.zip ss).map (fun (e, sub) => rec' sub e))
           | .array a, _ => vall (a.map (fun e => rec' v e))
           | _, _ => .pass)
        else if k == "additionalItems" then
          (match inst with
           | .array a =>
               if !itemsIsTuple then .pass
               else vall ((a.drop tupleLen).map (fun e => rec' v e))
           | _ => .pass)
        else if k == "required" then
          (match inst, v with
           | .object _, .array names =>
               vall (names.map (fun n => match n with
                 | .string nm => if (field? nm inst).isSome then .pass else .fail
                 | _          => .unsupported))
           | _, _ => .pass)
        else if k == "minProperties" then
          (match inst, instRat v with
           | .object o, some (n, 1) => if (o.length : Int) ≥ n then .pass else .fail
           | .object _, _ => .unsupported
           | _, _ => .pass)
        else if k == "maxProperties" then
          (match inst, instRat v with
           | .object o, some (n, 1) => if (o.length : Int) ≤ n then .pass else .fail
           | .object _, _ => .unsupported
           | _, _ => .pass)
        else if k == "properties" then
          (match inst, v with
           | .object _, .object ps =>
               vall (ps.map (fun (nm, sub) =>
                 match field? nm inst with
                 | some got => rec' sub got
                 | none     => .pass))
           | _, _ => .pass)
        else if k == "patternProperties" then
          (match inst, v with
           | .object o, .object ps =>
               vall (o.flatMap (fun (nm, got) =>
                 ps.filterMap (fun (pat, sub) =>
                   if L4Factoidal.Regex.regexMatch nm pat "" then some (rec' sub got)
                   else none)))
           | _, _ => .pass)
        else if k == "additionalProperties" then
          (match inst with
           | .object o =>
               vall (o.filterMap (fun (nm, got) =>
                 if props.contains nm then none
                 else if patProps.any (fun pat =>
                          L4Factoidal.Regex.regexMatch nm pat "") then none
                 else some (rec' v got)))
           | _ => .pass)
        else if k == "propertyNames" then
          (match inst with
           | .object o => vall (o.map (fun (nm, _) => rec' v (.string nm)))
           | _ => .pass)
        else if k == "dependencies" then
          (match inst, v with
           | .object _, .object ds =>
               vall (ds.map (fun (nm, dep) =>
                 if (field? nm inst).isNone then .pass
                 else match dep with
                   -- The ARRAY form lists names that must also be
                   -- present; any other form is a schema to apply.
                   | .array names =>
                       vall (names.map (fun n => match n with
                         | .string req =>
                             if (field? req inst).isSome then .pass else .fail
                         | _ => .unsupported))
                   | sub => rec' sub inst))
           | _, _ => .pass)
        else if k == "allOf" then
          (match v with
           | .array ss => vall (ss.map (fun s => rec' s inst))
           | _         => .unsupported)
        else if k == "anyOf" then
          (match v with
           | .array ss => vany (ss.map (fun s => rec' s inst))
           | _         => .unsupported)
        else if k == "oneOf" then
          (match v with
           | .array ss =>
               let rs := ss.map (fun s => rec' s inst)
               if rs.any (· == .unsupported) then .unsupported
               else if (rs.filter (· == .pass)).length == 1 then .pass else .fail
           | _ => .unsupported)
        else if k == "not" then
          (match rec' v inst with
           | .pass => .fail
           | .fail => .pass
           | .unsupported => .unsupported)
        else if k == "if" then
          -- `if` asserts nothing on its own: the verdict comes from
          -- the branch it selects. An UNSUPPORTED condition leaves the
          -- branch unknown, so the whole conditional is unsupported.
          (match rec' v inst with
           | .pass =>
               (match field? "then" schema with
                | some t => rec' t inst
                | none   => .pass)
           | .fail =>
               (match field? "else" schema with
                | some e => rec' e inst
                | none   => .pass)
           | .unsupported => .unsupported)
        else if k == "then" || k == "else" then
          -- Applied by the `if` branch above; alone they assert
          -- nothing (draft-07 §6.6.2/§6.6.3).
          (if (field? "if" schema).isSome then .pass else .pass)
        else if annotationKeywords.contains k then .pass
        else .unsupported))
  | _ => .unsupported

/-- Validate an instance against a whole schema DOCUMENT, with a
    registry of other documents its `$ref`s may name.

    The document REGISTERS ITSELF under its own `$id`, so a schema
    that refers to itself by absolute URI resolves without the caller
    supplying it. -/
def validateWith (reg : Registry) (schema inst : Json) : VResult :=
  let selfReg := match field? "$id" schema with
    | some (.string i) =>
        let base := match i.splitOn "#" with
          | b :: _ => b
          | []     => i
        [(base, schema)]
    | _ => []
  validateIn (selfReg ++ reg) schema 64 schema inst

/-- Validate an instance against a whole schema DOCUMENT. -/
def validate (schema inst : Json) : VResult := validateWith [] schema inst

end L4Factoidal.JSONSchema
