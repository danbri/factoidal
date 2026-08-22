/-
L4Factoidal.JSON.Value — the JSON value tree (RFC 8259).

Port of `formal/fstar/Parser.JSON.fst`'s `json_val` type and its
accessor functions (`json_get_field` / `json_get_string` / ...).

RFC 8259 (JSON), https://www.rfc-editor.org/rfc/rfc8259 :
  - §1 Introduction: the six JSON value kinds (object, array, number,
    string, `true`/`false`, `null`).
  - §4 Objects: "The names within an object SHOULD be unique" — SHOULD,
    not MUST, so a conforming parser must accept duplicates. This port
    keeps `object` as an ORDERED `List (String × Json)`, preserving
    both key order and duplicate keys exactly as the input had them —
    the same choice `Parser.JSON.fst`'s `JObject` makes, and the shape
    the later JSON-LD / SPARQL Results JSON ports rely on for
    `head.vars`-style ordered field access.
  - §6 Numbers: the NUMBER-AS-STRING choice. This port stores the
    validated RFC 8259 number lexeme verbatim rather than converting
    to a numeric type (`Parser.JSON.fst`'s `JNumber of string` — see
    that module's header comment). Downstream JSON-LD / SPARQL Results
    JSON code depends on exact lexical preservation; do not add a
    numeric conversion here.
-/

namespace L4Factoidal.JSON

/-- A JSON value tree. Port of `Parser.JSON.fst`'s `json_val`:
`JNull → null`, `JBool → bool`, `JString → string`, `JNumber → number`
(lexeme kept verbatim, RFC 8259 §6), `JArray → array`,
`JObject → object` (ordered, duplicates preserved — see module
header). -/
inductive Json where
  | null   : Json
  | bool   : Bool → Json
  | string : String → Json
  | number : String → Json
  | array  : List Json → Json
  | object : List (String × Json) → Json
  deriving Repr

namespace Json

/-! ## `DecidableEq` — hand-written, not derived

`deriving DecidableEq` does not apply to `Json`: it is a NESTED
inductive type (`array`/`object` recurse through `List`), and Lean's
`DecidableEq` deriving handler does not support that shape (confirmed
against this toolchain: even the minimal
`inductive Tree | leaf : Nat → Tree | node : List Tree → Tree` fails
the same way). The `induction` tactic also refuses nested inductive
types ("Consider using the `cases` tactic instead"), so the usual
"derive a boolean `beq`, prove it sound by `induction`" recipe does
not apply either.

The decision procedure below is written directly by structural
pattern matching (which the equation compiler DOES support for nested
inductive types — only the `induction` *tactic* is the gap), mirroring
how Lean's own derived instances are shaped: one mutually recursive
`Decidable` per level (`Json`, `List Json`, `List (String × Json)`),
matched-constructor cases combine sub-decisions, and mismatched
constructors close by `nomatch` on the (absurd) equality. Per the
project's own pitfall #1 (`skills/factoidal-lean-basics/SKILL.md`):
`DecidableEq`, not `deriving BEq` — `BEq`/`==` for `Json` comes for
free afterwards via `instBEqOfDecidableEq`, and IS lawful. -/

mutual

private def decEqJson (a b : Json) : Decidable (a = b) :=
  match a, b with
  | .null, .null => isTrue rfl
  | .bool b1, .bool b2 =>
    if h : b1 = b2 then isTrue (by rw [h]) else isFalse (fun he => h (by injection he))
  | .string s1, .string s2 =>
    if h : s1 = s2 then isTrue (by rw [h]) else isFalse (fun he => h (by injection he))
  | .number n1, .number n2 =>
    if h : n1 = n2 then isTrue (by rw [h]) else isFalse (fun he => h (by injection he))
  | .array xs, .array ys =>
    match decEqJsonList xs ys with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun he => h (by injection he))
  | .object fs, .object gs =>
    match decEqJsonFields fs gs with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun he => h (by injection he))
  | .null, .bool _ | .null, .string _ | .null, .number _ | .null, .array _ | .null, .object _
  | .bool _, .null | .bool _, .string _ | .bool _, .number _ | .bool _, .array _ | .bool _, .object _
  | .string _, .null | .string _, .bool _ | .string _, .number _ | .string _, .array _ | .string _, .object _
  | .number _, .null | .number _, .bool _ | .number _, .string _ | .number _, .array _ | .number _, .object _
  | .array _, .null | .array _, .bool _ | .array _, .string _ | .array _, .number _ | .array _, .object _
  | .object _, .null | .object _, .bool _ | .object _, .string _ | .object _, .number _ | .object _, .array _ =>
    isFalse (fun he => nomatch he)

private def decEqJsonList (xs ys : List Json) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match decEqJson x y with
    | isFalse h => isFalse (fun he => h (by injection he))
    | isTrue h =>
      match decEqJsonList xs ys with
      | isTrue h2 => isTrue (by rw [h, h2])
      | isFalse h2 => isFalse (fun he => h2 (by injection he))
  | [], _ :: _ => isFalse (fun he => nomatch he)
  | _ :: _, [] => isFalse (fun he => nomatch he)

private def decEqJsonFields (fs gs : List (String × Json)) : Decidable (fs = gs) :=
  match fs, gs with
  | [], [] => isTrue rfl
  | (k1, v1) :: fs, (k2, v2) :: gs =>
    if hk : k1 = k2 then
      match decEqJson v1 v2 with
      | isTrue hv =>
        match decEqJsonFields fs gs with
        | isTrue hr => isTrue (by rw [hk, hv, hr])
        | isFalse hr => isFalse (by intro he; apply hr; injection he with _ htl)
      | isFalse hv =>
        isFalse (by
          intro he; apply hv
          injection he with hhd _
          injection hhd with _ hv2)
    else
      isFalse (by
        intro he; apply hk
        injection he with hhd _
        injection hhd with hk2 _)
  | [], _ :: _ => isFalse (fun he => nomatch he)
  | _ :: _, [] => isFalse (fun he => nomatch he)

end

instance : DecidableEq Json := decEqJson

/-! ## Size — port of `json_size` / `json_size_items` / `json_size_fields`

One unit per value, plus one unit per array element and object member
visited. Not needed for parsing in this port (the parser is fuelled by
remaining input length, matching `Parser.JSON.fst`), but kept for
parity with the F* module, whose downstream consumers (e.g. the
JSON-LD port) use it to derive a fuel bound for tree-recursive
processing over an already-parsed value. -/

mutual

def size : Json → Nat
  | null       => 1
  | bool _     => 1
  | string _   => 1
  | number _   => 1
  | array xs   => 1 + sizeItems xs
  | object fs  => 1 + sizeFields fs

def sizeItems : List Json → Nat
  | []       => 0
  | hd :: tl => 1 + size hd + sizeItems tl

def sizeFields : List (String × Json) → Nat
  | []            => 0
  | (_, v) :: tl  => 1 + size v + sizeFields tl

end

/-! ## Field access — port of `json_get_field` and friends -/

/-- Field lookup by name on an object: the FIRST matching member.
RFC 8259 §4 permits duplicate names (see module header); first-match
is `Parser.JSON.fst`'s `json_get_field` convention
(`List.Tot.find (fun kv -> fst kv = key)`). `none` for a non-object or
an absent key. -/
def field? : Json → String → Option Json
  | object fields, key => (fields.find? (fun kv => kv.1 == key)).map Prod.snd
  | _,             _   => none

/-- Port of `json_get_string` composed with `json_get_field`. -/
def asString? : Json → Option String
  | string s => some s
  | _        => none

/-- Port of `json_get_bool` composed with `json_get_field`. -/
def asBool? : Json → Option Bool
  | bool b => some b
  | _      => none

/-- Port of `json_get_array` composed with `json_get_field`. -/
def asArray? : Json → Option (List Json)
  | array items => some items
  | _           => none

/-- `obj.getString? key`: port of `json_get_string key obj`. -/
def getString? (j : Json) (key : String) : Option String :=
  (j.field? key).bind asString?

/-- `obj.getBool? key`: port of `json_get_bool key obj`. -/
def getBool? (j : Json) (key : String) : Option Bool :=
  (j.field? key).bind asBool?

/-- `obj.getArray? key`: port of `json_get_array key obj`. -/
def getArray? (j : Json) (key : String) : Option (List Json) :=
  (j.field? key).bind asArray?

/-- A field's array value, string elements only, non-string elements
dropped. Port of `json_get_string_array` — used by SPARQL Results
JSON's `head.vars` ingestion (`Parser.JSONResults.fst`, migrated onto
this module per that file's header comment, issue #310). -/
def getStringArray? (j : Json) (key : String) : Option (List String) :=
  match j.field? key with
  | some (array items) => some (items.filterMap asString?)
  | _                   => none

end Json
end L4Factoidal.JSON
