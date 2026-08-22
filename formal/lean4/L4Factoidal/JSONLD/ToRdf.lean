/-
L4Factoidal.JSONLD.ToRdf — JSON-LD 1.1 to RDF.

Port of the toRdf half of `formal/fstar/Parser.JSONLD.fst`.

Specifications implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §8.2 Deserialize JSON-LD to RDF Algorithm — `datasetOfJson` and the
    node/property walk below;
  * §8.3 Object to RDF Conversion — `valueObjectToTerm`, `scalarToTerm`,
    `typeTerm`;
  * §8.4 List to RDF Conversion — `expandList`, one `rdf:first`/
    `rdf:rest` cell per original `@list` array member;
  * §8.6 Data Round Tripping — `numberCanonicalize` (the canonical
    `xsd:double` lexical form and the integer-versus-double default
    datatype promotion) and the `rdfDirection` option
    (`RdfDirectionMode`);
  * RFC 8785 JSON Canonicalization Scheme — `jcsDocument`, used for
    `@json` literals (`rdf:JSON`).

INPUT IS EXPANDED FORM ONLY: an array of node objects whose keys are
absolute IRIs or keywords, and whose property values are arrays of node
objects / node references / value objects / list objects.
`JSONLD.Expand.expand` produces exactly that shape.

## Deliberate exclusions, matching the F* source

  * **Generalized RDF.** A blank-node PREDICATE (`"_:property"` as an
    expanded property key, or an `@vocab` of `"_:"`) is DROPPED rather
    than emitted. §8.2's answer is "keep only when the produce
    generalized RDF flag is set"; this codebase's N-Quads grammar makes
    a blank-node predicate inexpressible either way, so dropping is both
    the spec's common case and the only representable one.
  * **Duplicate-triple suppression.** None: the house parsers keep
    duplicates, and `RDF.Graph` comparison is by set semantics anyway.
  * `@index` produces no triples (it is metadata).

## Blank node identifiers

Allocated from a threaded counter (§8.2's "generate blank node
identifier"), prefixed `_jld_anon` to stay visually distinct from
document-supplied `_:` labels. Labels are stored WITHOUT the `_:`
prefix, matching `RDF.Core.BNodeId`; `Syntax.NQuads` re-adds it.
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Serialize
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.Graph
import L4Factoidal.JSONLD.Expand

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON
open L4Factoidal.RDF

/-! ## RDF vocabulary constants -/

def rdfTypeIri      : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩
def rdfFirstIri     : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#first", rfl⟩
def rdfRestIri      : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", rfl⟩
def rdfNilIri       : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", rfl⟩
def rdfJsonIri      : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON", rfl⟩
def rdfValueIri     : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#value", rfl⟩
def rdfDirectionIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#direction", rfl⟩
def rdfLanguageIri  : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#language", rfl⟩

/-! ## Number lexeme decomposition

`numberParts` normalises an RFC 8259 number lexeme into sign, integer
digits, fraction digits, and exponent. Both the RFC 8785 (JCS) number
serialiser and §8.6's canonical `xsd:double` form need exactly this
decomposition, so — as in the F* source — they share one pass. -/

structure NumParts where
  neg        : Bool
  intDigits  : List Char
  fracDigits : List Char
  exp        : Int
  deriving Repr

def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (if '0' ≤ c && c ≤ '9' then c.toNat - 48 else 0)) 0

def numberParts (lexeme : String) : NumParts :=
  let cs0 := lexeme.toList
  let (neg, cs) := match cs0 with | '-' :: r => (true, r) | _ => (false, cs0)
  let (mant, expPart) :=
    match cs.findIdx? (fun c => c == 'e' || c == 'E') with
    | some i => (cs.take i, cs.drop (i + 1))
    | none   => (cs, [])
  let (ip, fp) :=
    match mant.findIdx? (· == '.') with
    | some i => (mant.take i, mant.drop (i + 1))
    | none   => (mant, [])
  let e : Int :=
    match expPart with
    | '+' :: ds => (digitsToNat ds : Int)
    | '-' :: ds => -(digitsToNat ds : Int)
    | ds        => (digitsToNat ds : Int)
  { neg := neg, intDigits := ip, fracDigits := fp, exp := e }

/-- A string of `k` `'0'` characters. -/
def zeros (k : Nat) : String := String.ofList (List.replicate k '0')

/-- The normalised form both serialisers work from: the significant
digits (no leading or trailing zeros) and the decimal exponent `n` with
`value = 0.<digits> * 10^n`. `none` when the value is zero. -/
structure NumNorm where
  neg     : Bool
  digits  : List Char
  /-- `value = digits (as an integer) * 10 ^ expTotal`. -/
  expTotal : Int
  deriving Repr

def normalizeNumber (lexeme : String) : Option NumNorm :=
  let p := numberParts lexeme
  let combined := p.intDigits ++ p.fracDigits
  let afterLead := combined.dropWhile (· == '0')
  if afterLead.isEmpty then none
  else
    -- Strip trailing zeros, moving them into the exponent.
    let rev := afterLead.reverse.dropWhile (· == '0')
    let digits := rev.reverse
    let tz := afterLead.length - digits.length
    some { neg := p.neg, digits := digits,
           expTotal := p.exp - (p.fracDigits.length : Int) + (tz : Int) }

/-! ## Shortest round-trip binary64 formatting (RFC 8785 §3.2.2.3)

A pure exact-integer implementation — no float type, no host call-out.
Used ONLY for a JSON-literal number whose significant-digit count
exceeds 15: such a lexeme carries more digits than distinguish adjacent
binary64 doubles, so its canonical form is the shortest decimal of its
NEAREST double, not a notation conversion of its own digits.

Method (Steele & White free-format, linear-search variant):
  1. `dtoaToDouble`: decimal `a * 10^pdec` to the nearest binary64
     `m * 2^q`, round-half-to-even, by exact big-integer arithmetic
     (Lean `Nat`/`Int` are arbitrary precision);
  2. `dtoaTry`: for `p = 1..17`, correctly round that double to `p`
     significant decimal digits and test whether the `p`-digit value
     maps BACK to the same `(m, q)`; the first `p` that round-trips is
     the shortest.

SCOPE: the binary64 normal range. Subnormal/overflow corner rounding is
not separately modelled, and the >15-digit gate keeps ordinary fixtures
out of this path entirely. -/

def pow2 (k : Nat) : Nat := 2 ^ k
def pow10 (k : Nat) : Nat := 10 ^ k

def bitlen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- Round `numr / denr` half-to-even. -/
def roundHE (numr : Nat) (denr : Nat) : Nat :=
  if denr == 0 then 0
  else
    let f := numr / denr
    let r := numr % denr
    let twice := 2 * r
    if twice < denr then f
    else if twice > denr then f + 1
    else if f % 2 == 0 then f else f + 1

/-- `2^e2 * den ≤ num`, for any integer `e2`. -/
def pow2Le (e2 : Int) (den num : Nat) : Bool :=
  if e2 ≥ 0 then pow2 e2.toNat * den ≤ num else den ≤ num * pow2 (-e2).toNat

/-- `10^b * den ≤ num`, for any integer `b`. -/
def pow10Le (b : Int) (den num : Nat) : Bool :=
  if b ≥ 0 then pow10 b.toNat * den ≤ num else den ≤ num * pow10 (-b).toNat

def adj2Down (e2 : Int) (den num : Nat) : Nat → Int
  | 0 => e2
  | fuel + 1 => if pow2Le e2 den num then e2 else adj2Down (e2 - 1) den num fuel

def adj2Up (e2 : Int) (den num : Nat) : Nat → Int
  | 0 => e2
  | fuel + 1 => if pow2Le (e2 + 1) den num then adj2Up (e2 + 1) den num fuel else e2

def adj10Down (b : Int) (den num : Nat) : Nat → Int
  | 0 => b
  | fuel + 1 => if pow10Le b den num then b else adj10Down (b - 1) den num fuel

def adj10Up (b : Int) (den num : Nat) : Nat → Int
  | 0 => b
  | fuel + 1 => if pow10Le (b + 1) den num then adj10Up (b + 1) den num fuel else b

/-- `a * 10^pdec` to the nearest binary64, as `(m, q)` with
`value ≈ m * 2^q` and `m ∈ [2^52, 2^53)`. -/
def dtoaToDouble (a : Nat) (pdec : Int) : Nat × Int :=
  if a == 0 then (0, 0)
  else
    let num : Nat := if pdec ≥ 0 then a * pow10 pdec.toNat else a
    let den : Nat := if pdec ≥ 0 then 1 else pow10 (-pdec).toNat
    let guess : Int := (bitlen num : Int) - (bitlen den : Int)
    let e2a := adj2Up guess den num 8
    let e2  := adj2Down e2a den num 8
    let shift : Int := 52 - e2
    let pnum : Nat := if shift ≥ 0 then num * pow2 shift.toNat else num
    let pden : Nat := if shift ≥ 0 then den else den * pow2 (-shift).toNat
    let m := roundHE pnum pden
    if m ≥ pow2 53 then (pow2 52, e2 + 1 - 52) else (m, e2 - 52)

/-- Round the double `m * 2^q` to `p` significant decimal digits,
returning `(c, dexp)` with `value ≈ c * 10^dexp`. -/
def dtoaRoundToP (m : Nat) (q : Int) (p : Nat) : Nat × Int :=
  let numd : Nat := if q ≥ 0 then m * pow2 q.toNat else m
  let dend : Nat := if q ≥ 0 then 1 else pow2 (-q).toNat
  let g10 : Int := ((bitlen numd : Int) - (bitlen dend : Int)) * 3 / 10
  let b0 := adj10Down g10 dend numd 40
  let flog10 := adj10Up b0 dend numd 40
  let bexp := flog10 + 1
  let kk := bexp - (p : Int)
  let rnum : Nat := if kk ≥ 0 then numd else numd * pow10 (-kk).toNat
  let rden : Nat := if kk ≥ 0 then dend * pow10 kk.toNat else dend
  let c := roundHE rnum rden
  if c == pow10 p then (c / 10, kk + 1) else (c, kk)

def dtoaMkLexeme (neg : Bool) (c : Nat) (dexp : Int) : String :=
  (if neg then "-" else "") ++ toString c ++ "e" ++ toString dexp

/-- Search `p = 1..17` for the shortest `p`-digit rounding that reads
back to the same double. -/
def dtoaTry (neg : Bool) (m : Nat) (q : Int) (p : Nat) : Nat → String
  | 0 => let (c, dexp) := dtoaRoundToP m q p; dtoaMkLexeme neg c dexp
  | fuel + 1 =>
    let (c, dexp) := dtoaRoundToP m q p
    let (m2, q2) := dtoaToDouble c dexp
    if m2 == m && q2 == q then dtoaMkLexeme neg c dexp
    else dtoaTry neg m q (p + 1) fuel

def dtoaShortest (neg : Bool) (a : Nat) (pdec : Int) : String :=
  let (m, q) := dtoaToDouble a pdec
  dtoaTry neg m q 1 20

/-! ## RFC 8785 §3.2.2.3 — JCS number serialization

ECMAScript `Number::toString` applied to the JSON number's value. With
`digits` the significant digits, `k = digits.length`, and `n` the
decimal exponent such that the value is `0.<digits> * 10^n`:
  * `k ≤ n ≤ 21`: `digits` then `n - k` zeros, no decimal point;
  * `0 < n ≤ 21`: the first `n` digits, `"."`, then the rest;
  * `-6 < n ≤ 0`: `"0."`, then `-n` zeros, then `digits`;
  * otherwise: exponential — first digit, `"."` and the rest (if more
    than one digit), `"e"`, an EXPLICIT sign, and `n - 1`. -/
def jcsNumberFmt (lexeme : String) : String :=
  match normalizeNumber lexeme with
  -- The value is zero. JCS §3.2.2.3: negative zero also serializes
  -- as "0".
  | none => "0"
  | some nn =>
    let k : Int := nn.digits.length
    let n : Int := nn.expTotal + k
    let signStr := if nn.neg then "-" else ""
    let ds := String.ofList nn.digits
    if k ≤ n && n ≤ 21 then signStr ++ ds ++ zeros (n - k).toNat
    else if 0 < n && n ≤ 21 then
      signStr ++ String.ofList (nn.digits.take n.toNat)
        ++ "." ++ String.ofList (nn.digits.drop n.toNat)
    else if (-6 : Int) < n && n ≤ 0 then signStr ++ "0." ++ zeros (-n).toNat ++ ds
    else
      let mantissa :=
        if k ≤ 1 then ds
        else String.ofList (nn.digits.take 1) ++ "." ++ String.ofList (nn.digits.drop 1)
      let e := n - 1
      let expStr := if e ≥ 0 then "+" ++ toString e else toString e
      signStr ++ mantissa ++ "e" ++ expStr

/-- The public JCS number canonicaliser. A lexeme with at most 15
significant digits is already its own shortest round-trip form and is
formatted directly; more than that needs the actual nearest-binary64
shortest decimal. -/
def jcsNumber (lexeme : String) : String :=
  match normalizeNumber lexeme with
  | none => "0"
  | some nn =>
    if nn.digits.length ≤ 15 then jcsNumberFmt lexeme
    else jcsNumberFmt (dtoaShortest nn.neg (digitsToNat nn.digits) nn.expTotal)

/-- JCS string: double-quoted, escaped per RFC 8785 §3.2.2.2 — the same
mandatory set RFC 8259 §7 defines, which `JSON.escapeString` already
implements. -/
def jcsString (s : String) : String := "\"" ++ escapeString s ++ "\""

/-- Insertion-sort an object's members by key (RFC 8785 §3.2.3, "sort by
code point"). -/
def jcsInsertSorted (kv : String × Json) : List (String × Json) → List (String × Json)
  | [] => [kv]
  | (k2, v2) :: rest =>
    if strLt kv.1 k2 then kv :: (k2, v2) :: rest else (k2, v2) :: jcsInsertSorted kv rest

def jcsSortFields : List (String × Json) → List (String × Json)
  | [] => []
  | kv :: rest => jcsInsertSorted kv (jcsSortFields rest)

mutual

/-- The JCS document: object keys sorted, array order preserved, the
tightest separators (`,` and `:` with nothing else). -/
def jcsSerialize : Json → Nat → String
  | _, 0 => "null"
  | .null, _ => "null"
  | .bool b, _ => if b then "true" else "false"
  | .number lex, _ => jcsNumber lex
  | .string s, _ => jcsString s
  | .array items, fuel + 1 => "[" ++ jcsSerializeItems items fuel ++ "]"
  | .object fields, fuel + 1 => "{" ++ jcsSerializeFields (jcsSortFields fields) fuel ++ "}"
termination_by _ fuel => fuel

def jcsSerializeItems : List Json → Nat → String
  | _, 0 => ""
  | [], _ => ""
  | [x], fuel + 1 => jcsSerialize x fuel
  | x :: rest, fuel + 1 => jcsSerialize x fuel ++ "," ++ jcsSerializeItems rest fuel
termination_by _ fuel => fuel

def jcsSerializeFields : List (String × Json) → Nat → String
  | _, 0 => ""
  | [], _ => ""
  | [(k, v)], fuel + 1 => jcsString k ++ ":" ++ jcsSerialize v fuel
  | (k, v) :: rest, fuel + 1 =>
    jcsString k ++ ":" ++ jcsSerialize v fuel ++ "," ++ jcsSerializeFields rest fuel
termination_by _ fuel => fuel

end

def jcsDocument (v : Json) : String := jcsSerialize v (10 * Json.size v + 32)

/-! ## §8.6 Data Round Tripping — canonical `xsd:double` form

Two INDEPENDENT decisions determined by the number's mathematical VALUE
(not its lexical shape — `-0e0` LOOKS double-shaped but its value 0 is a
plain integer): whether the value is integral, and whether its magnitude
is at least 1e21.

`forceDouble` (an explicit `xsd:double` term coercion) makes the
LEXICAL form double-shaped regardless of value. Independently, ANY
non-integral value or magnitude ≥ 1e21 also renders double-shaped, even
under a different declared datatype — the datatype IRI is whatever the
term declared; only the LEXICAL FORM tracks the value's own shape. When
no coercion applies at all, the same decision also picks the DEFAULT
datatype: `xsd:double` iff double-shaped, else `xsd:integer`. -/
def numberCanonicalize (lexeme : String) (forceDouble : Bool) : String × Bool :=
  match normalizeNumber lexeme with
  | none => if forceDouble then ("0.0E0", true) else ("0", false)
  | some nn =>
    let ndigits : Int := nn.digits.length
    let sciExp := nn.expTotal + ndigits - 1
    let isIntegral := nn.expTotal ≥ 0
    let magnitudeGe1e21 := sciExp ≥ 21
    let useDouble := forceDouble || !isIntegral || magnitudeGe1e21
    let signStr := if nn.neg then "-" else ""
    if useDouble then
      let first := String.ofList (nn.digits.take 1)
      let rest := if ndigits > 1 then String.ofList (nn.digits.drop 1) else "0"
      (signStr ++ first ++ "." ++ rest ++ "E" ++ toString sciExp, true)
    else
      (signStr ++ String.ofList nn.digits ++ zeros nn.expTotal.toNat, false)

/-! ## The `rdfDirection` option — §8.6 -/

/-- How a value object's `@direction` becomes RDF.
  * `drop` (no `rdfDirection` option): direction is dropped and the
    literal comes out as it would with no `@direction` at all;
  * `i18nDatatype`: the datatype becomes
    `https://www.w3.org/ns/i18n#<lang>_<dir>` (language lowercased,
    omitted entirely when absent), replacing `rdf:langString`/
    `xsd:string`;
  * `compoundLiteral`: the value object becomes a FRESH BLANK NODE
    bearing `rdf:value` / `rdf:direction` / `rdf:language` triples. -/
inductive RdfDirectionMode where
  | drop | i18nDatatype | compoundLiteral
  deriving DecidableEq, Repr

/-- The manifest's raw `option.rdfDirection` string. Absent or
unrecognised means `drop`, §8.6's default. -/
def rdfDirectionModeOf : Option String → RdfDirectionMode
  | some "i18n-datatype"    => .i18nDatatype
  | some "compound-literal" => .compoundLiteral
  | _                       => .drop

/-! ## Small helpers -/

/-- A fresh blank node from a threaded counter (§8.2's "generate blank
node identifier"). -/
def freshBnode (ctr : Nat) : String × Nat := ("_jld_anon" ++ toString ctr, ctr + 1)

/-- Begins with `_:`. -/
def isBnodeLabel (s : String) : Bool := charAtD s 0 == '_' && charAtD s 1 == ':'

/-- Strip the leading `_:` — `BNodeId` stores the label without it. -/
def stripBnodePrefix (s : String) : String :=
  if slen s ≥ 2 then substr s 2 (slen s - 2) else s

/-- A stricter-than-`isIri` gate for IRI strings arriving from JSON-LD
input. `RDF.isIri` is deliberately minimal (non-empty, contains a colon)
because every concrete-syntax PARSER enforces its own grammar before a
value reaches the shared model; the JSON-LD pipeline has no such
grammar, so a JSON string containing a raw space would otherwise sail
through as a "well-formed" IRI. Rejects the ASCII control range
(0x00–0x20, which covers the plain space) plus the characters RFC 3987
excludes from every IRI reference. An HONEST SUBSET: percent-encoding
validity and the rest of the grammar are NOT checked. -/
def forbiddenIriChar (c : Char) : Bool :=
  c.toNat ≤ 0x20 || c == '<' || c == '>' || c == '"' || c == '{' || c == '}'
  || c == '|' || c == '\\' || c == '^' || c == '`'

/-- RFC 3986 §3.5: an IRI reference has AT MOST ONE fragment delimiter,
since the fragment grammar excludes a bare `#`. A vocab-relative key
expansion that concatenates a vocabulary mapping ending in `#` onto a
key starting with `#` produces exactly this malformed shape — the
concatenation is the spec-mandated vocab expansion, so the doubly
fragmented result must be caught here, at the well-formedness gate. -/
def atMostOneFragment (s : String) : Bool :=
  (s.toList.filter (· == '#')).length ≤ 1

def iriWf (s : String) : Bool :=
  RDF.isIri s && !(s.toList.any forbiddenIriChar) && atMostOneFragment s

def langTagWf (s : String) : Bool := !(s.toList.any forbiddenIriChar)

/-- A PREDICATE position needs a stricter gate than `iriWf`: `isIri`
only requires a colon, so a blank-node identifier satisfies it and would
be serialised as the malformed pseudo-IRI `<_:property>`. See this
module's header on generalized RDF. -/
def predicateIriWf (s : String) : Bool := iriWf s && !isBnodeLabel s

def mkWfIri? (s : String) : Option WfIri :=
  if h : RDF.isIri s = true then some ⟨s, h⟩ else none

/-- An expanded-form `@id` string as a subject. A relative IRI yields
`none` (the triple is dropped). -/
def idToSubject (s : String) : Option Subject :=
  if isBnodeLabel s then some (.bnode (stripBnodePrefix s))
  else if iriWf s then (mkWfIri? s).map Subject.iri
  else none

def isKeywordKey (k : String) : Bool := charAtD k 0 == '@'

def jldAsArray (v : Json) : List Json :=
  match v with
  | .array items => items
  | _            => [v]

/-- Build a literal term only when well-formed. An invalid datatype IRI
(e.g. one containing a raw space) is rejected via `iriWf`, not the
shared minimal `isIri`; likewise an invalid `@language` value. -/
def makeLiteral (lexical dt : String) (lang : Option String) : Option Term :=
  if iriWf dt && (match lang with | some l => langTagWf l | none => true) then
    match mkWfIri? dt with
    | none => none
    | some dtWf =>
      let lit : Literal := { lexicalForm := lexical, datatype := dtWf,
                             langTag := lang, direction := none }
      if h : literalWf lit = true then some (.literal ⟨lit, h⟩) else none
  else none

/-- A bare JSON scalar in value position, wrapped as §5.2 Value
Expansion would: string to `xsd:string`, boolean to `xsd:boolean`,
number to `xsd:integer` or `xsd:double` per `numberCanonicalize`'s
promotion rule (the value's own magnitude and integrality, NOT its
lexical shape). Accepting bare scalars keeps context-free expanded input
loadable even though strict expanded form array-wraps every value. -/
def scalarToTerm : Json → Option Term
  | .string s => makeLiteral s xsdString.val none
  | .bool b   => makeLiteral (if b then "true" else "false") xsdBoolean.val none
  | .number n =>
    let (lex, isDouble) := numberCanonicalize n false
    makeLiteral lex (if isDouble then xsdDouble.val else xsdInteger.val) none
  | _ => none

/-! ## §8.3 Object to RDF Conversion — value objects -/

/-- The `i18n-datatype` encoding (§8.6): the datatype becomes
`https://www.w3.org/ns/i18n#<lang>_<dir>`, with the language part
LOWERCASED (the lexical value keeps its original casing) and omitted
entirely when there is no `@language`. -/
def i18nDirectionIri (lang : Option String) (dir : String) : String :=
  "https://www.w3.org/ns/i18n#" ++ (match lang with | some lg => lg.toLower | none => "")
    ++ "_" ++ dir

/-- §8.3, the value-object half, restricted to expanded form. `none` for
a non-conforming value object (both `@language` and `@type`; `@language`
on a non-string `@value`; a null or structured `@value`; an invalid
`@type` IRI). -/
def valueObjectToTerm (rdir : RdfDirectionMode) (obj : Json) : Option Term :=
  match obj.field? "@value" with
  | none => none
  | some v =>
    let lang := obj.getString? "@language"
    let dt := obj.getString? "@type"
    let dir := obj.getString? "@direction"
    match dir, dt with
    | some _, some _ => none
    | some d, none =>
      match rdir with
      | .drop =>
        match v with
        | .string s =>
          match lang with
          | some lg => makeLiteral s rdfLangString.val (some lg)
          | none    => makeLiteral s xsdString.val none
        | _ => none
      | .i18nDatatype =>
        match v with
        | .string s => makeLiteral s (i18nDirectionIri lang d) none
        | _ => none
      -- Handled one level up (`valueObjectStep`): a compound literal
      -- needs a fresh blank node plus three triples, which this
      -- single-term return shape cannot express.
      | .compoundLiteral => none
    | none, some d =>
      if d == "@json" then
        -- `JSONLD.Expand` keeps the ORIGINAL (unexpanded) value under
        -- `@value` for a `@json`-coerced term, so `v` may be any JSON
        -- shape.
        makeLiteral (jcsDocument v) rdfJsonIri.val none
      else
        match v with
        | .string s => makeLiteral s d none
        | .bool b   => makeLiteral (if b then "true" else "false") d none
        | .number n =>
          -- The LEXICAL form still tracks the value's own shape (double-
          -- shaped even under an `xsd:integer` coercion) while the
          -- DATATYPE IRI stays whatever the term declared.
          let (lex, _) := numberCanonicalize n (d == xsdDouble.val)
          makeLiteral lex d none
        | _ => none
    | none, none =>
      match lang with
      | some lg => match v with
                   | .string s => makeLiteral s rdfLangString.val (some lg)
                   | _ => none
      | none => scalarToTerm v

/-! ## `@type` entries on node objects -/

def typeTerm (t : String) : Option Term :=
  if isBnodeLabel t then some (.bnode (stripBnodePrefix t))
  else if iriWf t then (mkWfIri? t).map Term.iri
  else none

def typePrependItems (subj : Subject) : List Json → List Triple → List Triple
  | [], acc => acc
  | .string t :: rest, acc =>
    match typeTerm t with
    | some tm => typePrependItems subj rest ({ s := subj, p := rdfTypeIri, o := tm } :: acc)
    | none    => typePrependItems subj rest acc
  | _ :: rest, acc => typePrependItems subj rest acc

def typePrepend (subj : Subject) (v : Json) (acc : List Triple) : List Triple :=
  typePrependItems subj (jldAsArray v) acc

/-- Graph name slot for a named graph. A blank-node graph name is stored
as the literal string `"_:<label>"` inside the IRI-typed name field —
the `Syntax.NQuads` convention. -/
def graphNameOfSubject : Subject → Iri
  | .iri i   => i.val
  | .bnode b => "_:" ++ b

/-- §8.6 `compound-literal`: a `@direction`-bearing value object becomes
a FRESH BLANK NODE carrying `rdf:value` (the lexical form),
`rdf:direction` (the direction string), and — only when `@language` is
present — `rdf:language` (LOWERCASED) as plain `xsd:string` triples,
instead of a single literal term. -/
def compoundLiteralTerm (lex : String) (lang : Option String) (dir : String)
    (ctr : Nat) (acc : List Triple) : Term × List Triple × Nat :=
  let (b, ctr1) := freshBnode ctr
  let bsubj : Subject := .bnode b
  let plain (s : String) : Term :=
    .literal ⟨{ lexicalForm := s, datatype := xsdString, langTag := none, direction := none }, rfl⟩
  let acc1 := { s := bsubj, p := rdfValueIri, o := plain lex } :: acc
  let acc2 := { s := bsubj, p := rdfDirectionIri, o := plain dir } :: acc1
  let acc3 := match lang with
              | some lg => { s := bsubj, p := rdfLanguageIri, o := plain lg.toLower } :: acc2
              | none    => acc2
  (.bnode b, acc3, ctr1)

/-- Dispatcher for a value object: intercepts the one case
`valueObjectToTerm` cannot express and routes it to
`compoundLiteralTerm`. Every other value object is unaffected. -/
def valueObjectStep (rdir : RdfDirectionMode) (obj : Json) (ctr : Nat) (acc : List Triple)
    : Option Term × List Triple × Nat :=
  match rdir, obj.getString? "@direction", obj.getString? "@type", obj.field? "@value" with
  | .compoundLiteral, some dir, none, some (.string lex) =>
    let (t, acc1, ctr1) := compoundLiteralTerm lex (obj.getString? "@language") dir ctr acc
    (some t, acc1, ctr1)
  | _, _, _, _ => (valueObjectToTerm rdir obj, acc, ctr)

/-! ## The expansion walk — §8.2

Every function threads `(acc, named, ctr)` and PREPENDS triples onto its
accumulators; the caller reverses once at the end. `acc` always means
"the CURRENT graph's triples"; `named` is a growing GLOBAL list of every
named graph discovered anywhere in the document tree (the RDF dataset
model is flat, so a named graph cannot itself nest another). -/

/-- The state threaded through the walk. -/
structure RdfAcc where
  acc   : List Triple
  named : List NamedGraph
  ctr   : Nat

mutual

/-- A property value in expanded form: value object, list object, node
object, or node reference. Returns the term to link to (`none` when the
entry is non-conforming and must be dropped). -/
def expandValue (rdir : RdfDirectionMode) (v : Json) (st : RdfAcc) (fuel : Nat)
    : Option Term × RdfAcc :=
  match fuel with
  | 0 => (none, st)
  | fuel + 1 =>
    match v with
    | .object _ =>
      match v.field? "@value" with
      | some _ =>
        let (t, acc1, ctr1) := valueObjectStep rdir v st.ctr st.acc
        (t, { st with acc := acc1, ctr := ctr1 })
      | none =>
        match v.field? "@list" with
        | some lst =>
          let (t, st1) := expandList rdir (jldAsArray lst) st fuel
          (some t, st1)
        | none =>
          let (osubj, st1) := expandNodeR rdir v st fuel
          match osubj with
          | some subj => (some subj.toTerm, st1)
          | none      => (none, st1)
    | _ => (scalarToTerm v, st)
termination_by fuel

/-- §8.4 List to RDF Conversion: ONE `rdf:first`/`rdf:rest` cell per
original `@list` ARRAY MEMBER, allocated UNCONDITIONALLY (step 2
pre-allocates a blank node per item BEFORE attempting each item's own
Object to RDF conversion) and chained via `rdf:rest` regardless of
whether any individual member's conversion succeeds. Only the
`rdf:first` triple is conditional on that member producing a term (step
4c: "If result is not null, append…"). A member that fails to become a
term still gets its cell and its `rdf:rest` link — dropping the whole
cell would under-count cells and, for a single-item list, wrongly
collapse the property object straight to `rdf:nil`. -/
def expandList (rdir : RdfDirectionMode) (items : List Json) (st : RdfAcc) (fuel : Nat)
    : Term × RdfAcc :=
  match fuel with
  | 0 => (.iri rdfNilIri, st)
  | fuel + 1 =>
    match items with
    | [] => (.iri rdfNilIri, st)
    | item :: rest =>
      let (oterm, st1) := expandValue rdir item st fuel
      let (cell, ctr2) := freshBnode st1.ctr
      let (restTerm, st2) := expandList rdir rest { st1 with ctr := ctr2 } fuel
      let cellSubj : Subject := .bnode cell
      let acc3 := { s := cellSubj, p := rdfRestIri, o := restTerm } :: st2.acc
      let acc4 := match oterm with
                  | some t => { s := cellSubj, p := rdfFirstIri, o := t } :: acc3
                  | none   => acc3
      (.bnode cell, { st2 with acc := acc4 })
termination_by fuel

/-- A node object: the subject comes from `@id` (a fresh blank node when
absent), then every member. `none` subject (and nothing prepended) on a
malformed `@id`.

An `@graph` member introduces a FRESH, SEPARATE named graph: its
contents are expanded into their OWN triple list, added to `named` under
this node's subject as the graph name, while every OTHER member of the
same node object still describes the graph-name resource in the
ENCLOSING graph. -/
def expandNodeR (rdir : RdfDirectionMode) (v : Json) (st : RdfAcc) (fuel : Nat)
    : Option Subject × RdfAcc :=
  match fuel with
  | 0 => (none, st)
  | fuel + 1 =>
    match v with
    | .object fields =>
      let (subjOpt, ctr1) :=
        match v.field? "@id" with
        | some (.string idStr) => (idToSubject idStr, st.ctr)
        | some _ => (none, st.ctr)
        | none => let (b, c) := freshBnode st.ctr; (some (Subject.bnode b), c)
      let st := { st with ctr := ctr1 }
      match subjOpt with
      | none => (none, st)
      | some subj =>
        match v.field? "@graph" with
        | some g =>
          let stG := expandGraphNodes rdir (jldAsArray g) { st with acc := [] } fuel
          let ng : NamedGraph := { name := graphNameOfSubject subj, graph := stG.acc.reverse }
          let st1 := expandFieldsR rdir subj fields
                       { acc := st.acc, named := ng :: stG.named, ctr := stG.ctr } fuel
          (some subj, st1)
        | none =>
          let st1 := expandFieldsR rdir subj fields st fuel
          (some subj, st1)
    | _ => (none, st)
termination_by fuel

/-- Members of a node object. `@type` emits `rdf:type` triples;
`@reverse` emits swapped-direction triples; `@included` folds its nodes
into the CURRENT graph with no linking triple; `@graph` was already
consumed above; other keywords are skipped (`@id` was consumed); IRI
keys emit property triples; non-IRI (relative) keys are dropped. -/
def expandFieldsR (rdir : RdfDirectionMode) (subj : Subject) (fields : List (String × Json))
    (st : RdfAcc) (fuel : Nat) : RdfAcc :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match fields with
    | [] => st
    | (key, value) :: rest =>
      let st1 :=
        if key == "@type" then { st with acc := typePrepend subj value st.acc }
        else if key == "@reverse" then expandReverseMap rdir subj value st fuel
        else if key == "@included" then expandGraphNodes rdir (jldAsArray value) st fuel
        else if isKeywordKey key then st
        else if predicateIriWf key then
          match mkWfIri? key with
          | some p => expandPropertyR rdir subj p (jldAsArray value) st fuel
          | none   => st
        else st
      expandFieldsR rdir subj rest st1 fuel
termination_by fuel

/-- A node object's `@reverse` member: `{predIri: [items…], …}`, an
expanded-form-only shape produced by `JSONLD.Expand`. -/
def expandReverseMap (rdir : RdfDirectionMode) (subj : Subject) (v : Json) (st : RdfAcc)
    (fuel : Nat) : RdfAcc :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match v with
    | .object entries => expandReverseEntries rdir subj entries st fuel
    | _ => st
termination_by fuel

def expandReverseEntries (rdir : RdfDirectionMode) (subj : Subject)
    (entries : List (String × Json)) (st : RdfAcc) (fuel : Nat) : RdfAcc :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match entries with
    | [] => st
    | (prop, value) :: rest =>
      let st1 :=
        if predicateIriWf prop then
          match mkWfIri? prop with
          | some p => expandReverseProp rdir subj p (jldAsArray value) st fuel
          | none   => st
        else st
      expandReverseEntries rdir subj rest st1 fuel
termination_by fuel

/-- One reverse predicate's array of item values: each item expands as a
node reference / node object exactly like an ordinary property value,
and the emitted triple points FROM the item TO the enclosing node — the
direction swap that makes it a "reverse" property. -/
def expandReverseProp (rdir : RdfDirectionMode) (subj : Subject) (prop : WfIri)
    (vals : List Json) (st : RdfAcc) (fuel : Nat) : RdfAcc :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match vals with
    | [] => st
    | v :: rest =>
      let (osubj, st1) := expandNodeR rdir v st fuel
      let st2 := match osubj with
                 | some vsubj => { st1 with
                     acc := { s := vsubj, p := prop, o := subj.toTerm } :: st1.acc }
                 | none => st1
      expandReverseProp rdir subj prop rest st2 fuel
termination_by fuel

/-- The array of values of one property. -/
def expandPropertyR (rdir : RdfDirectionMode) (subj : Subject) (prop : WfIri)
    (vals : List Json) (st : RdfAcc) (fuel : Nat) : RdfAcc :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match vals with
    | [] => st
    | v :: rest =>
      let (oterm, st1) := expandValue rdir v st fuel
      let st2 := match oterm with
                 | some t => { st1 with acc := { s := subj, p := prop, o := t } :: st1.acc }
                 | none   => st1
      expandPropertyR rdir subj prop rest st2 fuel
termination_by fuel

/-- Expand every node object inside a `@graph` array (or an `@included`
array). One of these nodes may itself carry a further nested `@graph`. -/
def expandGraphNodes (rdir : RdfDirectionMode) (nodes : List Json) (st : RdfAcc) (fuel : Nat)
    : RdfAcc :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match nodes with
    | [] => st
    | n :: rest =>
      let (_, st1) := expandNodeR rdir n st fuel
      expandGraphNodes rdir rest st1 fuel
termination_by fuel

end

/-! ## Top level: default graph + named graphs -/

/-- One top-level array entry. -/
def expandTop (rdir : RdfDirectionMode) (v : Json) (st : RdfAcc) (fuel : Nat) : RdfAcc :=
  match v with
  | .object fields =>
    match v.field? "@graph" with
    | some g =>
      let (subjOpt, ctr1) :=
        match v.field? "@id" with
        | some (.string idStr) => (idToSubject idStr, st.ctr)
        | some _ => (none, st.ctr)
        | none => let (b, c) := freshBnode st.ctr; (some (Subject.bnode b), c)
      match subjOpt with
      | none => { st with ctr := ctr1 }
      | some gsubj =>
        let stG := expandGraphNodes rdir (jldAsArray g)
                     { acc := [], named := st.named, ctr := ctr1 } fuel
        -- Non-keyword members of the container node describe the
        -- graph-name resource in the DEFAULT graph.
        let stD := expandFieldsR rdir gsubj fields
                     { acc := st.acc, named := stG.named, ctr := stG.ctr } fuel
        let ng : NamedGraph := { name := graphNameOfSubject gsubj, graph := stG.acc.reverse }
        { stD with named := ng :: stD.named }
    | none => let (_, st1) := expandNodeR rdir v st fuel; st1
  | _ => st

def expandTops (rdir : RdfDirectionMode) : List Json → RdfAcc → Nat → RdfAcc
  | _, st, 0 => st
  | [], st, _ => st
  | v :: rest, st, fuel + 1 => expandTops rdir rest (expandTop rdir v st fuel) fuel

/-- Is `@graph` the only key of an object? Then it is the document
wrapper and its contents belong to the default graph. -/
def onlyGraphKeysJ (fields : List (String × Json)) : Bool :=
  fields.all (fun kv => kv.1 == "@graph")

/-- §8.2: deserialize an already-parsed EXPANDED-FORM value tree into an
RDF dataset. `none` when the top level is neither an array nor an
object. -/
def datasetOfJson (rdir : RdfDirectionMode) (root : Json) : Option Dataset :=
  let fuel := Json.size root + 1
  let finish (st : RdfAcc) : Dataset :=
    { default := st.acc.reverse, named := st.named.reverse }
  match root with
  | .array tops => some (finish (expandTops rdir tops { acc := [], named := [], ctr := 0 } fuel))
  | .object fields =>
    let tops :=
      if onlyGraphKeysJ fields then
        match root.field? "@graph" with
        | some g => jldAsArray g
        | none   => [root]
      else [root]
    some (finish (expandTops rdir tops { acc := [], named := [], ctr := 0 } fuel))
  | _ => none

/-! ## Public API -/

/-- True when a top-level JSON object carries an inline `@context`. A
top-level array never carries a shared `@context` (it only applies
within an object). -/
def hasInlineContext (root : Json) : Bool :=
  match root with
  | .object fields => fields.any (fun kv => kv.1 == "@context")
  | _ => false

/-- Parse a JSON-LD document into an RDF dataset.

`base` is the document's own base IRI (the manifest's `option.base`, or
the consumer's notion of where the document was loaded from).
`rdfDirection` and `processingMode` are the manifest's raw option
strings; only the exact string `"json-ld-1.0"` selects the 1.0
processing mode. `expandContext` (the manifest's
`option.expandContext`) is an ALREADY-ABSOLUTE IRI naming a context to
apply BEFORE the document's own inline `@context` — realised by treating
it exactly like a remote `@context` string reference.

A document carrying an inline `@context`, or for which `base` or
`expandContext` is given, is run through `JSONLD.Expand` first; a
document with none of the three goes straight to `datasetOfJson`, which
requires EXPANDED FORM input. -/
def parseJsonLd (loader : Loader) (input : String) (base : Option String)
    (rdfDirection : Option String) (expandContext : Option String)
    (processingMode : Option String) : Res Dataset :=
  let rdir := rdfDirectionModeOf rdfDirection
  let mode10 := processingMode == some "json-ld-1.0"
  match parseJson input with
  | .error _ => .error .notJsonLd
  | .ok root =>
    if hasInlineContext root || base.isSome || expandContext.isSome then
      let acSeed : ActiveContext :=
        { cur := { emptyContextCore with base := base, mode10 := mode10 }, prev := [] }
      match (match expandContext with
             | none => Except.ok acSeed
             | some ctxRef => contextProcess loader acSeed (.string ctxRef) false
                                contextFuel remoteContextFuel []) with
      | .error e => .error e
      | .ok ac0 =>
        match expand loader ac0 root with
        | .error e => .error e
        | .ok expanded =>
          match datasetOfJson rdir expanded with
          | some ds => .ok ds
          | none    => .error .notJsonLd
    else
      match datasetOfJson rdir root with
      | some ds => .ok ds
      | none    => .error .notJsonLd

/-- §5.1 Expansion as its own entry point (what the `expand` manifest
compares). Same setup as `parseJsonLd`'s context-bearing branch, but it
stops one step earlier and returns the expanded JSON. Expansion runs
UNCONDITIONALLY here: context-free documents must still go through the
algorithm to drop unmapped properties, array-wrap values, and so on. -/
def expandDocument (loader : Loader) (input : String) (base : Option String)
    (expandContext : Option String) (processingMode : Option String) : Res Json :=
  let mode10 := processingMode == some "json-ld-1.0"
  match parseJson input with
  | .error _ => .error .notJsonLd
  | .ok root =>
    let acSeed : ActiveContext :=
      { cur := { emptyContextCore with base := base, mode10 := mode10 }, prev := [] }
    match (match expandContext with
           | none => Except.ok acSeed
           | some ctxRef => contextProcess loader acSeed (.string ctxRef) false
                              contextFuel remoteContextFuel []) with
    | .error e => .error e
    | .ok ac0 => expand loader ac0 root

/-- Structural equality of two expanded documents, as the expansion
suite compares them: member order is INSIGNIFICANT (keys are sorted),
array element order IS significant (expanded property-value arrays are
ordered lists), and numbers compare by their RFC 8785 canonical value
rather than by lexeme. -/
def expandedEqual (a b : Json) : Bool := jcsDocument a == jcsDocument b

end L4Factoidal.JSONLD
