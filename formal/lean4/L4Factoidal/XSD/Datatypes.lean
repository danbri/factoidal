/-
L4Factoidal.XSD.Datatypes — XML Schema 1.1 Part 2, §3: the built-in
datatypes, each with its lexical space, value space, lexical mapping
and canonical mapping, plus the equality and order relations of §4.2.

  https://www.w3.org/TR/xmlschema11-2/

## One implementation, several consumers

Every part of the system that asks "is this string in the lexical
space of that datatype, and what value does it denote?" reads THIS
module: RDF D-entailment (`RDF/Datatypes.lean`), the SHACL datatype
and value facets (`SHACL/Validation.lean`), the CSVW datatype formats
(`CSVW/Formats.lean`), the RIF datatype and built-in library, and
XPath's type system. A second lexical mapping in any of those places
is a second answer to the same specification question.

## The value model

`Val` is the union of the primitive value spaces:

* `.str` — the `string` family. The value IS the (whiteSpace-processed)
  lexical form (§3.3.1: "the set of finite-length sequences of
  characters").
* `.bool` — `boolean` (§3.3.2), two values.
* `.dec` — `decimal` (§3.3.3) and the whole integer tower, as
  `mantissa × 10^-scale` with no trailing fraction zeros, so value
  equality is equality of the pair (§3.3.3: "the value space of
  decimal is the set of numbers that can be obtained by dividing an
  integer by a non-negative power of ten").
* `.flt` / `.dbl` — `float` (§3.3.4) and `double` (§3.3.5), the two
  IEEE-754 grids with their signed zeros, infinities and NaN
  (`XSD.IEEE754`). They are DISTINCT value spaces; nothing crosses.
* `.dur` — `duration` (§3.3.6) and its two derived types, as the pair
  (months, seconds) §3.3.6 calls the "two-property model".
* `.dt` — the seven date/time types (§3.3.7-§3.3.14), all on the same
  seven-property model (§3.3.7: year, month, day, hour, minute,
  second, timezoneOffset), tagged by which properties the type
  carries.
* `.bin` — `hexBinary` (§3.3.15) and `base64Binary` (§3.3.16), the
  finite-length sequences of binary octets.
* `.qname` — `QName` (§3.3.18) and `NOTATION` (§3.3.20), carried as
  the (prefix, local) pair; the namespace name a prefix expands to is
  not available to a datatype-only validator, so two QNames are
  compared by that pair and the caller that HAS the bindings compares
  expanded names instead.
* `.seq` — the value of a `list` datatype (§4.2.1.2 / §3.1.2), the
  finite-length sequence of its item type's values.

`.str` carries the type's primitive so that `xsd:string` and
`xsd:anyURI` values never compare equal across the two spaces (§4.2.1:
"the value spaces of the primitive datatypes are disjoint").

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD.IEEE754
import L4Factoidal.Regex.XSDPattern
import L4Factoidal.Regex.Exec
import L4Factoidal.XML.Document

namespace L4Factoidal.XSD

/-! ## §3 — the built-in datatypes -/

/-- Every built-in datatype of XSD 1.1 Part 2 §3, primitive (§3.3) and
ordinary/special (§3.2, §3.4). `precisionDecimal` is §3.2.5 (a type
defined in the specification but not required of a conforming
processor); `dateTimeStamp`, `yearMonthDuration` and `dayTimeDuration`
are the §3.4.27-§3.4.29 additions of 1.1. -/
inductive Builtin where
  | anySimpleType | anyAtomicType
  -- §3.3 primitives
  | string | boolean | decimal | float | double | duration | dateTime
  | time | date | gYearMonth | gYear | gMonthDay | gDay | gMonth
  | hexBinary | base64Binary | anyURI | qname | notation
  | precisionDecimal
  -- §3.4 ordinary built-ins
  | normalizedString | token | language | nmtoken | nmtokens
  | name | ncname | id | idref | idrefs | entity | entities
  | integer | nonPositiveInteger | negativeInteger | long | int | short
  | byte | nonNegativeInteger | unsignedLong | unsignedInt
  | unsignedShort | unsignedByte | positiveInteger
  | yearMonthDuration | dayTimeDuration | dateTimeStamp
deriving DecidableEq, Repr, Inhabited

/-- The local name in the XML Schema namespace. -/
def Builtin.localName : Builtin → String
  | .anySimpleType => "anySimpleType" | .anyAtomicType => "anyAtomicType"
  | .string => "string" | .boolean => "boolean" | .decimal => "decimal"
  | .float => "float" | .double => "double" | .duration => "duration"
  | .dateTime => "dateTime" | .time => "time" | .date => "date"
  | .gYearMonth => "gYearMonth" | .gYear => "gYear"
  | .gMonthDay => "gMonthDay" | .gDay => "gDay" | .gMonth => "gMonth"
  | .hexBinary => "hexBinary" | .base64Binary => "base64Binary"
  | .anyURI => "anyURI" | .qname => "QName" | .notation => "NOTATION"
  | .precisionDecimal => "precisionDecimal"
  | .normalizedString => "normalizedString" | .token => "token"
  | .language => "language" | .nmtoken => "NMTOKEN" | .nmtokens => "NMTOKENS"
  | .name => "Name" | .ncname => "NCName" | .id => "ID" | .idref => "IDREF"
  | .idrefs => "IDREFS" | .entity => "ENTITY" | .entities => "ENTITIES"
  | .integer => "integer" | .nonPositiveInteger => "nonPositiveInteger"
  | .negativeInteger => "negativeInteger" | .long => "long" | .int => "int"
  | .short => "short" | .byte => "byte"
  | .nonNegativeInteger => "nonNegativeInteger"
  | .unsignedLong => "unsignedLong" | .unsignedInt => "unsignedInt"
  | .unsignedShort => "unsignedShort" | .unsignedByte => "unsignedByte"
  | .positiveInteger => "positiveInteger"
  | .yearMonthDuration => "yearMonthDuration"
  | .dayTimeDuration => "dayTimeDuration"
  | .dateTimeStamp => "dateTimeStamp"

/-- Every built-in, so a lookup by name is a search of one list and a
new type cannot be added to the enum without appearing here. -/
def allBuiltins : List Builtin :=
  [ .anySimpleType, .anyAtomicType,
    .string, .boolean, .decimal, .float, .double, .duration, .dateTime,
    .time, .date, .gYearMonth, .gYear, .gMonthDay, .gDay, .gMonth,
    .hexBinary, .base64Binary, .anyURI, .qname, .notation,
    .precisionDecimal,
    .normalizedString, .token, .language, .nmtoken, .nmtokens,
    .name, .ncname, .id, .idref, .idrefs, .entity, .entities,
    .integer, .nonPositiveInteger, .negativeInteger, .long, .int, .short,
    .byte, .nonNegativeInteger, .unsignedLong, .unsignedInt,
    .unsignedShort, .unsignedByte, .positiveInteger,
    .yearMonthDuration, .dayTimeDuration, .dateTimeStamp ]

def builtinOfName? (s : String) : Option Builtin :=
  allBuiltins.find? (fun b => b.localName == s)

def xsdNamespace : String := "http://www.w3.org/2001/XMLSchema"

def builtinOfIri? (iri : String) : Option Builtin :=
  if iri.startsWith (xsdNamespace ++ "#")
  then builtinOfName? (iri.drop (xsdNamespace.length + 1)).toString
  else none

def Builtin.iri (b : Builtin) : String := xsdNamespace ++ "#" ++ b.localName

/-- §3.4: the base type of each ordinary built-in, and `none` for the
primitives and for `anySimpleType`. The derivation chain this encodes
is what `derivedFrom` walks. -/
def Builtin.base? : Builtin → Option Builtin
  | .anySimpleType => none
  | .anyAtomicType => some .anySimpleType
  | .string | .boolean | .decimal | .float | .double | .duration
  | .dateTime | .time | .date | .gYearMonth | .gYear | .gMonthDay
  | .gDay | .gMonth | .hexBinary | .base64Binary | .anyURI | .qname
  | .notation | .precisionDecimal => some .anyAtomicType
  | .normalizedString => some .string
  | .token => some .normalizedString
  | .language | .nmtoken | .name => some .token
  | .ncname => some .name
  | .id | .idref | .entity => some .ncname
  | .nmtokens => some .anySimpleType
  | .idrefs | .entities => some .anySimpleType
  | .integer => some .decimal
  | .nonPositiveInteger => some .integer
  | .negativeInteger => some .nonPositiveInteger
  | .long => some .integer
  | .int => some .long
  | .short => some .int
  | .byte => some .short
  | .nonNegativeInteger => some .integer
  | .unsignedLong => some .nonNegativeInteger
  | .unsignedInt => some .unsignedLong
  | .unsignedShort => some .unsignedInt
  | .unsignedByte => some .unsignedShort
  | .positiveInteger => some .nonNegativeInteger
  | .yearMonthDuration | .dayTimeDuration => some .duration
  | .dateTimeStamp => some .dateTime

/-- The primitive (§3.3) a built-in is ultimately derived from. The
three list types (`NMTOKENS`, `IDREFS`, `ENTITIES`) have none: a list
datatype's base is `anySimpleType` and its ITEM type has the
primitive. -/
def Builtin.primitive? : Builtin → Nat → Option Builtin
  | b, 0 => some b
  | b, fuel + 1 =>
    match b with
    | .string | .boolean | .decimal | .float | .double | .duration
    | .dateTime | .time | .date | .gYearMonth | .gYear | .gMonthDay
    | .gDay | .gMonth | .hexBinary | .base64Binary | .anyURI | .qname
    | .notation | .precisionDecimal => some b
    | .anySimpleType | .anyAtomicType => none
    | _ => match b.base? with
           | some p => Builtin.primitive? p fuel
           | none   => none

def Builtin.primitive (b : Builtin) : Option Builtin := b.primitive? 24

/-- Is `d` derived (§3.4, by restriction) from `b`, reflexively? -/
def derivedFromFuel : Nat → Builtin → Builtin → Bool
  | 0, _, _ => false
  | fuel + 1, d, b =>
    if d == b then true
    else match d.base? with
         | some p => derivedFromFuel fuel p b
         | none   => false

def derivedFrom (d b : Builtin) : Bool := derivedFromFuel 24 d b

/-! ## §4.3.6 — whiteSpace

The value of the `whiteSpace` facet is fixed for every built-in:
`preserve` for `string`, `replace` for `normalizedString`, `collapse`
for `token` and everything derived from it, and `collapse` for every
other primitive and its derivations (§3.3: each primitive other than
`string` fixes `whiteSpace` to `collapse`). -/

inductive WhiteSpace where
  | preserve | replace | collapse
deriving DecidableEq, Repr, Inhabited

def Builtin.whiteSpace : Builtin → WhiteSpace
  | .string | .anySimpleType | .anyAtomicType => .preserve
  | .normalizedString => .replace
  | _ => .collapse

def isXmlSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- §4.3.6 `replace`: every tab, line feed and carriage return becomes
a space. -/
def wsReplace (s : String) : String :=
  String.ofList (s.toList.map (fun c => if isXmlSpace c then ' ' else c))

/-- §4.3.6 `collapse`: `replace`, then contiguous spaces become one and
leading and trailing spaces are dropped. -/
def wsCollapse (s : String) : String :=
  String.intercalate " " ((wsReplace s).splitOn " " |>.filter (fun t => t != ""))

def applyWhiteSpace : WhiteSpace → String → String
  | .preserve, s => s
  | .replace,  s => wsReplace s
  | .collapse, s => wsCollapse s

/-! ## `decimal` values (§3.3.3) -/

/-- `mantissa × 10^-scale`. Normalised (no trailing fraction zeros) by
`Dec.norm`, so value equality is structural equality. -/
structure Dec where
  mantissa : Int
  scale    : Nat
deriving DecidableEq, Repr, Inhabited

def Dec.normFuel : Nat → Dec → Dec
  | 0, v => v
  | fuel + 1, v =>
    if v.scale > 0 && v.mantissa % 10 == 0
    then Dec.normFuel fuel ⟨v.mantissa / 10, v.scale - 1⟩
    else v

def Dec.norm (v : Dec) : Dec := Dec.normFuel (v.scale + 1) v

def Dec.ofInt (i : Int) : Dec := ⟨i, 0⟩
def Dec.zero : Dec := ⟨0, 0⟩

/-- Scale both to a common scale and compare mantissas. -/
def Dec.cmp (a b : Dec) : Ordering :=
  let s := max a.scale b.scale
  let ma := a.mantissa * (10 : Int) ^ (s - a.scale)
  let mb := b.mantissa * (10 : Int) ^ (s - b.scale)
  compare ma mb

def Dec.add (a b : Dec) : Dec :=
  let s := max a.scale b.scale
  Dec.norm ⟨a.mantissa * (10 : Int) ^ (s - a.scale)
            + b.mantissa * (10 : Int) ^ (s - b.scale), s⟩

def Dec.neg (a : Dec) : Dec := ⟨-a.mantissa, a.scale⟩

def Dec.sub (a b : Dec) : Dec := Dec.add a (Dec.neg b)

def Dec.mulInt (a : Dec) (k : Int) : Dec := Dec.norm ⟨a.mantissa * k, a.scale⟩

/-- The integer part, truncated toward zero, and the remainder. -/
def Dec.floorDiv (a : Dec) : Int := a.mantissa / (10 : Int) ^ a.scale

def Dec.isInt (a : Dec) : Bool := (Dec.norm a).scale == 0

def Dec.toInt? (a : Dec) : Option Int :=
  let n := Dec.norm a
  if n.scale == 0 then some n.mantissa else none

/-- §4.3.11 `totalDigits`: the number of digits in the value's
mantissa, after normalisation, with 0 counting as one digit. -/
def natDigits (n : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, acc => acc
    | fuel + 1, acc => if acc < 10 then 1 else 1 + go fuel (acc / 10)
  go (n + 1) n

def Dec.totalDigits (a : Dec) : Nat :=
  let n := Dec.norm a
  let d := natDigits n.mantissa.natAbs
  max d n.scale

/-- §4.3.12 `fractionDigits`. -/
def Dec.fractionDigits (a : Dec) : Nat := (Dec.norm a).scale

/-! ## The seven-property date/time model (§3.3.7) -/

/-- Which of the seven properties the datatype carries. `absent` for a
property a type omits is what makes `gYear` and `date` different value
spaces even when the underlying numbers agree. -/
inductive DTKind where
  | dateTime | time | date | gYearMonth | gYear | gMonthDay | gDay | gMonth
deriving DecidableEq, Repr, Inhabited

structure DTValue where
  year   : Option Int := none
  month  : Option Nat := none
  day    : Option Nat := none
  hour   : Option Nat := none
  minute : Option Nat := none
  second : Option Dec := none
  /-- The timezone offset in MINUTES, `none` for an absent timezone. -/
  tz     : Option Int := none
deriving DecidableEq, Repr, Inhabited

/-- The two-property duration model (§3.3.6): a month count and a
second count, each signed, both with the same sign in a value that has
a lexical representation. -/
structure DurValue where
  months  : Int
  seconds : Dec
deriving DecidableEq, Repr, Inhabited

/-! ## `Val` — the union of the primitive value spaces -/

inductive Val where
  | str (prim : Builtin) (s : String)
  | bool (b : Bool)
  | dec (d : Dec)
  | flt (f : Fval)
  | dbl (f : Fval)
  | dur (d : DurValue)
  | dt (k : DTKind) (v : DTValue)
  | bin (isHex : Bool) (bytes : List Nat)
  | qname (pfx : String) (lcl : String) (isNotation : Bool)
  | seq (vs : List Val)
deriving Repr, Inhabited

/-! Structural equality. `deriving DecidableEq` does not reach through
the `List Val` of `.seq`, so the comparison is written out, mutually
with the list case. -/
mutual
  def Val.beq : Val → Val → Bool
    | .str p1 s1, .str p2 s2 => p1 == p2 && s1 == s2
    | .bool a, .bool b => a == b
    | .dec a, .dec b => a == b
    | .flt a, .flt b => a == b
    | .dbl a, .dbl b => a == b
    | .dur a, .dur b => a == b
    | .dt k1 a, .dt k2 b => k1 == k2 && a == b
    | .bin h1 a, .bin h2 b => h1 == h2 && a == b
    | .qname p1 l1 n1, .qname p2 l2 n2 => p1 == p2 && l1 == l2 && n1 == n2
    | .seq a, .seq b => Val.beqList a b
    | _, _ => false

  def Val.beqList : List Val → List Val → Bool
    | [], [] => true
    | x :: xs, y :: ys => Val.beq x y && Val.beqList xs ys
    | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

/-! ## Lexical helpers -/

def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def allDigitsL (cs : List Char) : Bool := !cs.isEmpty && cs.all isDigitC

def natOfDigits (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- `n` digits exactly, all decimal. -/
def takeExact (n : Nat) (cs : List Char) : Option (List Char × List Char) :=
  if cs.length < n then none else some (cs.take n, cs.drop n)

def fixedNat (n : Nat) (cs : List Char) : Option (Nat × List Char) :=
  match takeExact n cs with
  | some (ds, rest) => if allDigitsL ds then some (natOfDigits ds, rest) else none
  | none => none

/-! ## §3.3.13 `integer` and §3.3.3 `decimal` -/

/-- §3.3.13: `'+'? | '-'?` then one or more digits. Leading zeros are
in the lexical space; the canonical mapping removes them. -/
def parseIntegerLex (s : String) : Option Int :=
  let cs := s.toList
  let (neg, ds) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _        => (false, cs)
  if allDigitsL ds then
    let n : Int := natOfDigits ds
    some (if neg then -n else n)
  else none

/-- §3.3.3: `'+'? | '-'?` then `digit+ ('.' digit*)?` or `'.' digit+`. -/
def parseDecimalLex (s : String) : Option Dec :=
  let cs := s.toList
  let (neg, body) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _        => (false, cs)
  let ip := body.takeWhile (fun c => c != '.')
  let rest := body.drop ip.length
  match rest with
  | [] =>
      if allDigitsL ip then
        let m : Int := natOfDigits ip
        some (Dec.norm ⟨if neg then -m else m, 0⟩)
      else none
  | '.' :: fp =>
      if (ip.isEmpty || ip.all isDigitC) && (fp.isEmpty || fp.all isDigitC)
         && !(ip.isEmpty && fp.isEmpty) then
        let m : Int := natOfDigits (ip ++ fp)
        some (Dec.norm ⟨if neg then -m else m, fp.length⟩)
      else none
  | _ => none

/-- The closed bounds of the bounded integer types (§3.4.16-§3.4.26).
`none` for the unbounded ones. -/
def intBounds : Builtin → Option (Option Int × Option Int)
  | .nonPositiveInteger => some (none, some 0)
  | .negativeInteger    => some (none, some (-1))
  | .nonNegativeInteger => some (some 0, none)
  | .positiveInteger    => some (some 1, none)
  | .long  => some (some (-9223372036854775808), some 9223372036854775807)
  | .int   => some (some (-2147483648), some 2147483647)
  | .short => some (some (-32768), some 32767)
  | .byte  => some (some (-128), some 127)
  | .unsignedLong  => some (some 0, some 18446744073709551615)
  | .unsignedInt   => some (some 0, some 4294967295)
  | .unsignedShort => some (some 0, some 65535)
  | .unsignedByte  => some (some 0, some 255)
  | .integer => some (none, none)
  | _ => none

def inIntBounds (b : Builtin) (i : Int) : Bool :=
  match intBounds b with
  | none => true
  | some (lo, hi) =>
      (match lo with | some l => l ≤ i | none => true) &&
      (match hi with | some h => i ≤ h | none => true)

/-! ## §3.3.2 `boolean` -/

def parseBooleanLex (s : String) : Option Bool :=
  if s == "true" || s == "1" then some true
  else if s == "false" || s == "0" then some false
  else none

/-! ## §3.3.15 `hexBinary` -/

def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexBytes : List Char → Option (List Nat)
  | [] => some []
  | [_] => none
  | a :: b :: rest =>
      match hexVal? a, hexVal? b, hexBytes rest with
      | some x, some y, some tl => some ((x * 16 + y) :: tl)
      | _, _, _ => none

def parseHexBinaryLex (s : String) : Option (List Nat) := hexBytes s.toList

def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- §3.3.15.2: the canonical representation uses UPPER-case digits. -/
def hexOfBytes (bs : List Nat) : String :=
  String.ofList (bs.flatMap (fun b => [hexDigitChar (b / 16), hexDigitChar (b % 16)]))

/-! ## §3.3.16 `base64Binary` -/

def b64Val? (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 65)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 71)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat + 4)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

def b64Char (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n)
  else if n < 52 then Char.ofNat (71 + n)
  else if n < 62 then Char.ofNat (n - 4)
  else if n == 62 then '+' else '/'

/-- Decode the quads. The final group carries the padding rules of
§3.3.16.1: `xx==` needs the second character in `[AQgw]` (its low four
bits must be zero) and `xxx=` needs the third in
`[AEIMQUYcgkosw048]` (its low two bits must be zero) — a lexical that
sets those bits is NOT in the lexical space. -/
def b64Decode : List Char → Option (List Nat)
  | [] => some []
  | [a, b, '=', '='] =>
      match b64Val? a, b64Val? b with
      | some x, some y => if y % 16 == 0 then some [x * 4 + y / 16] else none
      | _, _ => none
  | [a, b, c, '='] =>
      match b64Val? a, b64Val? b, b64Val? c with
      | some x, some y, some z =>
          if z % 4 == 0 then
            some [x * 4 + y / 16, (y % 16) * 16 + z / 4]
          else none
      | _, _, _ => none
  | a :: b :: c :: d :: rest =>
      match b64Val? a, b64Val? b, b64Val? c, b64Val? d, b64Decode rest with
      | some x, some y, some z, some w, some tl =>
          some ((x * 4 + y / 16) :: ((y % 16) * 16 + z / 4) :: ((z % 4) * 64 + w) :: tl)
      | _, _, _, _, _ => none
  | _ => none

def parseBase64Lex (s : String) : Option (List Nat) :=
  let cs := s.toList.filter (fun c => !isXmlSpace c)
  if cs.length % 4 != 0 then none else b64Decode cs

/-- §3.3.16.2 — the canonical form, no whitespace, padded. -/
def base64OfBytes : List Nat → String
  | [] => ""
  | [a] =>
      String.ofList [b64Char (a / 4), b64Char ((a % 4) * 16), '=', '=']
  | [a, b] =>
      String.ofList [b64Char (a / 4), b64Char ((a % 4) * 16 + b / 16),
                 b64Char ((b % 16) * 4), '=']
  | a :: b :: c :: rest =>
      String.ofList [b64Char (a / 4), b64Char ((a % 4) * 16 + b / 16),
                 b64Char ((b % 16) * 4 + c / 64), b64Char (c % 64)]
      ++ base64OfBytes rest

/-! ## §3.3.17 `anyURI`, §3.3.18 `QName`, the `string` family -/

open L4Factoidal.XML in
def isNCName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => c != ':' && isNameStartChar c
                 && rest.all (fun x => x != ':' && isNameChar x)

open L4Factoidal.XML in
def isXmlName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isNameStartChar c && rest.all isNameChar

open L4Factoidal.XML in
def isNmtoken (s : String) : Bool :=
  !s.isEmpty && s.toList.all isNameChar

/-- §3.3.18: `NCName` or `NCName ':' NCName`. -/
def parseQNameLex (s : String) : Option (String × String) :=
  match s.splitOn ":" with
  | [l] => if isNCName l then some ("", l) else none
  | [p, l] => if isNCName p && isNCName l then some (p, l) else none
  | _ => none

/-- §3.3.17: the lexical space of `anyURI` is the set of IRI
references. The characters excluded from an IRI by RFC 3987 are
rejected, and a `%` must introduce two hexadecimal digits; nothing
else is checked, because §3.3.17 explicitly admits relative
references, so almost every remaining string IS an IRI reference. -/
def percentEscapesOk : List Char → Bool
  | [] => true
  | '%' :: a :: b :: rest =>
      (hexVal? a).isSome && (hexVal? b).isSome && percentEscapesOk rest
  | '%' :: _ => false
  | _ :: rest => percentEscapesOk rest

def isAnyUriLex (s : String) : Bool :=
  let cs := s.toList
  let bad := ['<', '>', '"', '{', '}', '|', '\\', '^', '`', ' ']
  cs.all (fun c => !(bad.contains c) && c.toNat > 0x20) &&
  percentEscapesOk cs &&
  (cs.filter (fun c => c == '#')).length ≤ 1

/-- §3.3.19 `language`: `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*`. -/
def isAlphaC (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isAlnumC (c : Char) : Bool := isAlphaC c || isDigitC c

def isLanguageLex (s : String) : Bool :=
  match s.splitOn "-" with
  | [] => false
  | h :: tl =>
      let hs := h.toList
      !hs.isEmpty && hs.length ≤ 8 && hs.all isAlphaC &&
      tl.all (fun seg =>
        let ss := seg.toList
        !ss.isEmpty && ss.length ≤ 8 && ss.all isAlnumC)

/-! ## §3.3.6 `duration` and §3.4.26-27 -/

/-- Read `digit+` followed by `ch`; returns the number and the rest, or
`none` when `ch` is not the next designator. -/
def durComponent (ch : Char) (cs : List Char) : Option Nat × List Char :=
  let ds := cs.takeWhile isDigitC
  let rest := cs.drop ds.length
  match rest with
  | c :: r => if c == ch && !ds.isEmpty then (some (natOfDigits ds), r)
              else (none, cs)
  | [] => (none, cs)

/-- The seconds designator, which may carry a fraction. -/
def durSeconds (cs : List Char) : Option (Dec × List Char) :=
  let ip := cs.takeWhile isDigitC
  let r1 := cs.drop ip.length
  match r1 with
  | '.' :: r2 =>
      let fp := r2.takeWhile isDigitC
      let r3 := r2.drop fp.length
      match r3 with
      | 'S' :: r4 =>
          if ip.isEmpty || fp.isEmpty then none
          else some (Dec.norm ⟨natOfDigits (ip ++ fp), fp.length⟩, r4)
      | _ => none
  | 'S' :: r2 => if ip.isEmpty then none else some (Dec.ofInt (natOfDigits ip), r2)
  | _ => none

/-- §3.3.6.1 `duration` lexical mapping. `allowYM` / `allowDT` restrict
it to the `yearMonthDuration` (§3.4.27) and `dayTimeDuration`
(§3.4.28) sub-lexical-spaces. -/
def parseDurationLexGen (allowYM allowDT : Bool) (s : String) : Option DurValue :=
  let cs0 := s.toList
  let (neg, cs1) := match cs0 with
    | '-' :: r => (true, r)
    | _        => (false, cs0)
  match cs1 with
  | 'P' :: body =>
      let (yOpt, a1) := durComponent 'Y' body
      let (moOpt, a2) := durComponent 'M' a1
      let (dOpt, a3) := durComponent 'D' a2
      let dateEmpty := yOpt.isNone && moOpt.isNone && dOpt.isNone
      match a3 with
      | [] =>
          if dateEmpty then none
          else if !allowYM && (yOpt.isSome || moOpt.isSome) then none
          else if !allowDT && dOpt.isSome then none
          else
            let months : Int := (yOpt.getD 0) * 12 + (moOpt.getD 0)
            let secs := Dec.ofInt ((dOpt.getD 0 : Int) * 86400)
            some ⟨if neg then -months else months,
                  if neg then Dec.neg secs else secs⟩
      | 'T' :: tbody =>
          let (hOpt, b1) := durComponent 'H' tbody
          let (miOpt, b2) := durComponent 'M' b1
          match (if b2.isEmpty then some (Dec.zero, ([] : List Char))
                 else durSeconds b2) with
          | none => none
          | some (sec, leftover) =>
            let sOpt := if b2.isEmpty then none else some sec
            if !leftover.isEmpty then none
            else if hOpt.isNone && miOpt.isNone && sOpt.isNone then none
            else if !allowYM && (yOpt.isSome || moOpt.isSome) then none
            else if !allowDT then none
            else
              let months : Int := (yOpt.getD 0) * 12 + (moOpt.getD 0)
              let secs := Dec.add
                (Dec.ofInt ((dOpt.getD 0 : Int) * 86400
                            + (hOpt.getD 0 : Int) * 3600
                            + (miOpt.getD 0 : Int) * 60))
                (sOpt.getD Dec.zero)
              some ⟨if neg then -months else months,
                    if neg then Dec.neg secs else secs⟩
      | _ => none
  | _ => none

def parseDurationLex (s : String) : Option DurValue := parseDurationLexGen true true s
def parseYearMonthDurationLex (s : String) : Option DurValue :=
  parseDurationLexGen true false s
def parseDayTimeDurationLex (s : String) : Option DurValue :=
  parseDurationLexGen false true s

/-! ## §3.3.7-§3.3.14 — the date/time lexical mappings -/

/-- §3.3.7: is `y` a leap year in the proleptic Gregorian calendar? -/
def isLeapYear (y : Int) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (y : Int) (m : Nat) : Nat :=
  if m == 2 then (if isLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else 31

/-- `yearFrag` (§3.3.7.1): an optional minus, then four or more digits
with no leading zero unless the year is exactly four digits. Year 0000
IS in the XSD 1.1 lexical space (it denotes 1 BCE); XSD 1.0 excluded
it, and `strict10Year` below is where that difference lives. -/
def parseYearFrag (cs : List Char) : Option (Int × List Char) :=
  let (neg, rest) := match cs with
    | '-' :: r => (true, r)
    | _        => (false, cs)
  let ds := rest.takeWhile isDigitC
  if ds.length < 4 then none
  else if ds.length > 4 && ds.head? == some '0' then none
  else
    let n : Int := natOfDigits ds
    some ((if neg then -n else n), rest.drop ds.length)

/-- `timezoneFrag` (§3.3.7.1): `Z`, or a sign then `hh:mm` in
[-14:00, +14:00]. The result is the offset in MINUTES. -/
def parseTimezoneFrag (cs : List Char) : Option (Option Int) :=
  match cs with
  | [] => some none
  | ['Z'] => some (some 0)
  | sign :: rest =>
      if sign != '+' && sign != '-' then none
      else
        match fixedNat 2 rest with
        | some (h, ':' :: r2) =>
            match fixedNat 2 r2 with
            | some (m, []) =>
                if m > 59 then none
                else if h > 14 then none
                else if h == 14 && m != 0 then none
                else
                  let off : Int := (h : Int) * 60 + m
                  some (some (if sign == '-' then -off else off))
            | _ => none
        | _ => none

/-- `hh:mm:ss(.sss)?`, or the `24:00:00(.0+)?` end-of-day form. The
Bool says whether end-of-day was read. -/
def parseTimeBody (cs : List Char) : Option (Nat × Nat × Dec × Bool × List Char) :=
  match fixedNat 2 cs with
  | some (h, ':' :: r1) =>
    match fixedNat 2 r1 with
    | some (mi, ':' :: r2) =>
      match fixedNat 2 r2 with
      | some (se, r3) =>
        let (frac, r4) :=
          match r3 with
          | '.' :: fr =>
              let ds := fr.takeWhile isDigitC
              (some ds, fr.drop ds.length)
          | _ => (none, r3)
        match frac with
        | some ds =>
            if ds.isEmpty then none
            else
              let sec := Dec.norm ⟨(se : Int) * (10 : Int) ^ ds.length
                                   + natOfDigits ds, ds.length⟩
              if h == 24 then
                (if mi == 0 && se == 0 && ds.all (fun c => c == '0')
                 then some (24, 0, Dec.zero, true, r4) else none)
              else if h > 23 || mi > 59 || se > 59 then none
              else some (h, mi, sec, false, r4)
        | none =>
            if h == 24 then
              (if mi == 0 && se == 0 then some (24, 0, Dec.zero, true, r4) else none)
            else if h > 23 || mi > 59 || se > 59 then none
            else some (h, mi, Dec.ofInt se, false, r4)
      | _ => none
    | _ => none
  | _ => none

/-- The seven-property value of a lexical of `kind`. -/
def parseDateTimeLex (kind : DTKind) (s : String) : Option DTValue :=
  let cs := s.toList
  match kind with
  | .dateTime =>
      match parseYearFrag cs with
      | some (y, '-' :: r1) =>
        match fixedNat 2 r1 with
        | some (mo, '-' :: r2) =>
          match fixedNat 2 r2 with
          | some (d, 'T' :: r3) =>
            match parseTimeBody r3 with
            | some (h, mi, se, eod, r4) =>
              match parseTimezoneFrag r4 with
              | some tz =>
                  if mo < 1 || mo > 12 || d < 1 || d > daysInMonth y mo then none
                  else if eod then
                    -- §3.3.8: 24:00:00 is the start of the FOLLOWING day.
                    let (y2, mo2, d2) :=
                      if d < daysInMonth y mo then (y, mo, d + 1)
                      else if mo < 12 then (y, mo + 1, 1)
                      else (y + 1, 1, 1)
                    some { year := some y2, month := some mo2, day := some d2,
                           hour := some 0, minute := some 0,
                           second := some Dec.zero, tz := tz }
                  else
                    some { year := some y, month := some mo, day := some d,
                           hour := some h, minute := some mi,
                           second := some se, tz := tz }
              | none => none
            | none => none
          | _ => none
        | _ => none
      | _ => none
  | .time =>
      match parseTimeBody cs with
      | some (h, mi, se, eod, r) =>
        match parseTimezoneFrag r with
        | some tz =>
            if eod then
              some { hour := some 0, minute := some 0,
                     second := some Dec.zero, tz := tz }
            else
              some { hour := some h, minute := some mi,
                     second := some se, tz := tz }
        | none => none
      | none => none
  | .date =>
      match parseYearFrag cs with
      | some (y, '-' :: r1) =>
        match fixedNat 2 r1 with
        | some (mo, '-' :: r2) =>
          match fixedNat 2 r2 with
          | some (d, r3) =>
            match parseTimezoneFrag r3 with
            | some tz =>
                if mo < 1 || mo > 12 || d < 1 || d > daysInMonth y mo then none
                else some { year := some y, month := some mo, day := some d,
                            tz := tz }
            | none => none
          | _ => none
        | _ => none
      | _ => none
  | .gYearMonth =>
      match parseYearFrag cs with
      | some (y, '-' :: r1) =>
        match fixedNat 2 r1 with
        | some (mo, r2) =>
          match parseTimezoneFrag r2 with
          | some tz => if mo < 1 || mo > 12 then none
                       else some { year := some y, month := some mo, tz := tz }
          | none => none
        | _ => none
      | _ => none
  | .gYear =>
      match parseYearFrag cs with
      | some (y, r1) =>
        match parseTimezoneFrag r1 with
        | some tz => some { year := some y, tz := tz }
        | none => none
      | none => none
  | .gMonthDay =>
      match cs with
      | '-' :: '-' :: r0 =>
        match fixedNat 2 r0 with
        | some (mo, '-' :: r1) =>
          match fixedNat 2 r1 with
          | some (d, r2) =>
            match parseTimezoneFrag r2 with
            | some tz =>
                -- The day must be possible in that month in SOME year,
                -- so February admits 29 (§3.3.13).
                if mo < 1 || mo > 12 || d < 1 || d > daysInMonth 2004 mo then none
                else some { month := some mo, day := some d, tz := tz }
            | none => none
          | _ => none
        | _ => none
      | _ => none
  | .gDay =>
      match cs with
      | '-' :: '-' :: '-' :: r0 =>
        match fixedNat 2 r0 with
        | some (d, r1) =>
          match parseTimezoneFrag r1 with
          | some tz => if d < 1 || d > 31 then none
                       else some { day := some d, tz := tz }
          | none => none
        | _ => none
      | _ => none
  | .gMonth =>
      match cs with
      | '-' :: '-' :: r0 =>
        match fixedNat 2 r0 with
        | some (mo, r1) =>
          match parseTimezoneFrag r1 with
          | some tz => if mo < 1 || mo > 12 then none
                       else some { month := some mo, tz := tz }
          | none => none
        | _ => none
      | _ => none

/-! ## §4.2.2 — the order relations

Every order below is PARTIAL: `none` means the two values are
·incomparable·, which §4.3.7-§4.3.10 turn into "the facet is not
satisfied". `float`/`double` NaN is incomparable with everything, a
timezoned and an untimezoned date/time value are incomparable when the
±14:00 window straddles the other value, and two durations are
incomparable when the four reference dateTimes disagree. -/

/-- Magnitudes `m₁·2^e₁` and `m₂·2^e₂`, both positive. -/
def cmpDyadic (m1 : Nat) (e1 : Int) (m2 : Nat) (e2 : Int) : Ordering :=
  if e1 ≥ e2 then compare (m1 * 2 ^ (e1 - e2).toNat) m2
  else compare m1 (m2 * 2 ^ (e2 - e1).toNat)

/-- The IEEE-754 order (§3.3.4): `-INF < … < -0 = +0 < … < +INF`, and
NaN incomparable. The two zeros are EQUAL in the order even though
`fvalEq` (identity) separates them. -/
def fvalCmp (a b : Fval) : Option Ordering :=
  match a.cls, b.cls with
  | .nan, _ | _, .nan => none
  | .zero, .zero => some .eq
  | .zero, .inf  => some (if b.neg then .gt else .lt)
  | .inf,  .zero => some (if a.neg then .lt else .gt)
  | .zero, .finite _ _ => some (if b.neg then .gt else .lt)
  | .finite _ _, .zero => some (if a.neg then .lt else .gt)
  | .inf, .inf => some (if a.neg == b.neg then .eq else if a.neg then .lt else .gt)
  | .inf, .finite _ _ => some (if a.neg then .lt else .gt)
  | .finite _ _, .inf => some (if b.neg then .gt else .lt)
  | .finite m1 e1, .finite m2 e2 =>
      if a.neg != b.neg then some (if a.neg then .lt else .gt)
      else
        let mag := cmpDyadic m1 e1 m2 e2
        some (if a.neg then mag.swap else mag)

/-- The proleptic Gregorian day number of `(y, m, d)`, day 0 being
1970-01-01. -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y' : Int := if m ≤ 2 then y - 1 else y
  -- Hinnant's algorithm takes the era with a TRUNCATING division and
  -- writes `y' - 399` to emulate a floor. Lean 4's `Int` `/` is
  -- EUCLIDEAN, so with `/` the adjustment fires a second time and the
  -- era comes out one too low for every `y'` in `[-399, -1]`:
  -- `daysFromCivil (-44) 3 15` was one day short of the right answer.
  -- Found 2026-09-07 by the `civilFromDays`/`daysFromCivil` round-trip
  -- guard in `L4Factoidal/Fn/DateTime.lean`. `Int.tdiv` is named
  -- explicitly so the direction cannot drift again.
  let era : Int := Int.tdiv (if y' ≥ 0 then y' else y' - 399) 400
  let yoe : Int := y' - era * 400
  let mp : Nat := (m + 9) % 12
  let doy : Int := (153 * (mp : Int) + 2) / 5 + (d : Int) - 1
  let doe : Int := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- §E.3.4 `timeOnTimeline`, in seconds, with the specification's
defaults for the properties a datatype omits (year 1972, month 12, day
the last of that month, time zero) and the timezone offset removed. -/
def timeOnTimeline (v : DTValue) : Dec :=
  let y := v.year.getD 1972
  let mo := v.month.getD 12
  let d := v.day.getD (daysInMonth y mo)
  let h := v.hour.getD 0
  let mi := v.minute.getD 0
  let se := v.second.getD Dec.zero
  let off := v.tz.getD 0
  Dec.add (Dec.ofInt (daysFromCivil y mo d * 86400
                      + (h : Int) * 3600 + (mi : Int) * 60 - off * 60)) se

/-- §3.2.7.4: the order on a date/time value space. A value with no
timezone is compared through the ±14:00 window; when the window
straddles the other value the pair is incomparable. -/
def dtCompare (a b : DTValue) : Option Ordering :=
  match a.tz, b.tz with
  | some _, some _ => some (Dec.cmp (timeOnTimeline a) (timeOnTimeline b))
  | none, none     => some (Dec.cmp (timeOnTimeline a) (timeOnTimeline b))
  | none, some _ =>
      let lo := Dec.cmp (timeOnTimeline { a with tz := some 840 }) (timeOnTimeline b)
      let hi := Dec.cmp (timeOnTimeline { a with tz := some (-840) }) (timeOnTimeline b)
      if lo == hi then some lo else none
  | some _, none =>
      let lo := Dec.cmp (timeOnTimeline a) (timeOnTimeline { b with tz := some (-840) })
      let hi := Dec.cmp (timeOnTimeline a) (timeOnTimeline { b with tz := some 840 })
      if lo == hi then some lo else none

/-- §E.2.2 `dateTimePlusDuration`, restricted to what the duration
order needs: add the months (clamping the day into the target month)
and then the seconds. -/
def addDuration (s : DTValue) (d : DurValue) : DTValue :=
  let y := s.year.getD 1972
  let mo := s.month.getD 12
  let total : Int := (y * 12 + ((mo : Int) - 1)) + d.months
  let y2 : Int := if total ≥ 0 then total / 12 else (total - 11) / 12
  let mo2 : Nat := (total - y2 * 12).toNat + 1
  let dayIn := s.day.getD 1
  let d2 := min dayIn (daysInMonth y2 mo2)
  let base := Dec.ofInt (daysFromCivil y2 mo2 d2 * 86400
                         + (s.hour.getD 0 : Int) * 3600
                         + (s.minute.getD 0 : Int) * 60)
  let secs := Dec.add (Dec.add base (s.second.getD Dec.zero)) d.seconds
  -- Only the timeline position matters to the order, so the result is
  -- carried as a day-zero value whose seconds hold the whole offset.
  { year := some 1970, month := some 1, day := some 1,
    hour := some 0, minute := some 0, second := some secs, tz := some 0 }

/-- §3.3.6.2: the four reference dateTimes the duration order uses. -/
def durationReferences : List DTValue :=
  [ { year := some 1696, month := some 9, day := some 1, hour := some 0,
      minute := some 0, second := some Dec.zero, tz := some 0 },
    { year := some 1697, month := some 2, day := some 1, hour := some 0,
      minute := some 0, second := some Dec.zero, tz := some 0 },
    { year := some 1903, month := some 3, day := some 1, hour := some 0,
      minute := some 0, second := some Dec.zero, tz := some 0 },
    { year := some 1903, month := some 7, day := some 1, hour := some 0,
      minute := some 0, second := some Dec.zero, tz := some 0 } ]

/-- Two durations are ordered only when all four references agree
(§3.3.6.2); otherwise they are incomparable. -/
def durCompare (a b : DurValue) : Option Ordering :=
  let os := durationReferences.map (fun s =>
    Dec.cmp (timeOnTimeline (addDuration s a)) (timeOnTimeline (addDuration s b)))
  match os with
  | [] => none
  | o :: rest => if rest.all (fun x => x == o) then some o else none

/-- The order relation of the value space, per §4.2.2. `none` is
·incomparable·, which includes every cross-primitive pair. -/
def valCompare : Val → Val → Option Ordering
  | .dec a, .dec b => some (Dec.cmp a b)
  | .flt a, .flt b => fvalCmp a b
  | .dbl a, .dbl b => fvalCmp a b
  | .dur a, .dur b => durCompare a b
  | .dt k1 a, .dt k2 b => if k1 == k2 then dtCompare a b else none
  | .bool a, .bool b => some (compare a b)
  | _, _ => none

/-- Value identity (§2.1: the ·identity· relation), which is what
`enumeration` (§4.3.5) tests. It is finer than the order: `-0` and
`+0` are distinct float values and NaN IS identical to NaN, while the
order calls the first pair equal and the second incomparable. -/
def valIdentical : Val → Val → Bool
  | .flt a, .flt b => a == b
  | .dbl a, .dbl b => a == b
  | .dec a, .dec b => Dec.norm a == Dec.norm b
  | .dt k1 a, .dt k2 b =>
      k1 == k2 &&
      (match a.tz, b.tz with
       | some _, some _ | none, none => Dec.cmp (timeOnTimeline a) (timeOnTimeline b) == .eq
       | _, _ => false)
  | .dur a, .dur b => a.months == b.months && Dec.cmp a.seconds b.seconds == .eq
  | a, b => a == b

/-! ## §3 — the lexical mappings, one entry per built-in -/

/-- The `DTKind` of a date/time built-in. -/
def dtKindOf? : Builtin → Option DTKind
  | .dateTime | .dateTimeStamp => some .dateTime
  | .time => some .time
  | .date => some .date
  | .gYearMonth => some .gYearMonth
  | .gYear => some .gYear
  | .gMonthDay => some .gMonthDay
  | .gDay => some .gDay
  | .gMonth => some .gMonth
  | _ => none

/-- The three built-in LIST datatypes (§3.4.5, §3.4.9, §3.4.11) and
their item type. -/
def builtinListItem? : Builtin → Option Builtin
  | .nmtokens => some .nmtoken
  | .idrefs   => some .idref
  | .entities => some .entity
  | _ => none

/-- §3.3 / §3.4: the lexical mapping of a built-in, on a lexical form
that has ALREADY had the type's `whiteSpace` applied. `none` means the
string is not in the lexical space. -/
def lexicalMapFuel : Nat → Builtin → String → Option Val
  | 0, _, _ => none
  | fuel + 1, b, s =>
    match b with
    | .anySimpleType | .anyAtomicType => some (.str .string s)
    | .string => some (.str .string s)
    | .normalizedString | .token => some (.str .string s)
    | .language => if isLanguageLex s then some (.str .string s) else none
    | .name => if isXmlName s then some (.str .string s) else none
    | .ncname | .id | .idref | .entity =>
        if isNCName s then some (.str .string s) else none
    | .nmtoken => if isNmtoken s then some (.str .string s) else none
    | .nmtokens | .idrefs | .entities =>
        match builtinListItem? b with
        | none => none
        | some item =>
          let toks := s.splitOn " " |>.filter (fun t => t != "")
          if toks.isEmpty then none
          else
            let vs := toks.map (fun t => lexicalMapFuel fuel item t)
            if vs.all Option.isSome then some (.seq (vs.filterMap id)) else none
    | .boolean => (parseBooleanLex s).map Val.bool
    | .decimal => (parseDecimalLex s).map Val.dec
    | .integer | .nonPositiveInteger | .negativeInteger | .long | .int
    | .short | .byte | .nonNegativeInteger | .unsignedLong | .unsignedInt
    | .unsignedShort | .unsignedByte | .positiveInteger =>
        match parseIntegerLex s with
        | some i => if inIntBounds b i then some (.dec (Dec.ofInt i)) else none
        | none   => none
    | .float  => (parseLexical s).map (fun p => .flt (canonFloat p))
    | .double => (parseLexical s).map (fun p => .dbl (canonDouble p))
    | .duration => (parseDurationLex s).map Val.dur
    | .yearMonthDuration => (parseYearMonthDurationLex s).map Val.dur
    | .dayTimeDuration => (parseDayTimeDurationLex s).map Val.dur
    | .dateTimeStamp =>
        match parseDateTimeLex .dateTime s with
        | some v => if v.tz.isSome then some (.dt .dateTime v) else none
        | none   => none
    | .dateTime | .time | .date | .gYearMonth | .gYear | .gMonthDay
    | .gDay | .gMonth =>
        match dtKindOf? b with
        | some k => (parseDateTimeLex k s).map (Val.dt k)
        | none   => none
    | .hexBinary => (parseHexBinaryLex s).map (Val.bin true)
    | .base64Binary => (parseBase64Lex s).map (Val.bin false)
    | .anyURI => if isAnyUriLex s then some (.str .anyURI s) else none
    | .qname => (parseQNameLex s).map (fun p => .qname p.1 p.2 false)
    | .notation => (parseQNameLex s).map (fun p => .qname p.1 p.2 true)
    | .precisionDecimal =>
        -- §3.2.5 is not required of a conforming processor and its test
        -- sets are commented out of `suite.xml`; the decimal lexical
        -- space plus the three specials is what is modelled.
        if s == "NaN" || s == "INF" || s == "+INF" || s == "-INF"
        then some (.str .string s)
        else (parseDecimalLex s).map Val.dec

def lexicalMap (b : Builtin) (s : String) : Option Val := lexicalMapFuel 4 b s

/-- The lexical mapping with the type's `whiteSpace` applied first —
what a validator calls (§4.3.6: whiteSpace is applied before any other
facet, and before the lexical mapping). -/
def lexicalMapWs (b : Builtin) (s : String) : Option Val :=
  lexicalMap b (applyWhiteSpace b.whiteSpace s)

/-! ## §3 — the canonical mappings -/

def natToString (n : Nat) : String := toString n

def intToString (i : Int) : String := toString i

/-- §3.3.3.2: an integral value has no decimal point; a fractional one
has digits on both sides. -/
def Dec.canonical (a : Dec) : String :=
  let n := Dec.norm a
  if n.scale == 0 then intToString n.mantissa
  else
    let neg := n.mantissa < 0
    let digits := natToString n.mantissa.natAbs
    let padded := if digits.length ≤ n.scale
                  then String.ofList (List.replicate (n.scale + 1 - digits.length) '0')
                       ++ digits
                  else digits
    let cut := padded.length - n.scale
    (if neg then "-" else "") ++ (padded.take cut).toString ++ "."
      ++ (padded.drop cut).toString

def pad2 (n : Nat) : String :=
  if n < 10 then "0" ++ natToString n else natToString n

def padYear (y : Int) : String :=
  let a := y.natAbs
  let d := natToString a
  let padded := if d.length < 4
                then String.ofList (List.replicate (4 - d.length) '0') ++ d else d
  (if y < 0 then "-" else "") ++ padded

/-- The canonical timezone (§3.3.7.2): `Z` for UTC, `±hh:mm`. -/
def canonicalTz : Option Int → String
  | none => ""
  | some 0 => "Z"
  | some off =>
      let a := off.natAbs
      (if off < 0 then "-" else "+") ++ pad2 (a / 60) ++ ":" ++ pad2 (a % 60)

def canonicalSeconds (d : Dec) : String :=
  let n := Dec.norm d
  if n.scale == 0 then pad2 n.mantissa.natAbs
  else
    let s := Dec.canonical n
    match s.splitOn "." with
    | [ip, fp] =>
        (if ip.length < 2 then "0" ++ ip else ip) ++ "." ++ fp
    | _ => s

def canonicalDateTime (k : DTKind) (v : DTValue) : String :=
  let ymd := padYear (v.year.getD 0) ++ "-" ++ pad2 (v.month.getD 1)
             ++ "-" ++ pad2 (v.day.getD 1)
  let hms := pad2 (v.hour.getD 0) ++ ":" ++ pad2 (v.minute.getD 0)
             ++ ":" ++ canonicalSeconds (v.second.getD Dec.zero)
  let tz := canonicalTz v.tz
  match k with
  | .dateTime   => ymd ++ "T" ++ hms ++ tz
  | .time       => hms ++ tz
  | .date       => ymd ++ tz
  | .gYearMonth => padYear (v.year.getD 0) ++ "-" ++ pad2 (v.month.getD 1) ++ tz
  | .gYear      => padYear (v.year.getD 0) ++ tz
  | .gMonthDay  => "--" ++ pad2 (v.month.getD 1) ++ "-" ++ pad2 (v.day.getD 1) ++ tz
  | .gDay       => "---" ++ pad2 (v.day.getD 1) ++ tz
  | .gMonth     => "--" ++ pad2 (v.month.getD 1) ++ tz

/-- §3.3.6.2 — the canonical duration, `PnYnMnDTnHnMnS` with every
zero-valued component dropped except in the all-zero case. -/
def canonicalDuration (d : DurValue) : String :=
  let neg := d.months < 0 || (Dec.cmp d.seconds Dec.zero == .lt)
  let m := d.months.natAbs
  let secs := if Dec.cmp d.seconds Dec.zero == .lt then Dec.neg d.seconds else d.seconds
  let wholeSecs := Dec.floorDiv secs
  let frac := Dec.sub secs (Dec.ofInt wholeSecs)
  let days := wholeSecs / 86400
  let rem := wholeSecs % 86400
  let hours := rem / 3600
  let mins := (rem % 3600) / 60
  let ss := rem % 60
  let secStr :=
    if Dec.cmp frac Dec.zero == .eq then
      (if ss == 0 then "" else intToString ss ++ "S")
    else
      let full := Dec.canonical (Dec.add (Dec.ofInt ss) frac)
      full ++ "S"
  let dPart := (if m / 12 == 0 then "" else natToString (m / 12) ++ "Y")
             ++ (if m % 12 == 0 then "" else natToString (m % 12) ++ "M")
             ++ (if days == 0 then "" else intToString days ++ "D")
  let tPart := (if hours == 0 then "" else intToString hours ++ "H")
             ++ (if mins == 0 then "" else intToString mins ++ "M")
             ++ secStr
  let body := dPart ++ (if tPart == "" then "" else "T" ++ tPart)
  (if neg then "-" else "") ++ "P" ++ (if body == "" then "T0S" else body)

/-- The canonical representation of a `float`/`double` value. The
specification's §3.3.4.2 mapping emits the SHORTEST numeral that maps
back to the same value; this emits the exact decimal expansion of the
binary value in the same `d.dddE±e` shape. Both round-trip
(`canonicalRoundTrips` in `DatatypesTheorems.lean`); only the digit
count differs, and the difference is recorded as open in
`docs/designissues/2026-09-07-xml-schema-datatypes.md`. -/
def canonicalFval (v : Fval) : String :=
  match v.cls with
  | .nan => "NaN"
  | .inf => if v.neg then "-INF" else "INF"
  | .zero => if v.neg then "-0.0E0" else "0.0E0"
  | .finite m e =>
      let num : Nat := if e ≥ 0 then m * 2 ^ e.toNat else m
      -- num/den is exact and den is a power of two, so multiplying by
      -- 5^k for den = 2^k gives an exact decimal.
      let k : Nat := if e ≥ 0 then 0 else (-e).toNat
      let mantissa : Nat := num * 5 ^ k
      let d : Dec := Dec.norm ⟨(if v.neg then -(mantissa : Int) else mantissa), k⟩
      let digits := natToString d.mantissa.natAbs
      let exp : Int := (digits.length : Int) - 1 - (d.scale : Int)
      let head := (digits.take 1).toString
      let tail := (digits.drop 1).toString
      (if v.neg then "-" else "") ++ head ++ "."
        ++ (if tail == "" then "0" else tail) ++ "E" ++ intToString exp

/-- The canonical mapping of §3.3/§3.4, as a function of the datatype
and the value. -/
def canonicalMapFuel : Nat → Builtin → Val → String
  | 0, _, _ => ""
  | fuel + 1, b, v =>
    match v with
    | .str _ s => if b.whiteSpace == .collapse then wsCollapse s
                  else if b.whiteSpace == .replace then wsReplace s else s
    | .bool x => if x then "true" else "false"
    | .dec d => if derivedFrom b .integer then intToString (Dec.norm d).mantissa
                else Dec.canonical d
    | .flt f => canonicalFval f
    | .dbl f => canonicalFval f
    | .dur d => canonicalDuration d
    | .dt k w => canonicalDateTime k w
    | .bin isHex bs => if isHex then hexOfBytes bs else base64OfBytes bs
    | .qname p l _ => if p == "" then l else p ++ ":" ++ l
    | .seq vs =>
        let item := (builtinListItem? b).getD .string
        String.intercalate " " (vs.map (fun x => canonicalMapFuel fuel item x))

/-- The canonical mapping of §3.3/§3.4 (§3.1.2 for a list). -/
def canonicalMap (b : Builtin) (v : Val) : String := canonicalMapFuel 4 b v

end L4Factoidal.XSD
