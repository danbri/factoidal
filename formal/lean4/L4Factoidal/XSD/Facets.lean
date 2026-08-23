/-
L4Factoidal.XSD.Facets — the OWL 2 datatype map as a decidable value
space.

Port of `formal/fstar/XSD.Facets.fst`. This is the concrete-domain
half of the OWL DL reasoner: it answers "can a value satisfy all of
these datatype constraints at once?" and "how many distinct values
can this space hold?", from the facets and enumerations a graph
carries.

## Every answer is one-sided

The consumer of an empty-value-space verdict is a CLASH, which
refutes a whole ontology. So a value may be dropped from a space only
on a PROOF that it is outside, never on a failure to prove it inside.
"Not proved equal" is not "proved distinct": `"3.0"^^xsd:decimal` and
`"3"^^xsd:integer` denote ONE value in OWL 2's unified numeric value
space, so a pair like that must answer `false` to both
`termProvablyEqual` and `termProvablyDistinct`, keeping the element
and withholding the clash.

Withholding is always sound. Manufacturing emptiness is not. Every
`none` and every "kept" element below is that rule being applied.

## Four number lines, not one

OWL 2 Syntax §4.1 says the value space of `owl:real` is DISJOINT from
those of `xsd:double` and `xsd:float`, and §4.2 keeps the two
floating-point spaces distinct from each other. So the numeric part
of the datatype map is three pairwise-disjoint value spaces, plus
`xsd:dateTime` as a fourth dimension:

* the `owl:real` line — `owl:real ⊃ owl:rational ⊃ xsd:decimal ⊃
  xsd:integer ⊃` the derived integer types. DENSE, so an open
  interval is empty only when its endpoints cross or coincide;
* the IEEE-754 single grid (`xsd:float`). DISCRETE, so an open
  interval between ADJACENT floats IS empty — which is the whole
  content of `Datatype-Float-Discrete-001`;
* the IEEE-754 double grid (`xsd:double`);
* UTC instants (`xsd:dateTime`).

Modelling them as one line would let `"1.0"^^xsd:float` be proved
equal to `"1.0"^^xsd:decimal`, which OWL 2 denies.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.XSD

open L4Factoidal.RDF

/-! ## Datatype IRIs -/

def owlReal : WfIri := ⟨"http://www.w3.org/2002/07/owl#real", rfl⟩
def owlRational : WfIri := ⟨"http://www.w3.org/2002/07/owl#rational", rfl⟩
def xsdFloat : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#float", rfl⟩
def xsdDateTime : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTime", rfl⟩
def xsdLong : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#long", rfl⟩
def xsdInt : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#int", rfl⟩
def xsdShort : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#short", rfl⟩
def xsdByte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩
def xsdUnsignedLong : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedLong", rfl⟩
def xsdUnsignedInt : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedInt", rfl⟩
def xsdUnsignedShort : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedShort", rfl⟩
def xsdUnsignedByte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedByte", rfl⟩
def xsdNonNegativeInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩
def xsdPositiveInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#positiveInteger", rfl⟩
def xsdNonPositiveInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#nonPositiveInteger", rfl⟩
def xsdNegativeInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#negativeInteger", rfl⟩

def facetMinIncl : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#minInclusive", rfl⟩
def facetMaxIncl : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#maxInclusive", rfl⟩
def facetMinExcl : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#minExclusive", rfl⟩
def facetMaxExcl : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#maxExclusive", rfl⟩

def isFloatDatatype (dt : WfIri) : Bool := dt == xsdFloat

def isFloatingPointDatatype (dt : WfIri) : Bool := dt == xsdFloat || dt == xsdDouble

def isDateTimeDatatype (dt : WfIri) : Bool := dt == xsdDateTime

/-- The three datatypes whose value space is DENSE and unbounded. A
    min/max pair over one of them is empty only when its endpoints
    cross or coincide — never merely by adjacency, the way an
    integer-granularity pair can be. -/
def isDenseNumericDatatype (dt : WfIri) : Bool :=
  dt == owlReal || dt == owlRational || dt == xsdDecimal

def isIntegerFamilyDatatype (dt : WfIri) : Bool :=
  dt == xsdInteger || dt == xsdLong || dt == xsdInt || dt == xsdShort ||
  dt == xsdByte || dt == xsdUnsignedLong || dt == xsdUnsignedInt ||
  dt == xsdUnsignedShort || dt == xsdUnsignedByte ||
  dt == xsdNonNegativeInteger || dt == xsdPositiveInteger ||
  dt == xsdNonPositiveInteger || dt == xsdNegativeInteger

/-- The base families whose value spaces are pairwise disjoint. -/
inductive Family where
  | numeric   -- the owl:real number line
  | string
  | boolean
  | float     -- the IEEE single grid, plus the three specials
  | double    -- the IEEE double grid, plus the three specials
  deriving DecidableEq, Repr, Inhabited

/-- `xsd:dateTime` is deliberately NOT classified. A dateTime-typed
    filler simply never takes part in the family clash, which is
    sound: nothing is falsely flagged, a real dateTime clash is just
    not caught by this rule. -/
def classifyFamily (dt : WfIri) : Option Family :=
  if isIntegerFamilyDatatype dt || isDenseNumericDatatype dt then some .numeric
  else if dt == xsdString then some .string
  else if dt == xsdBoolean then some .boolean
  else if dt == xsdFloat then some .float
  else if dt == xsdDouble then some .double
  else none

/-! ## Integer lexical forms -/

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def digitVal (c : Char) : Int := (c.toNat : Int) - 48

/-- An optional sign then a run of digits, fully consumed. Anything
    else is `none` and every caller DROPS it. -/
def parseFacetInt (lex : String) : Option Int :=
  let cs := lex.toList
  let (neg, rest) := match cs with
    | '-' :: tl => (true, tl)
    | '+' :: tl => (false, tl)
    | _         => (false, cs)
  if rest.isEmpty || !(rest.all isAsciiDigit) then none
  else
    let v := rest.foldl (fun a c => a * 10 + digitVal c) (0 : Int)
    some (if neg then -v else v)

def literalIntValue (l : Literal) : Option Int :=
  if isIntegerFamilyDatatype l.datatype then parseFacetInt l.lexicalForm else none

def termIntOpt : Term → Option Int
  | .literal l => literalIntValue l.val
  | _          => none

def termFamily : Term → Option Family
  | .literal l => classifyFamily l.val.datatype
  | _          => none

def termBoolOpt : Term → Option Bool
  | .literal l =>
      if l.val.datatype == xsdBoolean then
        if l.val.lexicalForm == "true" || l.val.lexicalForm == "1" then some true
        else if l.val.lexicalForm == "false" || l.val.lexicalForm == "0" then some false
        else none
      else none
  | _ => none

/-! ## Integer-granularity intervals -/

inductive Bnd where
  | unbounded
  | incl (v : Int)
  | excl (v : Int)
  deriving DecidableEq, Repr, Inhabited

structure Interval where
  lo : Bnd := .unbounded
  hi : Bnd := .unbounded
  deriving DecidableEq, Repr, Inhabited

def fullInterval : Interval := {}

/-- PROVABLY empty — contains no INTEGER. An interval unbounded on
    either side is never reported empty: absence of a proof is not a
    proof of absence. -/
def intervalEmpty (iv : Interval) : Bool :=
  match iv.lo, iv.hi with
  | .incl lo, .incl hi => lo > hi
  | .incl lo, .excl hi => lo ≥ hi
  | .excl lo, .incl hi => lo ≥ hi
  | .excl lo, .excl hi => lo ≥ hi - 1
  | _, _               => false

/-- PROVABLY empty over a DENSE order. The discrete rule's
    `excl, excl → lo ≥ hi - 1` is UNSOUND here: `minExclusive T` with
    `maxExclusive T+1ms` is NOT empty, because `T+0.5ms` exists. An
    open interval on a dense line is empty only when its endpoints
    cross or coincide. -/
def intervalEmptyDense (iv : Interval) : Bool :=
  match iv.lo, iv.hi with
  | .incl lo, .incl hi => lo > hi
  | .incl lo, .excl hi => lo ≥ hi
  | .excl lo, .incl hi => lo ≥ hi
  | .excl lo, .excl hi => lo ≥ hi
  | _, _               => false

def tighterLo : Bnd → Bnd → Bnd
  | .unbounded, b => b
  | a, .unbounded => a
  | .incl x, .incl y => if x ≥ y then .incl x else .incl y
  | .excl x, .excl y => if x ≥ y then .excl x else .excl y
  | .incl x, .excl y => if x > y then .incl x else .excl y
  | .excl x, .incl y => if x ≥ y then .excl x else .incl y

def tighterHi : Bnd → Bnd → Bnd
  | .unbounded, b => b
  | a, .unbounded => a
  | .incl x, .incl y => if x ≤ y then .incl x else .incl y
  | .excl x, .excl y => if x ≤ y then .excl x else .excl y
  | .incl x, .excl y => if x < y then .incl x else .excl y
  | .excl x, .incl y => if x ≤ y then .excl x else .incl y

def intervalIntersect (a b : Interval) : Interval :=
  { lo := tighterLo a.lo b.lo, hi := tighterHi a.hi b.hi }

def valueInInterval (v : Int) (iv : Interval) : Bool :=
  (match iv.lo with | .unbounded => true | .incl lo => v ≥ lo | .excl lo => v > lo) &&
  (match iv.hi with | .unbounded => true | .incl hi => v ≤ hi | .excl hi => v < hi)

/-- The natural bounds of the finite integer subtypes. `xsd:integer`,
    `xsd:long` and `xsd:unsignedLong` get NO finite bound: none of the
    corpus fixtures need one, and inventing a bound would be unsound
    narrowing. -/
def baseIntervalFor (dt : WfIri) : Interval :=
  if dt == xsdByte then { lo := .incl (-128), hi := .incl 127 }
  else if dt == xsdUnsignedByte then { lo := .incl 0, hi := .incl 255 }
  else if dt == xsdShort then { lo := .incl (-32768), hi := .incl 32767 }
  else if dt == xsdUnsignedShort then { lo := .incl 0, hi := .incl 65535 }
  else if dt == xsdInt then { lo := .incl (-2147483648), hi := .incl 2147483647 }
  else if dt == xsdUnsignedInt then { lo := .incl 0, hi := .incl 4294967295 }
  else if dt == xsdNonNegativeInteger then { lo := .incl 0 }
  else if dt == xsdPositiveInteger then { lo := .incl 1 }
  else if dt == xsdNonPositiveInteger then { hi := .incl 0 }
  else if dt == xsdNegativeInteger then { hi := .incl (-1) }
  else fullInterval

/-- Fold one facet into an interval, given the value it names. A
    facet IRI this does not recognise leaves the accumulator
    untouched — sound narrowing: fewer constraints only make
    refutation harder. -/
def foldBound (firi : WfIri) (v : Int) (acc : Interval) : Interval :=
  if firi == facetMinIncl then intervalIntersect acc { lo := .incl v }
  else if firi == facetMaxIncl then intervalIntersect acc { hi := .incl v }
  else if firi == facetMinExcl then intervalIntersect acc { lo := .excl v }
  else if firi == facetMaxExcl then intervalIntersect acc { hi := .excl v }
  else acc

/-- Facets to an interval, restricted to min/max Inclusive/Exclusive
    on an INTEGER-family base. Every other facet and every other base
    type is dropped. -/
def facetsToInterval (baseDt : WfIri) (facets : List (WfIri × Term)) (acc : Interval)
    : Interval :=
  if !(isIntegerFamilyDatatype baseDt) then acc
  else facets.foldl (fun a (firi, fval) =>
    match fval with
    | .literal l => (match parseFacetInt l.val.lexicalForm with
                     | some v => foldBound firi v a
                     | none   => a)
    | _          => a) acc

/-! ## `xsd:dateTime` as a UTC millisecond key

An instant is a point on a fourth dimension, disjoint from every
numeric one. The key is the UTC-normalised millisecond count, and a
value WITHOUT an explicit timezone gets NO key: its instant is only
partially ordered against timezoned bounds (XML Schema leaves the
mixed comparison indeterminate), so it is kept in every intersection
rather than compared.

`L4Factoidal/SHACL/Validation.lean` carries the same parser for the
SHACL ordering facets. The duplication is deliberate and matches the
F\* tree: this module sits below SHACL in the import order, and the
two differ in exactly the place that matters — SHACL returns the
has-timezone flag and compares only same-flag pairs, this one drops
an untimezoned value outright. -/

def daysFromCivil (y m d : Int) : Int :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := (if y' ≥ 0 then y' else y' - 399) / 400
  let yoe := y' - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def substrOf (s : String) (start len : Nat) : String :=
  String.ofList ((s.toList.drop start).take len)

def parseDigitsSub (s : String) (start len : Nat) : Option Int :=
  let cs := (s.toList.drop start).take len
  if cs.length != len || !(cs.all isAsciiDigit) then none
  else some (cs.foldl (fun a c => a * 10 + digitVal c) 0)

/-- The `(.fraction)?(Z|±HH:MM)?` tail: fraction in ms, timezone
    offset in seconds, and whether a timezone was present. -/
def dtParseTail (tail : String) : Option (Int × Int × Bool) :=
  let cs := tail.toList
  let (fracMs, tzStart) : Option Int × Nat :=
    match cs with
    | '.' :: rest =>
        let digits := rest.takeWhile isAsciiDigit
        if digits.isEmpty then (none, 0)
        else
          let digLen := min digits.length 3
          match parseFacetInt (String.ofList (digits.take digLen)) with
          | some f =>
              let ms := if digLen == 1 then f * 100 else if digLen == 2 then f * 10 else f
              (some ms, 1 + digits.length)
          | none => (none, 0)
    | _ => (some 0, 0)
  match fracMs with
  | none      => none
  | some fms  =>
    let rest := cs.drop tzStart
    match rest with
    | []      => some (fms, 0, false)
    | ['Z']   => some (fms, 0, true)
    | sign :: _ =>
        if rest.length == 6 && (sign == '+' || sign == '-') then
          match parseFacetInt (String.ofList ((rest.drop 1).take 2)),
                parseFacetInt (String.ofList ((rest.drop 4).take 2)) with
          | some th, some tm =>
              let off := th * 3600 + tm * 60
              some (fms, if sign == '-' then -off else off, true)
          | _, _ => none
        else none

/-- The UTC millisecond key of a TIMEZONED `xsd:dateTime`. An
    untimezoned value, an expanded or negative year, or a malformed
    field answers `none` and is dropped. -/
def dtParseUtcMs (s : String) : Option Int :=
  let len := s.length
  if len < 19 then none
  else if substrOf s 0 1 == "-" then none
  else
    match parseDigitsSub s 0 4, parseDigitsSub s 5 2, parseDigitsSub s 8 2,
          parseDigitsSub s 11 2, parseDigitsSub s 14 2, parseDigitsSub s 17 2 with
    | some y, some mo, some d, some h, some mi, some se =>
        (match dtParseTail (String.ofList (s.toList.drop 19)) with
         | some (fms, tzoff, hasTz) =>
             if hasTz then
               let days := daysFromCivil y mo d
               let secs := days * 86400 + h * 3600 + mi * 60 + se - tzoff
               some (secs * 1000 + fms)
             else none
         | none => none)
    | _, _, _, _, _, _ => none

def termDateTimeKey : Term → Option Int
  | .literal l => if l.val.datatype == xsdDateTime then dtParseUtcMs l.val.lexicalForm
                  else none
  | _          => none

def dateTimeFacetsToInterval (facets : List (WfIri × Term)) (acc : Interval) : Interval :=
  facets.foldl (fun a (firi, fval) =>
    match termDateTimeKey fval with
    | some v => foldBound firi v a
    | none   => a) acc

/-! ## Exact rationals — the shared endpoint model of the `owl:real` line

`"0.5"^^xsd:decimal` and `"1/2"^^owl:rational` are the SAME real, and
this module has to be able to prove it. The value is carried as an
exact fraction, never as a float: rounding here would let two
different reals be proved equal.
-/

structure Rat where
  num : Int
  den : Int      -- always positive; the constructors below keep it so
  deriving DecidableEq, Repr, Inhabited

def pow10 : Nat → Int
  | 0     => 1
  | n + 1 => 10 * pow10 n

def pow2i : Nat → Int
  | 0     => 1
  | n + 1 => 2 * pow2i n

/-- Two exact rationals are equal exactly when the cross products
    agree. Both denominators are positive, so this needs no case
    split. -/
def ratEq (a b : Rat) : Bool := a.num * b.den == b.num * a.den
def ratLe (a b : Rat) : Bool := a.num * b.den ≤ b.num * a.den
def ratLt (a b : Rat) : Bool := a.num * b.den < b.num * a.den

/-- A maximal run of digits: its value, its length, and the rest. -/
def spanDigits : List Char → Int → Nat → Int × Nat × List Char
  | c :: tl, v, n => if isAsciiDigit c then spanDigits tl (v * 10 + digitVal c) (n + 1)
                     else (v, n, c :: tl)
  | [],      v, n => (v, n, [])

/-- `[+-]? d* ('.' d*)? ([eE] [+-]? d+)?` with at least one mantissa
    digit and FULL consumption. Anything else is `none`, and every
    caller drops it rather than guessing. -/
def parseDecimalRat (lex : String) : Option Rat :=
  let cs0 := lex.toList
  let (neg, cs1) := match cs0 with
    | '-' :: tl => (true, tl)
    | '+' :: tl => (false, tl)
    | _         => (false, cs0)
  let (ipart, ilen, cs2) := spanDigits cs1 0 0
  let (fpart, flen, cs3) := match cs2 with
    | '.' :: tl => spanDigits tl 0 0
    | _         => (0, 0, cs2)
  let (okExp, expv, cs4) := match cs3 with
    | c :: tl =>
        if c == 'e' || c == 'E' then
          let (eneg, ed) := match tl with
            | '-' :: tl2 => (true, tl2)
            | '+' :: tl2 => (false, tl2)
            | _          => (false, tl)
          let (ev, elen, r) := spanDigits ed 0 0
          if elen == 0 then (false, (0 : Int), r) else (true, (if eneg then -ev else ev), r)
        else (true, (0 : Int), cs3)
    | [] => (true, (0 : Int), cs3)
  if !okExp || !cs4.isEmpty || ilen + flen == 0 then none
  else
    let mantissa := ipart * pow10 flen + fpart
    let net := expv - flen
    let signed := if neg then -mantissa else mantissa
    if net ≥ 0 then some { num := signed * pow10 net.toNat, den := 1 }
    else some { num := signed, den := pow10 (-net).toNat }

def splitSlash (cs : List Char) : Option (List Char × List Char) :=
  match cs.findIdx? (· == '/') with
  | some i => some (cs.take i, cs.drop (i + 1))
  | none   => none

def parseRationalLex (lex : String) : Option Rat :=
  match splitSlash lex.toList with
  | none => none
  | some (ns, ds) =>
    match parseFacetInt (String.ofList ns), parseFacetInt (String.ofList ds) with
    | some n, some d => if d > 0 then some { num := n, den := d } else none
    | _,      _      => none

/-- The exact rational value of a literal whose datatype places it on
    the `owl:real` line with an EXACT lexical-to-value map.
    `xsd:float` and `xsd:double` are deliberately absent: their value
    is the ROUNDED grid point, a different value space, and
    conflating them would be unsound. -/
def termExactRat : Term → Option Rat
  | .literal l =>
      if isIntegerFamilyDatatype l.val.datatype then
        (parseFacetInt l.val.lexicalForm).map (fun v => { num := v, den := 1 })
      else if l.val.datatype == xsdDecimal then parseDecimalRat l.val.lexicalForm
      else if l.val.datatype == owlRational then parseRationalLex l.val.lexicalForm
      else none
  | _ => none

/-! ## Dense intervals with exact rational endpoints -/

inductive QBnd where
  | unbounded
  | incl (v : Rat)
  | excl (v : Rat)
  deriving DecidableEq, Repr, Inhabited

structure QInterval where
  lo : QBnd := .unbounded
  hi : QBnd := .unbounded
  deriving DecidableEq, Repr, Inhabited

def fullQInterval : QInterval := {}

def ratInQInterval (v : Rat) (iv : QInterval) : Bool :=
  (match iv.lo with
   | .unbounded => true | .incl lo => ratLe lo v | .excl lo => ratLt lo v) &&
  (match iv.hi with
   | .unbounded => true | .incl hi => ratLe v hi | .excl hi => ratLt v hi)

def qTighterLo : QBnd → QBnd → QBnd
  | .unbounded, b => b
  | a, .unbounded => a
  | .incl x, .incl y => if ratLe y x then .incl x else .incl y
  | .excl x, .excl y => if ratLe y x then .excl x else .excl y
  | .incl x, .excl y => if ratLt y x then .incl x else .excl y
  | .excl x, .incl y => if ratLe y x then .excl x else .incl y

def qTighterHi : QBnd → QBnd → QBnd
  | .unbounded, b => b
  | a, .unbounded => a
  | .incl x, .incl y => if ratLe x y then .incl x else .incl y
  | .excl x, .excl y => if ratLe x y then .excl x else .excl y
  | .incl x, .excl y => if ratLt x y then .incl x else .excl y
  | .excl x, .incl y => if ratLe x y then .excl x else .incl y

def qIntervalIntersect (a b : QInterval) : QInterval :=
  { lo := qTighterLo a.lo b.lo, hi := qTighterHi a.hi b.hi }

/-- DENSE emptiness: endpoints crossing or coinciding, never
    adjacency. Between any two distinct reals lies a third. -/
def qIntervalEmpty (iv : QInterval) : Bool :=
  match iv.lo, iv.hi with
  | .incl lo, .incl hi => ratLt hi lo
  | .incl lo, .excl hi => ratLe hi lo
  | .excl lo, .incl hi => ratLe hi lo
  | .excl lo, .excl hi => ratLe hi lo
  | _, _               => false

def ratFloor (r : Rat) : Int := Int.fdiv r.num r.den
def ratCeil (r : Rat) : Int := -(Int.fdiv (-r.num) r.den)
def ratIsInteger (r : Rat) : Bool := r.num % r.den == 0

/-- The bridge from the dense line to integer granularity: ceil the
    lower bound, floor the upper. Exactly the integers the dense
    interval contains. -/
def qBndToLo : QBnd → Bnd
  | .unbounded => .unbounded
  | .incl r    => .incl (ratCeil r)
  | .excl r    => if ratIsInteger r then .incl (ratFloor r + 1) else .incl (ratCeil r)

def qBndToHi : QBnd → Bnd
  | .unbounded => .unbounded
  | .incl r    => .incl (ratFloor r)
  | .excl r    => if ratIsInteger r then .incl (ratCeil r - 1) else .incl (ratFloor r)

def qIntervalToInterval (iv : QInterval) : Interval :=
  { lo := qBndToLo iv.lo, hi := qBndToHi iv.hi }

def denseFacetsToQInterval (facets : List (WfIri × Term)) (acc : QInterval) : QInterval :=
  facets.foldl (fun a (firi, fval) =>
    match termExactRat fval with
    | none   => a
    | some v =>
      if firi == facetMinIncl then qIntervalIntersect a { lo := .incl v }
      else if firi == facetMaxIncl then qIntervalIntersect a { hi := .incl v }
      else if firi == facetMinExcl then qIntervalIntersect a { lo := .excl v }
      else if firi == facetMaxExcl then qIntervalIntersect a { hi := .excl v }
      else a) acc

/-! ## The IEEE-754 single grid — a DISCRETE value space

Between two ADJACENT floats lies no representable value. So an open
interval `(minExclusive a, maxExclusive b)` whose endpoints are
adjacent floats IS empty, though the same interval over the reals is
not — `Datatype-Float-Discrete-001` asks exactly that: `(0, 2^-149)`
holds no float, because `2^-149` is the smallest positive subnormal.

The grid is coordinatised by ORDINAL, the value's rank in the sorted
grid: `0.0` is 0, the k-th positive subnormal is k. Two floats are
adjacent exactly when their ordinals differ by 1, so emptiness
reduces to the DISCRETE `intervalEmpty` rule on an ordinal interval.

`floatOrdinalOfLexical` is partial BY DESIGN: it places only `0.0`
and the subnormal band, and only when the parsed exact rational lies
STRICTLY inside that ordinal's round-to-nearest window. A tie, a
negative, a normal, or anything it cannot place answers `none`, and
the caller DROPS the bound — which WIDENS the interval and therefore
withholds the emptiness verdict.
-/

def floatOrdinalOfLexical (lex : String) : Option Int :=
  match parseDecimalRat lex with
  | none   => none
  | some r =>
    if r.num == 0 then some 0
    else if r.num < 0 then none
    else
      let n150 := r.num * pow2i 150
      let den := r.den
      let k := (n150 + den) / (2 * den)
      if k ≥ 1 && k ≤ pow2i 23 - 1 &&
         (2 * k - 1) * den < n150 && n150 < (2 * k + 1) * den
      then some k else none

def floatFacetsToOrdinalInterval (facets : List (WfIri × Term)) (acc : Interval)
    : Interval :=
  facets.foldl (fun a (firi, fval) =>
    match fval with
    | .literal l => (match floatOrdinalOfLexical l.val.lexicalForm with
                     | some v => foldBound firi v a
                     | none   => a)
    | _          => a) acc

/-- Is a `DatatypeRestriction` over `xsd:float` PROVABLY empty on the
    grid? Only when the ordinal interval is empty by the DISCRETE
    rule. An unknown ordinal widens the interval, so this never fires
    on a doubt. -/
def floatRestrictionProvablyEmpty (dt : WfIri) (facets : List (WfIri × Term)) : Bool :=
  isFloatDatatype dt && intervalEmpty (floatFacetsToOrdinalInterval facets fullInterval)

/-! ## The three IEEE specials

XSD 1.1 §3.3.5 and §3.3.6: each floating-point value space is the
grid "together with the three special values positive infinity,
negative infinity and not-a-number". They are the only members no
decimal lexical form denotes, so the parser above refuses them —
correct, but silent. Naming them makes the reason explicit and gives
the `owl:real` membership test something to point at: an infinity is
not a real number, so no `owl:real` constraint can admit one. That is
what the W3C test "Minus Infinity is not in owl:real" turns on. -/

inductive FloatSpecial where
  | posInf | negInf | nan
  deriving DecidableEq, Repr, Inhabited

def floatSpecialOfLexical (lex : String) : Option FloatSpecial :=
  if lex == "INF" || lex == "+INF" then some .posInf
  else if lex == "-INF" then some .negInf
  else if lex == "NaN" then some .nan
  else none

def termFloatSpecial : Term → Option FloatSpecial
  | .literal l => if isFloatingPointDatatype l.val.datatype
                  then floatSpecialOfLexical l.val.lexicalForm else none
  | _          => none

/-- THREE-VALUED membership in the `owl:real` value space.
    `some false` is a PROOF of exclusion, not a failure to include:
    OWL 2 Syntax §4.1 puts `xsd:float` and `xsd:double` outside
    `owl:real`, and XSD §3 makes the string and boolean spaces
    disjoint from it. An unrecognised datatype answers `none`, and no
    caller may turn that into "proved out". -/
def termInOwlReal : Term → Option Bool
  | .literal l => (match classifyFamily l.val.datatype with
                   | some .numeric => some true
                   | some _        => some false
                   | none          => none)
  | _          => none

/-! ## Provable equality and provable distinctness

The load-bearing pair. Both are one-sided, and a value that fails
BOTH is unknown — kept in every intersection, removed by no
complement. -/

def termProvablyEqual (a b : Term) : Bool :=
  a.eqb b
  || (match termIntOpt a, termIntOpt b with
      | some x, some y => x == y
      | _,      _      => false)
  || (match termBoolOpt a, termBoolOpt b with
      | some x, some y => x == y
      | _,      _      => false)
  -- Exact-rational equality ACROSS the owl:real line:
  -- `"0.5"^^xsd:decimal` and `"1/2"^^owl:rational` denote one real, so
  -- a `DataOneOf` enumerating them holds ONE value, not two.
  || (match termExactRat a, termExactRat b with
      | some x, some y => ratEq x y
      | _,      _      => false)

def bothString (a b : Term) : Bool :=
  match a, b with
  | .literal la, .literal lb =>
      la.val.datatype == xsdString && lb.val.datatype == xsdString
  | _, _ => false

def stringLexNeq (a b : Term) : Bool :=
  match a, b with
  | .literal la, .literal lb => la.val.lexicalForm != lb.val.lexicalForm
  | _, _ => false

def termProvablyDistinct (a b : Term) : Bool :=
  (match termIntOpt a, termIntOpt b with
   | some x, some y => x != y
   | _,      _      => false)
  || (match termFamily a, termFamily b with
      | some fa, some fb => fa != fb
      | _,       _       => false)
  || (bothString a b && stringLexNeq a b)
  || (match termBoolOpt a, termBoolOpt b with
      | some x, some y => x != y
      | _,      _      => false)

/-! ## Value sets -/

inductive ValueSet where
  | unconstrained
  | interval     (iv : Interval)
  /-- A DENSE stretch of the `owl:real` line. Kept apart from
      `interval` because emptiness there is the dense rule. -/
  | dense        (qi : QInterval)
  | dateInterval (iv : Interval)
  | enum         (xs : List Term)
  | family       (f : Family)
  | empty
  deriving Repr, Inhabited

def filterEnumBy (f : Term → Bool) (xs : List Term) : List Term := xs.filter f

/-- Keep `h` unless it is provably distinct from EVERY member of the
    other operand — drop only on a PROOF of absence. -/
def enumIntersect (xs ys : List Term) : List Term :=
  xs.filter (fun h => !(ys.all (termProvablyDistinct h)))

/-- Drop from an integer interval only when PROVABLY outside. A
    decimal or an unrecognised datatype is KEPT: its value might lie
    inside — `"5.0"^^xsd:decimal` is in `[4, 10]`. -/
def provablyOutsideInterval (iv : Interval) (t : Term) : Bool :=
  (match termIntOpt t with
   | some v => !(valueInInterval v iv)
   | none   => false)
  || (match termFamily t with
      | some f => f != Family.numeric
      | none   => false)

def provablyOutsideFamily (f : Family) (t : Term) : Bool :=
  match termFamily t with
  | some g => f != g
  | none   => false

/-- A timezone-less dateTime is KEPT: its instant is only partially
    ordered against timezoned bounds, so it might lie inside. -/
def provablyOutsideDateInterval (iv : Interval) (t : Term) : Bool :=
  (match termDateTimeKey t with
   | some v => !(valueInInterval v iv)
   | none   => false)
  || (termFamily t).isSome

def provablyOutsideDense (iv : QInterval) (t : Term) : Bool :=
  (match termExactRat t with
   | some q => !(ratInQInterval q iv)
   | none   => false)
  || (match termFamily t with
      | some f => f != Family.numeric
      | none   => false)

private def enumOr (e : List Term) : ValueSet :=
  if e.isEmpty then .empty else .enum e

def valueSetIntersect : ValueSet → ValueSet → ValueSet
  | .empty, _ => .empty
  | _, .empty => .empty
  | .unconstrained, x => x
  | x, .unconstrained => x
  | .dense qa, .dense qb =>
      let qi := qIntervalIntersect qa qb
      if qIntervalEmpty qi then .empty else .dense qi
  -- Integers ARE reals, so a dense stretch meeting an
  -- integer-granularity interval leaves exactly the integers in both.
  | .dense qa, .interval ib =>
      let ii := intervalIntersect (qIntervalToInterval qa) ib
      if intervalEmpty ii then .empty else .interval ii
  | .interval ia, .dense qb =>
      let ii := intervalIntersect ia (qIntervalToInterval qb)
      if intervalEmpty ii then .empty else .interval ii
  | .dense qa, .enum xs => enumOr (filterEnumBy (fun t => !(provablyOutsideDense qa t)) xs)
  | .enum xs, .dense qb => enumOr (filterEnumBy (fun t => !(provablyOutsideDense qb t)) xs)
  -- The owl:real line is disjoint from the string, boolean, float and
  -- double value spaces, and from xsd:dateTime.
  | .dense qa, .family f => if f == Family.numeric then .dense qa else .empty
  | .family f, .dense qb => if f == Family.numeric then .dense qb else .empty
  | .dense _, .dateInterval _ => .empty
  | .dateInterval _, .dense _ => .empty
  | .interval ia, .interval ib =>
      let ii := intervalIntersect ia ib
      if intervalEmpty ii then .empty else .interval ii
  | .dateInterval ia, .dateInterval ib =>
      let ii := intervalIntersect ia ib
      if intervalEmptyDense ii then .empty else .dateInterval ii
  | .dateInterval _, .interval _ => .empty
  | .interval _, .dateInterval _ => .empty
  | .dateInterval _, .family _ => .empty
  | .family _, .dateInterval _ => .empty
  | .dateInterval iv, .enum xs =>
      enumOr (filterEnumBy (fun t => !(provablyOutsideDateInterval iv t)) xs)
  | .enum xs, .dateInterval iv =>
      enumOr (filterEnumBy (fun t => !(provablyOutsideDateInterval iv t)) xs)
  | .enum xs, .enum ys => enumOr (enumIntersect xs ys)
  | .enum xs, .interval iv =>
      enumOr (filterEnumBy (fun t => !(provablyOutsideInterval iv t)) xs)
  | .interval iv, .enum xs =>
      enumOr (filterEnumBy (fun t => !(provablyOutsideInterval iv t)) xs)
  | .enum xs, .family f => enumOr (filterEnumBy (fun t => !(provablyOutsideFamily f t)) xs)
  | .family f, .enum xs => enumOr (filterEnumBy (fun t => !(provablyOutsideFamily f t)) xs)
  -- Every interval this module builds is over an integer-family base,
  -- so its value space is numeric: disjoint from string and boolean.
  | .interval iv, .family f => if f == Family.numeric then .interval iv else .empty
  | .family f, .interval iv => if f == Family.numeric then .interval iv else .empty
  | .family fa, .family fb => if fa == fb then .family fa else .empty

def valueSetIsEmpty : ValueSet → Bool
  | .empty          => true
  | .enum []        => true
  -- A restriction whose OWN facets already cross is empty before
  -- anything intersects it. Dense rule on both dense dimensions.
  | .dateInterval iv => intervalEmptyDense iv
  | .dense qi       => qIntervalEmpty qi
  | _               => false

/-- Subtract, for `DataComplementOf`. Only the enum/enum shape is
    representable exactly; every other combination is a sound no-op.
    An element is removed only when PROVABLY equal to a removed value
    — over-removal would manufacture emptiness. -/
def valueSetSubtract : ValueSet → ValueSet → ValueSet
  | .enum xs, .enum ys =>
      enumOr (filterEnumBy (fun t => !(ys.any (termProvablyEqual t))) xs)
  | acc, _ => acc

/-! ## How many values can this space hold?

A SOUND UPPER bound. The direction matters: the answer `M` must be at
least the true count, so that `k > M` implies `k` values cannot be
drawn. An over-count only WITHHOLDS a clash; an under-count would
manufacture one. -/

def bndLoIncl : Bnd → Option Int
  | .unbounded => none
  | .incl x    => some x
  | .excl x    => some (x + 1)

def bndHiIncl : Bnd → Option Int
  | .unbounded => none
  | .incl x    => some x
  | .excl x    => some (x - 1)

def intervalCount (iv : Interval) : Option Nat :=
  match bndLoIncl iv.lo, bndHiIncl iv.hi with
  | some lo, some hi => some (if hi ≥ lo then (hi - lo + 1).toNat else 0)
  | _,       _       => none

def dropProvablyEqual (h : Term) (xs : List Term) : List Term :=
  xs.filter (fun x => !(termProvablyEqual h x))

/-- Distinct-value count of a literal enum, collapsing ONLY
    provably-equal members — a sound upper bound. -/
partial def enumDistinctCount : List Term → Nat
  | []      => 0
  | h :: tl => 1 + enumDistinctCount (dropProvablyEqual h tl)

def valueSetMaxSize : ValueSet → Option Nat
  | .empty           => some 0
  | .enum []         => some 0
  | .enum xs         => some (enumDistinctCount xs)
  | .interval iv     => intervalCount iv
  | .dateInterval iv => if intervalEmptyDense iv then some 0 else none
  -- A non-empty stretch of the owl:real line holds infinitely many
  -- values, so no finite bound.
  | .dense qi        => if qIntervalEmpty qi then some 0 else none
  | .unconstrained   => none
  | .family _        => none

end L4Factoidal.XSD
