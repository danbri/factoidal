/-
L4Factoidal.XSD.SimpleType — XML Schema 1.1 Part 2 §4.3, the
constraining facets, and §4.1-§4.2, the three ways a simple type is
constructed: restriction of another simple type, `list`, and `union`.

  https://www.w3.org/TR/xmlschema11-2/#rf-facets

`validate` decides "·locally valid· with respect to this simple type"
for a character string, which is the whole of datatype validation:
apply `whiteSpace` (§4.3.6), test the `pattern` facets against the
normalized literal (§4.3.4), map it through the base type's lexical
mapping (`XSD.Datatypes.lexicalMap`), and test the value-space facets
against the resulting value.

## Facet checking order is not arbitrary

`whiteSpace` is applied before everything, because every other facet
speaks about the normalized literal or the value it maps to. `pattern`
is the only facet on the LEXICAL form; every other constraining facet
here is on the VALUE, so a lexical form outside the base type's
lexical space fails before any of them is consulted.

## Assertions and `explicitTimezone`

`explicitTimezone` (§4.3.13, new in 1.1) is decided here. `assertion`
(§4.3.12) needs XPath 2.0 over the value, which is
`L4Factoidal.XPath`; the field is carried so a schema that declares
one is CLASSIFIED as carrying an assertion rather than silently
validated without it.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.XSD

open L4Factoidal.Regex

/-- §4.3.13: the three values of `explicitTimezone`. -/
inductive ExplicitTz where
  | required | prohibited | optional
deriving DecidableEq, Repr, Inhabited

/-- The constraining facets of §4.3. `patterns` is a list of
ALTERNATIVE groups: within one restriction step several `pattern`
elements are alternatives (§4.3.4: "the value ... is the union"), and
across steps they conjoin, so the outer list is a conjunction of
disjunctions. -/
structure Facets where
  length       : Option Nat := none
  minLength    : Option Nat := none
  maxLength    : Option Nat := none
  patterns     : List (List String) := []
  enumeration  : Option (List String) := none
  whiteSpace   : Option WhiteSpace := none
  maxInclusive : Option String := none
  maxExclusive : Option String := none
  minInclusive : Option String := none
  minExclusive : Option String := none
  totalDigits  : Option Nat := none
  fractionDigits : Option Nat := none
  explicitTimezone : Option ExplicitTz := none
  /-- §4.3.12: an `assert` was declared. Not decided here. -/
  hasAssertion : Bool := false
deriving Repr, Inhabited

def Facets.empty : Facets := {}

/-- Merge a base type's effective facets with the ones a restriction
step adds (§4.1.2: the derived type's facets override, except
`pattern` and `enumeration`, which further restrict). -/
def Facets.merge (base derived : Facets) : Facets :=
  { length := derived.length.orElse (fun _ => base.length)
    minLength := derived.minLength.orElse (fun _ => base.minLength)
    maxLength := derived.maxLength.orElse (fun _ => base.maxLength)
    patterns := base.patterns ++ derived.patterns
    enumeration := derived.enumeration.orElse (fun _ => base.enumeration)
    whiteSpace := derived.whiteSpace.orElse (fun _ => base.whiteSpace)
    maxInclusive := derived.maxInclusive.orElse (fun _ => base.maxInclusive)
    maxExclusive := derived.maxExclusive.orElse (fun _ => base.maxExclusive)
    minInclusive := derived.minInclusive.orElse (fun _ => base.minInclusive)
    minExclusive := derived.minExclusive.orElse (fun _ => base.minExclusive)
    totalDigits := derived.totalDigits.orElse (fun _ => base.totalDigits)
    fractionDigits := derived.fractionDigits.orElse (fun _ => base.fractionDigits)
    explicitTimezone :=
      derived.explicitTimezone.orElse (fun _ => base.explicitTimezone)
    hasAssertion := base.hasAssertion || derived.hasAssertion }

/-- §4.1: a simple type definition, in the three variants of §4.1.1
(`{variety}` atomic, list, union). `atomic` carries the built-in it is
ultimately derived from, with the accumulated facets. -/
inductive SimpleType where
  | atomic (base : Builtin) (facets : Facets)
  | list (item : SimpleType) (facets : Facets)
  | union (members : List SimpleType) (facets : Facets)
deriving Repr, Inhabited

def SimpleType.facets : SimpleType → Facets
  | .atomic _ f => f
  | .list _ f   => f
  | .union _ f  => f

/-- The `whiteSpace` in force (§4.3.6): the facet if one is declared,
else `collapse` for a list or union, else the built-in's fixed value. -/
def SimpleType.whiteSpaceOf : SimpleType → WhiteSpace
  | .atomic b f => f.whiteSpace.getD b.whiteSpace
  | .list _ f   => f.whiteSpace.getD .collapse
  | .union _ f  => f.whiteSpace.getD .collapse

/-! ## §4.3.1-§4.3.3 — length -/

/-- The `length` of a value, in the unit §4.3.1 gives its datatype:
characters for the string family, `anyURI` and the QName types; octets
for `hexBinary` and `base64Binary`; items for a list. `none` where
`length` does not apply. -/
def valueLength? : Val → Option Nat
  | .str _ s => some s.length
  | .bin _ bs => some bs.length
  | .qname p l _ => some ((if p == "" then l else p ++ ":" ++ l).length)
  | .seq vs => some vs.length
  | _ => none

/-! ## §4.3.4 — pattern -/

/-- Does the normalized literal match every pattern group? Within a
group the alternatives are a union; a pattern the XSD regular-
expression parser cannot read makes the group VACUOUS rather than
failing the value, and the count of those is reported by the runner
rather than folded into a score. -/
def patternMatches (groups : List (List String)) (lit : String) : Bool :=
  let w := lit.toList.map Char.toNat
  groups.all (fun alts =>
    let parsed := alts.filterMap XSDPattern.parseXsdPattern
    parsed.isEmpty || parsed.any (fun r => Exec.acceptsNorm r w))

/-- A pattern the parser cannot read — reported, never scored. -/
def unreadablePatterns (groups : List (List String)) : List String :=
  groups.flatMap (fun alts =>
    alts.filter (fun p => (XSDPattern.parseXsdPattern p).isNone))

/-! ## The value-space facets -/

/-- §4.3.7-§4.3.10: the bound is a lexical form of the BASE type, so it
is mapped through the same lexical mapping before comparison
(§4.3.7.1: "{value} must be in the value space of {base type
definition}"). An incomparable pair fails the facet. -/
def boundOk (b : Builtin) (v : Val) (bound : Option String)
    (ok : Ordering → Bool) : Bool :=
  match bound with
  | none => true
  | some lex =>
      match lexicalMapWs b lex with
      | none => false
      | some bv => match valCompare v bv with
                   | some o => ok o
                   | none   => false

def explicitTimezoneOk (t : Option ExplicitTz) : Val → Bool
  | .dt _ v =>
      match t with
      | none => true
      | some .required => v.tz.isSome
      | some .prohibited => v.tz.isNone
      | some .optional => true
  | _ => true

/-- Every facet of §4.3 that speaks about the value, for a value of
built-in `b`. -/
def valueFacetsOk (b : Builtin) (f : Facets) (v : Val) : Bool :=
  (match f.length, valueLength? v with
   | some n, some l => l == n | some _, none => true | none, _ => true) &&
  (match f.minLength, valueLength? v with
   | some n, some l => l ≥ n | some _, none => true | none, _ => true) &&
  (match f.maxLength, valueLength? v with
   | some n, some l => l ≤ n | some _, none => true | none, _ => true) &&
  boundOk b v f.minInclusive (fun o => o != .lt) &&
  boundOk b v f.maxInclusive (fun o => o != .gt) &&
  boundOk b v f.minExclusive (fun o => o == .gt) &&
  boundOk b v f.maxExclusive (fun o => o == .lt) &&
  (match f.totalDigits, v with
   | some n, .dec d => d.totalDigits ≤ n | some _, _ => true | none, _ => true) &&
  (match f.fractionDigits, v with
   | some n, .dec d => d.fractionDigits ≤ n
   | some _, _ => true | none, _ => true) &&
  explicitTimezoneOk f.explicitTimezone v &&
  (match f.enumeration with
   | none => true
   | some lexs =>
       lexs.any (fun lex =>
         match lexicalMapWs b lex with
         | some ev => valIdentical v ev
         | none    => false))

/-! ## §4.1.4 / §3.1.2 — validation -/

/-- The value a literal denotes under this simple type, or `none` when
it is not ·locally valid·. The fuel bounds the union/list nesting. -/
def valueOfFuel : Nat → SimpleType → String → Option Val
  | 0, _, _ => none
  | fuel + 1, t, lit =>
    let ws := t.whiteSpaceOf
    let norm := applyWhiteSpace ws lit
    let f := t.facets
    if !patternMatches f.patterns norm then none
    else match t with
    | .atomic b bf =>
        match lexicalMap b norm with
        | none => none
        | some v => if valueFacetsOk b bf v then some v else none
    | .list item lf =>
        let toks := norm.splitOn " " |>.filter (fun s => s != "")
        let vs := toks.map (fun s => valueOfFuel fuel item s)
        if vs.any Option.isNone then none
        else
          let v := Val.seq (vs.filterMap id)
          -- §4.3.1: on a list, length/minLength/maxLength count items,
          -- and enumeration and the bounds do not apply.
          if (match lf.length with | some n => vs.length == n | none => true) &&
             (match lf.minLength with | some n => vs.length ≥ n | none => true) &&
             (match lf.maxLength with | some n => vs.length ≤ n | none => true)
          then some v else none
    | .union members _ =>
        let hits := members.filterMap (fun m => valueOfFuel fuel m norm)
        hits.head?

def valueOf (t : SimpleType) (lit : String) : Option Val := valueOfFuel 8 t lit

/-- Is the literal ·locally valid· with respect to the simple type? -/
def validate (t : SimpleType) (lit : String) : Bool := (valueOf t lit).isSome

end L4Factoidal.XSD
