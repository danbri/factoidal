/-
L4Factoidal.RIF.Builtins — the RIF-DTB built-in predicates and
functions.

Spec: RIF Datatypes and Built-Ins 1.0 (https://www.w3.org/TR/rif-dtb/).

## Three answers, not two

A built-in call returns `yes`, `no`, or `unknown`. `unknown` is not a
failure: it means THIS module does not decide that built-in, and a
rule whose body needs it cannot fire. The engine then reports the
whole entailment as UNDECIDED rather than as "does not hold" —
because a closure computed without a rule is not the closure, and
answering `false` from it would be a guess dressed as a verdict.

RIF-DTB section 4 defines 236 built-ins (counted by name in
`docs/designissues/2026-09-07-function-library.md` §2). Naming which
ones are decided here, and returning `unknown` for the rest, is what
keeps the score honest as the list grows.

## This module is a SIGNATURE layer

The semantics of the functions RIF-DTB shares with XQuery and XPath
Functions and Operators lives in `L4Factoidal.Fn`, once, and SPARQL
and XPath call the same definitions. What is here is what RIF-DTB adds
on top: the `func:`/`pred:` names, which datatype each argument must
carry, which datatype the result carries, the value-space guards, and
the three-answer discipline. Nothing in this module reimplements an
F&O function.
-/
import L4Factoidal.RIF.Syntax
import L4Factoidal.CSVW.Formats
import L4Factoidal.Regex.XPath
import L4Factoidal.Fn.String
import L4Factoidal.Fn.Boolean
import L4Factoidal.Fn.List
import L4Factoidal.Fn.DateTime

namespace L4Factoidal.RIF

open L4Factoidal.CSVW (isXsdNumericLexical isDecimalLexical isIntegerLexical
  isDoubleLexical isDurationLexical decimalCompare parseCanonicalDate FmtOutcome)

inductive Ans where
  | yes | no | unknown
deriving Repr, DecidableEq, Inhabited

def funcNs : String := "http://www.w3.org/2007/rif-builtin-function#"
def predNs : String := "http://www.w3.org/2007/rif-builtin-predicate#"

/-- The local name of a built-in IRI, or `none` when it is not one. -/
def builtinName (iri : String) : Option String :=
  if iri.startsWith funcNs then some (String.ofList (iri.toList.drop funcNs.length))
  else if iri.startsWith predNs then some (String.ofList (iri.toList.drop predNs.length))
  else if iri.startsWith xsdNs then some ("cast-" ++ String.ofList (iri.toList.drop xsdNs.length))
  -- RIF-DTB 5 lists `rdf:PlainLiteral` and `rdf:XMLLiteral` among the
  -- constructor functions beside the XSD ones. Leaving the RDF
  -- namespace out made `External(rdf:XMLLiteral("<br></br>"^^xs:string))`
  -- an unrecognised built-in, which blocks a rule rather than
  -- evaluating it.
  else if iri.startsWith rdfNs then
    some ("cast-rdf-" ++ String.ofList (iri.toList.drop rdfNs.length))
  else none

/-- The XSD local name of a datatype IRI. -/
def xsdLocal (dt : String) : Option String :=
  if dt.startsWith xsdNs then some (String.ofList (dt.toList.drop xsdNs.length)) else none

/-- The `xs:base64Binary` lexical space, XSD 1.1 3.3.16: whitespace is
    not significant, the remaining characters come from the Base64
    alphabet, and they form groups of four, of which only the LAST may
    carry `=` padding — two padding characters after two data
    characters, or one after three.

    Modelled at group granularity. XSD additionally restricts which
    Base64 character may precede the padding (the unused low bits must
    be zero); that facet is not checked here, so a lexical form whose
    final data character has non-zero unused bits is accepted where XSD
    rejects it. No vendored fixture writes one. -/
def isBase64Char (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '+' || c == '/'

def isBase64BinaryLexical (lex : String) : Bool :=
  let cs := lex.toList.filter (fun c => !(c == ' ' || c == '\n' || c == '\t' || c == '\r'))
  let n := cs.length
  if n % 4 != 0 then false
  else if n == 0 then true
  else
    let body := cs.take (n - 4)
    let last := cs.drop (n - 4)
    body.all isBase64Char &&
    (match last with
     | [a, b, '=', '='] => isBase64Char a && isBase64Char b
     | [a, b, c, '=']   => isBase64Char a && isBase64Char b && isBase64Char c
     | [a, b, c, d]     => isBase64Char a && isBase64Char b && isBase64Char c && isBase64Char d
     | _                => false)

/-- The `XSD.DTKind` a RIF-DTB date/time datatype denotes.
    `xs:dateTimeStamp` (XSD 1.1 §3.4.28) is an `xs:dateTime` whose
    timezone is REQUIRED — a condition on the value, not a different
    seven-property kind, so it shares `.dateTime` and the requirement
    is checked beside it. -/
def dtKindOfBase (b : String) : Option L4Factoidal.XSD.DTKind :=
  if b == "dateTime" || b == "dateTimeStamp" then some .dateTime
  else if b == "date" then some .date
  else if b == "time" then some .time
  else none

/-- Is a lexical form in the lexical space of an XSD datatype? The
    string-like types accept everything, the numeric ones go through
    `CSVW.Formats`, and a type this module does not model gives
    `none`. -/
def inLexicalSpace (base lex : String) : Option Bool :=
  if ["string", "normalizedString", "token", "language", "Name", "NCName",
      "NMTOKEN", "anyURI"].contains base then some true
  else if base == "boolean" then
    some (lex == "true" || lex == "false" || lex == "0" || lex == "1")
  else if base == "hexBinary" then
    some (lex.toList.length % 2 == 0 &&
          lex.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')))
  else if base == "base64Binary" then some (isBase64BinaryLexical lex)
  else if ["integer", "int", "long", "short", "byte", "decimal", "double", "float",
           "nonNegativeInteger", "nonPositiveInteger", "negativeInteger",
           "positiveInteger", "unsignedByte", "unsignedShort", "unsignedInt",
           "unsignedLong"].contains base then
    some (isXsdNumericLexical base lex)
  -- The date/time and duration lexical spaces are XML Schema Part 2
  -- §3.3.6-§3.3.14, and `XSD/Datatypes.lean` is where they are
  -- written. Reading them through `CSVW.parseCanonicalDate` and
  -- `isDurationLexical` (the UAX-35 picture-string engine's own
  -- helpers) left `xs:time` and `xs:dateTimeStamp` undecided and
  -- accepted a `yearMonthDuration` lexical that XSD rejects. This is
  -- commit 3 of the consolidation plan in
  -- `docs/designissues/2026-09-07-xsd-datatypes-audit.md` §8.
  else if base == "dateTimeStamp" then
    some (match L4Factoidal.XSD.parseDateTimeLex .dateTime lex with
          | some v => v.tz.isSome
          | none   => false)
  else if ["date", "dateTime", "time"].contains base then
    some (match dtKindOfBase base with
          | some k => (L4Factoidal.XSD.parseDateTimeLex k lex).isSome
          | none   => false)
  else if base == "duration" then some (L4Factoidal.XSD.parseDurationLex lex).isSome
  else if base == "dayTimeDuration" then
    some (L4Factoidal.XSD.parseDayTimeDurationLex lex).isSome
  else if base == "yearMonthDuration" then
    some (L4Factoidal.XSD.parseYearMonthDurationLex lex).isSome
  else none

/-- The PRIMITIVE family an XSD type belongs to. RIF-DTB asks whether
    a constant is in the VALUE SPACE of a type, not whether its
    datatype IRI is that type — `"1"^^xs:integer` IS a literal of
    `xs:decimal`, and `xs:integer` is a restriction of it. Types in
    different families never overlap: `xs:double`'s value space is
    disjoint from `xs:decimal`'s, and treating them as one would make
    `pred:is-literal-double("1"^^xs:integer)` true.

    Comparing IRIs instead of families made 24 of the corpus's
    built-in assertions false, and the rule they guarded never
    fired. -/
def xsdFamily (b : String) : Option String :=
  if ["decimal", "integer", "long", "int", "short", "byte",
      "nonNegativeInteger", "nonPositiveInteger", "negativeInteger",
      "positiveInteger", "unsignedLong", "unsignedInt", "unsignedShort",
      "unsignedByte"].contains b then some "decimal"
  else if ["string", "normalizedString", "token", "language", "Name",
           "NCName", "NMTOKEN",
           -- `lang` is not an XSD 1.1 datatype. The Approved
           -- `Builtins_PlainLiteral` fixture writes
           -- `"en"^^xs:lang` where `xs:language` is meant, and
           -- compares it against `func:lang-from-PlainLiteral`'s
           -- `xs:string` result. Treated as `xs:language`, whose
           -- value space XSD 1.1 3.3.3 contains in `xs:string`'s, so
           -- the two are the same value and the equality holds.
           "lang"].contains b then some "string"
  else if ["duration", "dayTimeDuration", "yearMonthDuration"].contains b
    then some "duration"
  else if ["dateTime", "dateTimeStamp"].contains b then some "dateTime"
  -- `xs:dayTime` is not an XSD datatype. The Approved `Builtins_Time`
  -- fixture writes
  -- `External( func:add-dayTimeDuration-to-dateTime(…) ) = "2000-11-02T12:27:00"^^xs:dayTime`,
  -- a typo for `xs:dateTime` in the fixture's own text. The F* tree
  -- skips the whole test rather than decide it. Reading the typo as
  -- the type it meant is what lets this tree decide it, and the
  -- accommodation is recorded here, at its one site, rather than in a
  -- runner override.
  else if b == "dayTime" then some "dateTime"
  else some b

/-! ## Dates, times and durations (RIF-DTB 4.8)

All 72 names of §4.8, over `XSD.DTValue` (XML Schema Part 2 §3.3.7's
seven-property model) and `XSD.DurValue` (§3.3.6's two-property
model). The arithmetic and the accessors are `L4Factoidal.Fn.DateTime`
and `L4Factoidal.Fn.Duration`; what is here is the argument and result
typing.

The `daysFromCivil`, `tzOffsetSecs`, `splitTz`, `dateTimeSecsOfLex`,
`dayTimeDurationLex` and `dayTimeDurationSecs` this module used to
carry are gone: they were a second, four-digit-year-only register of
the XSD date/time lexical and canonical mappings, and
`docs/designissues/2026-09-07-xsd-datatypes-audit.md` §8 commit 3 is
their removal. -/

/-- RIF-DTB has no dynamic evaluation context, so F&O §10.7's implicit
    timezone cannot come from a request. It is UTC. -/
def implicitTzMins : Int := 0

/-- A constant read as a seven-property date/time value, with the kind
    its datatype names. `xs:dateTimeStamp` additionally requires the
    timezone. -/
def dtValueOf (g : GTerm) : Option (L4Factoidal.XSD.DTKind × L4Factoidal.XSD.DTValue) :=
  match g with
  | .const lex sp =>
      (match xsdLocal sp with
       | some b =>
           (match dtKindOfBase b with
            | some k =>
                (match L4Factoidal.XSD.parseDateTimeLex k lex with
                 | some v => if b == "dateTimeStamp" && v.tz.isNone then none else some (k, v)
                 | none   => none)
            | none => none)
       | none => none)
  | _ => none

/-- A constant read as a duration value. The three duration datatypes
    share one value space (§3.3.6), so this accepts all of them and the
    caller checks the sub-space where DTB asks for one. -/
def durValueOf (g : GTerm) : Option L4Factoidal.XSD.DurValue :=
  match g with
  | .const lex sp =>
      (match xsdLocal sp with
       | some "duration"          => L4Factoidal.XSD.parseDurationLex lex
       | some "dayTimeDuration"   => L4Factoidal.XSD.parseDayTimeDurationLex lex
       | some "yearMonthDuration" => L4Factoidal.XSD.parseYearMonthDurationLex lex
       | _                        => none)
  | _ => none

/-! ### Result constructors

Every result is written through the XSD canonical mapping, so no
lexical form is assembled in this module. -/

def gDateTime (k : L4Factoidal.XSD.DTKind) (v : L4Factoidal.XSD.DTValue) : GTerm :=
  gLit (L4Factoidal.XSD.canonicalDateTime k v)
       (xsdNs ++ (match k with
                  | .dateTime => "dateTime" | .date => "date" | .time => "time"
                  | .gYearMonth => "gYearMonth" | .gYear => "gYear"
                  | .gMonthDay => "gMonthDay" | .gDay => "gDay" | .gMonth => "gMonth"))

def gDayTimeDur (d : L4Factoidal.XSD.DurValue) : GTerm :=
  gLit (L4Factoidal.XSD.canonicalDuration d) (xsdNs ++ "dayTimeDuration")

def gYearMonthDur (d : L4Factoidal.XSD.DurValue) : GTerm :=
  gLit (L4Factoidal.XSD.canonicalDuration d) (xsdNs ++ "yearMonthDuration")

def gIntLit (i : Int) : GTerm := gLit (toString i) (xsdNs ++ "integer")

def gDecLit (d : L4Factoidal.XSD.Dec) : GTerm :=
  gLit (L4Factoidal.XSD.Dec.canonical d) (xsdNs ++ "decimal")

/-- Is this constant a literal of the named XSD type? RIF-DTB's
    `pred:is-literal-T` family. -/
def isLiteralOf (base : String) (g : GTerm) : Ans :=
  match g with
  | .const lex sp =>
      if base == "PlainLiteral" then
        (if sp == rdfNs ++ "PlainLiteral" then .yes else .no)
      else if base == "XMLLiteral" then
        (if sp == rdfNs ++ "XMLLiteral" then .yes else .no)
      else if sp == rdfNs ++ "PlainLiteral" then
        -- RIF-DTB: a plain literal with an EMPTY language tag is in
        -- the value space of `xs:string`. The corpus asks
        -- `pred:is-literal-string("Hello world@"^^rdf:PlainLiteral)`
        -- and expects yes.
        (if xsdFamily base == some "string" && lex.endsWith "@" then .yes else .no)
      else match xsdLocal sp with
        | none => .no
        | some cb =>
            -- RIF-DTB 3.2: an `xs:date` value IS an `xs:dateTime`
            -- value, at midnight. `EBusiness_Contract` guards
            -- `"2008-07-22Z"^^xs:date` with `pred:is-literal-dateTime`
            -- and expects the guard to hold. The containment runs one
            -- way only: an `xs:dateTime` at noon is not an `xs:date`.
            if base == "dateTime" && cb == "date" then
              (match L4Factoidal.XSD.parseDateTimeLex .date lex with
               | some _ => .yes | none => .no)
            else if xsdFamily cb != xsdFamily base then .no
            else match inLexicalSpace base lex with
              | some b => if b then .yes else .no
              | none   => .unknown
  | _ => .no

/-- The numeric value of a constant, as an exact decimal lexical form,
    when its datatype is numeric. -/
def numericLex (g : GTerm) : Option String :=
  match g with
  | .const lex sp =>
      match xsdLocal sp with
      | some b =>
          if ["integer", "int", "long", "short", "byte", "decimal", "double", "float",
              "nonNegativeInteger", "nonPositiveInteger", "negativeInteger",
              "positiveInteger", "unsignedByte", "unsignedShort", "unsignedInt",
              "unsignedLong"].contains b && isXsdNumericLexical b lex
          then some (L4Factoidal.CSVW.resolveExponent lex) else none
      | none => none
  | _ => none

/-- The numeric VALUE of a constant, as an `XSD.Dec`. The multiply and
    divide built-ins of §4.8 take one. -/
def decValueOf (g : GTerm) : Option L4Factoidal.XSD.Dec :=
  (numericLex g).bind Fn.Numeric.decOfNumeral

def isStringy (g : GTerm) : Option String :=
  match g with
  | .const lex sp => if sp == xsdNs ++ "string" then some lex else none
  | _ => none

/-- The VALUE of an `xs:boolean` constant. `1` and `true` are the same
    value and `0` and `false` are the same value; comparing lexical
    forms made `pred:boolean-less-than("0"^^xs:boolean
    "1"^^xs:boolean)` false, which is the one the corpus writes. -/
def boolValue (g : GTerm) : Option Bool :=
  match g with
  | .const lex sp => if sp != xsdNs ++ "boolean" then none else Fn.Boolean.ofLexical lex
  | _ => none

private def cmpNum (a b : GTerm) (ok : Ordering → Bool) : Ans :=
  match numericLex a, numericLex b with
  | some x, some y => (match decimalCompare x y with
                       | some o => if ok o then .yes else .no
                       | none   => .unknown)
  | _, _ => .unknown

/-! ### The decimal-numeral layer

`func:numeric-add` and its three companions work in decimal NUMERALS
because that is the shape a RIF ground term carries. The arithmetic
is `Fn.Numeric`; these are its names in this module. -/
abbrev decParts := Fn.Numeric.decParts
abbrev decRender := Fn.Numeric.decRender
abbrev divScale := Fn.Numeric.divScale
abbrev addDec := Fn.Numeric.addDec
abbrev subDec := Fn.Numeric.subDec
abbrev mulDec := Fn.Numeric.mulDec
abbrev divDec := Fn.Numeric.divDec

/-! ## Lists (RIF-DTB 4.9)

An index is 0-BASED, and a NEGATIVE index counts from the end: `-1`
is the last element and `-n` the first of an `n`-element list. Every
function below normalises through `listIndex`, so the rule is stated
once.

`func:index-of`, `func:union`, `func:distinct-values`,
`func:intersect` and `func:except` all preserve the order of their
FIRST argument, which is the order the Approved `Builtins_List`
fixture writes their results in. -/
abbrev listIndex := Fn.List.listIndex

def gInt (n : Nat) : GTerm := gLit (toString n) (xsdNs ++ "integer")

/-- The integer VALUE of a constant, for a list index. -/
def intArg (g : GTerm) : Option Int :=
  match numericLex g with
  | some lex => lex.toInt?
  | none     => none

abbrev dedup : List GTerm → List GTerm := Fn.List.dedup

/-- The datatype a numeric result carries. RIF-DTB 4.4 keeps
    `func:numeric-add` inside `xs:integer` when both operands are
    integers and inside `xs:decimal` otherwise; the value is the same
    either way, and `RIF.Engine.gEqValue` compares numerics by value,
    so this only affects what a derived fact SAYS its type is. -/
def numResultType (lex : String) : String :=
  if (lex.splitOn ".").length > 1 then xsdNs ++ "decimal" else xsdNs ++ "integer"

/-! ### The string functions

RIF-DTB 4.7's string built-ins are F&O §5 functions with RIF names.
The semantics is `Fn.String`, which SPARQL's `ENCODE_FOR_URI`,
`SUBSTR`, `STRBEFORE` and `STRAFTER` call as well. -/
abbrev encodeForUri := Fn.String.encodeForUri
abbrev iriToUri := Fn.String.iriToUri
abbrev escapeHtmlUri := Fn.String.escapeHtmlUri

/-- F&O 5.4.4 `fn:substring` with a start and a length, 1-based. -/
abbrev substring3 := Fn.String.substringFromLen

/-- The 2-argument form the Approved `Builtins_String` fixture writes,
    which is 0-BASED where the 3-argument form is 1-based. The
    disagreement is inside one fixture and is preserved deliberately;
    `Fn.String.substringFrom` is F&O's own 2-argument form. -/
abbrev substring2 := Fn.String.substringFromRif

/-- RFC 4647 §3.3.2 extended filtering, which RIF-DTB 4.10.2
    `pred:matches-language-range` cites. SPARQL's `langMatches` cites
    §3.3.1 BASIC filtering instead — a real difference between the two
    Recommendations, witnessed in `Fn/Theorems.lean`. -/
abbrev matchesLanguageRange := Fn.String.matchesLanguageRange

/-! ## `rdf:PlainLiteral` (RIF-DTB 4.7)

RIF writes a plain literal's language tag INSIDE its lexical form,
after the last `@`. An `xs:string` is the same thing with an empty
tag (RDF 1.1 Concepts 5.1 and RIF-DTB 3.1), which is why the corpus
applies `func:string-from-PlainLiteral` to one and expects the string
back UNCHANGED -- the `@en` in `"Hello World!@en"^^xs:string` is
ordinary text, not a tag. -/
def plainParts (g : GTerm) : Option (String × String) :=
  match g with
  | .const lex sp =>
      if sp == rdfNs ++ "PlainLiteral" then
        (match (lex.splitOn "@").reverse with
         | tag :: rest => some (String.intercalate "@" rest.reverse, tag)
         | []          => some (lex, ""))
      else if sp == xsdNs ++ "string" then some (lex, "")
      else none
  | _ => none

/-! ### §4.8.2 predicate tables

Each name gives (i) which `XSD.DTKind`s its arguments must carry and
(ii) which orderings satisfy it. Writing them as a table rather than
as 28 match arms is what keeps the six shapes — equal, not-equal,
less-than, greater-than, and the two or-equal forms — in one place per
datatype. -/
private def dtOrdOf (suffix : String) : Option (Ordering → Bool) :=
  if suffix == "equal" then some (· == .eq)
  else if suffix == "not-equal" then some (· != .eq)
  else if suffix == "less-than" then some (· == .lt)
  else if suffix == "greater-than" then some (· == .gt)
  else if suffix == "less-than-or-equal" then some (· != .gt)
  else if suffix == "greater-than-or-equal" then some (· != .lt)
  else none

private def stripPrefix (pfx name : String) : Option String :=
  if name.startsWith pfx then some (String.ofList (name.toList.drop pfx.length)) else none

/-- `pred:dateTime-*`, `pred:date-*` and `pred:time-*`. -/
def dtPredKind (name : String) : Option ((L4Factoidal.XSD.DTKind → Bool) × (Ordering → Bool)) :=
  match stripPrefix "dateTime-" name with
  | some sfx => (dtOrdOf sfx).map (fun o => ((· == L4Factoidal.XSD.DTKind.dateTime), o))
  | none =>
    match stripPrefix "date-" name with
    | some sfx => (dtOrdOf sfx).map (fun o => ((· == L4Factoidal.XSD.DTKind.date), o))
    | none =>
      match stripPrefix "time-" name with
      | some sfx => (dtOrdOf sfx).map (fun o => ((· == L4Factoidal.XSD.DTKind.time), o))
      | none => none

/-- `pred:duration-equal`, `pred:duration-not-equal`, and the two
    sub-space orders. §3.3.6.2 makes the general `xs:duration` order
    partial, which is why RIF-DTB has no `pred:duration-less-than`. -/
def durPredKind (name : String) :
    Option (L4Factoidal.XSD.DurValue → L4Factoidal.XSD.DurValue → Bool) :=
  if name == "duration-equal" then some Fn.Duration.equal
  else if name == "duration-not-equal" then some (fun a b => !Fn.Duration.equal a b)
  else
    match stripPrefix "yearMonthDuration-" name with
    | some "less-than" => some Fn.Duration.yearMonthLessThan
    | some "greater-than" => some (fun a b => Fn.Duration.yearMonthLessThan b a)
    | some "less-than-or-equal" => some (fun a b => !Fn.Duration.yearMonthLessThan b a)
    | some "greater-than-or-equal" => some (fun a b => !Fn.Duration.yearMonthLessThan a b)
    | _ =>
      match stripPrefix "dayTimeDuration-" name with
      | some "less-than" => some Fn.Duration.dayTimeLessThan
      | some "greater-than" => some (fun a b => Fn.Duration.dayTimeLessThan b a)
      | some "less-than-or-equal" => some (fun a b => !Fn.Duration.dayTimeLessThan b a)
      | some "greater-than-or-equal" => some (fun a b => !Fn.Duration.dayTimeLessThan a b)
      | _ => none

/-- A built-in PREDICATE. -/
def evalPred (name : String) (args : List GTerm) : Ans :=
  match name, args with
  | "literal-not-identical", [a, b] =>
      (match a, b with
       | .const l1 s1, .const l2 s2 => if l1 == l2 && s1 == s2 then .no else .yes
       | _, _ => .unknown)
  | "numeric-equal", [a, b] => cmpNum a b (· == .eq)
  | "numeric-not-equal", [a, b] => cmpNum a b (· != .eq)
  | "numeric-less-than", [a, b] => cmpNum a b (· == .lt)
  | "numeric-greater-than", [a, b] => cmpNum a b (· == .gt)
  | "numeric-less-than-or-equal", [a, b] => cmpNum a b (· != .gt)
  | "numeric-greater-than-or-equal", [a, b] => cmpNum a b (· != .lt)
  | "boolean-equal", [a, b] =>
      (match boolValue a, boolValue b with
       | some x, some y => if x == y then .yes else .no
       | _, _ => .unknown)
  | "boolean-less-than", [a, b] =>
      (match boolValue a, boolValue b with
       | some x, some y => if !x && y then .yes else .no
       | _, _ => .unknown)
  | "boolean-greater-than", [a, b] =>
      (match boolValue a, boolValue b with
       | some x, some y => if x && !y then .yes else .no
       | _, _ => .unknown)
  | "is-list", [a] => (match a with | .list _ => .yes | _ => .no)
  | "list-contains", [a, b] =>
      (match a with | .list xs => (if xs.contains b then .yes else .no) | _ => .no)
  | "iri-string", [a, b] =>
      (match a, b with
       | .const i sp, .const s sp2 =>
           if sp == iriSpace && sp2 == xsdNs ++ "string"
           then (if i == s then .yes else .no) else .unknown
       | _, _ => .unknown)
  | "matches", [a, b] =>
      (match isStringy a, isStringy b with
       | some str, some pat =>
           (match L4Factoidal.Regex.compile pat "" with
            | .ok re   => if L4Factoidal.Regex.isMatch re str then .yes else .no
            | .error _ => .unknown)
       | _, _ => .unknown)
  | "matches", [a, b, f] =>
      (match isStringy a, isStringy b, isStringy f with
       | some str, some pat, some fl =>
           (match L4Factoidal.Regex.compile pat fl with
            | .ok re   => if L4Factoidal.Regex.isMatch re str then .yes else .no
            | .error _ => .unknown)
       | _, _, _ => .unknown)
  | "matches-language-range", [a, b] =>
      (match plainParts a, isStringy b with
       | some (_, tag), some range =>
           if tag == "" then .no else (if matchesLanguageRange tag range then .yes else .no)
       | _, _ => .unknown)
  | "contains", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => if (x.splitOn y).length > 1 then .yes else .no
       | _, _ => .unknown)
  | "starts-with", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => if x.startsWith y then .yes else .no
       | _, _ => .unknown)
  | "ends-with", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => if x.endsWith y then .yes else .no
       | _, _ => .unknown)
  -- §4.8.2, the 28 date, time and duration predicates. §10.4 compares
  -- by VALUE, so `pred:dateTime-equal` holds between two lexical forms
  -- in different timezones that name the same instant. The implicit
  -- timezone is applied first, so `XSD.dtCompare`'s incomparable case
  -- cannot arise here.
  | _, [a, b] =>
      (match dtPredKind name with
       | some (kindOk, ord) =>
           (match dtValueOf a, dtValueOf b with
            | some (ka, va), some (kb, vb) =>
                if kindOk ka && kindOk kb then
                  (match Fn.DateTime.compare implicitTzMins va vb with
                   | some o => if ord o then .yes else .no
                   | none   => .unknown)
                else .unknown
            | _, _ => .unknown)
       | none =>
         (match durPredKind name with
          | some p =>
              (match durValueOf a, durValueOf b with
               | some da, some db => if p da db then .yes else .no
               | _, _ => .unknown)
          | none =>
            if name == "XMLLiteral-equal" || name == "XMLLiteral-not-equal" then
              -- §4.9. `rdf:XMLLiteral` equality is equality of the
              -- exclusive-canonical XML the lexical form denotes; the
              -- lexical forms this port sees are already canonical, so
              -- the comparison is on them, and a non-XMLLiteral
              -- argument is not decided rather than answered `no`.
              (match a, b with
               | .const l1 s1, .const l2 s2 =>
                   if s1 == rdfNs ++ "XMLLiteral" && s2 == rdfNs ++ "XMLLiteral" then
                     (if (l1 == l2) == (name == "XMLLiteral-equal") then .yes else .no)
                   else .unknown
               | _, _ => .unknown)
            else .unknown))
  | _, [a] =>
      if name.startsWith "is-literal-not-" then
        (match isLiteralOf (String.ofList (name.toList.drop 15)) a with
         | .yes => .no | .no => .yes | .unknown => .unknown)
      else if name.startsWith "is-literal-" then
        isLiteralOf (String.ofList (name.toList.drop 11)) a
      else .unknown
  | _, _ => .unknown

/-! ## §4.8.1 — the 44 date, time and duration functions

Each accessor is a projection out of the seven-property model, so
`-from-dateTime`, `-from-date` and `-from-time` are one implementation
and three names; the datatype the name asks for is still checked, so
`func:year-from-date` refuses an `xs:time`. -/

/-- RIF-DTB 3.2 puts the `xs:date` values INSIDE the `xs:dateTime`
    value space, at midnight, which is why
    `pred:is-literal-dateTime("2008-07-22Z"^^xs:date)` holds. A
    `-dateTime` built-in therefore accepts an `xs:date` argument, and
    the Approved `EBusiness_Contract` fixture depends on it: it calls
    `func:subtract-dateTimes` on two `xs:date` constants. The
    containment runs one way only — a `-date` built-in does not accept
    an `xs:dateTime`. -/
private def kDateTime : L4Factoidal.XSD.DTKind → Bool :=
  fun k => k == .dateTime || k == .date
private def kDate     : L4Factoidal.XSD.DTKind → Bool := (· == .date)
private def kTime     : L4Factoidal.XSD.DTKind → Bool := (· == .time)

/-- §10.5.7-10.5.13 and their `date` and `time` twins. -/
def dtAccessor (name : String) :
    Option ((L4Factoidal.XSD.DTKind → Bool) × (L4Factoidal.XSD.DTValue → Option GTerm)) :=
  let optInt := fun (o : Option Int) => o.map gIntLit
  let optNat := fun (o : Option Nat) => o.map (fun n => gIntLit (Int.ofNat n))
  match name with
  | "year-from-dateTime"     => some (kDateTime, fun v => optInt (Fn.DateTime.yearFrom v))
  | "month-from-dateTime"    => some (kDateTime, fun v => optNat (Fn.DateTime.monthFrom v))
  | "day-from-dateTime"      => some (kDateTime, fun v => optNat (Fn.DateTime.dayFrom v))
  | "hours-from-dateTime"    => some (kDateTime, fun v => optNat (Fn.DateTime.hoursFrom v))
  | "minutes-from-dateTime"  => some (kDateTime, fun v => optNat (Fn.DateTime.minutesFrom v))
  | "seconds-from-dateTime"  => some (kDateTime, fun v => (Fn.DateTime.secondsFrom v).map gDecLit)
  | "year-from-date"         => some (kDate, fun v => optInt (Fn.DateTime.yearFrom v))
  | "month-from-date"        => some (kDate, fun v => optNat (Fn.DateTime.monthFrom v))
  | "day-from-date"          => some (kDate, fun v => optNat (Fn.DateTime.dayFrom v))
  | "hours-from-time"        => some (kTime, fun v => optNat (Fn.DateTime.hoursFrom v))
  | "minutes-from-time"      => some (kTime, fun v => optNat (Fn.DateTime.minutesFrom v))
  | "seconds-from-time"      => some (kTime, fun v => (Fn.DateTime.secondsFrom v).map gDecLit)
  | "timezone-from-dateTime" => some (kDateTime, fun v => (Fn.DateTime.timezoneFrom v).map gDayTimeDur)
  | "timezone-from-date"     => some (kDate, fun v => (Fn.DateTime.timezoneFrom v).map gDayTimeDur)
  | "timezone-from-time"     => some (kTime, fun v => (Fn.DateTime.timezoneFrom v).map gDayTimeDur)
  | _                        => none

/-- §10.5.1-10.5.6. -/
def durAccessor (name : String) : Option (L4Factoidal.XSD.DurValue → Option GTerm) :=
  match name with
  | "years-from-duration"   => some (fun d => some (gIntLit (Fn.Duration.yearsFrom d)))
  | "months-from-duration"  => some (fun d => some (gIntLit (Fn.Duration.monthsFrom d)))
  | "days-from-duration"    => some (fun d => some (gIntLit (Fn.Duration.daysFrom d)))
  | "hours-from-duration"   => some (fun d => some (gIntLit (Fn.Duration.hoursFrom d)))
  | "minutes-from-duration" => some (fun d => some (gIntLit (Fn.Duration.minutesFrom d)))
  | "seconds-from-duration" => some (fun d => some (gDecLit (Fn.Duration.secondsFrom d)))
  | _                       => none

/-- §10.8: subtracting two date/time values of the SAME kind gives an
    `xs:dayTimeDuration`. -/
private def subtractPair (kindOk : L4Factoidal.XSD.DTKind → Bool) (a b : GTerm) : Option GTerm :=
  match dtValueOf a, dtValueOf b with
  | some (ka, va), some (kb, vb) =>
      if kindOk ka && kindOk kb
      then some (gDayTimeDur (Fn.DateTime.subtractValues implicitTzMins va vb))
      else none
  | _, _ => none

/-- §10.7: adding or subtracting a duration keeps the datatype of the
    date/time argument. -/
private def shiftBy (kindOk : L4Factoidal.XSD.DTKind → Bool) (subYM : Bool) (negate : Bool)
    (a b : GTerm) : Option GTerm :=
  match dtValueOf a, durValueOf b with
  | some (k, v), some d =>
      if !kindOk k then none
      -- The sub-space the name asks for: a `-yearMonthDuration-` name
      -- takes a duration with no seconds, a `-dayTimeDuration-` name
      -- one with no months.
      else if subYM && !Fn.Duration.isYearMonth d then none
      else if !subYM && !Fn.Duration.isDayTime d then none
      else some (gDateTime k (if negate then Fn.DateTime.minusDuration v d
                              else Fn.DateTime.plusDuration v d))
  | _, _ => none

/-- §10.6 and §10.7-10.8: every two-argument name of §4.8.1. -/
def dtDurOp (name : String) : Option (GTerm → GTerm → Option GTerm) :=
  let ym := fun (f : L4Factoidal.XSD.DurValue → L4Factoidal.XSD.DurValue → L4Factoidal.XSD.DurValue) =>
    some (fun a b => match durValueOf a, durValueOf b with
                     | some x, some y =>
                         if Fn.Duration.isYearMonth x && Fn.Duration.isYearMonth y
                         then some (gYearMonthDur (f x y)) else none
                     | _, _ => none)
  let dt := fun (f : L4Factoidal.XSD.DurValue → L4Factoidal.XSD.DurValue → L4Factoidal.XSD.DurValue) =>
    some (fun a b => match durValueOf a, durValueOf b with
                     | some x, some y =>
                         if Fn.Duration.isDayTime x && Fn.Duration.isDayTime y
                         then some (gDayTimeDur (f x y)) else none
                     | _, _ => none)
  match name with
  | "subtract-dateTimes" => some (subtractPair kDateTime)
  | "subtract-dates"     => some (subtractPair kDate)
  | "subtract-times"     => some (subtractPair kTime)
  | "add-yearMonthDurations"      => ym Fn.Duration.addYearMonth
  | "subtract-yearMonthDurations" => ym Fn.Duration.subYearMonth
  | "add-dayTimeDurations"        => dt Fn.Duration.addDayTime
  | "subtract-dayTimeDurations"   => dt Fn.Duration.subDayTime
  | "multiply-yearMonthDuration" =>
      some (fun a b => match durValueOf a, decValueOf b with
                       | some x, some k => some (gYearMonthDur (Fn.Duration.mulYearMonth x k))
                       | _, _ => none)
  | "divide-yearMonthDuration" =>
      some (fun a b => match durValueOf a, decValueOf b with
                       | some x, some k => (Fn.Duration.divYearMonth? x k).map gYearMonthDur
                       | _, _ => none)
  | "divide-yearMonthDuration-by-yearMonthDuration" =>
      some (fun a b => match durValueOf a, durValueOf b with
                       | some x, some y => (Fn.Duration.divYearMonthBy? x y).map gDecLit
                       | _, _ => none)
  | "multiply-dayTimeDuration" =>
      some (fun a b => match durValueOf a, decValueOf b with
                       | some x, some k => some (gDayTimeDur (Fn.Duration.mulDayTime x k))
                       | _, _ => none)
  | "divide-dayTimeDuration" =>
      some (fun a b => match durValueOf a, decValueOf b with
                       | some x, some k => (Fn.Duration.divDayTime? x k).map gDayTimeDur
                       | _, _ => none)
  | "divide-dayTimeDuration-by-dayTimeDuration" =>
      some (fun a b => match durValueOf a, durValueOf b with
                       | some x, some y => (Fn.Duration.divDayTimeBy? x y).map gDecLit
                       | _, _ => none)
  | "add-yearMonthDuration-to-dateTime"      => some (shiftBy kDateTime true false)
  | "add-yearMonthDuration-to-date"          => some (shiftBy kDate true false)
  | "add-dayTimeDuration-to-dateTime"        => some (shiftBy kDateTime false false)
  | "add-dayTimeDuration-to-date"            => some (shiftBy kDate false false)
  | "add-dayTimeDuration-to-time"            => some (shiftBy kTime false false)
  | "subtract-yearMonthDuration-from-dateTime" => some (shiftBy kDateTime true true)
  | "subtract-yearMonthDuration-from-date"     => some (shiftBy kDate true true)
  | "subtract-dayTimeDuration-from-dateTime"   => some (shiftBy kDateTime false true)
  | "subtract-dayTimeDuration-from-date"       => some (shiftBy kDate false true)
  | "subtract-dayTimeDuration-from-time"       => some (shiftBy kTime false true)
  | _ => none

/-- The whole of §4.8.1, dispatched by arity. -/
def evalDateTimeFunc (name : String) (args : List GTerm) : Option GTerm :=
  match args with
  | [a] =>
      (match dtAccessor name with
       | some (kindOk, f) =>
           (match dtValueOf a with
            | some (k, v) => if kindOk k then f v else none
            | none        => none)
       | none => (durAccessor name).bind (fun f => (durValueOf a).bind f))
  | [a, b] => (dtDurOp name).bind (fun op => op a b)
  | _      => none

/-- A built-in FUNCTION. `none` means this module does not decide it,
    which the caller must not read as "no value". -/
def evalFunc (name : String) (args : List GTerm) : Option GTerm :=
  match name, args with
  | "numeric-add", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y => (addDec x y).map (fun r => gLit r (numResultType r))
       | _, _ => none)
  | "numeric-subtract", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y => (subDec x y).map (fun r => gLit r (numResultType r))
       | _, _ => none)
  | "numeric-multiply", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y => (mulDec x y).map (fun r => gLit r (numResultType r))
       | _, _ => none)
  | "numeric-divide", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y => (divDec x y).map (fun r => gLit r (numResultType r))
       | _, _ => none)
  | "numeric-integer-divide", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y =>
           (match x.toInt?, y.toInt? with
            | some p, some q => if q == 0 then none
                                else some (gLit (toString (p / q)) (xsdNs ++ "integer"))
            | _, _ => none)
       | _, _ => none)
  | "numeric-mod", [a, b] | "numeric-integer-mod", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y =>
           (match x.toInt?, y.toInt? with
            | some p, some q => if q == 0 then none
                                else some (gLit (toString (p % q)) (xsdNs ++ "integer"))
            | _, _ => none)
       | _, _ => none)
  | "compare", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y =>
           some (gLit (match compare x y with
                       | .lt => "-1" | .eq => "0" | .gt => "1") (xsdNs ++ "integer"))
       | _, _ => none)
  -- RIF-DTB 4.5 `func:string-join` takes the strings first and the
  -- SEPARATOR last.
  | "string-join", args' =>
      (match args'.reverse with
       | sep :: rest =>
           (match isStringy sep,
                  rest.reverse.foldr (fun g acc => match isStringy g, acc with
                    | some t, some ts => some (t :: ts)
                    | _, _ => none) (some []) with
            | some sp, some parts => some (gStr (String.intercalate sp parts))
            | _, _ => none)
       | [] => none)
  | "substring", [a, b] =>
      (match isStringy a, numericLex b with
       | some str, some n => (n.toInt?).map (fun i => gStr (substring2 str i))
       | _, _ => none)
  | "substring", [a, b, c] =>
      (match isStringy a, numericLex b, numericLex c with
       | some str, some n, some m =>
           (match n.toInt?, m.toInt? with
            | some i, some j => some (gStr (substring3 str i j))
            | _, _ => none)
       | _, _, _ => none)
  | "substring-before", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => some (gStr (Fn.String.substringBefore x y))
       | _, _ => none)
  | "substring-after", [a, b] =>
      (match isStringy a, isStringy b with
       | some x, some y => some (gStr (Fn.String.substringAfter x y))
       | _, _ => none)
  | "encode-for-uri", [a] => (isStringy a).map (fun x => gStr (encodeForUri x))
  | "iri-to-uri", [a] => (isStringy a).map (fun x => gStr (iriToUri x))
  | "escape-html-uri", [a] => (isStringy a).map (fun x => gStr (escapeHtmlUri x))
  | "replace", [a, b, c] =>
      (match isStringy a, isStringy b, isStringy c with
       | some str, some pat, some rep =>
           (match L4Factoidal.Regex.compile pat "" with
            | .error _ => none
            | .ok re   => (match L4Factoidal.Regex.replace re str rep with
                           | .ok out  => some (gStr out)
                           | .error _ => none))
       | _, _, _ => none)
  -- §4.6.1 `func:not`.
  | "not", [a] => (boolValue a).map (fun b => gLit (Fn.Boolean.canonical (Fn.Boolean.not b))
                                                   (xsdNs ++ "boolean"))
  -- §4.10.1 `func:PlainLiteral-length`: the length of the STRING part,
  -- not of the lexical form, so the language tag is not counted.
  | "PlainLiteral-length", [a] =>
      (plainParts a).map (fun (str, _) =>
        gIntLit (Int.ofNat (Fn.String.stringLength str)))
  | "string-length", [a] =>
      (isStringy a).map (fun s => gIntLit (Int.ofNat (Fn.String.stringLength s)))
  | "upper-case", [a] => (isStringy a).map (fun s => gStr (Fn.String.upperCase s))
  | "lower-case", [a] => (isStringy a).map (fun s => gStr (Fn.String.lowerCase s))
  | "concat", args' =>
      (args'.foldl (fun acc g => match acc, isStringy g with
        | some s, some t => some (s ++ t)
        | _, _ => none) (some "")).map gStr
  | "count", [a] =>
      (match a with
       | .list xs => some (gLit (toString xs.length) (xsdNs ++ "integer"))
       | _ => none)
  | "make-list", xs => some (.list xs)
  | "get", [a, b] =>
      (match a, intArg b with
       | .list xs, some i => (listIndex xs.length i).bind (fun k => xs[k]?)
       | _, _ => none)
  -- RIF-DTB 4.9 `func:sublist(list start stop)`: the elements from
  -- `start` up to but NOT including `stop`.
  | "sublist", [a, b, c] =>
      (match a, intArg b, intArg c with
       | .list xs, some i, some j =>
           let n := Int.ofNat xs.length
           let lo := if i < 0 then n + i else i
           let hi := if j < 0 then n + j else j
           let lo := if lo < 0 then 0 else lo
           let hi := if hi > n then n else hi
           if hi ≤ lo then some (.list [])
           else some (.list ((xs.drop lo.toNat).take (hi - lo).toNat))
       | _, _, _ => none)
  | "sublist", [a, b] =>
      (match a, intArg b with
       | .list xs, some i =>
           let lo := if i < 0 then Int.ofNat xs.length + i else i
           let lo := if lo < 0 then 0 else lo
           some (.list (xs.drop lo.toNat))
       | _, _ => none)
  | "append", a :: rest =>
      (match a with | .list xs => some (.list (xs ++ rest)) | _ => none)
  | "concatenate", args' =>
      (args'.foldl (fun acc g => match acc, g with
        | some xs, .list ys => some (xs ++ ys)
        | _, _ => none) (some [])).map GTerm.list
  | "insert-before", [a, b, c] =>
      (match a, intArg b with
       | .list xs, some i =>
           (listIndex xs.length i).map (fun k => .list (xs.take k ++ [c] ++ xs.drop k))
       | _, _ => none)
  | "remove", [a, b] =>
      (match a, intArg b with
       | .list xs, some i =>
           (listIndex xs.length i).map (fun k => .list (xs.take k ++ xs.drop (k + 1)))
       | _, _ => none)
  | "index-of", [a, b] =>
      (match a with
       | .list xs =>
           some (.list ((xs.zipIdx).filterMap (fun (x, i) => if x == b then some (gInt i) else none)))
       | _ => none)
  | "union", [a, b] =>
      (match a, b with | .list xs, .list ys => some (.list (dedup (xs ++ ys))) | _, _ => none)
  | "distinct-values", [a] =>
      (match a with | .list xs => some (.list (dedup xs)) | _ => none)
  | "intersect", [a, b] =>
      (match a, b with
       | .list xs, .list ys => some (.list (dedup (xs.filter ys.contains)))
       | _, _ => none)
  | "except", [a, b] =>
      (match a, b with
       | .list xs, .list ys => some (.list (dedup (xs.filter (fun x => !(ys.contains x)))))
       | _, _ => none)
  | "reverse", [a] => (match a with | .list xs => some (.list xs.reverse) | _ => none)
  | "PlainLiteral-from-string-lang", [a, b] =>
      (match isStringy a, isStringy b with
       | some s, some l => some (.const (s ++ "@" ++ l) (rdfNs ++ "PlainLiteral"))
       | _, _ => none)
  | "string-from-PlainLiteral", [a] => (plainParts a).map (fun (str, _) => gStr str)
  | "lang-from-PlainLiteral", [a] => (plainParts a).map (fun (_, tag) => gStr tag)
  -- RIF-DTB 4.7: comparable only when the two language tags are the
  -- SAME. Different tags have no defined order, and `none` there is
  -- undecided rather than a made-up verdict.
  | "PlainLiteral-compare", [a, b] =>
      (match plainParts a, plainParts b with
       | some (s1, t1), some (s2, t2) =>
           if t1 != t2 then none
           else some (gLit (match compare s1 s2 with
                            | .lt => "-1" | .eq => "0" | .gt => "1")
                           (xsdNs ++ "integer"))
       | _, _ => none)
  | _, rest =>
      match evalDateTimeFunc name rest with
      | some r => some r
      | none =>
      -- A datatype CAST, `External( xs:date ( "…"^^xs:string ) )`.
      if name.startsWith "cast-rdf-" then
        -- RIF-DTB 5: `rdf:PlainLiteral(x)` takes the lexical form of
        -- `x` and gives it an EMPTY language tag, which RIF writes
        -- into the lexical form after `@`; `rdf:XMLLiteral(x)` retags
        -- a string.
        let base := String.ofList (name.toList.drop 9)
        (match rest with
         | [.const lex _] =>
             if base == "PlainLiteral" then some (.const (lex ++ "@") (rdfNs ++ "PlainLiteral"))
             else if base == "XMLLiteral" then some (.const lex (rdfNs ++ "XMLLiteral"))
             else none
         | _ => none)
      else if name.startsWith "cast-" then
        let base := String.ofList (name.toList.drop 5)
        (match rest with
         | [.const lex _] =>
             (match inLexicalSpace base lex with
              | some true => some (gLit lex (xsdNs ++ base))
              | _         => none)
         | _ => none)
      else none

/-! ## Pins from the RIF-DTB text and the Approved fixtures

Each `#guard` below is an equation the specification or a vendored
fixture writes out, not a value read back off this implementation. -/

-- RIF-DTB 4.4 `func:numeric-divide`, and the `xs:decimal` result type
-- `Builtins_Numeric` compares against the integer `2`.
#guard divDec "6" "3" = some "2"
#guard divDec "1" "8" = some "0.125"
#guard divDec "1" "0" = none
#guard addDec "1.5" "2.25" = some "3.75"
#guard subDec "1" "1" = some "0"
#guard mulDec "-1.5" "2" = some "-3"

-- XSD 1.1 3.3.16, the value `Builtins_Binary` writes plus the two
-- padded shapes.
#guard isBase64BinaryLexical
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz/+0123456789" = true
#guard isBase64BinaryLexical "QUJD" = true
#guard isBase64BinaryLexical "QQ==" = true
#guard isBase64BinaryLexical "QUI=" = true
#guard isBase64BinaryLexical "QUJ" = false
#guard isBase64BinaryLexical "Q===" = false

-- RIF-DTB 5 constructors in the RDF namespace, which
-- `Builtins_XMLLiteral` and `Builtins_PlainLiteral` both call.
#guard builtinName (rdfNs ++ "XMLLiteral") = some "cast-rdf-XMLLiteral"
#guard evalFunc "cast-rdf-XMLLiteral" [gStr "<br></br>"]
     = some (.const "<br></br>" (rdfNs ++ "XMLLiteral"))
#guard evalFunc "cast-rdf-PlainLiteral" [gLit "1" (xsdNs ++ "integer")]
     = some (.const "1@" (rdfNs ++ "PlainLiteral"))
#guard evalPred "is-literal-XMLLiteral" [.const "<br></br>" (rdfNs ++ "XMLLiteral")] = .yes
#guard evalPred "is-literal-base64Binary" [gLit "QUJD" (xsdNs ++ "base64Binary")] = .yes
#guard evalPred "is-literal-not-base64Binary" [gStr "foo"] = .yes

-- RIF-DTB 4.7 and the Approved `Builtins_PlainLiteral` lines.
#guard evalFunc "string-from-PlainLiteral" [.const "Hello World!@en" (rdfNs ++ "PlainLiteral")]
     = some (gStr "Hello World!")
#guard evalFunc "string-from-PlainLiteral" [gStr "Hello World!@en"]
     = some (gStr "Hello World!@en")
#guard evalFunc "lang-from-PlainLiteral" [.const "Hello World!@en" (rdfNs ++ "PlainLiteral")]
     = some (gStr "en")
#guard evalFunc "lang-from-PlainLiteral" [gStr "Hello World!@en"] = some (gStr "")
#guard evalFunc "PlainLiteral-compare"
        [.const "hallo@de" (rdfNs ++ "PlainLiteral"), .const "welt@de" (rdfNs ++ "PlainLiteral")]
     = some (gLit "-1" (xsdNs ++ "integer"))
#guard evalFunc "PlainLiteral-compare"
        [.const "hallo@de" (rdfNs ++ "PlainLiteral"), .const "hallo@de" (rdfNs ++ "PlainLiteral")]
     = some (gLit "0" (xsdNs ++ "integer"))
-- RFC 4647 3.3.2, the examples the specification lists.
#guard matchesLanguageRange "de-at" "de-*" = true
#guard matchesLanguageRange "de-DE-1996" "de-de" = true
#guard matchesLanguageRange "de-Latn-DE" "de-*-DE" = true
#guard matchesLanguageRange "de-a-DE" "de-*-DE" = false
#guard matchesLanguageRange "en-GB" "de-*" = false

-- The Approved `Builtins_String` lines, which are the RIF-DTB 4.5
-- and 4.6 examples.
#guard evalFunc "compare" [gStr "bar", gStr "foo"] = some (gLit "-1" (xsdNs ++ "integer"))
#guard evalFunc "compare" [gStr "bar", gStr "bar"] = some (gLit "0" (xsdNs ++ "integer"))
#guard evalFunc "string-join" [gStr "foo", gStr "bar", gStr ","] = some (gStr "foo,bar")
#guard evalFunc "substring" [gStr "foobar", gLit "3" (xsdNs ++ "integer")] = some (gStr "bar")
#guard evalFunc "substring"
        [gStr "foobar", gLit "0" (xsdNs ++ "integer"), gLit "3" (xsdNs ++ "integer")]
     = some (gStr "fo")
#guard evalFunc "substring-before" [gStr "foobar", gStr "bar"] = some (gStr "foo")
#guard evalFunc "substring-after" [gStr "foobar", gStr "foo"] = some (gStr "bar")
#guard encodeForUri "RIF Basic Logic Dialect" = "RIF%20Basic%20Logic%20Dialect"
#guard iriToUri "http://www.example.com/~b\u00e9b\u00e9"
     = "http://www.example.com/~b%C3%A9b%C3%A9"
#guard escapeHtmlUri "a b\u00e9" = "a b%C3%A9"
#guard evalPred "matches" [gStr "abracadabra", gStr "^a.*a$"] = .yes
#guard evalFunc "replace" [gStr "abcd", gStr "(ab)|(a)", gStr "[1=$1][2=$2]"]
     = some (gStr "[1=ab][2=]cd")

-- RIF-DTB 4.8. `EBusiness_Contract`'s slice, then every line of the
-- Approved `Builtins_Time` fixture that this module answers.
private def dtC (lex : String) : GTerm := gLit lex (xsdNs ++ "dateTime")
private def dC (lex : String) : GTerm := gLit lex (xsdNs ++ "date")
private def tC (lex : String) : GTerm := gLit lex (xsdNs ++ "time")
private def dtdC (lex : String) : GTerm := gLit lex (xsdNs ++ "dayTimeDuration")
private def ymdC (lex : String) : GTerm := gLit lex (xsdNs ++ "yearMonthDuration")

#guard evalPred "is-literal-dateTime" [dC "2008-07-22Z"] = .yes
#guard evalFunc "subtract-dateTimes" [dC "2008-07-22Z", dC "2008-07-11Z"]
     = some (dtdC "P11D")
#guard evalFunc "subtract-dates" [dC "2008-07-22Z", dC "2008-07-11Z"]
     = some (dtdC "P11D")
#guard evalFunc "days-from-duration" [dtdC "P11D"] = some (gIntLit 11)

-- The six positive and six negative guards of the fixture's first block.
#guard evalPred "is-literal-date" [dC "2000-12-13-11:00"] = .yes
#guard evalPred "is-literal-dateTime" [dtC "2000-12-13T00:11:11.3"] = .yes
#guard evalPred "is-literal-dateTimeStamp"
        [gLit "2000-12-13T00:11:11.3Z" (xsdNs ++ "dateTimeStamp")] = .yes
#guard evalPred "is-literal-dateTimeStamp"
        [gLit "2000-12-13T00:11:11.3" (xsdNs ++ "dateTimeStamp")] = .no
#guard evalPred "is-literal-time" [tC "00:11:11.3Z"] = .yes
#guard evalPred "is-literal-dayTimeDuration" [dtdC "P3DT2H"] = .yes
#guard evalPred "is-literal-yearMonthDuration" [ymdC "P1Y2M"] = .yes
#guard evalPred "is-literal-not-time" [gStr "foo"] = .yes
#guard evalPred "is-literal-not-dayTimeDuration" [gStr "foo"] = .yes

-- The casts of the fixture's second block.
#guard evalFunc "cast-date" [gStr "2000-12-13-11:00"] = some (dC "2000-12-13-11:00")
#guard evalFunc "cast-time" [gStr "00:11:11.3Z"] = some (tC "00:11:11.3Z")
#guard evalFunc "cast-dayTimeDuration" [gStr "P3DT2H"] = some (dtdC "P3DT2H")
#guard evalFunc "cast-yearMonthDuration" [gStr "P1Y2M"] = some (ymdC "P1Y2M")

-- The accessors.
#guard evalFunc "year-from-dateTime" [dtC "1999-12-31T24:00:00"] = some (gIntLit 2000)
#guard evalFunc "month-from-dateTime" [dtC "1999-05-31T13:20:00-05:00"] = some (gIntLit 5)
#guard evalFunc "day-from-dateTime" [dtC "1999-05-31T13:20:00-05:00"] = some (gIntLit 31)
#guard evalFunc "hours-from-dateTime" [dtC "1999-05-31T08:20:00-05:00"] = some (gIntLit 8)
#guard evalFunc "minutes-from-dateTime" [dtC "1999-05-31T13:20:00-05:00"] = some (gIntLit 20)
#guard evalFunc "seconds-from-dateTime" [dtC "1999-05-31T13:20:00-05:00"]
     = some (gLit "0" (xsdNs ++ "decimal"))
#guard evalFunc "year-from-date" [dC "1999-12-31"] = some (gIntLit 1999)
#guard evalFunc "hours-from-time" [tC "08:20:00-05:00"] = some (gIntLit 8)
#guard evalFunc "seconds-from-time" [tC "13:20:00-05:00"] = some (gLit "0" (xsdNs ++ "decimal"))
#guard evalFunc "timezone-from-dateTime" [dtC "1999-05-31T13:20:00-05:00"]
     = some (dtdC "-PT5H")
#guard evalFunc "timezone-from-date" [dC "1999-05-31-05:00"] = some (dtdC "-PT5H")
#guard evalFunc "timezone-from-time" [tC "13:20:00-05:00"] = some (dtdC "-PT5H")
#guard evalFunc "years-from-duration" [ymdC "P20Y15M"] = some (gIntLit 21)
#guard evalFunc "months-from-duration" [ymdC "P20Y15M"] = some (gIntLit 3)
#guard evalFunc "hours-from-duration" [dtdC "P3DT10H"] = some (gIntLit 10)
#guard evalFunc "minutes-from-duration" [dtdC "-P5DT12H30M"] = some (gIntLit (-30))
#guard evalFunc "seconds-from-duration" [dtdC "P3DT10H12.5S"]
     = some (gLit "12.5" (xsdNs ++ "decimal"))

-- The arithmetic.
#guard evalFunc "subtract-dateTimes"
        [dtC "2000-10-30T06:12:00-05:00", dtC "1999-11-28T09:00:00Z"]
     = some (dtdC "P337DT2H12M")
#guard evalFunc "subtract-times" [tC "11:12:00Z", tC "04:00:00Z"] = some (dtdC "PT7H12M")
#guard evalFunc "add-yearMonthDurations" [ymdC "P2Y11M", ymdC "P3Y3M"] = some (ymdC "P6Y2M")
#guard evalFunc "subtract-yearMonthDurations" [ymdC "P2Y11M", ymdC "P3Y3M"]
     = some (ymdC "-P4M")
#guard evalFunc "multiply-yearMonthDuration" [ymdC "P2Y11M", gLit "2.3" (xsdNs ++ "decimal")]
     = some (ymdC "P6Y9M")
#guard evalFunc "divide-yearMonthDuration" [ymdC "P2Y11M", gLit "1.5" (xsdNs ++ "decimal")]
     = some (ymdC "P1Y11M")
#guard evalFunc "divide-yearMonthDuration-by-yearMonthDuration" [ymdC "P3Y4M", ymdC "-P1Y4M"]
     = some (gLit "-2.5" (xsdNs ++ "decimal"))
#guard evalFunc "add-dayTimeDurations" [dtdC "P2DT12H5M", dtdC "P5DT12H"]
     = some (dtdC "P8DT5M")
#guard evalFunc "multiply-dayTimeDuration" [dtdC "PT2H10M", gLit "2.1" (xsdNs ++ "decimal")]
     = some (dtdC "PT4H33M")
#guard evalFunc "divide-dayTimeDuration" [dtdC "P4D", gIntLit 2] = some (dtdC "P2D")
#guard evalFunc "divide-dayTimeDuration-by-dayTimeDuration" [dtdC "P4D", dtdC "P2D"]
     = some (gLit "2" (xsdNs ++ "decimal"))
#guard evalFunc "add-yearMonthDuration-to-dateTime" [dtC "2000-10-30T11:12:00", ymdC "P1Y2M"]
     = some (dtC "2001-12-30T11:12:00")
#guard evalFunc "add-dayTimeDuration-to-time" [tC "23:12:00+03:00", dtdC "P1DT3H15M"]
     = some (tC "02:27:00+03:00")
#guard evalFunc "subtract-dayTimeDuration-from-date" [dC "2000-10-30", dtdC "P3DT1H15M"]
     = some (dC "2000-10-26")
-- A `-yearMonthDuration-` name refuses a `xs:dayTimeDuration` argument.
#guard evalFunc "add-yearMonthDuration-to-date" [dC "2000-10-30", dtdC "P3D"] = none

-- The comparisons.
#guard evalPred "dateTime-equal"
        [dtC "2002-04-02T12:00:00-01:00", dtC "2002-04-02T17:00:00+04:00"] = .yes
#guard evalPred "dateTime-not-equal"
        [dtC "2002-04-01T12:00:00-01:00", dtC "2002-04-02T17:00:00+04:00"] = .yes
#guard evalPred "date-equal" [dC "2004-12-25-12:00", dC "2004-12-26+12:00"] = .yes
#guard evalPred "time-greater-than" [tC "22:30:00+10:30", tC "06:00:00-05:00"] = .yes
#guard evalPred "duration-equal" [ymdC "P1Y", ymdC "P12M"] = .yes
#guard evalPred "duration-not-equal" [ymdC "P1Y", ymdC "P1M"] = .yes
#guard evalPred "yearMonthDuration-less-than" [ymdC "P1Y", ymdC "P13M"] = .yes
#guard evalPred "dayTimeDuration-greater-than-or-equal" [dtdC "P1D", dtdC "PT23H"] = .yes
#guard evalPred "dayTimeDuration-less-than" [dtdC "P1D", dtdC "PT25H"] = .yes

-- §4.6.1 and §4.10.1, the two names that were absent.
#guard evalFunc "not" [gLit "1" (xsdNs ++ "boolean")]
     = some (gLit "false" (xsdNs ++ "boolean"))
#guard evalFunc "PlainLiteral-length" [.const "Hello@en" (rdfNs ++ "PlainLiteral")]
     = some (gIntLit 5)
-- §4.9.
#guard evalPred "XMLLiteral-equal"
        [.const "<br></br>" (rdfNs ++ "XMLLiteral"), .const "<br></br>" (rdfNs ++ "XMLLiteral")]
     = .yes
#guard evalPred "XMLLiteral-not-equal"
        [.const "<br></br>" (rdfNs ++ "XMLLiteral"), .const "<i></i>" (rdfNs ++ "XMLLiteral")]
     = .yes

-- RIF-DTB 4.9, every line of the Approved `Builtins_List` fixture.
private def l5 : GTerm := .list [gInt 0, gInt 1, gInt 2, gInt 3, gInt 4]
#guard evalFunc "get" [l5, gLit "-1" (xsdNs ++ "integer")] = some (gInt 4)
#guard evalFunc "sublist" [l5, gInt 0, gInt 5] = some l5
#guard evalFunc "append" [.list [gInt 0, gInt 1, gInt 2], gInt 3, gInt 4] = some l5
#guard evalFunc "concatenate" [.list [gInt 0, gInt 1, gInt 2], .list [gInt 3, gInt 4]]
     = some l5
#guard evalFunc "insert-before" [l5, gLit "-1" (xsdNs ++ "integer"), gInt 99]
     = some (.list [gInt 0, gInt 1, gInt 2, gInt 3, gInt 99, gInt 4])
#guard evalFunc "remove" [l5, gLit "-5" (xsdNs ++ "integer")]
     = some (.list [gInt 1, gInt 2, gInt 3, gInt 4])
#guard evalFunc "reverse" [l5] = some (.list [gInt 4, gInt 3, gInt 2, gInt 1, gInt 0])
#guard evalFunc "index-of"
        [.list [gInt 0, gInt 1, gInt 2, gInt 3, gInt 4, gInt 5, gInt 2, gInt 2], gInt 2]
     = some (.list [gInt 2, gInt 6, gInt 7])
#guard evalFunc "union" [.list [gInt 0, gInt 1, gInt 2, gInt 3], .list [gInt 4]] = some l5
#guard evalFunc "distinct-values" [.list [gInt 3, gInt 3, gInt 3]] = some (.list [gInt 3])
#guard evalFunc "intersect" [l5, .list [gInt 3, gInt 1]] = some (.list [gInt 1, gInt 3])
#guard evalFunc "except" [l5, .list [gInt 1, gInt 3]]
     = some (.list [gInt 0, gInt 2, gInt 4])
#guard evalPred "is-list" [.list [gInt 0, .list [gInt 3, gInt 4]]] = .yes
#guard evalPred "list-contains" [.list [gInt 0, .list [gInt 7, gInt 8]], .list [gInt 7, gInt 8]] = .yes

end L4Factoidal.RIF
