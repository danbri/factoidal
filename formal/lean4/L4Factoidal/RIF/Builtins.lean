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

RIF-DTB defines 197 built-ins. Naming which ones are decided here, and
returning `unknown` for the rest, is what keeps the score honest as
the list grows.
-/
import L4Factoidal.RIF.Syntax
import L4Factoidal.CSVW.Formats

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
  else none

/-- The XSD local name of a datatype IRI. -/
def xsdLocal (dt : String) : Option String :=
  if dt.startsWith xsdNs then some (String.ofList (dt.toList.drop xsdNs.length)) else none

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
  else if base == "base64Binary" then none
  else if ["integer", "int", "long", "short", "byte", "decimal", "double", "float",
           "nonNegativeInteger", "nonPositiveInteger", "negativeInteger",
           "positiveInteger", "unsignedByte", "unsignedShort", "unsignedInt",
           "unsignedLong"].contains base then
    some (isXsdNumericLexical base lex)
  else if ["date", "dateTime", "time", "dateTimeStamp"].contains base then
    some (match parseCanonicalDate base lex with | .valid _ => true | _ => false)
  else if ["duration", "dayTimeDuration", "yearMonthDuration"].contains base then
    some (isDurationLexical lex &&
          (if base == "dayTimeDuration" then !(lex.toList.contains 'Y')
           else if base == "yearMonthDuration" then
             !(lex.toList.contains 'T') && !(lex.toList.contains 'D')
           else true))
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
           "NCName", "NMTOKEN"].contains b then some "string"
  else if ["duration", "dayTimeDuration", "yearMonthDuration"].contains b
    then some "duration"
  else if ["dateTime", "dateTimeStamp"].contains b then some "dateTime"
  else some b

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
            if xsdFamily cb != xsdFamily base then .no
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
  | .const lex sp =>
      if sp != xsdNs ++ "boolean" then none
      else if lex == "true" || lex == "1" then some true
      else if lex == "false" || lex == "0" then some false
      else none
  | _ => none

private def cmpNum (a b : GTerm) (ok : Ordering → Bool) : Ans :=
  match numericLex a, numericLex b with
  | some x, some y => (match decimalCompare x y with
                       | some o => if ok o then .yes else .no
                       | none   => .unknown)
  | _, _ => .unknown

/-- Sum, difference, product of two exact decimals, as a lexical
    form. Kept exact: RIF numbers are `xs:integer` and `xs:decimal`
    here, and a float would make `func:numeric-add` approximate on
    values the corpus compares for equality. -/
def addDec (a b : String) : Option String :=
  match a.toInt?, b.toInt? with
  | some x, some y => some (toString (x + y))
  | _, _ => none

def subDec (a b : String) : Option String :=
  match a.toInt?, b.toInt? with
  | some x, some y => some (toString (x - y))
  | _, _ => none

def mulDec (a b : String) : Option String :=
  match a.toInt?, b.toInt? with
  | some x, some y => some (toString (x * y))
  | _, _ => none

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
  | _, [a] =>
      if name.startsWith "is-literal-not-" then
        (match isLiteralOf (String.ofList (name.toList.drop 15)) a with
         | .yes => .no | .no => .yes | .unknown => .unknown)
      else if name.startsWith "is-literal-" then
        isLiteralOf (String.ofList (name.toList.drop 11)) a
      else .unknown
  | _, _ => .unknown

/-- A built-in FUNCTION. `none` means this module does not decide it,
    which the caller must not read as "no value". -/
def evalFunc (name : String) (args : List GTerm) : Option GTerm :=
  match name, args with
  | "numeric-add", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y => (addDec x y).map (fun r => gLit r (xsdNs ++ "integer"))
       | _, _ => none)
  | "numeric-subtract", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y => (subDec x y).map (fun r => gLit r (xsdNs ++ "integer"))
       | _, _ => none)
  | "numeric-multiply", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y => (mulDec x y).map (fun r => gLit r (xsdNs ++ "integer"))
       | _, _ => none)
  | "numeric-integer-divide", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y =>
           (match x.toInt?, y.toInt? with
            | some p, some q => if q == 0 then none
                                else some (gLit (toString (p / q)) (xsdNs ++ "integer"))
            | _, _ => none)
       | _, _ => none)
  | "numeric-integer-mod", [a, b] =>
      (match numericLex a, numericLex b with
       | some x, some y =>
           (match x.toInt?, y.toInt? with
            | some p, some q => if q == 0 then none
                                else some (gLit (toString (p % q)) (xsdNs ++ "integer"))
            | _, _ => none)
       | _, _ => none)
  | "string-length", [a] =>
      (isStringy a).map (fun s => gLit (toString s.toList.length) (xsdNs ++ "integer"))
  | "upper-case", [a] => (isStringy a).map (fun s => gStr s.toUpper)
  | "lower-case", [a] => (isStringy a).map (fun s => gStr s.toLower)
  | "concat", args' | "concatenate", args' =>
      (args'.foldl (fun acc g => match acc, isStringy g with
        | some s, some t => some (s ++ t)
        | _, _ => none) (some "")).map gStr
  | "count", [a] =>
      (match a with
       | .list xs => some (gLit (toString xs.length) (xsdNs ++ "integer"))
       | _ => none)
  | "make-list", xs => some (.list xs)
  | "reverse", [a] => (match a with | .list xs => some (.list xs.reverse) | _ => none)
  | "concatenate-lists", [a, b] =>
      (match a, b with | .list x, .list y => some (.list (x ++ y)) | _, _ => none)
  | "PlainLiteral-from-string-lang", [a, b] =>
      (match isStringy a, isStringy b with
       | some s, some l => some (.const (s ++ "@" ++ l) (rdfNs ++ "PlainLiteral"))
       | _, _ => none)
  | "string-from-PlainLiteral", [a] =>
      (match a with
       | .const lex sp =>
           if sp == rdfNs ++ "PlainLiteral" then
             some (gStr (match (lex.splitOn "@").reverse with
                         | _ :: rest => String.intercalate "@" rest.reverse
                         | []        => lex))
           else none
       | _ => none)
  | "lang-from-PlainLiteral", [a] =>
      (match a with
       | .const lex sp =>
           if sp == rdfNs ++ "PlainLiteral" then
             some (gStr ((lex.splitOn "@").getLast?.getD ""))
           else none
       | _ => none)
  | _, _ =>
      -- A datatype CAST, `External( xs:date ( "…"^^xs:string ) )`.
      if name.startsWith "cast-" then
        let base := String.ofList (name.toList.drop 5)
        (match args with
         | [.const lex _] =>
             (match inLexicalSpace base lex with
              | some true => some (gLit lex (xsdNs ++ base))
              | _         => none)
         | _ => none)
      else none

end L4Factoidal.RIF
