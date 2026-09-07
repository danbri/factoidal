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

/-- A decimal numeral as an exact MANTISSA and SCALE: the value is
    `mant / 10 ^ scale`. Kept exact because RIF numbers are
    `xs:integer` and `xs:decimal`, and a float would make
    `func:numeric-add` approximate on values the corpus compares for
    equality. -/
def decParts (s : String) : Option (Int × Nat) :=
  match (s.splitOn ".") with
  | [i]    => (i.toInt?).map (fun m => (m, 0))
  | [i, f] =>
      if !(f.toList.all (·.isDigit)) then none
      else
        let neg := i.startsWith "-"
        let ii := if i == "" || i == "-" || i == "+" then (if neg then "-0" else "0") else i
        (match ii.toInt? with
         | some m =>
             let frac : Int := Int.ofNat (f.toNat?.getD 0)
             let pow : Int := (10 : Int) ^ f.length
             some ((if neg then m * pow - frac else m * pow + frac), f.length)
         | none   => none)
  | _      => none

/-- Render `mant / 10 ^ scale` as a decimal numeral, without a trailing
    fractional zero run. -/
def decRender (m : Int) (scale : Nat) : String :=
  if scale == 0 then toString m
  else
    let neg := m < 0
    let a := (if neg then -m else m).toNat
    let p := 10 ^ scale
    let ip := a / p
    let fp := a % p
    let fs := (toString fp)
    let fs := String.ofList (List.replicate (scale - fs.length) '0') ++ fs
    let fs := String.ofList (fs.toList.reverse.dropWhile (· == '0')).reverse
    (if neg then "-" else "") ++ toString ip ++ (if fs == "" then "" else "." ++ fs)

private def align (a b : String) : Option (Int × Int × Nat) :=
  match decParts a, decParts b with
  | some (ma, sa), some (mb, sb) =>
      let sc := Nat.max sa sb
      some (ma * (10 : Int) ^ (sc - sa), mb * (10 : Int) ^ (sc - sb), sc)
  | _, _ => none

def addDec (a b : String) : Option String :=
  (align a b).map (fun (x, y, sc) => decRender (x + y) sc)

def subDec (a b : String) : Option String :=
  (align a b).map (fun (x, y, sc) => decRender (x - y) sc)

def mulDec (a b : String) : Option String :=
  match decParts a, decParts b with
  | some (ma, sa), some (mb, sb) => some (decRender (ma * mb) (sa + sb))
  | _, _ => none

/-- Digits kept after the point by `func:numeric-divide`. XSD 1.1
    3.3.4 gives `xs:decimal` arbitrary precision but lets an
    implementation state a limit; this is ours, and a quotient with a
    longer expansion is TRUNCATED here rather than rounded. -/
def divScale : Nat := 18

/-- RIF-DTB 4.4 `func:numeric-divide`. Division by zero has no value
    and gives `none`, which the engine reads as undecided rather than
    as a false answer. -/
def divDec (a b : String) : Option String :=
  match decParts a, decParts b with
  | some (ma, sa), some (mb, sb) =>
      if mb == 0 then none
      else
        let num := ma * (10 : Int) ^ (sb + divScale)
        let den := mb * (10 : Int) ^ sa
        -- `Int./` truncates toward zero, which is the direction this
        -- states, and both signs go the same way.
        some (decRender (num / den) divScale)
  | _, _ => none

/-- The datatype a numeric result carries. RIF-DTB 4.4 keeps
    `func:numeric-add` inside `xs:integer` when both operands are
    integers and inside `xs:decimal` otherwise; the value is the same
    either way, and `RIF.Engine.gEqValue` compares numerics by value,
    so this only affects what a derived fact SAYS its type is. -/
def numResultType (lex : String) : String :=
  if (lex.splitOn ".").length > 1 then xsdNs ++ "decimal" else xsdNs ++ "integer"

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
      if name.startsWith "cast-rdf-" then
        -- RIF-DTB 5: `rdf:PlainLiteral(x)` takes the lexical form of
        -- `x` and gives it an EMPTY language tag, which RIF writes
        -- into the lexical form after `@`; `rdf:XMLLiteral(x)` retags
        -- a string.
        let base := String.ofList (name.toList.drop 9)
        (match args with
         | [.const lex _] =>
             if base == "PlainLiteral" then some (.const (lex ++ "@") (rdfNs ++ "PlainLiteral"))
             else if base == "XMLLiteral" then some (.const lex (rdfNs ++ "XMLLiteral"))
             else none
         | _ => none)
      else if name.startsWith "cast-" then
        let base := String.ofList (name.toList.drop 5)
        (match args with
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

end L4Factoidal.RIF
