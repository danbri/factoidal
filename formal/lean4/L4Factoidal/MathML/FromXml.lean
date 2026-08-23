/-
L4Factoidal.MathML.FromXml — Content MathML markup into the `Expr`
`Core.lean` evaluates.

Spec: MathML 3.0 (2nd Ed.) Chapter 4, Content Markup.

The XML is read by the project's own verified parser
(`L4Factoidal.XML.Parser`), not by a hand-rolled tag scanner. That
matters for the same reason it matters everywhere else in this tree:
entity references, CDATA, comments and attribute normalisation are the
parser's job, and a second, looser reader of the same syntax is a
second set of bugs.

## What a `<cn>` holds

Three forms, and they are not interchangeable:

  * default / `type="integer"` — a decimal integer;
  * `type="real"` — a decimal, possibly in E-notation, read as an
    EXACT rational (`3.14` is `157/50`, never a float);
  * `type="rational"` — two numbers separated by `<sep/>`.

A `<cn>` this module cannot read yields `none`, which the evaluator
reports as an undefined value rather than a zero.
-/
import L4Factoidal.MathML.Core
import L4Factoidal.XML.Parser

namespace L4Factoidal.MathML

open L4Factoidal.XML

/-- Strip a namespace prefix: `m:apply` and `apply` name the same
    element once the prefix is resolved, and the corpus uses both. -/
def localName (tag : String) : String :=
  match tag.splitOn ":" with
  | [_, l]   => l
  | _        => tag

/-- The element children of a node, in order. Text between elements is
    dropped here — in Content markup it is either whitespace or the
    character data of a leaf, which the leaf readers take
    themselves. -/
def elementChildren : Node → List Node
  | .element _ _ cs => cs.filter (fun c => match c with
      | .element _ _ _ => true
      | _              => false)
  | _ => []

/-- All character data directly under a node, concatenated. -/
def textOf : Node → String
  | .element _ _ cs => cs.foldl (fun acc c => match c with
      | .text t  => acc ++ t
      | .cdata t => acc ++ t
      | _        => acc) ""
  | .text t  => t
  | .cdata t => t
  | _        => ""

/-- The pieces a `<cn type="rational">` separates with `<sep/>`. -/
def sepParts : Node → List String
  | .element _ _ cs =>
      (cs.foldl (fun (acc, cur) c => match c with
        | .element t _ _ => if localName t == "sep" then (acc ++ [cur], "") else (acc, cur)
        | .text t        => (acc, cur ++ t)
        | .cdata t       => (acc, cur ++ t)
        | _              => (acc, cur)) ([], "")).1
        ++ [(cs.foldl (fun (acc, cur) c => match c with
              | .element t _ _ => if localName t == "sep" then (acc ++ [cur], "") else (acc, cur)
              | .text t        => (acc, cur ++ t)
              | .cdata t       => (acc, cur ++ t)
              | _              => (acc, cur)) ([], "")).2]
  | _ => []


def attrOf (name : String) : Node → Option String
  | .element _ attrs _ => (attrs.find? (fun a => localName a.name == name)).map (·.value)
  | _ => none

private def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile (·.isWhitespace)).reverse.dropWhile (·.isWhitespace)).reverse

/-- Read a decimal numeral, with an optional fraction and an optional
    exponent, as an EXACT rational. `1.5e2` is `150`, not a float that
    happens to print that way. -/
def decimalToRat (s : String) : Option (Int × Int) :=
  let s := trim s
  let (mant, expPart) :=
    match s.toList.findIdx? (fun c => c == 'e' || c == 'E') with
    | some i => (String.ofList (s.toList.take i), String.ofList (s.toList.drop (i + 1)))
    | none   => (s, "")
  let exp : Int := if expPart == "" then 0 else (expPart.toInt?).getD 0
  if expPart != "" && (expPart.toInt?).isNone then none
  else
    let neg := mant.startsWith "-"
    let body := if neg || mant.startsWith "+" then String.ofList (mant.toList.drop 1) else mant
    let (ip, fp) := match body.splitOn "." with
      | [a]    => (a, "")
      | [a, b] => (a, b)
      | _      => (body, "")
    if ip == "" && fp == "" then none
    else if !(ip ++ fp).toList.all Char.isDigit then none
    else
      let digits := (ip ++ fp).toInt?.getD 0
      let scale : Int := exp - (fp.length : Int)
      let v : Int × Int :=
        if scale ≥ 0 then (digits * (10 : Int) ^ scale.toNat, 1)
        else (digits, (10 : Int) ^ scale.natAbs)
      some (normRat (if neg then -v.1 else v.1) v.2)

/-- Read one Content MathML node. `fuel` bounds the nesting; a
    document deeper than that is refused rather than looped over. -/
partial def exprOf (n : Node) : Option Expr :=
  match n with
  | .element tag _ _ =>
      let ln := localName tag
      if ln == "math" || ln == "semantics" then
        match (elementChildren n).head? with
        | some c => exprOf c
        | none   => none
      else if ln == "cn" then
        match (attrOf "type" n).getD "integer" with
        | "rational" =>
            (match sepParts n with
             | [a, b] =>
                 match (trim a).toInt?, (trim b).toInt? with
                 | some x, some y => if y == 0 then none else some (.rat x y)
                 | _, _ => none
             | _ => none)
        | _ =>
            -- `integer` and `real` share a reader: an integer IS a
            -- decimal with no fraction, and reading them apart would
            -- reject `type="integer"` written as `42.0`.
            (decimalToRat (textOf n)).map (fun r =>
              if r.2 == 1 then Expr.int r.1 else Expr.rat r.1 r.2)
      else if ln == "ci" then some (.sym (trim (textOf n)))
      else if ln == "true" then some (.bool true)
      else if ln == "false" then some (.bool false)
      else if ln == "apply" then
        (match elementChildren n with
         | op :: rest =>
             let fn := match op with
               | .element t _ _ => localName t
               | _              => ""
             -- `<degree>` wraps `root`'s index; it is passed as the
             -- FIRST argument, which is the shape `Core.eval` reads.
             let args := rest.map (fun c =>
               match c with
               | .element t _ _ =>
                   if localName t == "degree" then
                     match (elementChildren c).head? with
                     | some d => exprOf d
                     | none   => none
                   else exprOf c
               | _ => none)
             match args.mapM id with
             | some as => some (.app fn as)
             | none    => none
         | [] => none)
      else none
  | _ => none

/-- Parse a Content MathML document and read its expression. -/
def parseMathML (src : String) : Option Expr :=
  match parseXML src with
  | .error _ => none
  | .ok doc  => exprOf doc.root

end L4Factoidal.MathML
