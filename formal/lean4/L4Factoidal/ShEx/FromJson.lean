/-
L4Factoidal.ShEx.FromJson — ShExJ (the JSON serialisation of a ShEx
schema) into the `Schema` `Schema.lean` defines.

Spec: ShEx 2.1 §D, "ShExJ".

Why the JSON and not the compact syntax: the corpus ships BOTH for
every schema (`0.shex` and `0.json`), and ShExJ is the specification's
own abstract syntax written down. A ShExC parser is a separate piece
of work; reading the JSON is what lets the validator be MEASURED
today, and the two are not in tension — a ShExC parser, when it lands,
produces the same `Schema`.

Every shape this reader does not recognise yields `none` rather than
an empty schema. A schema silently read as "no shapes" validates
nothing and REPORTS nothing, which is the failure mode that reads as a
passing test.
-/
import L4Factoidal.ShEx.Schema
import L4Factoidal.JSON.Value

namespace L4Factoidal.ShEx

open L4Factoidal.JSON

private def fld? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match fld? k v with
  | some (.string s) => some s
  | _                => none

private def bool? (k : String) (v : Json) : Option Bool :=
  match fld? k v with
  | some (.bool b) => some b
  | _              => none

private def int? (k : String) (v : Json) : Option Int :=
  match fld? k v with
  | some (.number n) => n.toInt?
  | some (.string s) => s.toInt?
  | _                => none

private def arr (k : String) (v : Json) : List Json :=
  match fld? k v with
  | some (.array a) => a
  | some x          => [x]     -- ShExJ allows a lone value for a list
  | none            => []

private def strList (k : String) (v : Json) : List String :=
  (arr k v).filterMap (fun x => match x with | .string s => some s | _ => none)

/-- One `SemAct`. The `code` is kept VERBATIM: this reader does not
    know any extension's language, and an extension nobody implements
    must reach the evaluator intact rather than be dropped here. -/
def semActOf (j : Json) : Option SemAct :=
  (str? "name" j).map (fun n => { name := n, code := str? "code" j })

def semActsOf (j : Json) : List SemAct := (arr "semActs" j).filterMap semActOf

/-- The SCHEMA's own actions live under `startActs`, not `semActs`. -/
def startActsOf (j : Json) : List SemAct := (arr "startActs" j).filterMap semActOf

def nodeKindOf (s : String) : Option NodeKind :=
  if s == "iri" then some .iri
  else if s == "bnode" then some .bnode
  else if s == "nonliteral" then some .nonLiteral
  else if s == "literal" then some .literal
  else none

/-- An `ObjectValue`: a bare IRI string, or a literal object. -/
def objectValueOf (j : Json) : Option ObjectValue :=
  match j with
  | .string s => some (.iri s)
  | .object _ =>
      match str? "value" j with
      | some v => some (.literal v ((str? "language" j).map String.toLower) (str? "type" j))
      | none   => (str? "@id" j).map ObjectValue.iri
  | _ => none

private def vsvKindOf (ty : String) : Option VsvKind :=
  if ty.startsWith "Iri" then some .iri
  else if ty.startsWith "Literal" then some .literal
  else if ty.startsWith "Language" then some .language
  else none

/-- One exclusion of a stem range. A BARE STRING means whatever the
    range's kind means: an IRI in an `IriStemRange`, a literal VALUE in
    a `LiteralStemRange`, a language TAG in a `LanguageStemRange`.
    Reading it as an IRI in every case is what made literal and
    language exclusions inert. -/
def exclusionOf (k : VsvKind) (j : Json) : Option Exclusion :=
  match j with
  | .string s =>
      some (match k with
            | .iri      => .value (.iri s)
            | .literal  => .value (.literal s none none)
            | .language => .lang s)
  | .object _ =>
      (match str? "type" j with
       | some ty =>
           if ty.endsWith "Stem" then
             (match fld? "stem" j with
              | some (.string p) => some (Exclusion.stem p)
              | _                => none)
           else (objectValueOf j).map Exclusion.value
       | none => (objectValueOf j).map Exclusion.value)
  | _ => none

/-- A member of a `values` set: an exact object, a stem, a stem range
    with exclusions, or a language tag. -/
def valueSetValueOf (j : Json) : Option ValueSetValue :=
  match j with
  | .string _ => (objectValueOf j).map ValueSetValue.object
  | .object _ =>
      match str? "type" j with
      | some ty =>
          if ty == "Language" then
            ((str? "languageTag" j).map String.toLower).map ValueSetValue.language
          else
            match vsvKindOf ty with
            | none => (objectValueOf j).map ValueSetValue.object
            | some k =>
                let stem := match fld? "stem" j with
                  | some (.string s) => Stem.plain s
                  | some _           => Stem.wildcard
                  | none             => Stem.wildcard
                if ty.endsWith "StemRange" then
                  some (.stemRange k stem
                    ((arr "exclusions" j).filterMap (exclusionOf k)))
                else some (.stem k stem)
      | none => (objectValueOf j).map ValueSetValue.object
  | _ => none

def nodeConstraintOf (j : Json) : NodeConstraint :=
  { nodeKind := (str? "nodeKind" j).bind nodeKindOf
    datatype := str? "datatype" j
    values := (arr "values" j).filterMap valueSetValueOf
    length := int? "length" j
    minLength := int? "minlength" j |>.orElse (fun _ => int? "minLength" j)
    maxLength := int? "maxlength" j |>.orElse (fun _ => int? "maxLength" j)
    pattern := str? "pattern" j
    flags := str? "flags" j
    minInclusive := (fld? "mininclusive" j |>.orElse (fun _ => fld? "minInclusive" j)).bind
      (fun x => match x with
                | .number n => some (canonNumericLexeme n)
                | .string s => some (canonNumericLexeme s)
                | _         => none)
    maxInclusive := (fld? "maxinclusive" j |>.orElse (fun _ => fld? "maxInclusive" j)).bind
      (fun x => match x with
                | .number n => some (canonNumericLexeme n)
                | .string s => some (canonNumericLexeme s)
                | _         => none)
    minExclusive := (fld? "minexclusive" j |>.orElse (fun _ => fld? "minExclusive" j)).bind
      (fun x => match x with
                | .number n => some (canonNumericLexeme n)
                | .string s => some (canonNumericLexeme s)
                | _         => none)
    maxExclusive := (fld? "maxexclusive" j |>.orElse (fun _ => fld? "maxExclusive" j)).bind
      (fun x => match x with
                | .number n => some (canonNumericLexeme n)
                | .string s => some (canonNumericLexeme s)
                | _         => none)
    totalDigits := int? "totaldigits" j |>.orElse (fun _ => int? "totalDigits" j)
    fractionDigits := int? "fractiondigits" j |>.orElse (fun _ => int? "fractionDigits" j) }

mutual

/-- A shape expression. A bare STRING is a reference — ShExJ writes a
    `shapeExprRef` that way, and reading it as anything else loses
    every recursive schema in the corpus. -/
partial def shapeExprOf (j : Json) : Option ShapeExpr :=
  match j with
  | .string s => some (.ref s)
  | .object _ =>
      match str? "type" j with
      | some "ShapeAnd"      => some (.shapeAnd ((arr "shapeExprs" j).filterMap shapeExprOf))
      | some "ShapeOr"       => some (.shapeOr ((arr "shapeExprs" j).filterMap shapeExprOf))
      | some "ShapeNot"      => (fld? "shapeExpr" j).bind shapeExprOf |>.map ShapeExpr.shapeNot
      | some "NodeConstraint" => some (.nodeConstraint (nodeConstraintOf j))
      | some "ShapeExternal" => some .external
      | some "Shape"         =>
          some (.shape (.mk ((bool? "closed" j).getD false)
                            (strList "extra" j)
                            ((fld? "expression" j).bind tripleExprOf)
                            (semActsOf j) [] (strList "extends" j)))
      | some "ShapeDecl"     => (fld? "shapeExpr" j).bind shapeExprOf
      | _ => none
  | _ => none

/-- A triple expression. A bare string is a `tripleExprRef`. -/
partial def tripleExprOf (j : Json) : Option TripleExpr :=
  match j with
  | .string s => some (.ref s)
  | .object _ =>
      match str? "type" j with
      | some "TripleConstraint" =>
          (str? "predicate" j).map (fun p =>
            .tripleConstraint (.mk (str? "id" j)
                                   ((bool? "inverse" j).getD false)
                                   p
                                   ((fld? "valueExpr" j).bind shapeExprOf)
                                   ((int? "min" j).getD 1)
                                   ((int? "max" j).getD 1)
                                   (semActsOf j) []))
      | some "EachOf" =>
          some (.eachOf (.mk (str? "id" j) ((arr "expressions" j).filterMap tripleExprOf)
                             (int? "min" j) (int? "max" j) (semActsOf j) []))
      | some "OneOf" =>
          some (.oneOf (.mk (str? "id" j) ((arr "expressions" j).filterMap tripleExprOf)
                            (int? "min" j) (int? "max" j) (semActsOf j) []))
      | _ => none
  | _ => none

end

/-- One `shapes` member: the modern `ShapeDecl` wrapper, or a bare
    shape expression carrying its own `id`. -/
def shapeDeclOf (j : Json) : Option ShapeDecl :=
  match str? "id" j with
  | none => none
  | some id =>
      match str? "type" j with
      | some "ShapeDecl" =>
          ((fld? "shapeExpr" j).bind shapeExprOf).map (fun e =>
            { id := id, isAbstract := (bool? "abstract" j).getD false, expr := e })
      | _ => (shapeExprOf j).map (fun e => { id := id, expr := e })

/-- Read a whole ShExJ document. `none` when it is not a Schema at
    all — never an empty schema, which would validate nothing and
    report nothing. -/
def schemaOf (j : Json) : Option Schema :=
  match str? "type" j with
  | some "Schema" =>
      some { start := (fld? "start" j).bind shapeExprOf
             startActs := startActsOf j
             shapes := (arr "shapes" j).filterMap shapeDeclOf
             imports := strList "imports" j }
  | _ => none

end L4Factoidal.ShEx
