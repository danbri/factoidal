/-
L4Factoidal.CSVW.Common — emitting COMMON PROPERTIES as RDF.

Spec: tabular-metadata §5.8 (common properties) and csv2rdf §6, which
says a common property on a table group / table / column becomes a
triple on that object's node, with the value read the way JSON-LD
reads a value.

This is a JSON-LD SUBSET, deliberately, and the boundary is stated so
nobody reads it as "we run JSON-LD here": the shapes handled are a
bare string / number / boolean, `@value` with `@type` or `@language`,
`@id`, `@type` on a nested node, arrays of any of those, and nested
objects (which become blank nodes and recurse). What is NOT handled is
everything that needs a live `@context`: term definitions, `@vocab`,
containers, and `@graph`. A metadata document's `@context` in this
corpus carries `@language` and `@base` only, which is what
`MetadataParse.Ctx` keeps.

A value whose shape is not handled emits NO triple rather than a
guessed one. That is the same rule the cell path follows for an
unresolvable predicate, and for the same reason: a metadata error is
not a licence to invent a term.
-/
import L4Factoidal.CSVW.MetadataParse
import L4Factoidal.CSVW.Emit
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.CSVW

open L4Factoidal.RDF
open L4Factoidal.JSON

/-- Build a checked IRI from a reference, resolved against `base`. -/
def refIri? (base : String) (r : String) : Option WfIri :=
  let abs := if isIri r && !(r.startsWith "#") then r
             else L4Factoidal.Syntax.resolveIri base r
  if h : isIri abs then some ⟨abs, h⟩ else none

/-- The datatype a bare JSON scalar carries, per JSON-LD's own value
    mapping: a boolean is `xsd:boolean`, a number with no fraction or
    exponent is `xsd:integer`, any other number is `xsd:double`. -/
def jsonScalarDatatype (n : String) : String :=
  if n.any (fun c => c == '.' || c == 'e' || c == 'E')
  then "http://www.w3.org/2001/XMLSchema#double"
  else "http://www.w3.org/2001/XMLSchema#integer"

private def xsdIri? (s : String) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

/-- The object term a LEAF common-property value denotes, if it is a
    leaf at all (`none` for an array or a nested node, which the
    caller handles). -/
def commonLeafTerm (base : String) (defaultLang : Option String) (v : Json)
    : Option Term :=
  match v with
  | .string s =>
      match defaultLang with
      | some tag => some (.literal (Literal.langString s tag))
      | none     => some (.literal (Literal.string s))
  | .bool b =>
      ((xsdIri? "http://www.w3.org/2001/XMLSchema#boolean").map
        (fun dt => Term.literal (typedLiteral dt (if b then "true" else "false"))))
  | .number n =>
      ((xsdIri? (jsonScalarDatatype n)).map
        (fun dt => Term.literal (typedLiteral dt n)))
  | .null => none
  | .array _ => none
  | .object _ =>
      match jStrField? "@value" v with
      | some lex =>
          match jStrField? "@language" v with
          | some tag => some (.literal (Literal.langString lex tag))
          | none =>
              match (jStrField? "@type" v).map expandPrefixed with
              | some ty =>
                  (refIri? base ty).map (fun dt => Term.literal (typedLiteral dt lex))
              | none =>
                  match defaultLang with
                  | some tag => some (.literal (Literal.langString lex tag))
                  | none     => some (.literal (Literal.string lex))
      | none =>
          match jStrField? "@id" v with
          | some i => (refIri? base i).map Term.iri
          | none   => none

/-- Triples for one common property on `subj`. `path` keys the blank
    nodes a nested node object needs; it must be unique per occurrence,
    so it carries the subject's own path plus the property name.

    `fuel` bounds nesting. It is not a hedge against unknown depth: a
    metadata document is finite, but the recursion is over `Json`
    values that Lean's structural checker cannot see shrinking through
    `List.flatMap`, and a fuel bound is the honest way to stay total
    without an `unsafe` or a `partial`. -/
def commonTriples (base : String) (defaultLang : Option String)
    : Nat → String → Subject → String → Json → List Triple
  | 0,        _,    _,    _,    _ => []
  | fuel + 1, path, subj, prop, v =>
      match refIri? base prop with
      | none => []
      | some p =>
          match v with
          | .array items =>
              (items.zipIdx).flatMap (fun (it, i) =>
                commonTriples base defaultLang fuel
                  (path ++ "_" ++ toString i) subj prop it)
          | _ =>
              match commonLeafTerm base defaultLang v with
              | some o => [⟨subj, p, o⟩]
              | none =>
                  match v with
                  | .object ms =>
                      let node : Subject := .bnode ("cp_" ++ path)
                      let inner := ms.flatMap (fun (k, w) =>
                        if k == "@id" || k == "@value" || k == "@language" then []
                        else if k == "@type" then
                          match (jStr? w).map expandPrefixed with
                          | some ty =>
                              match refIri? base ty with
                              | some t => [(⟨node, rdfTypeIri, .iri t⟩ : Triple)]
                              | none   => []
                          | none => []
                        else
                          commonTriples base defaultLang fuel
                            (path ++ "_" ++ k) node (expandPrefixed k) w)
                      ⟨subj, p, node.toTerm⟩ :: inner
                  | _ => []

/-- Every common property of one metadata object, on one node. -/
def commonPropsTriples (base : String) (defaultLang : Option String)
    (path : String) (subj : Subject) (ps : List CommonProp) : List Triple :=
  (ps.zipIdx).flatMap (fun (cp, i) =>
    commonTriples base defaultLang 16 (path ++ "_" ++ toString i) subj cp.prop cp.value)

end L4Factoidal.CSVW
