/-
L4Factoidal.RML.Model — the mapping document, as a value.

Spec: RML-Core (https://w3id.org/rml/core/spec). A mapping is a set of
TRIPLES MAPS; each names a LOGICAL SOURCE, a SUBJECT MAP, and
PREDICATE-OBJECT MAPS.

The model is kept apart from the RDF graph it is read out of
(`RML/FromGraph.lean`) and from the evaluation that runs it
(`RML/Eval.lean`). That is not tidiness: a mapping graph is arbitrary
RDF and reading it can fail in many ways, while evaluation is a total
function of a mapping and a source, and mixing the two would make
"this mapping is malformed" and "this record has no value" the same
kind of answer.
-/
import L4Factoidal.RML.Mapping

namespace L4Factoidal.RML

/-- `rml:logicalSource` — where the records come from. -/
structure LogicalSource where
  /-- `rml:path` of the `rml:RelativePathSource`. -/
  path           : String := ""
  /-- `rml:iterator` — the expression that cuts the document into
      records. Absent means the whole document is one record. -/
  iterator       : Option String := none
  /-- `rml:referenceFormulation`, as an IRI. -/
  refFormulation : String := ""
deriving Repr, Inhabited

/-- `rml:joinCondition` — one `rml:child` / `rml:parent` pair.

    Both sides are TERM MAPS, not reference strings. The shortcut
    `rml:child "$.ID"` is the common form, but `rml:childMap` may hold
    a template, and `RMLTC0030b` joins
    `rml:childMap [ rml:template "http://example.com/{$.Sport}" ]`
    against a parent template. Storing a string threw the template
    away and the join then compared the wrong things. -/
structure JoinCondition where
  child  : TermMap
  parent : TermMap
deriving Repr

/-- An OBJECT map: either a term map, or a reference to another
    triples map with join conditions.

    The two are not variants of one thing. A term map produces a term
    from THIS record; a `rml:RefObjectMap` produces the SUBJECTS of
    another triples map's records, filtered by the joins. Modelling
    the second as a term map with extra fields would hide that it
    reads a different source. -/
inductive ObjectMap where
  | term (base : TermMap) (datatypeMap : Option TermMap) (languageMap : Option TermMap)
  | ref  (parent : String) (joins : List JoinCondition)
deriving Repr

structure PredicateObjectMap where
  predicates : List TermMap := []
  objects    : List ObjectMap := []
  graphs     : List TermMap := []
deriving Repr

structure TriplesMap where
  /-- The IRI (or blank-node label) the mapping graph gives it —
      what a `rml:parentTriplesMap` names. -/
  id       : String
  /-- `rml:baseIRI` — what a RELATIVE result resolves against. -/
  base     : Option String := none
  source   : LogicalSource := {}
  subject  : TermMap
  /-- `rml:class` on the subject map. -/
  classes  : List String := []
  /-- `rml:graph` / `rml:graphMap` on the SUBJECT map: they apply to
      every triple the map generates, not only to the type triples. -/
  graphs   : List TermMap := []
  poms     : List PredicateObjectMap := []
deriving Repr

abbrev Mapping := List TriplesMap

end L4Factoidal.RML
