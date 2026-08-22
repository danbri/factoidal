/-
L4Factoidal.CSVW.EmitTests — build-time checks for csv2rdf triple
emission in both modes.
-/
import L4Factoidal.CSVW.Emit

namespace L4Factoidal.CSVW
open L4Factoidal.RDF

private def look : String → Option String := rowLookup [("name", "Alice")] 1 2

private def nameCol : Inherited :=
  { propertyUrl := some "http://ex/name" }

private def cell : CellResult := convertCell nameCol "name" look "Alice"

-- Minimal mode emits exactly the cell triple.
#guard (rowTriplesMinimal 1 [(nameCol, cell)]).length == 1
#guard match rowTriplesMinimal 1 [(nameCol, cell)] with
       | [t] => t.p.val == "http://ex/name"
       | _   => false
#guard match rowTriplesMinimal 1 [(nameCol, cell)] with
       | [⟨_, _, .literal l⟩] => l.val.lexicalForm == "Alice"
       | _ => false

-- A cell with an UNRESOLVABLE predicate emits nothing rather than a
-- malformed term.
private def badCol : Inherited := { propertyUrl := some "not an iri" }
#guard (rowTriplesMinimal 1 [(badCol, convertCell badCol "c" look "v")]).isEmpty

-- A NULL cell emits nothing, but does not stop its siblings.
private def nullCol : Inherited :=
  { propertyUrl := some "http://ex/p", null := some "NA" }
#guard (rowTriplesMinimal 1 [(nullCol, convertCell nullCol "c" look "NA")]).isEmpty
#guard (rowTriplesMinimal 1
          [(nullCol, convertCell nullCol "c" look "NA"), (nameCol, cell)]).length == 1

-- A language tag wins over a datatype: RDF 1.1 makes any
-- language-tagged literal rdf:langString.
private def langCol : Inherited :=
  { propertyUrl := some "http://ex/p", lang := some "en",
    datatype := some (.named "integer") }
#guard match rowTriplesMinimal 1 [(langCol, convertCell langCol "c" look "5")] with
       | [⟨_, _, .literal l⟩] => l.val.langTag == some "en"
       | _ => false

-- A datatype becomes the literal's type.
private def intCol : Inherited :=
  { propertyUrl := some "http://ex/p", datatype := some (.named "integer") }
#guard match rowTriplesMinimal 1 [(intCol, convertCell intCol "c" look "5")] with
       | [⟨_, _, .literal l⟩] =>
           l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#integer"
       | _ => false

-- A `separator` cell emits one triple PER element, sharing subject
-- and predicate.
private def listCol : Inherited :=
  { propertyUrl := some "http://ex/p", separator := some "," }
#guard (rowTriplesMinimal 1 [(listCol, convertCell listCol "c" look "a,b,c")]).length == 3

-- valueUrl produces an IRI object, not a literal.
private def urlCol : Inherited :=
  { propertyUrl := some "http://ex/p", valueUrl := some "http://ex/v/{name}" }
#guard match rowTriplesMinimal 1 [(urlCol, convertCell urlCol "c" look "x")] with
       | [⟨_, _, .iri i⟩] => i.val == "http://ex/v/Alice"
       | _ => false

-- STANDARD mode adds the row description on top of the cell triples.
#guard (rowTriplesStandard "http://ex/t.csv" 1 2 [(nameCol, cell)]).length
       == 1 + 3   -- cell + describes + rownum + url
#guard (rowTriplesStandard "http://ex/t.csv" 1 2 [(nameCol, cell)]).any
         (fun t => t.p.val == csvwNs ++ "rownum")
#guard (rowTriplesStandard "http://ex/t.csv" 1 2 [(nameCol, cell)]).any
         (fun t => t.p.val == csvwNs ++ "describes")

-- The checked-IRI helper.
#guard (toIri? "http://ex/ok").isSome
#guard (toIri? "not an iri").isNone

end L4Factoidal.CSVW
