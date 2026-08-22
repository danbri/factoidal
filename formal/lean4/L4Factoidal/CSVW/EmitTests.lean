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
#guard (rowTriplesStandard "" "http://ex/t.csv" 1 2 [(nameCol, cell)]).length
       == 1 + 4   -- cell + type + describes + rownum + url
#guard (rowTriplesStandard "" "http://ex/t.csv" 1 2 [(nameCol, cell)]).any
         (fun t => t.p.val == csvwNs ++ "rownum")
#guard (rowTriplesStandard "" "http://ex/t.csv" 1 2 [(nameCol, cell)]).any
         (fun t => t.p.val == csvwNs ++ "describes")
-- The row node is TYPED. The W3C no-metadata tests all expect
-- `a csvw:Row`, and its absence was a third of the missing graph.
#guard (rowTriplesStandard "" "http://ex/t.csv" 1 2 [(nameCol, cell)]).any
         (fun t => t.p == rdfTypeIri && t.o == Term.iri csvwRowCls)
-- The `#row=` fragment reports the SOURCE row, not the table row:
-- with a header they differ by one, and reporting the wrong one
-- makes every row URL off by a line.
#guard (rowTriplesStandard "" "http://ex/t.csv" 1 2 [(nameCol, cell)]).any
         (fun t => t.o == Term.iri ⟨"http://ex/t.csv#row=2", rfl⟩)

-- The whole standard-mode output: group node, table node, and the
-- links that hold them together.
private def oneRow : RowInput := { rowNum := 1, sourceRow := 2, cells := [(nameCol, cell)] }
private def std : List Triple := tableGroupTriplesStandard "http://ex/t.csv" [oneRow]

#guard std.any (fun t => t.p == rdfTypeIri && t.o == Term.iri csvwTableGroup)
#guard std.any (fun t => t.p == rdfTypeIri && t.o == Term.iri csvwTableCls)
#guard std.any (fun t => t.p == csvwTableProp)
#guard std.any (fun t => t.p == csvwRowProp)
-- group(type + table) + table(type + url + row) + row(4) + cell(1)
#guard std.length == 2 + 3 + 4 + 1
-- The `csvw:row` link and the row description must name the SAME
-- blank node; if they drift the graph has an orphan row and every
-- isomorphism check fails for a reason that reads as a data bug.
#guard match std.find? (fun t => t.p == csvwRowProp) with
       | some t => std.any (fun u => u.s.toTerm == t.o && u.p == csvwRownumProp)
       | none   => false

-- The checked-IRI helper.
#guard (toIri? "http://ex/ok").isSome
#guard (toIri? "not an iri").isNone

end L4Factoidal.CSVW
