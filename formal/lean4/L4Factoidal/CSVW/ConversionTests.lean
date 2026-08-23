/-
L4Factoidal.CSVW.ConversionTests — build-time checks for csv2rdf cell
conversion.
-/
import L4Factoidal.CSVW.Conversion

namespace L4Factoidal.CSVW

private def look : String → Option String :=
  rowLookup [("name", "Alice"), ("code", "AD")] 1 2

-- Row-scoped variables, csv2rdf's underscore convention.
#guard look "_row" == some "1"
#guard look "_sourceRow" == some "2"
#guard look "name" == some "Alice"
#guard look "absent" == none

-- §6.4.2 whitespace rule: the STRING family preserves surrounding
-- space, every other base strips it before lexical parsing. This is
-- what lets a date cell parse through its padding while a string cell
-- keeps it.
#guard dtPreservesWs "string"
#guard dtPreservesWs "json"
#guard !(dtPreservesWs "date")
#guard !(dtPreservesWs "integer")
-- `prepareLexical` returns the lexical form AND whether the column's
-- datatype applies to it. A cell that fails its own format keeps its
-- text and loses the datatype claim.
#guard prepareLexical (some (.named "string")) "  x  " == ("  x  ", true)
#guard prepareLexical (some (.named "date")) " 2010-10-18 " == ("2010-10-18", true)
#guard prepareLexical none "  x  " == ("  x  ", true)   -- absent datatype is string
#guard prepareLexical
         (some (.object (some "date") (some "M/d/yyyy") none none none none
                 none none none none none none none none none))
         "10/18/2010" == ("2010-10-18", true)
#guard prepareLexical
         (some (.object (some "date") (some "M/d/yyyy") none none none none
                 none none none none none none none none none))
         "not a date" == ("not a date", false)

-- `separator` makes the cell a LIST; elements are trimmed.
#guard splitSeparated "," "a,b, c " == ["a", "b", "c"]
#guard splitSeparated " " "a b" == ["a", "b"]
-- An EMPTY cell yields NO elements, not one empty element.
#guard splitSeparated "," "" == []

-- `null` names a string meaning "no value"; absent, only "" is null.
#guard isNullCell (some "NA") "NA"
#guard !(isNullCell (some "NA") "")
#guard isNullCell none ""
#guard !(isNullCell none "x")

-- `default` fills an EMPTY cell before datatype parsing.
#guard applyDefault (some "NO") "" == "NO"
#guard applyDefault (some "NO") "YES" == "YES"
#guard applyDefault none "" == ""

-- A null cell contributes no objects, but still reports its
-- property, so the caller can do standard-mode bookkeeping.
private def nullCol : Inherited :=
  { null := some "NA", propertyUrl := some "http://ex/p" }
#guard (convertCell nullCol "c" look "NA").lexicals == []
#guard (convertCell nullCol "c" look "NA").propertyRef == some "http://ex/p"

-- valueUrl wins over a literal value, and expands as a template.
private def urlCol : Inherited := { valueUrl := some "http://ex/{code}" }
#guard (convertCell urlCol "c" look "ignored").valueRefs == ["http://ex/AD"]
#guard (convertCell urlCol "c" look "ignored").lexicals == []

-- A separated cell yields one literal per element.
private def listCol : Inherited := { separator := some "," }
#guard (convertCell listCol "c" look "a,b,c").lexicals == ["a", "b", "c"]

-- Default property IRI: table URL + column name as a fragment.
#guard defaultPropertyRef "http://ex/t.csv" "col name" == "http://ex/t.csv#col%20name"

end L4Factoidal.CSVW
