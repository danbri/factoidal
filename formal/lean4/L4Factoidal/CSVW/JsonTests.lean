/-
L4Factoidal.CSVW.JsonTests — build-time checks for csv2json output.
-/
import L4Factoidal.CSVW.Json

namespace L4Factoidal.CSVW
open L4Factoidal.JSON

private def look : String → Option String := rowLookup [("name", "Alice")] 1 2
private def plain : Inherited := {}
private def listCol : Inherited := { separator := some "," }
private def nullCol : Inherited := { null := some "NA" }

-- A plain cell is a single value.
#guard cellJson plain (convertCell plain "c" look "Alice") == some (.string "Alice")

-- A NULL cell contributes NO member at all — csv2json omits it
-- rather than emitting JSON null.
#guard cellJson nullCol (convertCell nullCol "c" look "NA") == none
#guard rowJsonMinimal [("c", nullCol, convertCell nullCol "c" look "NA")]
       == Json.object []

-- A `separator` column is ALWAYS an array, even with one element —
-- the list-ness comes from the metadata, not from the cell content.
#guard cellJson listCol (convertCell listCol "c" look "solo")
       == some (.array [.string "solo"])
#guard cellJson listCol (convertCell listCol "c" look "a,b")
       == some (.array [.string "a", .string "b"])

-- Minimal mode keys by column name.
#guard rowJsonMinimal [("name", plain, convertCell plain "name" look "Alice")]
       == Json.object [("name", .string "Alice")]

-- Standard mode wraps the row in url/rownum/describes.
private def std : Json :=
  rowJsonStandard "http://ex/t.csv" 1 2 []
    [("name", plain, convertCell plain "name" look "Alice")]
#guard match std with
       | .object ms => ms.any (fun (k, _) => k == "url") &&
                       ms.any (fun (k, _) => k == "rownum") &&
                       ms.any (fun (k, _) => k == "describes")
       | _ => false
#guard match std with
       | .object ms => (ms.find? (fun (k, _) => k == "rownum")).map (·.2)
                       == some (.number "1")
       | _ => false

-- `titles` appears only when there are titles.
#guard match rowJsonStandard "http://ex/t.csv" 1 2 ["T"] [] with
       | .object ms => ms.any (fun (k, _) => k == "titles")
       | _ => false
#guard match std with
       | .object ms => !(ms.any (fun (k, _) => k == "titles"))
       | _ => false

-- An EMPTY comment list must produce NO `rdfs:comment` member: the
-- spec says to remove the property rather than emit an empty array.
#guard commentPairs [] == []
#guard commentPairs ["note"] == [("rdfs:comment", .array [.string "note"])]

-- A suppressed table contributes nothing to the minimal document.
#guard documentJsonMinimal [(true, [.string "x"]), (false, [.string "y"])]
       == Json.array [.string "y"]

-- Standard document nests tables under `tables`.
#guard match documentJsonStandard [("http://ex/t.csv", [], [])] with
       | .object [("tables", .array [_])] => true
       | _ => false

end L4Factoidal.CSVW
