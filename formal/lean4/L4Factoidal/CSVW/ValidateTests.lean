/-
L4Factoidal.CSVW.ValidateTests — build-time checks for CSVW metadata
validation, with the error/warning line pinned explicitly.
-/
import L4Factoidal.CSVW.Validate

namespace L4Factoidal.CSVW
open L4Factoidal.JSON

-- Language tags.
#guard langValid "en"
#guard langValid "en-GB"
#guard !(langValid "e")
#guard !(langValid "toolongsubtag")
#guard !(langValid "1234")

-- A blank-node @id is an ERROR.
#guard checkId "column" (.object [("@id", .string "_:foo")]) == [err "column @id must not be a blank node"]
#guard checkId "column" (.object [("@id", .string "http://ex/c")]) == []
-- A NON-STRING @id is graceful degradation, NOT flagged here.
#guard checkId "column" (.object [("@id", .number "42")]) == []

-- @type must match its role; missing @type is fine.
#guard checkType "Column" (.object [("@type", .string "Column")]) == []
#guard (checkType "Column" (.object [("@type", .string "Table")])).length == 1
#guard checkType "Column" (.object []) == []

-- An unknown datatype NAME is a WARNING, never an error — the suite
-- classifies it as a WarningValidationTest, so a document carrying it
-- must still pass.
#guard checkDatatype (.object [("datatype", .string "integer")]) == []
#guard (checkDatatype (.object [("datatype", .string "madeUpType")])).length == 1
#guard match checkDatatype (.object [("datatype", .string "madeUpType")]) with
       | [f] => f.severity == .warning
       | _   => false
#guard passes (checkDatatype (.object [("datatype", .string "madeUpType")]))

-- ...whereas a blank-node @id must NOT pass.
#guard !(passes (checkId "column" (.object [("@id", .string "_:x")])))

-- Titles keyed by an invalid language tag.
#guard checkTitles (.object [("titles", .object [("en", .string "T")])]) == []
#guard (checkTitles (.object [("titles", .object [("1", .string "T")])])).length == 1

-- Nested traversal: a bad column inside a schema inside a table
-- inside a group is still found.
private def doc : Json :=
  .object [("tables", .array [
    .object [("tableSchema", .object [("columns", .array [
      .object [("@id", .string "_:bad")]])])]])]
#guard !(passes (validate doc))
#guard (validate doc).length == 1

-- A clean document passes with no findings at all.
#guard validate (.object [("tables", .array [
         .object [("tableSchema", .object [("columns", .array [
           .object [("titles", .object [("en", .string "Name")]),
                    ("datatype", .string "string")]])])]])]) == []

-- A bare table object is a valid root too.
#guard validate (.object [("tableSchema", .object [("columns", .array [])])]) == []

end L4Factoidal.CSVW
