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
--
-- Every table here carries a `url`. It is REQUIRED (§5.4), and the
-- suite tests its absence (test090); these documents used to omit it
-- and still pass, which recorded a missing check as expected
-- behaviour.
private def doc : Json :=
  .object [("tables", .array [
    .object [("url", .string "t.csv"),
             ("tableSchema", .object [("columns", .array [
      .object [("@id", .string "_:bad")]])])]])]
#guard !(passes (validate doc))
#guard (validate doc).length == 1

-- A clean document passes with no findings at all.
#guard validate (.object [("tables", .array [
         .object [("url", .string "t.csv"),
                  ("tableSchema", .object [("columns", .array [
           .object [("titles", .object [("en", .string "Name")]),
                    ("datatype", .string "string")]])])]])]) == []

-- A bare table object is a valid root too.
#guard validate (.object [("url", .string "t.csv"),
                          ("tableSchema", .object [("columns", .array [])])]) == []

-- A table with no `url` is REJECTED, and an empty `tables` array is
-- rejected rather than converted to nothing (test074, test090).
#guard !(passes (validate (.object [("tables", .array [.object []])])))
#guard !(passes (validate (.object [("tables", .array [])])))

/-! ## The value-constraint rules (§5.11.2)

Each of these is a `NegativeRdfTest` in the suite: the document must be
REJECTED, not converted with a warning. -/

private def dtDoc (dt : Json) : Json :=
  .object [("url", .string "t.csv"),
           ("tableSchema", .object [("columns", .array [
             .object [("titles", .string "c"), ("datatype", dt)]])])]

#guard !(passes (validate (dtDoc (.object
  [("base", .string "string"), ("length", .number "5"),
   ("minLength", .number "10")]))))          -- length < minLength
#guard !(passes (validate (dtDoc (.object
  [("base", .string "string"), ("minLength", .number "10"),
   ("maxLength", .number "5")]))))           -- maxLength < minLength
#guard !(passes (validate (dtDoc (.object
  [("base", .string "date"), ("length", .number "5")]))))
                                             -- a length facet on a date
#guard !(passes (validate (dtDoc (.object
  [("base", .string "string"), ("minimum", .number "1")]))))
                                             -- a range on a string
#guard !(passes (validate (dtDoc (.object
  [("base", .string "integer"), ("minInclusive", .number "1"),
   ("minExclusive", .number "2")]))))        -- mutually exclusive bounds
#guard !(passes (validate (dtDoc (.object
  [("base", .string "integer"), ("minInclusive", .number "5"),
   ("maxInclusive", .number "1")]))))        -- an empty range
#guard passes (validate (dtDoc (.object
  [("base", .string "integer"), ("minInclusive", .number "1"),
   ("maxInclusive", .number "5")])))         -- a sane range still passes

/-! ## Common properties (§5.8) -/

private def cpDoc (k : String) (v : Json) : Json :=
  .object [("url", .string "t.csv"), (k, v)]

#guard !(passes (validate (cpDoc "dc:x" (.object [("@context", .string "c")]))))
#guard !(passes (validate (cpDoc "dc:x" (.object [("@list", .array [])]))))
#guard !(passes (validate (cpDoc "dc:x" (.object [("@set", .array [])]))))
#guard !(passes (validate (cpDoc "dc:x" (.object [("@foo", .string "x")]))))
#guard !(passes (validate (cpDoc "dc:x" (.object [("@type", .number "1")]))))
#guard !(passes (validate (cpDoc "dc:x" (.object [("@id", .string "_:b")]))))
-- `@value` is exclusive: not both `@type` and `@language`, and no
-- other member beside it.
#guard !(passes (validate (cpDoc "dc:x" (.object
  [("@value", .string "v"), ("@type", .string "t"), ("@language", .string "en")]))))
#guard !(passes (validate (cpDoc "dc:x" (.object
  [("@value", .string "v"), ("dc:y", .string "z")]))))
-- `@language` with nothing to tag.
#guard !(passes (validate (cpDoc "dc:x" (.object [("@language", .string "en")]))))
-- The ordinary shapes still pass.
#guard passes (validate (cpDoc "dc:x" (.string "plain")))
#guard passes (validate (cpDoc "dc:x" (.object
  [("@value", .string "v"), ("@language", .string "en")])))
#guard passes (validate (cpDoc "dc:x" (.object [("@id", .string "http://ex/x")])))

-- `@context` may carry only `@base` and `@language` (test274).
#guard !(passes (validate (.object
  [("@context", .array [.string "http://www.w3.org/ns/csvw",
                        .object [("@vocab", .string "http://ex/")]]),
   ("url", .string "t.csv")])))
#guard passes (validate (.object
  [("@context", .array [.string "http://www.w3.org/ns/csvw",
                        .object [("@language", .string "en")]]),
   ("url", .string "t.csv")]))

/-! ## Schema-level structure -/

private def schemaDoc (sch : Json) : Json :=
  .object [("url", .string "t.csv"), ("tableSchema", sch)]

-- Duplicate column names (test128).
#guard !(passes (validate (schemaDoc (.object [("columns", .array [
  .object [("name", .string "a")], .object [("name", .string "a")]])]))))
-- A virtual column before a real one (test133).
#guard !(passes (validate (schemaDoc (.object [("columns", .array [
  .object [("name", .string "a"), ("virtual", .bool true)],
  .object [("name", .string "b")]])]))))
#guard passes (validate (schemaDoc (.object [("columns", .array [
  .object [("name", .string "b")],
  .object [("name", .string "a"), ("virtual", .bool true)]])])))
-- A foreign key naming a column that does not exist (test104).
#guard !(passes (validate (schemaDoc (.object
  [("columns", .array [.object [("name", .string "a")]]),
   ("foreignKeys", .array [.object
     [("columnReference", .string "zzz"),
      ("reference", .object [("resource", .string "r.csv"),
                             ("columnReference", .string "a")])]])]))))
-- A foreign key carrying a property the specification does not define
-- (test271/test272).
#guard !(passes (validate (schemaDoc (.object
  [("columns", .array [.object [("name", .string "a")]]),
   ("foreignKeys", .array [.object
     [("columnReference", .string "a"),
      ("dc:description", .string "no"),
      ("reference", .object [("resource", .string "r.csv"),
                             ("columnReference", .string "a")])]])]))))

end L4Factoidal.CSVW
