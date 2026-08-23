/-
L4Factoidal.CSVW.PipelineTests — build-time checks for the two rules
metadata DISCOVERY turns on.
-/
import L4Factoidal.CSVW.Pipeline

namespace L4Factoidal.CSVW

open L4Factoidal.RDF

private def suite : String := "http://www.w3.org/2013/csvw/tests/"

/-! ## §5.2: discovered metadata that does not reference the requested
file MUST be ignored.

Five tests in the corpus put a `csv-metadata.json` next to a CSV it
does NOT describe, and check that the CSV is converted on its own.
Without the rule the converter went looking for the table the
metadata DID name, did not find it, and the run reported "table file
not found" — a skip that reads as a missing fixture rather than as an
unimplemented rule. -/

private def refsOther : TableGroup :=
  { tables := [{ url := "test117-ref.csv" }] }

private def refsIt : TableGroup :=
  { tables := [{ url := "test117.csv" }] }

#guard !(describesTable (suite ++ "test117.csv-metadata.json") refsOther
           (suite ++ "test117.csv"))
#guard describesTable (suite ++ "test117.csv-metadata.json") refsIt
         (suite ++ "test117.csv")

-- The comparison is on the RESOLVED url, so a metadata document in a
-- subdirectory naming `action.csv` describes the file beside it and
-- not a same-named file at the top level.
#guard describesTable (suite ++ "test119/csv-metadata.json")
         { tables := [{ url := "action.csv" }] } (suite ++ "test119/action.csv")
#guard !(describesTable (suite ++ "test119/csv-metadata.json")
           { tables := [{ url := "action.csv" }] } (suite ++ "action.csv"))

/-! ## §5.1: `@base` in the `@context` moves the document's base URL

`@base` is resolved against the metadata document's own location, and
everything the document says is then relative to the result. test273
puts `"@base": "test273/"` on a document at the top level, so its
`"url": "action.csv"` names `test273/action.csv`. -/

#guard effectiveBase (suite ++ "test273-metadata.json") { base := some "test273/" }
       == suite ++ "test273/"
#guard effectiveBase (suite ++ "test011/csv-metadata.json") {}
       == suite ++ "test011/csv-metadata.json"
#guard describesTable (effectiveBase (suite ++ "test273-metadata.json")
                        { base := some "test273/" })
         { tables := [{ url := "action.csv" }] } (suite ++ "test273/action.csv")

/-! ## §5.4 `suppressOutput`, `@id`, and `notes` -/

private def twoRows : Table :=
  { header := [{ num := 1, cells := ["a"] }],
    rows := [{ num := 2, cells := ["x"] }] }

private def plainTable : TableDesc := { url := "t.csv" }
private def hushed : TableDesc := { url := "s.csv", suppress := some true }

-- A suppressed table contributes NOTHING: no rows, no table node, no
-- link from the group. csv2json honoured this and csv2rdf did not, so
-- test034 emitted 105 triples where 60 were expected.
#guard (convert (suite ++ "m.json") {} { tables := [hushed] } false
          [(hushed, twoRows)]).length == 1     -- the TableGroup type triple alone
#guard (convert (suite ++ "m.json") {} { tables := [hushed] } true
          [(hushed, twoRows)]) == []

-- `@id` makes the table node an IRI; absent, it is a blank node.
#guard tableNodeOf (suite ++ "m.json") 0 plainTable == Subject.bnode "table0"
#guard (match tableNodeOf (suite ++ "m.json") 0
              { url := "t.csv", id := some "http://example.org/tree-ops-ext" } with
        | .iri i => i.val == "http://example.org/tree-ops-ext"
        | _      => false)
-- An `@id` that is present but NOT A STRING makes the table take the
-- metadata document's own URL. That is observed from test102, which
-- writes `"@id": 1` and expects every triple on
-- `<…/test102-metadata.json>`; the specification says the value is
-- invalid and does not say what identity remains.
#guard (match tableNodeOf (suite ++ "test102-metadata.json") 0
              { url := "t.csv", idNonString := true } with
        | .iri i => i.val == suite ++ "test102-metadata.json"
        | _      => false)

-- An explicit `@value` object with no `@language` is a PLAIN literal.
-- The default language applies to a bare string, not to a value
-- object that states its value and states no language; re-tagging it
-- put `"text/plain"@en` where test036 expects `"text/plain"`.
#guard commonLeafTerm (suite ++ "m.json") (some "en")
         (.object [("@value", .string "text/plain")])
       == some (Term.literal (Literal.string "text/plain"))
#guard commonLeafTerm (suite ++ "m.json") (some "en") (.string "text/plain")
       == some (Term.literal (Literal.langString "text/plain" "en"))

end L4Factoidal.CSVW
