/-
L4Factoidal.CSVW.PipelineTests — build-time checks for the two rules
metadata DISCOVERY turns on.
-/
import L4Factoidal.CSVW.Pipeline

namespace L4Factoidal.CSVW

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

end L4Factoidal.CSVW
