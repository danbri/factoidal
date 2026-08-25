/-
L4Factoidal.HTTP.RunQueryTests — build-time checks for the response
policy.
-/
import L4Factoidal.HTTP.RunQuery

namespace L4Factoidal.HTTP

open L4Factoidal.SPARQL

/-! ## The (shape, format) grid, including where it is NOT full

ASK has a boolean serialiser in JSON and XML only, so CSV and TSV
fall back to JSON — a stated choice, not an accident. A caller asking
for CSV of an ASK gets JSON and the JSON content type, never a CSV
content type over a JSON body. -/

#guard (strategyForAsk .xml).1 == Strategy.booleanXml
#guard (strategyForAsk .csv).1 == Strategy.booleanJson
#guard (strategyForAsk .csv).2 == contentTypeFor .json
#guard (strategyForAsk .tsv).1 == Strategy.booleanJson

#guard (strategyForSelect .csv).1 == Strategy.rowsCsv
#guard (strategyForSelect .tsv).1 == Strategy.rowsTsv
#guard (strategyForSelect .xml).1 == Strategy.rowsXml
#guard (strategyForSelect .json).1 == Strategy.rowsJson

/-! CONSTRUCT and DESCRIBE produce triples, which belong in an RDF
    format. Until triples output lands they are SELECT-shaped, and
    CSV/TSV fall back to JSON. -/
#guard (strategyForConstructDescribe .csv).1 == Strategy.rowsJson
#guard (strategyForConstructDescribe .xml).1 == Strategy.rowsXml

/-! ## The cap is a STRICT overflow

Exactly `maxRows` passes; `maxRows + 1` does not. An off-by-one here
turns a legal result into a 413, which reads as a server limit rather
than as a bug. -/

private def rowsOf (n : Nat) : List Binding := List.replicate n []

#guard !(rowCountOverflows 3 (rowsOf 3))
#guard rowCountOverflows 3 (rowsOf 4)
#guard !(rowCountOverflows 0 (rowsOf 0))
#guard rowCountOverflows 0 (rowsOf 1)

#guard (runQuery .select .json 3 [] none (some (rowsOf 4))).status == 413
#guard (runQuery .select .json 3 [] none (some (rowsOf 3))).status == 200

/-! ## Status codes and content types -/

#guard (makeParseErrorResponse "bad").status == 400
#guard (makeParseErrorResponse "bad").body == "SPARQL parse error: bad\n"
#guard (makeParseErrorResponse "bad").contentType == plainText
#guard (makeEvalErrorResponse "boom" "at ...").status == 500

/-! ## An ASK response carries a boolean document, not an empty row set -/

#guard (runQuery .ask .json 10 [] (some true) none).status == 200
#guard (runQuery .ask .json 10 [] (some true) none).contentType == contentTypeFor .json
#guard ((runQuery .ask .json 10 [] (some true) none).body.splitOn "true").length > 1

/-! A missing ASK result defaults to FALSE, which is what the F* module
    does. It is a default, and it is here so that a caller which lost
    its result cannot make the server emit a document claiming
    `true`. -/
#guard ((runQuery .ask .json 10 [] none none).body.splitOn "false").length > 1

end L4Factoidal.HTTP
