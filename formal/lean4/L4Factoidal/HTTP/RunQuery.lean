/-
L4Factoidal.HTTP.RunQuery — the SPARQL Protocol RESPONSE POLICY: which
status code, which content type, which serialiser.

Port of `formal/fstar/SPARQL.HTTP.RunQuery.fst`. Spec: SPARQL 1.1
Protocol (https://www.w3.org/TR/sparql11-protocol/) §2.1 and the
SPARQL 1.1 Query Results formats.

A server has three decisions to make per request, and all three live
here rather than in whatever code owns the socket:

  1. a PARSE error → 400 with a plain-text body;
  2. an EVALUATION error → 500 with a plain-text body;
  3. SUCCESS → pick the serialiser from the query FORM and the
     negotiated FORMAT.

## Not every (shape, format) pair has a serialiser

The Query Results formats define four wire formats and three result
shapes, and the grid is not full:

  * ASK has a boolean serialiser in JSON and XML only. CSV and TSV
    are NOT defined for a boolean result, so they fall back to JSON —
    which is a choice, stated here, not an accident;
  * SELECT has all four;
  * CONSTRUCT and DESCRIBE produce TRIPLES, which belong in an RDF
    format rather than a Query Results one. Until triples output
    lands they are serialised SELECT-shaped, in JSON or XML.

## The row cap is a STRICT overflow

`rowCountOverflows maxRows rows` is true exactly when
`rows.length > maxRows`, so a result of exactly `maxRows` passes
through. An off-by-one here turns a legal result into a 413, which
looks like a server limit rather than a bug.
-/
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsCsvTsv

namespace L4Factoidal.HTTP

open L4Factoidal.SPARQL

/-! ## Status codes -/

def parseErrorStatus : Nat := 400
def evalErrorStatus : Nat := 500
def successStatus : Nat := 200
def resultCapStatus : Nat := 413

/-! ## Wire formats -/

inductive Fmt where
  | json | xml | csv | tsv
deriving Repr, DecidableEq, Inhabited

def contentTypeFor : Fmt → String
  | .json => "application/sparql-results+json; charset=utf-8"
  | .xml  => "application/sparql-results+xml; charset=utf-8"
  | .csv  => "text/csv; charset=utf-8"
  | .tsv  => "text/tab-separated-values; charset=utf-8"

/-- The query FORM, as far as the response policy needs to know it. -/
inductive Form where
  | ask | select | constructOrDescribe
deriving Repr, DecidableEq, Inhabited

/-- Which serialiser to call. Naming the choice as a value rather than
    calling it inline is what lets the decision be tested apart from
    the serialisers themselves. -/
inductive Strategy where
  | booleanJson | booleanXml | rowsJson | rowsXml | rowsCsv | rowsTsv
deriving Repr, DecidableEq, Inhabited

/-- ASK: JSON and XML only; CSV and TSV fall back to JSON. -/
def strategyForAsk : Fmt → Strategy × String
  | .xml => (.booleanXml, contentTypeFor .xml)
  | _    => (.booleanJson, contentTypeFor .json)

/-- SELECT: all four formats. -/
def strategyForSelect : Fmt → Strategy × String
  | .xml => (.rowsXml, contentTypeFor .xml)
  | .csv => (.rowsCsv, contentTypeFor .csv)
  | .tsv => (.rowsTsv, contentTypeFor .tsv)
  | _    => (.rowsJson, contentTypeFor .json)

/-- CONSTRUCT and DESCRIBE: SELECT-shaped for now, JSON or XML. -/
def strategyForConstructDescribe : Fmt → Strategy × String
  | .xml => (.rowsXml, contentTypeFor .xml)
  | _    => (.rowsJson, contentTypeFor .json)

/-! ## Response bodies -/

structure ResponseBody where
  status      : Nat
  contentType : String
  body        : String
deriving Repr, Inhabited

def plainText : String := "text/plain; charset=utf-8"

def parseErrorBody (msg : String) : String := "SPARQL parse error: " ++ msg ++ "\n"

/-- The evaluation-error body carries the host's own message and
    backtrace. Neither is synthesised here: the caller captures them
    from its runtime and passes them in, because a message this module
    invented would describe a failure it did not see. -/
def evalErrorBody (msg backtrace : String) : String :=
  "Query evaluation error: " ++ msg ++ "\n" ++ "Backtrace:\n" ++ backtrace

def makeParseErrorResponse (msg : String) : ResponseBody :=
  { status := parseErrorStatus, contentType := plainText, body := parseErrorBody msg }

def makeEvalErrorResponse (msg backtrace : String) : ResponseBody :=
  { status := evalErrorStatus, contentType := plainText,
    body := evalErrorBody msg backtrace }

def resultCapBody (maxRows : Nat) : String :=
  "{\"head\":{},\"error\":\"result set exceeds the server cap of "
    ++ toString maxRows ++ " rows\"}"

def makeResultCapResponse (maxRows : Nat) : ResponseBody :=
  { status := resultCapStatus, contentType := "application/json; charset=utf-8",
    body := resultCapBody maxRows }

/-- STRICT overflow: true exactly when there are MORE than `maxRows`
    rows, so a result of exactly `maxRows` passes through. -/
def rowCountOverflows (maxRows : Nat) (rows : List Binding) : Bool :=
  rows.length > maxRows

/-! ## Dispatch -/

def bodyForAsk (s : Strategy) (b : Bool) : String :=
  match s with
  | .booleanXml => QueryResult.toSrx (.boolean b)
  | _           => QueryResult.toSrj (.boolean b)

/-- A CSV or TSV serialiser can REFUSE (a blank node label it cannot
    write, say). The refusal is carried through as a 500 rather than
    replaced by an empty body, which would report success for a
    document that was never written. -/
def bodyForRows (s : Strategy) (vars : List VarName) (rows : List Binding)
    : Except String String :=
  let r : QueryResult := .bindings vars rows
  match s with
  | .rowsXml => .ok (QueryResult.toSrx r)
  | .rowsCsv => QueryResult.toCsv r
  | .rowsTsv => QueryResult.toTsv r
  | _        => .ok (QueryResult.toSrj r)

/-- The whole response policy for a successful evaluation. -/
def runQuery (form : Form) (fmt : Fmt) (maxRows : Nat) (vars : List VarName)
    (askResult : Option Bool) (rowsResult : Option (List Binding)) : ResponseBody :=
  match form with
  | .ask =>
      let b := askResult.getD false
      let (strat, ct) := strategyForAsk fmt
      { status := successStatus, contentType := ct, body := bodyForAsk strat b }
  | .select | .constructOrDescribe =>
      let rows := rowsResult.getD []
      if rowCountOverflows maxRows rows then makeResultCapResponse maxRows
      else
        let (strat, ct) := match form with
          | .ask => strategyForAsk fmt
          | .select => strategyForSelect fmt
          | .constructOrDescribe => strategyForConstructDescribe fmt
        match bodyForRows strat vars rows with
        | .ok b    => { status := successStatus, contentType := ct, body := b }
        | .error e => makeEvalErrorResponse e ""

end L4Factoidal.HTTP
