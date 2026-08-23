/-
L4Factoidal.RML.Sources — the RML logical-source iterator model.

Port of `formal/fstar/RML.Sources.fst` (455 lines): the source-row
model, the CSV logical source (an RFC 4180 tokenizer plus the
header-row binding model), and the iterate / reference entry points for
both JSON and CSV.

## The JSONPath half is already here

`L4Factoidal/RML/JsonPath.lean` ports the F\* module's JSONPath subset —
the same subset, surveyed from the same corpus. This module uses it
rather than restating it, so `jsonIterate` and `jsonReferenceValues`
are thin wrappers and the path grammar exists once.

## The CSV tokenizer lives here, not in a shared parser

The F\* module's own reasoning, carried across: the SPARQL 1.1 CSV/TSV
RESULTS format is a different dialect — bare IRIs and typed-literal
lexical conventions belong to that format, not to arbitrary RFC 4180
tabular data — so reusing it would import conventions RML does not
have.

Quoting rules: a leading `"` opens a quoted field only on an empty
field buffer; `""` inside quotes is a literal `"`; commas and newlines
inside quotes are data; a bare `\r` is dropped so `\r\n` and a lone
`\n` tokenize the same.

## Two data-error rules that must NOT be best-effort

Both come from the vendored suites and both make the whole source
empty rather than partially usable:

* an invalid iterator path (`"$.students[*]]"`, RMLTC0002g) means the
  logical source is malformed, so there are NO iterations — not a
  best-effort parse of the well-formed prefix;
* a data row whose field count differs from the header's
  (RMLSTC0010a/b) invalidates the whole source — no rows at all —
  rather than truncating or padding that row.

`#guard`s pin both, because "returns fewer rows" and "returns no rows"
are easy to confuse and only one is correct.

## The dialect layer is separate on purpose

`csvParseRows` is the normative RML and csv2rdf path and takes no
dialect. `csvParseRowsDialect` adds the CSVW tabular-data-model §8
`trim` and `skipColumns`, and a runner calls it only when the table
carries an explicit dialect. Keeping them apart is what makes the
no-dialect path byte-for-byte unchanged.
-/
import L4Factoidal.RML.JsonPath

namespace L4Factoidal.RML

open L4Factoidal.JSON

/-! ## Logical-source rows -/

inductive SourceRow where
  | json (v : Json)
  | csv  (bindings : List (String × String))

def SourceRow.jsonVal : SourceRow → Json
  | .json v => v
  | .csv _ => .null

def SourceRow.csvBindings : SourceRow → List (String × String)
  | .csv b => b
  | .json _ => []

/-! ## The JSON logical source -/

/-- An invalid iterator path means the source is malformed: no
    iterations at all. -/
def jsonIterate (root : Json) (iterator : String) : List SourceRow :=
  match parseJsonPath iterator with
  | none => []
  | some _ => (evalPath iterator root).map SourceRow.json

/-- `rml:reference` and a template's reference segment, against one
    row. -/
def jsonReferenceValues (row : SourceRow) (path : String) : List Json :=
  evalPath path row.jsonVal

/-! ## The CSV logical source -/

def flushCsvField (buf : String) (rowAcc : List String) : List String :=
  buf :: rowAcc

def flushCsvRow (buf : String) (rowAcc : List String)
    (rowsAcc : List (List String)) : List (List String) :=
  (flushCsvField buf rowAcc).reverse :: rowsAcc

/-- A single-pass RFC 4180 scan over the character list. The F\*
    original indexes a string by position with an explicit fuel; the
    list here decreases structurally, which is the same recursion with
    the totality witness supplied by the shape. -/
def csvScanAcc (delim : Char) (cs : List Char) (inQuotes : Bool) (buf : String)
    (rowAcc : List String) (rowsAcc : List (List String)) : List (List String) :=
  match cs, inQuotes with
  | [], _ =>
      (if buf != "" || !rowAcc.isEmpty then flushCsvRow buf rowAcc rowsAcc
       else rowsAcc).reverse
  -- inside quotes: `""` is one literal quote, a lone `"` closes
  | '"' :: '"' :: rest, true =>
      csvScanAcc delim rest true (buf ++ "\"") rowAcc rowsAcc
  | '"' :: rest, true => csvScanAcc delim rest false buf rowAcc rowsAcc
  | c :: rest, true => csvScanAcc delim rest true (buf.push c) rowAcc rowsAcc
  | c :: rest, false =>
      -- a `"` opens a quoted field ONLY at the start of one
      if c == '"' && buf == "" then csvScanAcc delim rest true buf rowAcc rowsAcc
      else if c == delim then
        csvScanAcc delim rest false "" (flushCsvField buf rowAcc) rowsAcc
      else if c == '\n' then
        csvScanAcc delim rest false "" [] (flushCsvRow buf rowAcc rowsAcc)
      else if c == '\r' then csvScanAcc delim rest false buf rowAcc rowsAcc
      else csvScanAcc delim rest false (buf.push c) rowAcc rowsAcc

def csvParseRowsDelim (delim : Char) (s : String) : List (List String) :=
  csvScanAcc delim s.toList false "" [] []

/-- The RML default and the CSVW default: comma-separated. -/
def csvParseRows (s : String) : List (List String) := csvParseRowsDelim ',' s

/-! ### The CSVW dialect layer -/

inductive CsvTrim where
  | none
  | start
  | «end»
  | both
  deriving DecidableEq, Repr

def isWsChar (c : Char) : Bool := c == ' ' || c == '\t'

def dropLeadingWs : List Char → List Char
  | c :: rest => if isWsChar c then dropLeadingWs rest else c :: rest
  | [] => []

def trimCell (mode : CsvTrim) (s : String) : String :=
  let cs := s.toList
  String.ofList (match mode with
    | .none => cs
    | .start => dropLeadingWs cs
    | .«end» => (dropLeadingWs cs.reverse).reverse
    | .both => dropLeadingWs (dropLeadingWs cs.reverse).reverse)

/-- CSVW `skipColumns`: the leading columns are not tabular data, and
    dropping them from the header AND every data row is what keeps the
    columns aligned. -/
def dropFirstN (n : Nat) (xs : List String) : List String := xs.drop n

def csvParseRowsDialect (delim : Char) (mode : CsvTrim) (skipCols : Nat)
    (s : String) : List (List String) :=
  (csvParseRowsDelim delim s).map (fun r =>
    (dropFirstN skipCols r).map (trimCell mode))

/-! ### Rows and references -/

def zipStrings : List String → List String → List (String × String)
  | x :: xs, y :: ys => (x, y) :: zipStrings xs ys
  | _, _ => []

def allRowsMatchWidth (n : Nat) (rows : List (List String)) : Bool :=
  rows.all (fun r => r.length == n)

/-- Header row to column names, every later row to a binding list with
    the `rml:null` values filtered out — a filtered column then yields
    no value, which is the same "no RDF term" outcome as a missing JSON
    field.

    A width mismatch invalidates the WHOLE source. -/
def csvIterate (csvText : String) (nullValues : List String) : List SourceRow :=
  match csvParseRows csvText with
  | [] => []
  | header :: dataRows =>
      if !allRowsMatchWidth header.length dataRows then []
      else dataRows.map (fun row =>
        SourceRow.csv ((zipStrings header row).filter
          (fun p => !nullValues.contains p.2)))

/-- A CSV reference is a bare column name, not a JSONPath. -/
def csvReferenceValues (row : SourceRow) (column : String) : List String :=
  match row with
  | .csv bindings =>
      match bindings.find? (fun p => p.1 == column) with
      | some (_, v) => [v]
      | none => []
  | .json _ => []

/-! ## Build-time checks

### The RFC 4180 rules, one guard each -/

#guard csvParseRows "a,b\n1,2" == [["a", "b"], ["1", "2"]]
#guard csvParseRows "a,b\r\n1,2\r\n" == [["a", "b"], ["1", "2"]]
#guard csvParseRows "a,b\n1,2\n" == [["a", "b"], ["1", "2"]]

/-! A quoted field carries commas and newlines as data. -/

#guard csvParseRows "a,b\n\"x,y\",2" == [["a", "b"], ["x,y", "2"]]
#guard csvParseRows "a\n\"x\ny\"" == [["a"], ["x\ny"]]

/-! `\"\"` inside quotes is one literal quote. -/

#guard csvParseRows "a\n\"he said \"\"hi\"\"\"" == [["a"], ["he said \"hi\""]]

/-! A quote that is NOT at the start of a field is ordinary data — the
    `buf == ""` guard. -/

#guard csvParseRows "a\nx\"y" == [["a"], ["x\"y"]]

/-! An empty field, and a trailing empty field, both survive. -/

#guard csvParseRows "a,b,c\n1,,3" == [["a", "b", "c"], ["1", "", "3"]]
#guard csvParseRows "a,b\n1," == [["a", "b"], ["1", ""]]

/-! A different delimiter. -/

#guard csvParseRowsDelim '\t' "a\tb\n1\t2" == [["a", "b"], ["1", "2"]]

/-! ### The width rule: a short row empties the SOURCE, not the row

RMLSTC0010a/b ship a header of three columns and a data row of two.
Returning that row with two bindings, or padding it, would both be
wrong. -/

#guard (csvIterate "id,name,age\n1,Ross,30" []).length == 1
#guard (csvIterate "id,name,age\n1,Ross,30\n2,Phoebe" []).length == 0
#guard (csvIterate "id,name,age\n6,Phoebe Buffay 37" []).length == 0

/-! ### `rml:null` filters a column out of the binding, which makes a
    reference to it yield nothing -/

private def rowsWithNull : List SourceRow :=
  csvIterate "id,name\n1,NULL\n2,Ross" ["NULL"]

#guard rowsWithNull.length == 2
#guard csvReferenceValues (rowsWithNull.headD (.json .null)) "id" == ["1"]
#guard csvReferenceValues (rowsWithNull.headD (.json .null)) "name" == []
#guard csvReferenceValues (rowsWithNull.getD 1 (.json .null)) "name" == ["Ross"]

/-! A reference to a column that is not in the header yields nothing,
    and a CSV reference against a JSON row yields nothing. -/

#guard csvReferenceValues (rowsWithNull.headD (.json .null)) "absent" == []
#guard csvReferenceValues (.json (.string "x")) "id" == []

/-! ### The dialect layer, and that the plain path is untouched by it -/

#guard csvParseRowsDialect ',' .none 0 "a,b\n1,2" == csvParseRows "a,b\n1,2"
#guard csvParseRowsDialect ',' .both 0 " a , b \n 1 , 2 " == [["a", "b"], ["1", "2"]]
#guard csvParseRowsDialect ',' .start 0 " a, b" == [["a", "b"]]
#guard csvParseRowsDialect ',' .«end» 0 "a ,b " == [["a", "b"]]
#guard csvParseRowsDialect ',' .none 1 "skip,a,b\n0,1,2" == [["a", "b"], ["1", "2"]]

/-! ### The JSON source

An invalid iterator path gives NO rows — the source is malformed, and a
best-effort parse of its well-formed prefix would be a different and
wrong answer. -/

private def jsonDoc : Json :=
  .object [("students", .array [.object [("ID", .string "1")],
                                .object [("ID", .string "2")]])]

#guard (jsonIterate jsonDoc "$.students[*]").length == 2
#guard (jsonIterate jsonDoc "$.students[*]]").length == 0
#guard (jsonIterate jsonDoc "$.absent[*]").length == 0

#guard jsonReferenceValues ((jsonIterate jsonDoc "$.students[*]").headD
         (.json .null)) "$.ID" == [Json.string "1"]

/-! A JSON reference against a CSV row yields nothing, and the row
    accessors do not leak one representation into the other. -/

#guard jsonReferenceValues (.csv [("a", "b")]) "$.a" == []
#guard (SourceRow.csv [("a", "b")]).csvBindings == [("a", "b")]
#guard (SourceRow.json (.string "x")).csvBindings == []

end L4Factoidal.RML
