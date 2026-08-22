/-
L4Factoidal.CSVW.Json — csv2json output, ported from
`formal/fstar/CSVW.Json.fst`.

Spec: "Generating JSON from Tabular Data on the Web"
(https://www.w3.org/TR/csv2json/), minimal mode §5 and standard
mode §6.

csv2json is a separate conformance suite from csv2rdf, so it is a
separate output rather than a rendering of the triples: the shapes
differ (`describes` arrays, `rownum`/`url` members, `rdfs:comment`)
and deriving one from the other would lose the distinctions the tests
check.
-/
import L4Factoidal.CSVW.Conversion
import L4Factoidal.JSON.Value

namespace L4Factoidal.CSVW

open L4Factoidal.JSON

/-- One cell's JSON value: an array when a `separator` made it a
    list, a single value otherwise, and ABSENT (no member at all)
    when the cell is null. -/
def cellJson (inh : Inherited) (r : CellResult) : Option Json :=
  let vals := (r.valueRefs.map Json.string) ++ (r.literals.map Json.string)
  match vals with
  | []  => none
  | [v] => if inh.separator.isSome then some (.array [v]) else some v
  | vs  => some (.array vs)

/-- The member name for a column in csv2json output: the column name,
    since csv2json keys by name rather than by property IRI. -/
def cellMemberName (colName : String) : String := colName

/-- Minimal mode, one row: an object of column-name → value members,
    with null cells OMITTED rather than emitted as JSON null. -/
def rowJsonMinimal (cells : List (String × Inherited × CellResult)) : Json :=
  .object (cells.filterMap (fun (nm, inh, r) =>
    (cellJson inh r).map (fun v => (cellMemberName nm, v))))

/-- Standard mode, one row: `url`, `rownum`, optional `titles`, and a
    `describes` array holding the row's object(s). -/
def rowJsonStandard (tableUrl : String) (rowNum sourceRow : Nat)
    (titles : List String) (cells : List (String × Inherited × CellResult)) : Json :=
  let core := rowJsonMinimal cells
  let titlePairs :=
    match titles with
    | [] => []
    | ts => [("titles", Json.array (ts.map Json.string))]
  .object (
    [ ("url", .string (tableUrl ++ "#row=" ++ toString sourceRow)),
      ("rownum", .number (toString rowNum)) ]
    ++ titlePairs
    ++ [ ("describes", .array [core]) ])

/-- The table-level `rdfs:comment` member. Present ONLY when the
    table produced at least one comment: csv2json says verbatim "If
    M.rdfs:comment is an empty array, remove the rdfs:comment
    property from M", so an empty array is wrong output, not a
    harmless one. -/
def commentPairs (comments : List String) : List (String × Json) :=
  match comments with
  | [] => []
  | cs => [("rdfs:comment", .array (cs.map Json.string))]

/-- Minimal mode, whole document: a flat array of row objects across
    all non-suppressed tables. -/
def documentJsonMinimal (tables : List (Bool × List Json)) : Json :=
  .array (tables.flatMap (fun (suppressed, rows) => if suppressed then [] else rows))

/-- Standard mode, whole document: `{ tables: [ { url, row: [...],
    rdfs:comment? } ] }`. -/
def documentJsonStandard
    (tables : List (String × List Json × List String)) : Json :=
  .object [("tables", .array (tables.map (fun (url, rows, comments) =>
    .object ([("url", .string url), ("row", .array rows)] ++ commentPairs comments))))]

end L4Factoidal.CSVW
