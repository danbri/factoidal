/-
L4Factoidal.CSVW.Conversion — csv2rdf cell and row conversion, ported
from `formal/fstar/CSVW.Conversion.fst`.

Spec: "Generating RDF from Tabular Data on the Web"
(https://www.w3.org/TR/csv2rdf/) plus the tabular data model §6.4
cell-value parsing.

This slice covers what turns a CELL into terms: the row-scoped
variable lookup, null handling, the `separator` list split, the
whitespace rule, and the aboutUrl/propertyUrl/valueUrl template
resolution. Row and table assembly build on it.
-/
import L4Factoidal.CSVW.Metadata
import L4Factoidal.CSVW.UriTemplate
import L4Factoidal.CSVW.Formats

namespace L4Factoidal.CSVW

/-- The CSVW vocabulary namespace. -/
def csvwNs : String := "http://www.w3.org/ns/csvw#"

/-- ASCII whitespace, tabular-data-model §6.4: space, tab, LF, CR. -/
def isCsvwWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

def csvwTrim (s : String) : String :=
  String.ofList
    ((s.toList.dropWhile isCsvwWs).reverse.dropWhile isCsvwWs).reverse

/-- Which datatype bases PRESERVE surrounding whitespace. Only the
    string family and the structured literals; every other base
    (numeric, date/time, duration, boolean, …) has leading and
    trailing whitespace stripped before lexical parsing
    (tabular-data-model §6.4.2).

    This distinction is load-bearing, not cosmetic: it is why a
    `string` cell keeps its spaces while a `date` cell parses THROUGH
    them, so `" 10/18/2010 "` becomes `2010-10-18` while
    `"  padded  "` stays padded. -/
def dtPreservesWs (baseName : String) : Bool :=
  baseName == "string" || baseName == "normalizedString" ||
  baseName == "anyAtomicType" || baseName == "xml" ||
  baseName == "html" || baseName == "json"

/-- The row-scoped variable lookup a template expands against.
    `_row` is the 1-based row number within the table; `_sourceRow`
    is the line number in the source file. Column names bind to their
    cell values. -/
def rowLookup (bindings : List (String × String)) (rowNum sourceRow : Nat)
    : String → Option String := fun v =>
  if v == "_row" then some (toString rowNum)
  else if v == "_sourceRow" then some (toString sourceRow)
  else (bindings.find? (fun (k, _) => k == v)).map (·.2)

/-- The COLUMN-scoped variables a template sees, on top of the
    row-scoped ones: `_name` is the column's name, `_column` its
    1-based position among the described columns and `_sourceColumn`
    its position in the file.

    Without `_name` a `propertyUrl` of `http://schema.org/{_name}`
    expands to `http://schema.org/` for EVERY column, so a whole table
    collapses onto one predicate — the right number of triples, all
    of them wrong (measured on the csv2rdf corpus, 2026-08-22). -/
def cellLookup (row : String → Option String) (name : String)
    (colNum sourceCol : Nat) : String → Option String := fun v =>
  if v == "_name" then some name
  else if v == "_column" then some (toString colNum)
  else if v == "_sourceColumn" then some (toString sourceCol)
  else row v

/-- Worker for `splitSeparated`. -/
partial def goSplit (sep : String) (cur : List Char) (acc : List String)
    : List Char → List String
  | [] => acc ++ [csvwTrim (String.ofList cur.reverse)]
  | cs =>
      if sep != "" && (String.ofList cs).startsWith sep then
        goSplit sep [] (acc ++ [csvwTrim (String.ofList cur.reverse)])
          (cs.drop sep.length)
      else match cs with
        | c :: rest => goSplit sep (c :: cur) acc rest
        | []        => acc

/-- Split a cell on its column's `separator`, trimming each element
    (tabular-data-model §6.4): a separator makes the cell a LIST
    value, one object term per element. An EMPTY cell with a
    separator yields no elements at all, not one empty element. -/
def splitSeparated (sep : String) (cell : String) : List String :=
  if cell == "" then []
  else
    -- `partial` because the separator step drops `sep.length`
    -- characters, which the structural checker cannot see is a
    -- decrease; the empty-separator case is guarded above so it
    -- always makes progress.
    goSplit sep [] [] cell.toList

/-- Is this cell the column's null value? The `null` inherited
    property names a string that means "no value"; absent, only the
    empty string is null. -/
def isNullCell (nullProp : Option String) (cell : String) : Bool :=
  match nullProp with
  | some n => cell == n
  | none   => cell == ""

/-- Apply the `default` inherited property: an EMPTY cell takes the
    default before datatype parsing. -/
def applyDefault (dflt : Option String) (cell : String) : String :=
  if cell == "" then dflt.getD cell else cell

/-- Prepare a cell's lexical form for its datatype: apply the
    whitespace rule from §6.4.2, then the datatype's `format`.

    Applying the format here is not cosmetic. Without it a `date`
    column with `"format": "M/d/yyyy"` emits its SOURCE text under an
    `xsd:date` datatype — `"10/18/2010"^^xsd:date` where the value is
    `"2010-10-18"^^xsd:date`. The triple count, the subject and the
    predicate are all right and the value is wrong, which is the shape
    of error a count-based check cannot see (measured across the
    csv2rdf corpus, 2026-08-22).

    An INVALID value keeps its written form. §6.4.2 makes a failed
    parse a validation error, not a conversion failure: the cell is
    still reported, and it is `Validate` that says it is bad. Dropping
    it here would lose data on the strength of a format this module
    might have read wrongly. -/
def prepareLexical (dt : Option Datatype) (cell : String) : String × Bool :=
  let base := (dt.bind Datatype.baseName).getD "string"
  let trimmed := if dtPreservesWs base then cell else csvwTrim cell
  match dt with
  | none => (trimmed, true)
  | some d =>
      match formatConvert base (Datatype.formatOf d) (Datatype.patternOf d)
              (Datatype.groupCharOf d) (Datatype.decimalCharOf d) trimmed with
      | .valid lex => (lex, true)
      | .invalid   => (trimmed, false)
      | .noFormat  => (trimmed, true)

/-- What one cell contributes, before RDF terms are built: the
    resolved property IRI reference, and the object values (several
    when a `separator` applies, none when the cell is null). -/
structure CellResult where
  propertyRef : Option String
  aboutRef    : Option String
  valueRefs   : List String      -- when valueUrl applies
  /-- Otherwise the lexical forms, each paired with whether the
      column's datatype APPLIES to it.

      The flag is not decoration. csv2rdf gives a cell that fails its
      datatype's format NO typed value: the corpus expects
      `"123,,456.789"` plain where the column says `decimal` with a
      `groupChar`, and emitting `^^xsd:decimal` on unparsed text
      asserts something false about the value (measured 2026-08-22,
      the whole test160–177 family). -/
  literals    : List (String × Bool)
deriving Repr, Inhabited

/-- Convert one cell under its effective inherited properties.

    Template resolution note carried from the F* module: aboutUrl /
    propertyUrl / valueUrl resolve against the CURRENT TABLE's own
    already-resolved URL, not the outer document base — csv2rdf's URI
    Template Properties. The caller passes that resolved table URL in
    as `lookup`'s context; this function does not re-resolve against a
    document base a second time. -/
def convertCell (inh : Inherited) (colName : String)
    (lookup : String → Option String) (cell : String) : CellResult :=
  let cell := applyDefault inh.default cell
  let propertyRef := inh.propertyUrl.map (UriTemplate.expand lookup)
  let aboutRef := inh.aboutUrl.map (UriTemplate.expand lookup)
  if isNullCell inh.null cell then
    ⟨propertyRef, aboutRef, [], []⟩
  else
    match inh.valueUrl with
    | some tmpl => ⟨propertyRef, aboutRef, [UriTemplate.expand lookup tmpl], []⟩
    | none =>
        let parts := match inh.separator with
          | some sep => splitSeparated sep cell
          | none     => [cell]
        let lits := parts.filter (fun p => !(isNullCell inh.null p))
        ⟨propertyRef, aboutRef, [], lits.map (prepareLexical inh.datatype)⟩

/-- The lexical forms alone, for callers that do not care whether the
    datatype applied (csv2json emits strings either way). -/
def CellResult.lexicals (r : CellResult) : List String := r.literals.map (·.1)

/-- The default property IRI for a column with no `propertyUrl`: the
    table URL with the column name as a fragment, per csv2rdf. -/
def defaultPropertyRef (tableUrl colName : String) : String :=
  tableUrl ++ "#" ++ UriTemplate.encodeFragment colName

end L4Factoidal.CSVW
