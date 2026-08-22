/-
L4Factoidal.SPARQL.ResultsCsvTsv — the SPARQL Query Results CSV and TSV
formats: parser and serialiser for both.

Spec: SPARQL 1.1 Query Results CSV and TSV Formats, W3C Recommendation,
https://www.w3.org/TR/sparql11-results-csv-tsv/ .
  * §2 CSV: header = variable names (no `?`), RFC 4180 quoting; a cell
    is the term's "plain" lexical value — datatype/language-tag
    information is LOST, by design (§2's own wording: "this format
    does not... preserve... datatype"). This is the LOSSY half the
    harness has to compare leniently — see the bottom of this file.
  * §3 TSV: header = `?`-prefixed variable names, TAB-separated; a
    cell is the term written in (roughly) SPARQL/N-Triples syntax —
    `<iri>`, `_:label`, `"lex"@lang`/`"lex"^^<dt>` — so TSV, unlike
    CSV, keeps full typing.

Port of `formal/fstar/Parser.CSVResults.fst` (parsing) and the CSV/TSV
half of `formal/fstar/SPARQL.Protocol.fst` Part 11 (`csv_plain_term`/
`serialise_response_csv`, `tsv_term`/`serialise_response_tsv`,
serialising). Both F* modules have **zero** `assume val`s (confirmed
by grep, see `PORT_NOTES.md`).

## TSV term syntax reuse — the port brief's own suggestion

TSV cells ARE (approximately) N-Triples term syntax, so this port
reuses `Syntax.Lexing`'s readers (`readIriRef`, `readBlankNodeLabel`)
and `Syntax.NTriples`'s `readLiteral`/`mkIri`/`Term.toNTriples` for the
IRI/bnode/literal/triple-term cases, rather than hand-rolling a second
caret/at-sign scanner the way `Parser.CSVResults.fst`'s
`parse_tsv_quoted_literal` does (that F* function exists only because
the F* tree did not yet have a shared N-Triples term reader to reuse
when `Parser.CSVResults.fst` was written). Bare (unquoted) numeric
literals (`4`, `5.5`, `1.0e3`) are NOT N-Triples syntax, so their
digit-sniffing (`isIntegerStr`/`isDecimalStr`/`isDoubleStr` below) is
still a direct port of the F* source.
-/
import L4Factoidal.SPARQL.Results
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.Syntax (Mode ParseError readIriRef readBlankNodeLabel readLiteral mkIri Term.toNTriples)

/-! ## Line and field splitting — shared by CSV and TSV -/

/-- Split on LF, CRLF, or bare CR line boundaries — the same three
`SPARQL11.Algebra`/RDF-syntax line conventions this project already
treats as one boundary elsewhere. Port of `split_lines_acc`. -/
def splitLinesAcc : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | '\r' :: '\n' :: rest, acc => acc.reverse :: splitLinesAcc rest []
  | '\r' :: rest, acc => acc.reverse :: splitLinesAcc rest []
  | '\n' :: rest, acc => acc.reverse :: splitLinesAcc rest []
  | c :: rest, acc => splitLinesAcc rest (c :: acc)

/-- Port of `split_lines`. -/
def splitLines (s : String) : List String :=
  (splitLinesAcc s.toList []).map String.ofList

/-- Drop trailing empty lines (a trailing newline in the input produces
one). Port of `remove_trailing_empty`. -/
def dropTrailingEmptyRev : List String → List String
  | [] => []
  | "" :: rest => dropTrailingEmptyRev rest
  | ls => ls

def removeTrailingEmpty (lines : List String) : List String :=
  (dropTrailingEmptyRev lines.reverse).reverse

/-- Split a line on `,`, honouring RFC 4180 double-quoted fields (a
separator or newline inside `"..."` is literal; `""` inside a quoted
field is one escaped `"`). Port of `csv_split_fields_acc`. -/
def csvSplitFieldsAcc : List Char → Bool → List Char → List String
  | [], _, acc => [String.ofList acc.reverse]
  | '"' :: '"' :: rest, true, acc => csvSplitFieldsAcc rest true ('"' :: acc)
  | '"' :: rest, true, acc => csvSplitFieldsAcc rest false acc
  | c :: rest, true, acc => csvSplitFieldsAcc rest true (c :: acc)
  | ',' :: rest, false, acc => String.ofList acc.reverse :: csvSplitFieldsAcc rest false []
  | '"' :: rest, false, acc => csvSplitFieldsAcc rest true acc
  | c :: rest, false, acc => csvSplitFieldsAcc rest false (c :: acc)

/-- Port of `csv_split_fields` (specialised to `,`; CSV results always
use comma per §2). -/
def csvSplitFields (line : String) : List String :=
  csvSplitFieldsAcc line.toList false []

/-- TSV fields are never quoted at the field level (quotes are part of
the N-Triples-style TERM syntax, not field framing) — a plain TAB
split. Port of `tsv_split_fields_acc`. -/
def tsvSplitFieldsAcc : List Char → List Char → List String
  | [], acc => [String.ofList acc.reverse]
  | '\t' :: rest, acc => String.ofList acc.reverse :: tsvSplitFieldsAcc rest []
  | c :: rest, acc => tsvSplitFieldsAcc rest (c :: acc)

def tsvSplitFields (line : String) : List String :=
  tsvSplitFieldsAcc line.toList []

/-! ## Headers -/

/-- Port of `parse_csv_header`. -/
def parseCsvHeader (line : String) : List VarName := csvSplitFields line

/-- Strip a leading `?`. Port of `strip_question_mark`. -/
def stripQuestionMark (s : String) : String :=
  match s.toList with
  | '?' :: rest => String.ofList rest
  | _ => s

/-- Port of `parse_tsv_header`. -/
def parseTsvHeader (line : String) : List VarName :=
  (tsvSplitFields line).map stripQuestionMark

/-! ## CSV value parsing — §2, lossy by design -/

def isBlankNodeStr (s : String) : Bool :=
  match s.toList with
  | '_' :: ':' :: _ => true
  | _ => false

def bnodeLabel (s : String) : String :=
  String.ofList (s.toList.drop 2)

/-- CSV IRIs are bare (no `<>`); detected by `RDF.isIri`'s own
"contains a colon" gate — CSV cannot otherwise distinguish an IRI from
a plain literal that happens to contain a colon (the format is
inherently lossy here; §2 does not define a quoting convention for
literals that look IRI-shaped). Port of `looks_like_iri`. -/
def looksLikeIri (s : String) : Bool := isIri s

/-- Port of `parse_csv_value`. -/
def parseCsvValue (field : String) : Option Term :=
  if field.isEmpty then none
  else if isBlankNodeStr field then some (mkResultBnode (bnodeLabel field))
  else if looksLikeIri field then mkResultUri field
  else mkResultLiteral field xsdString.val none

/-- Port of `parse_csv_row`. -/
def parseCsvRow (line : String) : List (Option Term) :=
  (csvSplitFields line).map parseCsvValue

/-! ## TSV value parsing — §3, reusing `Syntax` N-Triples-style readers -/

def isAsciiDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'

def allDigits : List Char → Bool
  | [] => true
  | c :: rest => isAsciiDigit c && allDigits rest

/-- Port of `is_integer_str`. -/
def isIntegerStr (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
      if c == '-' || c == '+' then !rest.isEmpty && allDigits rest
      else isAsciiDigit c && allDigits rest

def hasDot : List Char → Bool
  | [] => false
  | c :: rest => c == '.' || hasDot rest

def allDigitOrDot : List Char → Bool
  | [] => true
  | c :: rest => (isAsciiDigit c || c == '.') && allDigitOrDot rest

/-- Port of `is_decimal_str`. -/
def isDecimalStr (s : String) : Bool :=
  let cs := s.toList
  if cs.isEmpty then false
  else
    let signStripped := match cs with
      | c :: rest => if c == '-' || c == '+' then rest else cs
      | [] => cs
    hasDot signStripped && allDigitOrDot signStripped

def hasExponent : List Char → Bool
  | [] => false
  | c :: rest => c == 'e' || c == 'E' || hasExponent rest

/-- Port of `is_double_str` (checked BEFORE `isDecimalStr` at the call
site, since a double's lexeme also has a dot — F*'s own comment). -/
def isDoubleStr (s : String) : Bool := hasExponent s.toList

/-- Build a well-formed typed literal for a bare numeric TSV field.
`dt` is always one of this port's fixed `xsd*` constants, so
`mkResultLiteral` cannot actually fail; the `Option`→`Except` fold
below keeps the function total without a proof obligation. -/
def mkTsvNumeric (field : String) (dt : WfIri) : Except ResultsError (Option Term) :=
  match mkResultLiteral field dt.val none with
  | some t => .ok (some t)
  | none => .error ⟨"TSV: internal error building numeric literal"⟩

/-- Parse one TSV field. Port of `parse_tsv_value`; the `<...>`, `"..."`
and `_:...` cases delegate to `Syntax.Lexing`/`Syntax.NTriples`'s
N-Triples-style readers (RDF 1.2 mode, so `--ltr`/`--rtl` directional
literals and triple terms are accepted — see the module header). -/
def parseTsvValue (field : String) : Except ResultsError (Option Term) :=
  if field.isEmpty then .ok none
  else
    match field.toList with
    | '<' :: _ =>
        match readIriRef 0 field.toList with
        | .error e => .error ⟨s!"TSV: {e}"⟩
        | .ok (iriStr, _, rest) =>
            if !rest.isEmpty then .error ⟨"TSV: trailing characters after IRIREF"⟩
            else match mkIri 0 iriStr with
              | .error e => .error ⟨s!"TSV: {e}"⟩
              | .ok wi => .ok (some (Term.iri wi))
    | '"' :: _ =>
        match readLiteral .rdf12 0 field.toList with
        | .error e => .error ⟨s!"TSV: {e}"⟩
        | .ok (wl, _, rest) =>
            if !rest.isEmpty then .error ⟨"TSV: trailing characters after literal"⟩
            else .ok (some (Term.literal wl))
    | '_' :: ':' :: _ =>
        match readBlankNodeLabel 0 field.toList with
        | .error e => .error ⟨s!"TSV: {e}"⟩
        | .ok (label, _, rest) =>
            if !rest.isEmpty then .error ⟨"TSV: trailing characters after blank node label"⟩
            else .ok (some (Term.bnode label))
    | '_' :: _ =>
        -- F* fallback: a field starting with '_' that is not "_:..."
        -- is treated as a plain xsd:string literal, not a syntax error.
        mkTsvNumeric field xsdString
    | _ =>
        if isIntegerStr field then mkTsvNumeric field xsdInteger
        else if isDoubleStr field then mkTsvNumeric field xsdDouble
        else if isDecimalStr field then mkTsvNumeric field xsdDecimal
        else mkTsvNumeric field xsdString

/-! ## Row assembly — shared, port of `pad_row`/`build_solution_mapping` -/

/-- Pad or truncate a row to exactly `n` fields (a short row pads with
`none` = unbound; a long row is truncated). Port of `pad_row`. -/
def padRow : List (Option Term) → Nat → List (Option Term)
  | _, 0 => []
  | [], n + 1 => none :: padRow [] n
  | v :: rest, n + 1 => v :: padRow rest n

/-- Port of `build_solution_mapping`: only `some` values become
bindings. -/
def buildSolutionMapping : List VarName → List (Option Term) → Binding
  | [], _ => []
  | _ :: _, [] => []
  | v :: vrest, some t :: orest => (v, t) :: buildSolutionMapping vrest orest
  | _ :: vrest, none :: orest => buildSolutionMapping vrest orest

/-! ## Top-level parsers

CSV/TSV define only SELECT-shaped results (§1: "results of SPARQL
SELECT queries"); both parsers below only ever return
`QueryResult.bindings`. -/

/-- Port of `parse_csv_results` + `results_to_solution_mappings` +
`parse_csv_to_solutions`, fused into one `QueryResult`-returning
function. -/
def parseCsv (input : String) : Except ResultsError QueryResult :=
  match removeTrailingEmpty (splitLines input) with
  | [] => .error ⟨"CSV: empty input (no header line)"⟩
  | headerLine :: dataLines =>
      let vars := parseCsvHeader headerLine
      if vars.isEmpty then .error ⟨"CSV: empty header"⟩
      else
        let nvars := vars.length
        let rows := dataLines.map (fun line => buildSolutionMapping vars (padRow (parseCsvRow line) nvars))
        .ok (.bindings vars rows)

/-- Port of `parse_tsv_results` + `results_to_solution_mappings` +
`parse_tsv_to_solutions`. Unlike CSV, a TSV FIELD can itself be
ill-formed (a bad IRIREF/literal/blank-node label), so per-row parsing
can fail — a genuine `Except`, not silently dropped like SRX's
unparseable bindings. -/
def parseTsv (input : String) : Except ResultsError QueryResult :=
  match removeTrailingEmpty (splitLines input) with
  | [] => .error ⟨"TSV: empty input (no header line)"⟩
  | headerLine :: dataLines =>
      let vars := parseTsvHeader headerLine
      if vars.isEmpty then .error ⟨"TSV: empty header"⟩
      else
        let nvars := vars.length
        let rowsE : Except ResultsError (List Binding) :=
          dataLines.foldr (fun line acc =>
            match acc with
            | .error e => .error e
            | .ok rowsAcc =>
                match (tsvSplitFields line).mapM parseTsvValue with
                | .error e => .error e
                | .ok raw => .ok (buildSolutionMapping vars (padRow raw nvars) :: rowsAcc))
            (.ok [])
        rowsE.map (fun rows => .bindings vars rows)

/-! ## Serialisers -/

/-- Does `s` need RFC 4180 quoting (contains `,`, CR, LF, or `"`)?
Port of `csv_needs_quoting_chars`. -/
def csvNeedsQuoting (s : String) : Bool :=
  s.toList.any fun c => c == ',' || c == '\n' || c == '\r' || c == '"'

/-- Double every embedded `"`. Port of `csv_double_quotes_chars`. -/
def csvDoubleQuotes (s : String) : String :=
  String.join (s.toList.map fun c => if c == '"' then "\"\"" else String.singleton c)

/-- Port of `csv_escape`. -/
def csvEscape (s : String) : String :=
  if csvNeedsQuoting s then "\"" ++ csvDoubleQuotes s ++ "\"" else s

/-- The "plain" (untyped) rendering of a term for a CSV cell — datatype
and language tag are DROPPED, by §2 design. RDF 1.2 triple terms
render in `<<( )>>` N-Triples-ish form, recursing through the object.
Port of `csv_plain_term`. -/
def csvPlainTerm : Term → String
  | .iri i => i.val
  | .bnode b => "_:" ++ b
  | .literal wl => wl.val.lexicalForm
  | .tripleTerm s p o =>
      let subj := match s with | .iri i => i.val | .bnode b => "_:" ++ b
      "<<( " ++ subj ++ " " ++ p.val ++ " " ++ csvPlainTerm o ++ " )>>"

/-- Port of `csv_cell` (unbound = empty). -/
def csvCell : Option Term → String
  | none => ""
  | some t => csvEscape (csvPlainTerm t)

/-- Term rendering for a TSV cell — SPARQL/N-Triples syntax, reusing
`Syntax.NTriples.Term.toNTriples .rdf12` (see the module header). Under
`.rdf12` that function never fails (RDF 1.2 mode accepts every term
shape this port can construct), so unwrapping with a placeholder
default on `.error` is dead code, not a silent swallow. -/
def tsvTerm (t : Term) : String :=
  match Term.toNTriples .rdf12 t with
  | .ok s => s
  | .error _ => ""

/-- Port of `tsv_cell`. -/
def tsvCell : Option Term → String
  | none => ""
  | some t => tsvTerm t

/-- `r.toCsv`/`r.toTsv` — CSV/TSV define no boolean (ASK) encoding at
all (§1 scopes both formats to SELECT results), so a `.boolean` result
is an `Except` failure here rather than an invented convention. Port
of `serialise_response_csv`/`serialise_response_tsv` for the
`.bindings` case. -/
def QueryResult.toCsv : QueryResult → Except String String
  | .bindings vars rows =>
      let header := String.intercalate "," (vars.map csvEscape)
      let rowLines := rows.map fun row =>
        String.intercalate "," (vars.map fun v => csvCell (row.lookup v))
      .ok (header ++ "\r\n" ++ String.join (rowLines.map (· ++ "\r\n")))
  | .boolean _ =>
      .error "SPARQL 1.1 CSV/TSV Results Format defines no boolean (ASK) encoding"

def QueryResult.toTsv : QueryResult → Except String String
  | .bindings vars rows =>
      let header := String.intercalate "\t" (vars.map fun v => "?" ++ v)
      let rowLines := rows.map fun row =>
        String.intercalate "\t" (vars.map fun v => tsvCell (row.lookup v))
      .ok (header ++ "\n" ++ String.join (rowLines.map (· ++ "\n")))
  | .boolean _ =>
      .error "SPARQL 1.1 CSV/TSV Results Format defines no boolean (ASK) encoding"

/-! ## The CSV-lenient comparison rule — what the W3C harness needs

CSV loses type information (§2), so an ACTUAL result read back from a
`.csv` fixture (always `xsd:string`-typed by `parseCsvValue`) has to be
compared against an EXPECTED, properly-typed term (e.g. `"4"^^
xsd:integer` from the query engine's own evaluation) leniently, or
every CSV-backed W3C test would spuriously fail on datatype mismatch.
Port of `bin/w3c-runner/w3c_runner.ml`'s `term_equal_csv_lenient`
(around line 730): when the term on the EXPECTED (query-engine) side is
a plain `xsd:string` literal, compare lexical forms only; otherwise
fall back to ordinary engine equality (`Term.eqb`), with blank nodes
matching any blank node exactly as `Term.eqb` already does not (engine
equality treats bnode labels as significant; the W3C harness's
notion of "matching" is coarser — see `w3c_runner.ml`'s own
`term_equal`, which this mirrors for the non-string case only for
blank nodes; literal comparison otherwise uses `Term.eqb`). -/
def Term.eqbCsvLenient (expected actual : Term) : Bool :=
  match expected, actual with
  | .iri i1, .iri i2 => i1 == i2
  | .bnode _, .bnode _ => true
  | .literal l1, .literal l2 =>
      if l1.val.datatype == xsdString && l1.val.langTag == none then
        l1.val.lexicalForm == l2.val.lexicalForm
      else
        Term.eqb expected actual
  | _, _ => false

end L4Factoidal.SPARQL
