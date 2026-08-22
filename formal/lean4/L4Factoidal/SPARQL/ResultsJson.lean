/-
L4Factoidal.SPARQL.ResultsJson — the SPARQL Query Results JSON (SRJ)
format: parser and serialiser.

Spec: SPARQL 1.1 Query Results JSON Format, W3C Recommendation,
https://www.w3.org/TR/sparql11-results-json/ . RDF 1.2 additions
(`"type":"triple"` bindings, the `"its:dir"` base-direction member)
follow the SPARQL 1.2 Query Results Formats Working Draft, mirroring
what `SPARQL.Protocol.fst`'s `json_term` and `Parser.JSONResults.fst`
already do — this is the shape the project's npm package and the hub
demos already consume (per the port brief).

Port of `formal/fstar/Parser.JSONResults.fst` (parsing) and the JSON
half of `formal/fstar/SPARQL.Protocol.fst` Part 9 (`json_term`/
`serialise_response_json`/`serialise_response_boolean_json`,
serialising). Both F* modules have **zero** `assume val`s (confirmed by
grep on this landing, see `PORT_NOTES.md`).

Built on `L4Factoidal.JSON` (`Value`/`Parser`/`Serialize`) — binding
VALUES are built as `Json` trees and rendered with
`JSON.toStringCompact`/`escapeString` (reusing that module's verified
RFC 8259 escaping rather than re-deriving it); the document-level
`{"head":...,"results":...}` / `{"head":{},"boolean":...}` wrapper is
hand-composed exactly as `serialise_response_json` composes it (see
`ResultsTheorems.lean`'s N-row shape theorem, which depends on this
wrapper being written this way rather than through a second generic
`Json.object` layer).

## Deviation from `Parser.JSONResults.fst`: one parser, `head` required

The F* source ships two separate functions, `parse_srj_results` and
`parse_srj_boolean`, and leaves the caller to pick one based on the
expected test type; neither requires a `"head"` member (a missing
`head` silently reads as `vars = []`). This port:
  1. unifies them into one `parseSrj : String → Except ResultsError
     QueryResult` (needed for a single `QueryResult` sum type) that
     dispatches on whether the top-level object has a `"boolean"`
     member;
  2. REQUIRES the `"head"` member (§2.1's grammar has it as
     non-optional in both the `results` and `boolean` cases) — a
     document missing it is a `ResultsError`, one of the port brief's
     required negative-test cases, rather than a silent empty `vars`.
-/
import L4Factoidal.SPARQL.Results
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.JSON (Json parseJson escapeString)

/-! ## Binding-value ↔ `Json` mapping — SRJ §3.3, port of `json_term` -/

/-- Render one term as an SRJ binding-value object
(`{"type":...,"value":...}`), building a `Json` tree so the actual
text is produced by the already-verified `JSON.Serialize` writer. Port
of `json_term`. -/
def jsonOfTerm : Term → Json
  | .iri i => .object [("type", .string "uri"), ("value", .string i.val)]
  | .bnode b => .object [("type", .string "bnode"), ("value", .string b)]
  | .literal wl =>
      let l := wl.val
      match l.langTag with
      | some tag =>
          let dirField : List (String × Json) := match l.direction with
            | some .ltr => [("its:dir", .string "ltr")]
            | some .rtl => [("its:dir", .string "rtl")]
            | none => []
          .object ([("type", .string "literal"), ("value", .string l.lexicalForm),
                     ("xml:lang", .string tag)] ++ dirField)
      | none =>
          if l.datatype == xsdString then
            .object [("type", .string "literal"), ("value", .string l.lexicalForm)]
          else
            .object [("type", .string "literal"), ("value", .string l.lexicalForm),
                      ("datatype", .string l.datatype.val)]
  | .tripleTerm s p o =>
      let subj := match s with
        | .iri i => Json.object [("type", .string "uri"), ("value", .string i.val)]
        | .bnode b => Json.object [("type", .string "bnode"), ("value", .string b)]
      let pred := Json.object [("type", .string "uri"), ("value", .string p.val)]
      .object [("type", .string "triple"),
               ("value", .object [("subject", subj), ("predicate", pred), ("object", jsonOfTerm o)])]

/-- Decode an SRJ binding-value object back into a `Term`. `fuel`
bounds RDF 1.2 triple-term nesting depth, matching
`Parser.JSONResults.fst`'s `parse_binding_value_fuel`. -/
def parseSrjBindingValueFuel : Nat → Json → Option Term
  | 0, _ => none
  | fuel' + 1, obj =>
      match obj.getString? "type" with
      | none => none
      | some typ =>
          let valStr := (obj.getString? "value").getD ""
          if typ == "uri" then mkResultUri valStr
          else if typ == "bnode" then some (mkResultBnode valStr)
          else if typ == "literal" || typ == "typed-literal" then
            let lang := obj.getString? "xml:lang"
            let dt := obj.getString? "datatype"
            let itsDir := obj.getString? "its:dir"
            match lang, itsDir with
            | some langVal, some dirStr =>
                match parseResultDirection dirStr with
                | some dirVal => mkResultDirLiteral valStr langVal dirVal
                | none => mkResultLiteral valStr rdfLangString.val (some langVal)
            | some langVal, none => mkResultLiteral valStr rdfLangString.val (some langVal)
            | none, _ =>
                match dt with
                | some dtVal => mkResultLiteral valStr dtVal none
                | none => mkResultLiteral valStr xsdString.val none
          else if typ == "triple" then
            match obj.field? "value" with
            | none => none
            | some tval =>
                match tval.field? "subject", tval.field? "predicate", tval.field? "object" with
                | some sj, some pj, some oj =>
                    mkResultTriple (parseSrjBindingValueFuel fuel' sj)
                      (parseSrjBindingValueFuel fuel' pj) (parseSrjBindingValueFuel fuel' oj)
                | _, _, _ => none
          else none

/-- Same fixed nesting bound as `Parser.JSONResults.fst`'s
`parse_binding_value`. -/
def parseBindingValueJson (obj : Json) : Option Term :=
  parseSrjBindingValueFuel 64 obj

/-- One binding ROW: `{"x":{...},"y":{...}}` → a `Binding`. Port of
`parse_binding_row`. -/
def parseBindingRowJson : Json → Binding
  | .object fields =>
      fields.filterMap (fun (varName, valObj) =>
        (parseBindingValueJson valObj).map (fun t => (varName, t)))
  | _ => []

/-! ## Top-level document

`rowJson`/`rowsJoined`/`varListJson` are written as the DIRECT
(non-accumulator) recursion `SPARQL.Protocol.RoundTrip.fst` calls
`json_rows_joined` — the spec form that file's `lemma_srj_n_rows`
bridges the F* tree's tail-recursive accumulator serialiser to (see
that F* module's Part on `json_rows_body_acc`). This Lean port has no
accumulator/reverse detour to bridge — see `ResultsTheorems.lean`. -/

/-- `"x","y","z"` from `[x, y, z]`. Port of `json_var_list`. -/
def varListJson (vars : List VarName) : String :=
  String.intercalate "," (vars.map fun v => "\"" ++ escapeString v ++ "\"")

/-- One row's bindings object: `{"x":...,"y":...}`, only VARIABLES
actually bound in this row appear (§3.3.2). Port of `json_row`. -/
def rowJson (row : Binding) : String :=
  "{" ++ String.intercalate ","
    (row.map fun (v, t) => "\"" ++ escapeString v ++ "\":" ++ (jsonOfTerm t).toString) ++ "}"

/-- Comma-joined row objects, no accumulator. Port of
`SPARQL.Protocol.RoundTrip.fst`'s `json_rows_joined` (the spec form
`serialise_response_json` computes via its own accumulator variant). -/
def rowsJoined : SolutionSeq → String
  | [] => ""
  | [r] => rowJson r
  | r :: rest => rowJson r ++ "," ++ rowsJoined rest

/-- `r.toSrj` — the complete SRJ document. Port of
`serialise_response_json`/`serialise_response_boolean_json`. -/
def QueryResult.toSrj : QueryResult → String
  | .bindings vars rows =>
      "{\"head\":{\"vars\":[" ++ varListJson vars ++ "]}," ++
      "\"results\":{\"bindings\":[" ++ rowsJoined rows ++ "]}}"
  | .boolean b =>
      "{\"head\":{},\"boolean\":" ++ (if b then "true" else "false") ++ "}"

/-- `head.vars`, or `[]` if absent/not a string array. Port of the
`json_get_string_array "vars" head` half of `parse_srj_results`. -/
def headVarsJson (root : Json) : List VarName :=
  match root.field? "head" with
  | some head => (head.getStringArray? "vars").getD []
  | none => []

/-- `results.bindings`, if present. Port of the corresponding half of
`parse_srj_results`. -/
def rowsFieldJson (root : Json) : Option (List Json) :=
  (root.field? "results").bind (fun r => r.getArray? "bindings")

/-- Parse a complete SRJ document. Port of `parse_srj_results` +
`parse_srj_boolean`, unified — see the module header for the two
deviations (`head` required; dispatch on `"boolean"` presence instead
of the caller choosing a parser). -/
def parseSrj (input : String) : Except ResultsError QueryResult :=
  match parseJson input with
  | .error e => .error ⟨s!"SRJ: {e}"⟩
  | .ok root =>
      match root with
      | .object _ =>
          match root.field? "head" with
          | none => .error ⟨"SRJ: missing required 'head' member"⟩
          | some _ =>
              match root.getBool? "boolean" with
              | some b => .ok (.boolean b)
              | none =>
                  let vars := headVarsJson root
                  match rowsFieldJson root with
                  | some bindings => .ok (.bindings vars (bindings.map parseBindingRowJson))
                  | none => .ok (.bindings vars [])
      | _ => .error ⟨"SRJ: top-level JSON value is not an object"⟩

end L4Factoidal.SPARQL
