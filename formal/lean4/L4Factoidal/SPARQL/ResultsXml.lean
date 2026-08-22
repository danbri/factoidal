/-
L4Factoidal.SPARQL.ResultsXml — the SPARQL Query Results XML (SRX)
format: parser and serialiser.

Spec: SPARQL 1.1 Query Results XML Format, W3C Recommendation,
https://www.w3.org/TR/rdf-sparql-XMLres/ . Every definition below cites
the section it implements. RDF 1.2 triple-term bindings
(`<triple><subject/><predicate/><object/></triple>`) follow the SPARQL
1.2 Query Results Formats Working Draft, mirroring what
`SPARQL.Protocol.fst`'s `xml_term`/`Parser.SRX.fst` already do.

Built on `L4Factoidal.XML` (`Document`/`Parser`/`Theorems`) — this
module walks the already-parsed XML infoset via `Node.elementTag`/
`Node.textContent`/`findAttr`; it does NOT re-implement XML parsing
(iron rule #7's spirit: no cobbling a second XML reader).

Port of `formal/fstar/Parser.SRX.fst` (parsing) and the XML half of
`formal/fstar/SPARQL.Protocol.fst` Part 10 (`xml_term`/
`serialise_response_xml`/`serialise_response_boolean_xml`,
serialising). Both F* modules have **zero** `assume val`s (confirmed
by grep on this landing, see `PORT_NOTES.md`).

## Deviation from `Parser.SRX.fst`: root element validated

`Parser.SRX.fst`'s `parse_srx_results`/`parse_srx_boolean` never check
that the document's root element is actually `<sparql>` — they just
descend into whatever `children` the root happens to have. This port
adds that check (§2's `<sparql>` root is a MUST of the format, and the
port brief's negative-test set names "wrong root element" as a case to
cover), returning `ResultsError` when it fails rather than silently
reading an unrelated document as an empty result set.
-/
import L4Factoidal.SPARQL.Results
import L4Factoidal.XML.Parser

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.XML (Node parseXML findAttr)

/-! ## Namespace-flexible tag matching — SRX §2

SRX documents declare `xmlns='http://www.w3.org/2005/sparql-results#'`
and may (rarely) use a namespace PREFIX (`<rs:result>`) instead of the
bare tag; `Parser.XML` (this port's XML layer, like the F* source's)
is deliberately not namespace-aware at the tree level (see
`XML.Namespaces`'s module header), so SRX has to do its own
prefix-insensitive tag comparison. Port of `Parser.SRX.fst`'s
`find_colon_in_list`/`strip_ns_prefix`/`tag_matches`. -/

/-- The characters of `tag` after its first `:`, or `none` if `tag` has
no colon. Port of `find_colon_in_list`, phrased as a search rather than
an accumulator. -/
private def afterFirstColon : List Char → Option (List Char)
  | [] => none
  | c :: rest => if c == ':' then some rest else afterFirstColon rest

/-- Strip a namespace prefix: `"rs:result" ↦ "result"`, `"result" ↦
"result"`. Port of `strip_ns_prefix`. -/
def stripNsPrefix (tag : String) : String :=
  match afterFirstColon tag.toList with
  | some rest => String.ofList rest
  | none => tag

/-- `actual` names `expected`, either directly or with a namespace
prefix stripped. Port of `tag_matches`. -/
def tagMatches (expected actual : String) : Bool :=
  actual == expected || stripNsPrefix actual == expected

/-! ## Tree navigation — port of `find_child`/`find_children`/`get_attr`/
`collect_text` -/

/-- The first child element tagged `tag` (namespace-flexible). Port of
`find_child`. -/
def findChildTag (tag : String) (children : List Node) : Option Node :=
  children.find? (fun n => match n.elementTag with
    | some t => tagMatches tag t
    | none => false)

/-- Every child element tagged `tag` (namespace-flexible). Port of
`find_children`. -/
def findChildrenTag (tag : String) (children : List Node) : List Node :=
  children.filter (fun n => match n.elementTag with
    | some t => tagMatches tag t
    | none => false)

/-! ## Binding-value parsers — SRX §3.1/§3.2/§3.4

Each `<binding>` element wraps exactly one `<uri>`/`<bnode>`/
`<literal>` (RDF 1.1) or `<triple>` (RDF 1.2 draft) child. -/

/-- `<uri>...</uri>`. Port of `parse_uri_value`. -/
def parseUriValue (node : Node) : Option Term :=
  mkResultUri node.textContent

/-- `<bnode>...</bnode>`. Port of `parse_bnode_value`. -/
def parseBnodeValue (node : Node) : Option Term :=
  some (mkResultBnode node.textContent)

/-- `<literal ...>...</literal>`: plain (→ `xsd:string`), `xml:lang=`
(→ `rdf:langString`), or `datatype=` (→ that datatype). Port of
`parse_literal_value`. -/
def parseLiteralValue (node : Node) : Option Term :=
  match node with
  | .element _ attrs children =>
      let lex := Node.textContentList children
      let lang := findAttr "xml:lang" attrs
      let dt := findAttr "datatype" attrs
      match lang, dt with
      | some langVal, _ => mkResultLiteral lex rdfLangString.val (some langVal)
      | none, some dtVal => mkResultLiteral lex dtVal none
      | none, none => mkResultLiteral lex xsdString.val none
  | _ => none

/-- The value child of a `<binding>` (or of a `<subject>`/`<predicate>`/
`<object>` triple-term wrapper): the first ELEMENT child, dispatched on
its (namespace-stripped) local tag. `fuel` bounds triple-term nesting
depth exactly as `Parser.SRX.fst`'s `parse_binding_value_fuel` does.
Port of `parse_binding_value_fuel`. -/
def parseSrxBindingValueFuel : Nat → Node → Option Term
  | 0, _ => none
  | fuel' + 1, node =>
      match node with
      | .element _ _ children =>
          match children.filter (fun c => c.elementTag.isSome) with
          | [] => none
          | valueNode :: _ =>
              match valueNode with
              | .element t _ vchildren =>
                  let localTag := stripNsPrefix t
                  if localTag == "uri" then parseUriValue valueNode
                  else if localTag == "bnode" then parseBnodeValue valueNode
                  else if localTag == "literal" then parseLiteralValue valueNode
                  else if localTag == "triple" then
                    match findChildTag "subject" vchildren,
                          findChildTag "predicate" vchildren,
                          findChildTag "object" vchildren with
                    | some sj, some pj, some oj =>
                        mkResultTriple (parseSrxBindingValueFuel fuel' sj)
                          (parseSrxBindingValueFuel fuel' pj)
                          (parseSrxBindingValueFuel fuel' oj)
                    | _, _, _ => none
                  else none
              | _ => none
      | _ => none

/-- `Parser.SRX.fst` bounds triple-term nesting at a fixed depth of 64
(`parse_binding_value`); this port keeps the same constant so the two
trees accept/reject the same inputs. -/
def parseSrxBindingValue (node : Node) : Option Term :=
  parseSrxBindingValueFuel 64 node

/-! ## Row and header parsers — SRX §2.1/§2.2 -/

/-- `<binding name="x">...</binding>` → `(x, value)`, or `none` if the
`name` attribute is absent or the value fails to decode. Port of
`parse_binding`. -/
def parseBindingNode (node : Node) : Option (VarName × Term) :=
  match node with
  | .element _ attrs _ =>
      match findAttr "name" attrs with
      | some varName => (parseSrxBindingValue node).map (fun t => (varName, t))
      | none => none
  | _ => none

/-- `<result>` → a `Binding`. Bindings that fail to decode are dropped
rather than aborting the row — SRX has no way to mark "this one
binding is unparseable" separately from "this variable is unbound", so
`Parser.SRX.fst`'s `parse_result_row` treats both the same way; this
port matches it. -/
def parseResultRow (node : Node) : Binding :=
  match node with
  | .element _ _ children => (findChildrenTag "binding" children).filterMap parseBindingNode
  | _ => []

/-- `<head><variable name="x"/>...</head>` → the declared variable
list. Port of `parse_head_vars`. -/
def parseHeadVars (headNode : Node) : List VarName :=
  match headNode with
  | .element _ _ children =>
      (findChildrenTag "variable" children).filterMap (fun v =>
        match v with
        | .element _ attrs _ => findAttr "name" attrs
        | _ => none)
  | _ => []

/-! ## Top-level parser -/

/-- Parse a complete SRX document. Port of `parse_srx_results` +
`parse_srx_boolean`, unified into one `QueryResult`-returning function
(the F* source keeps them separate because F* has no shared sum type
for "bindings or boolean" at that layer) and made stricter in one way:
the root element must actually be (namespace-flexibly) `<sparql>` — see
the module header. -/
def parseSrx (input : String) : Except ResultsError QueryResult :=
  match parseXML input with
  | .error e => .error ⟨s!"SRX: {e}"⟩
  | .ok doc =>
      match doc.root with
      | .element rootTag _ children =>
          if !tagMatches "sparql" rootTag then
            .error ⟨s!"SRX: root element <{rootTag}> is not <sparql>"⟩
          else
            let vars := match findChildTag "head" children with
              | some headNode => parseHeadVars headNode
              | none => []
            match findChildTag "boolean" children with
            | some boolNode =>
                let txt := boolNode.textContent
                if txt == "true" then .ok (.boolean true)
                else if txt == "false" then .ok (.boolean false)
                else .error ⟨s!"SRX: <boolean> content '{txt}' is neither 'true' nor 'false'"⟩
            | none =>
                match findChildTag "results" children with
                | some (.element _ _ rchildren) =>
                    .ok (.bindings vars ((findChildrenTag "result" rchildren).map parseResultRow))
                | some _ => .error ⟨"SRX: <results> has no element form"⟩
                | none => .ok (.bindings vars [])
      | _ => .error ⟨"SRX: document root is not an element"⟩

/-! ## Serialiser — SRX §2, port of `SPARQL.Protocol.fst` Part 10

`xml_escape` there escapes `&`, `<`, `>`, `"`, `'`, and CR for BOTH
attribute values (`name="..."`) and element text content with ONE
function; this port keeps that (rather than reaching for
`XML.Theorems`'s `escapeText`/`escapeAttrValue`, which draw the
text-vs-attribute line differently, e.g. `escapeText` does not escape
`"`) so the SRX wire bytes match the F* tree's exactly. -/

/-- Port of `xml_escape`. -/
def srxEscape (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '&' then "&amp;"
    else if c == '<' then "&lt;"
    else if c == '>' then "&gt;"
    else if c == '"' then "&quot;"
    else if c == '\'' then "&apos;"
    else if c == '\r' then "&#13;"
    else String.singleton c)

/-- Port of `xml_head_vars_body`. -/
def xmlHeadVarsBody (vars : List VarName) : String :=
  String.join (vars.map fun v => "<variable name=\"" ++ srxEscape v ++ "\"/>")

/-- Render one term as an SRX `<uri>`/`<bnode>`/`<literal>`/`<triple>`
binding value. Port of `xml_term`. -/
def termToXml : Term → String
  | .iri i => "<uri>" ++ srxEscape i.val ++ "</uri>"
  | .bnode b => "<bnode>" ++ srxEscape b ++ "</bnode>"
  | .literal wl =>
      let l := wl.val
      match l.langTag with
      | some tag =>
          let dirAttr := match l.direction with
            | some .ltr => " its:dir=\"ltr\""
            | some .rtl => " its:dir=\"rtl\""
            | none => ""
          "<literal xml:lang=\"" ++ srxEscape tag ++ "\"" ++ dirAttr ++ ">" ++
            srxEscape l.lexicalForm ++ "</literal>"
      | none =>
          if l.datatype == xsdString then
            "<literal>" ++ srxEscape l.lexicalForm ++ "</literal>"
          else
            "<literal datatype=\"" ++ srxEscape l.datatype.val ++ "\">" ++
              srxEscape l.lexicalForm ++ "</literal>"
  | .tripleTerm s p o =>
      let subj := match s with
        | .iri i => "<uri>" ++ srxEscape i.val ++ "</uri>"
        | .bnode b => "<bnode>" ++ srxEscape b ++ "</bnode>"
      "<triple><subject>" ++ subj ++ "</subject>" ++
        "<predicate><uri>" ++ srxEscape p.val ++ "</uri></predicate>" ++
        "<object>" ++ termToXml o ++ "</object></triple>"

/-- Port of `xml_binding`. -/
def bindingToXml (name : VarName) (t : Term) : String :=
  "<binding name=\"" ++ srxEscape name ++ "\">" ++ termToXml t ++ "</binding>"

/-- Port of `xml_row`. -/
def rowToXml (row : Binding) : String :=
  "<result>" ++ String.join (row.map fun (v, t) => bindingToXml v t) ++ "</result>"

/-- `r.toSrx` — the complete SRX document. Port of
`serialise_response_xml`/`serialise_response_boolean_xml`. -/
def QueryResult.toSrx : QueryResult → String
  | .bindings vars rows =>
      "<?xml version=\"1.0\"?>\n" ++
      "<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">" ++
      "<head>" ++ xmlHeadVarsBody vars ++ "</head>" ++
      "<results>" ++ String.join (rows.map rowToXml) ++ "</results>" ++
      "</sparql>"
  | .boolean b =>
      "<?xml version=\"1.0\"?>\n" ++
      "<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">" ++
      "<head></head>" ++
      "<boolean>" ++ (if b then "true" else "false") ++ "</boolean>" ++
      "</sparql>"

end L4Factoidal.SPARQL
