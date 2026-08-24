/-
Wasm.Abi — the JSON string-in / string-out application binary interface
that the WebAssembly build exposes to JavaScript.

Shape mirrors the F* tree's npm entry point (`bin/npm-entry/entry_jsoo.ml`):
every entry point takes JSON strings and returns a JSON string, so the C
boundary only ever carries UTF-8 byte strings and no structured values
cross it.

Wire formats (both directions) reuse the SPARQL 1.1 Query Results JSON
term encoding (W3C Rec. 21 March 2013, §3.2.2), so the Lean engine speaks
the same term vocabulary as the F*-backed engine already on the hub:

  {"type":"uri",     "value":"http://example.org/alice"}
  {"type":"bnode",   "value":"b0"}
  {"type":"literal", "value":"Alice"}
  {"type":"literal", "value":"30", "datatype":"http://...#integer"}
  {"type":"literal", "value":"chat", "xml:lang":"fr"}
  {"type":"triple",  "value":{"subject":…,"predicate":…,"object":…}}

plus, in a Basic Graph Pattern only, the query-variable form

  {"type":"var", "value":"s"}

`l4_bgp_query(dataJson, bgpJson)` takes a JSON array of triple objects
`{"subject":…,"predicate":…,"object":…}` and a JSON array of triple
*pattern* objects of the same shape, evaluates the BGP with
`L4Factoidal.SPARQL.evalBgp` (SPARQL 1.1 §18.3), and returns a SPARQL
Query Results JSON document.

PHASE-1 SHIM — READ THIS BEFORE EXTENDING.
The JSON reader/writer below is a deliberately small, self-contained
implementation living inside the ABI module. It exists ONLY because the
real `L4Factoidal.JSON` module and the N-Triples/N-Quads parsers are in
flight on separate branches (`lean4/json`, `lean4/syntax-ntriples-nquads`)
and are not on this branch. When those land, delete everything in the
`L4Wasm.Json` namespace and re-point `decode*`/`encode*` at them; the
exported C symbols and the wire format do not change.

Scope limits of the shim, stated plainly:
  * numbers are integers only (the RDF wire format never needs a JSON
    number — numeric RDF literals travel as lexical form + datatype);
  * no SPARQL query STRING is parsed on the Lean side yet — the data and
    the BGP are handed over as tables, not as Turtle and a query string.

Totality: every function here is total (`Nat` fuel where the recursion is
not structural), per the project's no-`sorry`/no-`partial` policy.
-/
-- Targeted imports, not the L4Factoidal umbrella: the wasm module
-- initializes every module its root imports, so the umbrella pays
-- init cost (and init RISK) for all 374 modules when the ABI needs a
-- fraction of them. This list is the v1 surface's import closure —
-- extend it op by op, never back to the umbrella.
import L4Factoidal.RDF.Graph
import L4Factoidal.SPARQL.Query
import L4Factoidal.Syntax.NQuads

namespace L4Wasm

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ## Version string reported by the `l4_version` export -/

/-- Version of the Lean-side ABI, not of the Lean toolchain. Bump when
the wire format changes in a way a caller can observe. -/
def abiVersion : String := "l4factoidal-wasm 0.1.0 (phase 1: BGP only)"

/-! ## A minimal JSON value, reader and writer — PHASE-1 SHIM -/

namespace Json

/-- A JSON value. Numbers are restricted to integers (see module note). -/
inductive Value where
  | null
  | bool (b : Bool)
  | int  (n : Int)
  | str  (s : String)
  | arr  (xs : List Value)
  | obj  (kvs : List (String × Value))
  deriving Inhabited, Repr

/-! ### Writer -/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'a'.toNat)

private def hex4 (n : Nat) : String :=
  String.ofList [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16),
             hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- Escape a string for a JSON string literal (RFC 8259 §7). -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else if c == '\r' then acc ++ "\\r"
    else if c == '\t' then acc ++ "\\t"
    else if c.toNat < 0x20 then acc ++ "\\u" ++ hex4 c.toNat
    else acc.push c

mutual

/-- Serialise a JSON value. -/
def render : Value → String
  | .null      => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .int n     => toString n
  | .str s     => "\"" ++ escape s ++ "\""
  | .arr xs    => "[" ++ renderArr xs ++ "]"
  | .obj kvs   => "{" ++ renderObj kvs ++ "}"

private def renderArr : List Value → String
  | []      => ""
  | [x]     => render x
  | x :: xs => render x ++ "," ++ renderArr xs

private def renderObj : List (String × Value) → String
  | []           => ""
  | [(k, v)]     => "\"" ++ escape k ++ "\":" ++ render v
  | (k, v) :: xs => "\"" ++ escape k ++ "\":" ++ render v ++ "," ++ renderObj xs

end

/-! ### Reader

Recursion is on an explicit `Nat` fuel rather than on the character list,
so every function is structurally recursive and total with no
well-founded-recursion obligations. Each fuel step consumes at least one
input character, so `2 * input.length + 16` is always enough. -/

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '\r'

private def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | []      => []

private def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Read the body of a string literal (the opening quote is already
consumed); `acc` collects characters in reverse. -/
private def pStr : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _ + 1, acc, '"' :: rest => some (String.ofList acc.reverse, rest)
  | fuel + 1, acc, '\\' :: e :: rest =>
      match e with
      | '"'  => pStr fuel ('"' :: acc) rest
      | '\\' => pStr fuel ('\\' :: acc) rest
      | '/'  => pStr fuel ('/' :: acc) rest
      | 'b'  => pStr fuel (Char.ofNat 8 :: acc) rest
      | 'f'  => pStr fuel (Char.ofNat 12 :: acc) rest
      | 'n'  => pStr fuel ('\n' :: acc) rest
      | 'r'  => pStr fuel ('\r' :: acc) rest
      | 't'  => pStr fuel ('\t' :: acc) rest
      | 'u'  =>
          match rest with
          | h1 :: h2 :: h3 :: h4 :: rest' =>
              match hexVal h1, hexVal h2, hexVal h3, hexVal h4 with
              | some a, some b, some c, some d =>
                  pStr fuel (Char.ofNat (((a * 16 + b) * 16 + c) * 16 + d) :: acc) rest'
              | _, _, _, _ => none
          | _ => none
      | _ => none
  | fuel + 1, acc, c :: rest => pStr fuel (c :: acc) rest
  | _ + 1, _, [] => none

/-- Read a run of decimal digits, most significant first. -/
private def pDigits : Nat → Nat → Bool → List Char → Option (Nat × List Char)
  | 0, _, _, _ => none
  | fuel + 1, acc, seen, c :: rest =>
      if c.isDigit then pDigits fuel (acc * 10 + (c.toNat - '0'.toNat)) true rest
      else if seen then some (acc, c :: rest) else none
  | _ + 1, acc, seen, [] => if seen then some (acc, []) else none

mutual

/-- Read one JSON value. -/
private def pValue : Nat → List Char → Option (Value × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
      match skipWs cs with
      | 't' :: 'r' :: 'u' :: 'e' :: rest             => some (.bool true, rest)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest      => some (.bool false, rest)
      | 'n' :: 'u' :: 'l' :: 'l' :: rest             => some (.null, rest)
      | '"' :: rest => match pStr fuel [] rest with
          | some (s, rest') => some (.str s, rest')
          | none            => none
      | '-' :: rest => match pDigits fuel 0 false rest with
          | some (n, rest') => some (.int (-(Int.ofNat n)), rest')
          | none            => none
      | '[' :: rest => pArr fuel [] rest
      | '{' :: rest => pObj fuel [] rest
      | cs' => match pDigits fuel 0 false cs' with
          | some (n, rest') => some (.int (Int.ofNat n), rest')
          | none            => none

/-- Read the remainder of an array (the `[` is already consumed). -/
private def pArr : Nat → List Value → List Char → Option (Value × List Char)
  | 0, _, _ => none
  | fuel + 1, acc, cs =>
      match skipWs cs with
      | ']' :: rest => some (.arr acc.reverse, rest)
      | ',' :: rest => pArr fuel acc rest
      | cs' => match pValue fuel cs' with
          | some (v, rest) => pArr fuel (v :: acc) rest
          | none           => none

/-- Read the remainder of an object (the `{` is already consumed). -/
private def pObj : Nat → List (String × Value) → List Char → Option (Value × List Char)
  | 0, _, _ => none
  | fuel + 1, acc, cs =>
      match skipWs cs with
      | '}' :: rest => some (.obj acc.reverse, rest)
      | ',' :: rest => pObj fuel acc rest
      | '"' :: rest =>
          match pStr fuel [] rest with
          | none => none
          | some (k, rest') =>
              match skipWs rest' with
              | ':' :: rest'' =>
                  match pValue fuel rest'' with
                  | some (v, rest3) => pObj fuel ((k, v) :: acc) rest3
                  | none            => none
              | _ => none
      | _ => none

end

/-- Parse a complete JSON document. Trailing whitespace is allowed;
trailing non-whitespace is an error. -/
def parse (s : String) : Except String Value :=
  let cs := s.toList
  match pValue (2 * cs.length + 16) cs with
  | none => .error "invalid JSON"
  | some (v, rest) =>
      match skipWs rest with
      | [] => .ok v
      | _  => .error "trailing content after JSON value"

end Json

/-! ## Decoding RDF terms, triples and triple patterns from JSON -/

open Json (Value)

private def field? (o : List (String × Value)) (k : String) : Option Value :=
  (o.find? (fun kv => kv.1 == k)).map Prod.snd

private def strField? (o : List (String × Value)) (k : String) : Option String :=
  match field? o k with
  | some (.str s) => some s
  | _             => none

/-- Build a well-formed IRI, checking `isIri` at run time (the Lean
counterpart of the F* refinement `s:iri{is_iri s}`). -/
def mkIri (s : String) : Except String WfIri :=
  if h : isIri s then .ok ⟨s, h⟩ else .error s!"not a well-formed IRI: '{s}'"

/-- Build a well-formed literal from the SPARQL-Results-JSON fields.
A language tag forces the datatype (`rdf:langString`, or
`rdf:dirLangString` when a base direction is present), per RDF 1.1/1.2
Concepts §3.3 — a `datatype` key supplied alongside `xml:lang` is
ignored rather than allowed to produce an ill-formed literal. -/
def mkLiteral (lex : String) (dt lang dir : Option String) :
    Except String WfLiteral := do
  let direction ← match dir with
    | none       => pure none
    | some "ltr" => pure (some TextDirection.ltr)
    | some "rtl" => pure (some TextDirection.rtl)
    | some d     => throw s!"unknown base direction '{d}' (expected ltr or rtl)"
  let dtIri ← match lang, direction with
    | some _, none   => pure rdfLangString
    | some _, some _ => pure rdfDirLangString
    | none,   _      => match dt with
        | some d => mkIri d
        | none   => pure xsdString
  let l : Literal :=
    { lexicalForm := lex, datatype := dtIri, langTag := lang, direction := direction }
  if h : literalWf l then .ok ⟨l, h⟩
  else .error s!"ill-formed literal '{lex}'"

private def litOf (o : List (String × Value)) (v : String) : Except String WfLiteral :=
  mkLiteral v (strField? o "datatype") (strField? o "xml:lang") (strField? o "its:dir")

/-- The `"value"` string of a term object. -/
private def reqValue (o : List (String × Value)) : Except String String :=
  match strField? o "value" with
  | some v => .ok v
  | none   => .error "term object has no string \"value\""

private def reqKey (o : List (String × Value)) (k : String) : Except String Value :=
  match field? o k with
  | some v => .ok v
  | none   => .error s!"missing key \"{k}\""

private def reqType (o : List (String × Value)) : Except String String :=
  match strField? o "type" with
  | some v => .ok v
  | none   => .error "term object has no \"type\""

mutual

/-- Decode one RDF term. `fuel` bounds triple-term nesting. -/
def decodeTerm : Nat → Value → Except String Term
  | 0, _ => .error "triple-term nesting too deep"
  | fuel + 1, .obj o => do
      let ty ← reqType o
      match ty with
      | "uri" | "iri" => return .iri (← mkIri (← reqValue o))
      | "bnode"       => return .bnode (← reqValue o)
      | "literal"     => return .literal (← litOf o (← reqValue o))
      | "triple"      =>
          match field? o "value" with
          | some (.obj t) => do
              let s ← decodeSubject fuel (← reqKey t "subject")
              let p ← mkIri (← termIriString fuel (← reqKey t "predicate"))
              let ob ← decodeTerm fuel (← reqKey t "object")
              return .tripleTerm s p ob
          | _ => throw "triple term needs an object \"value\""
      | other => throw s!"unknown term type '{other}'"
  | _ + 1, _ => .error "expected a term object"

/-- Decode a term in subject position (IRI or blank node only). -/
def decodeSubject : Nat → Value → Except String Subject
  | 0, _ => .error "triple-term nesting too deep"
  | fuel + 1, j => do
      match ← decodeTerm fuel j with
      | .iri i   => return .iri i
      | .bnode b => return .bnode b
      | _        => throw "a literal or triple term cannot be a subject"

/-- Decode a term that must be an IRI, returning its string. -/
private def termIriString : Nat → Value → Except String String
  | 0, _ => .error "triple-term nesting too deep"
  | fuel + 1, j => do
      match ← decodeTerm fuel j with
      | .iri i => return i.val
      | _      => throw "a predicate must be an IRI"

end

/-- Decode one triple `{"subject":…,"predicate":…,"object":…}`. -/
def decodeTriple (j : Value) : Except String Triple := do
  match j with
  | .obj o =>
      let s ← decodeSubject 8 (← reqKey o "subject")
      let p ← mkIri (← termIriString 8 (← reqKey o "predicate"))
      let ob ← decodeTerm 8 (← reqKey o "object")
      return { s := s, p := p, o := ob }
  | _ => throw "expected a triple object"

/-- Decode the data graph: a JSON array of triple objects. -/
def decodeGraph (j : Value) : Except String Graph := do
  match j with
  | .arr xs => xs.mapM decodeTriple
  | _       => throw "data must be a JSON array of triples"

/-! ### Pattern terms — the same encoding plus `{"type":"var"}` -/

mutual

/-- Decode a term in a triple pattern; `{"type":"var"}` binds a query
variable (SPARQL 1.1 §18.1.6). -/
def decodePatternTerm : Nat → Value → Except String PatternTerm
  | 0, _ => .error "triple-term-pattern nesting too deep"
  | fuel + 1, .obj o => do
      let ty ← reqType o
      match ty with
      | "var"         => return .var (← reqValue o)
      | "uri" | "iri" => return .iri (← mkIri (← reqValue o))
      | "bnode"       => return .bnode (← reqValue o)
      | "literal"     => return .literal (← litOf o (← reqValue o))
      | "triple"      =>
          match field? o "value" with
          | some (.obj t) => do
              let s ← decodePatternTerm fuel (← reqKey t "subject")
              let p ← decodePatternTerm fuel (← reqKey t "predicate")
              let ob ← decodePatternTerm fuel (← reqKey t "object")
              return .tripleTerm s p ob
          | _ => throw "triple-term pattern needs an object \"value\""
      | other => throw s!"unknown pattern term type '{other}'"
  | _ + 1, _ => .error "expected a pattern-term object"

/-- Decode a triple pattern's subject position. -/
def decodePatternSubject : Nat → Value → Except String PatternSubject
  | 0, _ => .error "triple-term-pattern nesting too deep"
  | fuel + 1, j => do
      match ← decodePatternTerm fuel j with
      | .var v            => return .var v
      | .iri i            => return .iri i
      | .bnode b          => return .bnode b
      | .tripleTerm s p o => return .tripleTerm s p o
      | .literal _        => throw "a literal cannot be a subject"

end

/-- Decode one triple pattern. -/
def decodePattern (j : Value) : Except String TriplePattern := do
  match j with
  | .obj o =>
      let s ← decodePatternSubject 8 (← reqKey o "subject")
      let p ← decodePatternTerm 8 (← reqKey o "predicate")
      let ob ← decodePatternTerm 8 (← reqKey o "object")
      return { s := s, p := p, o := ob }
  | _ => throw "expected a triple-pattern object"

/-- Decode a Basic Graph Pattern: a JSON array of triple patterns. -/
def decodeBgp (j : Value) : Except String Bgp := do
  match j with
  | .arr xs => xs.mapM decodePattern
  | _       => throw "the BGP must be a JSON array of triple patterns"

/-! ## Encoding results -/

/-- Encode a subject back to the results-JSON term shape. -/
def encodeSubject : Subject → Value
  | .iri i   => .obj [("type", .str "uri"), ("value", .str i.val)]
  | .bnode b => .obj [("type", .str "bnode"), ("value", .str b)]

/-- Encode an RDF term in the SPARQL Query Results JSON shape (§3.2.2).
`xsd:string` is emitted without a `datatype` key, matching the encoding
the F*-backed engine produces for plain literals. -/
def encodeTerm : Term → Value
  | .iri i   => .obj [("type", .str "uri"), ("value", .str i.val)]
  | .bnode b => .obj [("type", .str "bnode"), ("value", .str b)]
  | .literal l =>
      let base := [("type", Value.str "literal"), ("value", .str l.val.lexicalForm)]
      let withLang := match l.val.langTag with
        | some t => base ++ [("xml:lang", Value.str t)]
        | none   => base
      let withDir := match l.val.direction with
        | some .ltr => withLang ++ [("its:dir", Value.str "ltr")]
        | some .rtl => withLang ++ [("its:dir", Value.str "rtl")]
        | none      => withLang
      if l.val.langTag.isSome || l.val.datatype == xsdString then .obj withDir
      else .obj (withDir ++ [("datatype", Value.str l.val.datatype.val)])
  | .tripleTerm s p o =>
      .obj [("type", .str "triple"),
            ("value", .obj [("subject", encodeSubject s),
                            ("predicate", .obj [("type", .str "uri"), ("value", .str p.val)]),
                            ("object", encodeTerm o)])]

/-! ### Result variables, in order of first appearance in the BGP -/

private def insertNew (v : VarName) (acc : List VarName) : List VarName :=
  if acc.contains v then acc else acc ++ [v]

private def ptVars : PatternTerm → List VarName → List VarName
  | .var v, acc            => insertNew v acc
  | .tripleTerm s p o, acc => ptVars o (ptVars p (ptVars s acc))
  | _, acc                 => acc

private def psVars : PatternSubject → List VarName → List VarName
  | .var v, acc            => insertNew v acc
  | .tripleTerm s p o, acc => ptVars o (ptVars p (ptVars s acc))
  | _, acc                 => acc

/-- The query variables of a BGP, in order of first appearance — the
`head.vars` array of the results document. -/
def bgpVars (b : Bgp) : List VarName :=
  b.foldl (fun acc tp => ptVars tp.o (ptVars tp.p (psVars tp.s acc))) []

private def encodeRow (vars : List VarName) (mu : Binding) : Value :=
  .obj (vars.filterMap fun v => (mu.lookup v).map fun t => (v, encodeTerm t))

/-- Encode a solution sequence as a SPARQL 1.1 Query Results JSON
document (W3C Rec. 21 March 2013, §3). -/
def encodeResults (vars : List VarName) (omega : SolutionSeq) : Value :=
  .obj [("head", .obj [("vars", .arr (vars.map Value.str))]),
        ("results", .obj [("bindings", .arr (omega.map (encodeRow vars)))])]

/-! ## The entry points, as pure `String → String` functions -/

private def errorDoc (msg : String) : String :=
  Json.render (.obj [("error", .str msg)])

/-- `l4_bgp_query` — evaluate a Basic Graph Pattern over a graph, both
given as JSON, and return SPARQL Query Results JSON. On any decoding
error the result is `{"error":"…"}`, so the C boundary never has to
carry an exception. -/
def bgpQuery (dataJson bgpJson : String) : String :=
  match Json.parse dataJson with
  | .error e => errorDoc s!"data: {e}"
  | .ok dataV =>
    match Json.parse bgpJson with
    | .error e => errorDoc s!"bgp: {e}"
    | .ok bgpV =>
      match decodeGraph dataV with
      | .error e => errorDoc s!"data: {e}"
      | .ok g =>
        match decodeBgp bgpV with
        | .error e => errorDoc s!"bgp: {e}"
        | .ok b    => Json.render (encodeResults (bgpVars b) (evalBgp b g))

/-- `l4_version` — identify the ABI to the caller. -/
def version : String := abiVersion

end L4Wasm
