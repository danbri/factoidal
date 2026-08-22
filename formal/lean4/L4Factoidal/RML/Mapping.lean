/-
L4Factoidal.RML.Mapping — the RML mapping model and term generation,
ported from `formal/fstar/RML.Mapping.fst` and `RML.Eval.fst`.

Spec: RML-Core (https://w3id.org/rml/core/spec) — logical sources,
term maps, subject/predicate/object maps and referencing object maps.

A term map produces terms from a data record three ways: a CONSTANT,
a REFERENCE to a field, or a TEMPLATE with `{field}` placeholders.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.RML

open L4Factoidal.RDF

/-- The term type a map produces.

    `iri` and `uri` are NOT synonyms, and the F* module records the
    correction: `rml:IRI` applies IRI-safe (RFC 3987) encoding, where
    most non-ASCII stays unencoded, while `rml:URI` applies URI-safe
    (RFC 3986, ASCII-only) percent-encoding. The two are observably
    different — `"Zoë Krüger"` under `rml:URI` becomes
    `"Zo%C3%AB%20Kr%C3%BCger"`, under `rml:IRI` it does not. -/
inductive TermType where
  | iri | uri | unsafeIri | blankNode | literal
deriving Repr, DecidableEq, Inhabited

inductive RefFormulation where
  | jsonPath | xPath | csv | other (s : String)
deriving Repr, DecidableEq, Inhabited

/-- How a term map produces its value. -/
inductive TermMapForm where
  | constant  (t : Term)
  | reference (field : String)
  | template  (raw : String)
  | unknown
deriving Repr

structure TermMap where
  form     : TermMapForm
  termType : Option TermType := none
  datatype : Option String := none
  language : Option String := none
deriving Repr

/-! ## Templates -/

inductive TemplateSegment where
  | literal   (s : String)
  | reference (field : String)
deriving Repr, DecidableEq

/-- Parse `a{field}b`. A backslash escapes a brace, which RML needs
    and RFC 6570 does not — the CSVW template port deliberately has no
    escaping, and these two must not be merged for that reason. -/
def parseTemplate (raw : String) : List TemplateSegment :=
  let rec go (cur : List Char) (acc : List TemplateSegment) (inBrace esc : Bool)
      : List Char → List TemplateSegment
    | [] =>
        if cur.isEmpty then acc
        else acc ++ [if inBrace then .reference (String.ofList cur.reverse)
                     else .literal (String.ofList cur.reverse)]
    | c :: rest =>
        if esc then go (c :: cur) acc inBrace false rest
        else if c == '\\' then go cur acc inBrace true rest
        else if !inBrace && c == '{' then
          let acc := if cur.isEmpty then acc
                     else acc ++ [.literal (String.ofList cur.reverse)]
          go [] acc true false rest
        else if inBrace && c == '}' then
          go [] (acc ++ [.reference (String.ofList cur.reverse)]) false false rest
        else go (c :: cur) acc inBrace false rest
  go [] [] false false raw.toList

private def isUnreservedAscii (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') ||
  c == '-' || c == '.' || c == '_' || c == '~'

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)

private def pctEncode (c : Char) : String :=
  String.ofList ((String.mk [c]).toUTF8.toList.flatMap (fun b =>
    ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]))

/-- URI-safe encoding (RFC 3986): ASCII-only, so every non-ASCII
    character is percent-encoded. -/
def encodeUriSafe (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if isUnreservedAscii c then String.mk [c] else pctEncode c)) ""

/-- IRI-safe encoding (RFC 3987): the `iunreserved` set keeps most
    non-ASCII characters as themselves. -/
def encodeIriSafe (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if isUnreservedAscii c || c.toNat > 0x7F then String.mk [c] else pctEncode c)) ""

/-- Expand a template against a record. An ABSENT field makes the
    WHOLE template produce nothing — RML says a term map with an
    unresolved reference generates no term, which is not the same as
    generating an empty string. -/
def expandTemplate (segs : List TemplateSegment) (tt : TermType)
    (lookup : String → Option String) : Option String :=
  segs.foldl (fun acc seg =>
    match acc, seg with
    | none, _ => none
    | some s, .literal l => some (s ++ l)
    | some s, .reference f =>
        match lookup f with
        | none   => none
        | some v => some (s ++ (match tt with
            | .uri        => encodeUriSafe v
            | .unsafeIri  => v
            | _           => encodeIriSafe v))) (some "")

/-! ## Term generation -/

private def mkIri? (s : String) : Option Term :=
  if h : isIri s then some (.iri ⟨s, h⟩) else none

/-- Build a literal, honouring datatype then language. A language tag
    wins, since RDF 1.1 types every tagged literal `rdf:langString`. -/
private def mkLiteral (tm : TermMap) (lex : String) : Term :=
  match tm.language with
  | some tag => .literal (Literal.langString lex tag)
  | none =>
      match tm.datatype.bind (fun d => if h : isIri d then some (⟨d, h⟩ : WfIri) else none) with
      | some dt =>
          if h : (dt != rdfLangString && dt != rdfDirLangString) = true then
            .literal ⟨{ lexicalForm := lex, datatype := dt, langTag := none,
                        direction := none }, by simpa [literalWf] using h⟩
          else .literal (Literal.string lex)
      | none => .literal (Literal.string lex)

/-- The default term type when a map does not state one: a template
    or constant IRI position defaults to `iri`, a reference to
    `literal`. -/
def defaultTermType : TermMapForm → TermType
  | .reference _ => .literal
  | _            => .iri

/-- Generate the term a map produces from one record. `none` means
    NO TERM — an unresolved reference, or a value that is not a valid
    IRI where one is required. -/
def generateTerm (tm : TermMap) (lookup : String → Option String) : Option Term :=
  let tt := tm.termType.getD (defaultTermType tm.form)
  match tm.form with
  | .constant t => some t
  | .unknown    => none
  | .reference f =>
      match lookup f with
      | none   => none
      | some v =>
          match tt with
          | .literal   => some (mkLiteral tm v)
          | .blankNode => some (.bnode v)
          | .uri       => mkIri? (encodeUriSafe v)
          | .unsafeIri => mkIri? v
          | .iri       => mkIri? v
  | .template raw =>
      match expandTemplate (parseTemplate raw) tt lookup with
      | none   => none
      | some v =>
          match tt with
          | .literal   => some (mkLiteral tm v)
          | .blankNode => some (.bnode v)
          | _          => mkIri? v

end L4Factoidal.RML
