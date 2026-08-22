/-
L4Factoidal.Syntax.NTriples — the N-Triples parser and serialiser.

Port of `formal/fstar/Parser.NTriples.fst`'s triple-level grammar
(`parse_subject` / `parse_object` / `parse_triple` / `parse_ntriples_strict`
/ `parse_ntriples_strict_12`) and of the N-Triples half of
`formal/fstar/RDF.NQuads.Serialize.fst` (`nq_term_to_string` /
`nq_subject_to_string` / `nq_line_for_triple_default_graph`), built on the
character-level readers in `Syntax.Lexing`.

Grammar productions ported (RDF 1.1 N-Triples, https://www.w3.org/TR/n-triples/):
  [1] ntriplesDoc  [2] triple  [3] subject  [4] predicate  [5] object
  [6] literal
plus the RDF 1.2 object-position extension (W3C Working Draft, epic #305):
  triple term `<<( subject predicate object )>>`.

This port ships only the F* source's STRICT entry points
(`parse_ntriples_strict` / `_strict_12`): the WHOLE document either parses
or the whole call reports one `ParseError`. The F* source's LENIENT
`parse_ntriples`/`parse_ntriples_acc` (skip a malformed line, keep going)
and its streaming/count/validate-only variants
(`fold_ntriples`, `count_ntriples`, `validate_*`) are CLI/performance
pragmatics over the same grammar, not additional semantics, and are
deliberately not ported — matching the spec/pragmatics split already
established for the rest of `L4Factoidal` (see `PORT_NOTES.md`).

Also not ported: the RDF 1.2 c14n suite's `extra_whitespace-*` relaxation
(inline whitespace between a closing quote and a following `@lang`/
`^^datatype`) — see the note in `Syntax.Lexing`'s module header.
-/

import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## RDF 1.1 / RDF 1.2 processing mode

Port of the F* source's `rdf_syntax_mode` (`Mode_11` / `Mode_12`), threaded
as an explicit parameter — never a global — through every syntax parser
and serialiser exactly as the F* source's module banner requires. -/

/-- Which grammar to parse/serialise against.
* `.rdf11` — RDF 1.1: rejects the 1.2 lexical forms (`<<( )>>` triple
  terms, `@lang--dir` directional literals) exactly as the 1.1 grammar
  does. This is the default everywhere (the F* source's `Mode_11`).
* `.rdf12` — RDF 1.2: additionally accepts object-position triple terms
  and directional language strings; still rejects the retired RDF-star
  `<< s p o >>` quoted-triple form in both modes. -/
inductive Mode where
  | rdf11
  | rdf12
  deriving DecidableEq, Repr

/-! ## Term/literal construction with well-formedness checks

`readIriRef`/`readStringLiteralQuoted` (`Syntax.Lexing`) hand back plain
`String`s; wrapping them into `RDF.WfIri`/`RDF.WfLiteral` needs the
well-formedness predicates from `RDF.Core`, which is why this lives here
and not in `Syntax.Lexing`. -/

/-- Wrap a raw IRI string as a `WfIri`, or report the failure at `pos`.
Port of `parse_iri`'s `is_iri i` check. -/
def mkIri (pos : Nat) (s : String) : Except ParseError WfIri :=
  if h : isIri s then .ok ⟨s, h⟩
  else .error ⟨s!"invalid IRI (not absolute — missing ':'): <{s}>", pos⟩

/-- Wrap a `Literal` record as a `WfLiteral`, or report the failure at
`pos`. Port of every `parse_literal*` branch's `if literal_wf lit then
... else ParseFail "invalid literal" pos`. -/
def mkLiteral (pos : Nat) (l : Literal) : Except ParseError WfLiteral :=
  if h : literalWf l then .ok ⟨l, h⟩
  else .error ⟨"ill-formed literal (language tag / direction / datatype combination)", pos⟩

/-! ## Literal — [6] literal

`literal ::= STRING_LITERAL_QUOTED ('^^' IRIREF | LANGTAG)?` -/

/-- `'^^' IRIREF` — port of `parse_datatype`. -/
def readDatatype (pos : Nat) : List Char → Except ParseError (WfIri × Nat × List Char)
  | '^' :: '^' :: rest =>
      match readIriRef (pos + 2) rest with
      | .error e => .error e
      | .ok (iriStr, pos', rest') =>
          match mkIri pos iriStr with
          | .error e => .error e
          | .ok wi => .ok (wi, pos', rest')
  | _ => .error ⟨"expected '^^'", pos⟩

/-- A literal (mode-parametrised): the string body, then optionally a
LANGTAG (with RDF 1.2's `--ltr`/`--rtl` suffix under `.rdf12`) or a
`^^`-datatype. Port of `parse_literal` (`.rdf11`) / `parse_literal_12`
(`.rdf12`, minus the inline-whitespace relaxation — see module header). -/
def readLiteral (mode : Mode) (pos : Nat) (cs : List Char) :
    Except ParseError (WfLiteral × Nat × List Char) :=
  match readStringLiteralQuoted pos cs with
  | .error e => .error e
  | .ok (lex, pos1, rest1) =>
      match rest1 with
      | '@' :: _ =>
          match mode with
          | .rdf11 =>
              match readLangTag pos1 rest1 with
              | .error e => .error e
              | .ok (tag, pos2, rest2) =>
                  match mkLiteral pos1
                      { lexicalForm := lex, datatype := rdfLangString,
                        langTag := some tag, direction := none } with
                  | .error e => .error e
                  | .ok wl => .ok (wl, pos2, rest2)
          | .rdf12 =>
              match readLangDir12 pos1 rest1 with
              | .error e => .error e
              | .ok ((tag, dopt), pos2, rest2) =>
                  let dt := match dopt with
                    | none => rdfLangString
                    | some _ => rdfDirLangString
                  let dir := dopt.map (fun b => if b then TextDirection.rtl else TextDirection.ltr)
                  match mkLiteral pos1
                      { lexicalForm := lex, datatype := dt,
                        langTag := some tag, direction := dir } with
                  | .error e => .error e
                  | .ok wl => .ok (wl, pos2, rest2)
      | '^' :: '^' :: _ =>
          match readDatatype pos1 rest1 with
          | .error e => .error e
          | .ok (dt, pos2, rest2) =>
              match mkLiteral pos1
                  { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
              | .error e => .error e
              | .ok wl => .ok (wl, pos2, rest2)
      | _ =>
          match mkLiteral pos1
              { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none } with
          | .error e => .error e
          | .ok wl => .ok (wl, pos1, rest1)

/-! ## Subject — [3] subject

`subject ::= IRIREF | BLANK_NODE_LABEL` (same production for the RDF 1.2
triple-term subject slot — RDF 1.2 does not allow a triple term AS a
subject). Port of `parse_subject`. -/

def readSubject (pos : Nat) (cs : List Char) : Except ParseError (Subject × Nat × List Char) :=
  match cs with
  | '<' :: _ =>
      match readIriRef pos cs with
      | .error e => .error e
      | .ok (s, pos', rest') =>
          match mkIri pos s with
          | .error e => .error e
          | .ok wi => .ok (.iri wi, pos', rest')
  | '_' :: ':' :: _ =>
      match readBlankNodeLabel pos cs with
      | .error e => .error e
      | .ok (label, pos', rest') => .ok (.bnode label, pos', rest')
  | _ => .error ⟨"expected subject (IRIREF or BLANK_NODE_LABEL)", pos⟩

/-! ## Predicate — [4] predicate: `predicate ::= IRIREF` -/

def readPredicate (pos : Nat) (cs : List Char) : Except ParseError (WfIri × Nat × List Char) :=
  match readIriRef pos cs with
  | .error e => .error e
  | .ok (s, pos', rest') =>
      match mkIri pos s with
      | .error e => .error e
      | .ok wi => .ok (wi, pos', rest')

/-! ## Object — [5] object (RDF 1.1)

`object ::= IRIREF | BLANK_NODE_LABEL | literal`. Port of `parse_object`. -/

def readObject11 (pos : Nat) (cs : List Char) : Except ParseError (Term × Nat × List Char) :=
  match cs with
  | '<' :: _ =>
      match readIriRef pos cs with
      | .error e => .error e
      | .ok (s, pos', rest') =>
          match mkIri pos s with
          | .error e => .error e
          | .ok wi => .ok (.iri wi, pos', rest')
  | '_' :: ':' :: _ =>
      match readBlankNodeLabel pos cs with
      | .error e => .error e
      | .ok (label, pos', rest') => .ok (.bnode label, pos', rest')
  | '"' :: _ =>
      match readLiteral .rdf11 pos cs with
      | .error e => .error e
      | .ok (wl, pos', rest') => .ok (.literal wl, pos', rest')
  | _ => .error ⟨"expected object (IRIREF, BLANK_NODE_LABEL, or literal)", pos⟩

/-! ## Object — RDF 1.2 extension: `object12 ::= object | tripleTerm`

`tripleTerm ::= '<<(' subject IRIREF object12 ')>>'`. Port of
`parse_object_12_f` / `parse_triple_term_12_f` — the F* source's mutual
recursion collapses into one function with the triple-term case inlined,
since only the OBJECT slot of a triple term recurses (never the subject
or predicate). `fuel` bounds triple-term NESTING depth (one unit per
`<<(` opened) — the one place this port keeps the F* source's fuel style,
because unlike every reader in `Syntax.Lexing` the recursive call here is
not on a direct cons-pattern suffix of the char list (it is reached after
parsing a subject/predicate in between), so plain structural recursion on
the list is not available; structural recursion on `fuel : Nat` is. -/
def readObject12 : Nat → Nat → List Char → Except ParseError (Term × Nat × List Char)
  | 0, pos, _ => .error ⟨"triple-term nesting too deep", pos⟩
  | fuel' + 1, pos, cs =>
      match cs with
      | '<' :: '<' :: '(' :: rest =>
          let (p1, r1) := skipWs (pos + 3) rest
          match readSubject p1 r1 with
          | .error e => .error e
          | .ok (subj, p2, r2) =>
              let (p3, r3) := skipWs p2 r2
              match readPredicate p3 r3 with
              | .error e => .error e
              | .ok (pred, p4, r4) =>
                  let (p5, r5) := skipWs p4 r4
                  match readObject12 fuel' p5 r5 with
                  | .error e => .error e
                  | .ok (obj, p6, r6) =>
                      let (p7, r7) := skipWs p6 r6
                      match r7 with
                      | ')' :: '>' :: '>' :: r8 =>
                          .ok (.tripleTerm subj pred obj, p7 + 3, r8)
                      | _ => .error ⟨"expected ')>>'", p7⟩
      | '<' :: '<' :: _ =>
          .error ⟨"legacy '<< >>' quoted triple is not RDF 1.2 syntax", pos⟩
      | '<' :: _ =>
          (match readIriRef pos cs with
           | .error e => .error e
           | .ok (s, pos', rest') =>
               match mkIri pos s with
               | .error e => .error e
               | .ok wi => .ok (.iri wi, pos', rest'))
      | '_' :: ':' :: _ =>
          (match readBlankNodeLabel pos cs with
           | .error e => .error e
           | .ok (label, pos', rest') => .ok (.bnode label, pos', rest'))
      | '"' :: _ =>
          (match readLiteral .rdf12 pos cs with
           | .error e => .error e
           | .ok (wl, pos', rest') => .ok (.literal wl, pos', rest'))
      | _ =>
          .error ⟨"expected object (IRIREF, BLANK_NODE_LABEL, literal, or triple term)", pos⟩

/-! ## Triple — [2] triple: `triple ::= subject predicate object '.'` -/

/-- RDF 1.1 triple. Port of `parse_triple`. -/
def readTriple11 (pos : Nat) (cs : List Char) : Except ParseError (Triple × Nat × List Char) :=
  let (p1, r1) := skipWs pos cs
  match readSubject p1 r1 with
  | .error e => .error e
  | .ok (subj, p2, r2) =>
      let (p3, r3) := skipWs p2 r2
      match readPredicate p3 r3 with
      | .error e => .error e
      | .ok (pred, p4, r4) =>
          let (p5, r5) := skipWs p4 r4
          match readObject11 p5 r5 with
          | .error e => .error e
          | .ok (obj, p6, r6) =>
              let (p7, r7) := skipWs p6 r6
              match r7 with
              | '.' :: r8 => .ok ({ s := subj, p := pred, o := obj }, p7 + 1, r8)
              | _ => .error ⟨"expected '.' terminator", p7⟩

/-- RDF 1.2 triple: the subject and predicate slots are unchanged (RDF 1.2
does not add triple terms there); only the object slot may be a triple
term. Port of `parse_triple_12`. -/
def readTriple12 (pos : Nat) (cs : List Char) : Except ParseError (Triple × Nat × List Char) :=
  let (p1, r1) := skipWs pos cs
  match readSubject p1 r1 with
  | .error e => .error e
  | .ok (subj, p2, r2) =>
      let (p3, r3) := skipWs p2 r2
      match readPredicate p3 r3 with
      | .error e => .error e
      | .ok (pred, p4, r4) =>
          let (p5, r5) := skipWs p4 r4
          match readObject12 (r5.length + 1) p5 r5 with
          | .error e => .error e
          | .ok (obj, p6, r6) =>
              let (p7, r7) := skipWs p6 r6
              match r7 with
              | '.' :: r8 => .ok ({ s := subj, p := pred, o := obj }, p7 + 1, r8)
              | _ => .error ⟨"expected '.' terminator", p7⟩

/-! ## Document — [1] ntriplesDoc

`ntriplesDoc ::= triple? (EOL triple?)*`, plus `#`-comments and blank
lines (RDF 1.1 N-Triples §"Comments"). STRICT: any malformed line aborts
the whole parse with that line's `ParseError` — port of
`parse_ntriples_strict` / `parse_ntriples_strict_12`. `fuel` bounds the
number of lines processed; every branch below strictly shortens the
remaining char list by at least one element before recursing (a comment
or blank line consumes at least its introducing character, a triple
consumes at least its terminating `.`), so `fuel := cs.length + 1`
(the top-level call, mirroring the F* source's `len + 1`) never runs out
before the input does. -/
def parseLinesAcc (mode : Mode) :
    Nat → Nat → List Char → List Triple → Except ParseError (List Triple)
  | 0, pos, _, _ =>
      .error ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
  | fuel' + 1, pos, cs, acc =>
      let (pos1, cs1) := skipWs pos cs
      match cs1 with
      | [] => .ok acc.reverse
      | '#' :: _ =>
          let (pos2, cs2) := skipComment pos1 cs1
          let (pos3, cs3) := skipEol pos2 cs2
          parseLinesAcc mode fuel' pos3 cs3 acc
      | '\n' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          parseLinesAcc mode fuel' pos2 cs2 acc
      | '\r' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          parseLinesAcc mode fuel' pos2 cs2 acc
      | _ =>
          let step := match mode with
            | .rdf11 => readTriple11 pos1 cs1
            | .rdf12 => readTriple12 pos1 cs1
          match step with
          | .error e => .error e
          | .ok (t, pos2, cs2) =>
              let (pos3, cs3) := skipWs pos2 cs2
              let (pos4, cs4) := skipComment pos3 cs3
              let (pos5, cs5) := skipEol pos4 cs4
              parseLinesAcc mode fuel' pos5 cs5 (t :: acc)

/-- Parse a complete N-Triples document. Default mode is RDF 1.1 (`.rdf11`
— the F* source's `Mode_11` default: the RDF 1.2 concrete syntax is still
a W3C Working Draft, so 1.1 stays the normative default). Port of
`parse_ntriples_mode`, restricted to the strict entry points (see module
header). -/
def parseNTriples (s : String) (mode : Mode := .rdf11) : Except ParseError Graph :=
  let cs := s.toList
  parseLinesAcc mode (cs.length + 1) 0 cs []

/-! ## Serialisation

Port of `RDF.NQuads.Serialize.fst`'s N-Triples-shaped renderers
(`nq_term_to_string`, `nq_subject_to_string`,
`nq_line_for_triple_default_graph`) — the EMIT-MINIMAL wire form (escapes
control characters and `"`/`\`, appends `--ltr`/`--rtl` and `<<( )>>` only
for terms that actually need them, so a purely-RDF-1.1 graph serialises
identically regardless of `mode`). The F* source's separate CANONICAL
form (`nq_canon_term`, uppercase `\u00XX` for every C0/DEL byte,
lowercased language tags, U+FFFE/U+FFFF escaping) is a distinct rendering
contract or the RDFC-1.0 c14n suite, not the general wire serialiser this
module ports — ported below, in its own section. -/

/-- Escape a literal's lexical form for embedding in a quoted string:
`\` → `\\`, `"` → `\"`, LF → `\n`, CR → `\r`, TAB → `\t`; every other
character passes through unescaped. Port of `nq_escape_literal`. -/
def escapeLiteral (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c =>
    match c with
    | '\\' => ['\\', '\\']
    | '"'  => ['\\', '"']
    | '\n' => ['\\', 'n']
    | '\r' => ['\\', 'r']
    | '\t' => ['\\', 't']
    | _    => [c]))

/-- Serialise a `Subject` (IRI or blank node). Port of
`nq_subject_to_string`. -/
def Subject.toNTriples : Subject → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b

/-- Serialise a `Term` in N-Triples object position, mode-parametrised:
under `.rdf11` a term that needs RDF 1.2 lexical syntax (a triple term or
a directional literal) is a serialisation ERROR (port of the F* source's
`nq_term_to_string_mode`'s `Mode_11` branch returning `None`), never
silently emitted. Under `.rdf12` every term serialises (port of
`nq_term_to_string`, extended with the `<<( )>>` / `--ltr`/`--rtl` forms). -/
def Term.toNTriples (mode : Mode) : Term → Except String String
  | .iri i   => .ok ("<" ++ i.val ++ ">")
  | .bnode b => .ok ("_:" ++ b)
  | .literal wl =>
      let l := wl.val
      let esc := escapeLiteral l.lexicalForm
      match l.langTag with
      | some tag =>
          match l.direction with
          | some _ =>
              if mode = .rdf11 then
                .error "RDF 1.2 directional literal requires mode .rdf12"
              else
                let dirSuffix := match l.direction with
                  | some .ltr => "--ltr"
                  | some .rtl => "--rtl"
                  | none => ""
                .ok ("\"" ++ esc ++ "\"@" ++ tag ++ dirSuffix)
          | none => .ok ("\"" ++ esc ++ "\"@" ++ tag)
      | none =>
          if l.datatype = xsdString then .ok ("\"" ++ esc ++ "\"")
          else .ok ("\"" ++ esc ++ "\"^^<" ++ l.datatype.val ++ ">")
  | .tripleTerm s p o =>
      if mode = .rdf11 then .error "RDF 1.2 triple term requires mode .rdf12"
      else
        match Term.toNTriples mode o with
        | .error e => .error e
        | .ok oStr =>
            .ok ("<<( " ++ Subject.toNTriples s ++ " <" ++ p.val ++ "> " ++ oStr ++ " )>>")

/-- Serialise one `Triple` as an N-Triples line, `" .\n"`-terminated.
Port of `nq_line_for_triple_default_graph`. -/
def Triple.toNTriples (mode : Mode) (t : Triple) : Except String String :=
  match Term.toNTriples mode t.o with
  | .error e => .error e
  | .ok oStr => .ok (Subject.toNTriples t.s ++ " <" ++ t.p.val ++ "> " ++ oStr ++ " .\n")

/-- Serialise a whole graph, one line per triple, input order preserved.
Fails (propagating the first offending triple's message) if any triple
needs RDF 1.2 syntax under `.rdf11`. Not a direct F* port (the F* source
has no single "serialise a whole in-memory graph" entry point at this
layer — callers fold `nq_line_for_triple_default_graph` themselves) but a
straightforward `List.foldl`/`Except` composition of it. -/
def Graph.toNTriples (g : Graph) (mode : Mode := .rdf11) : Except String String :=
  g.foldl (fun acc t =>
    match acc with
    | .error e => .error e
    | .ok s =>
        match Triple.toNTriples mode t with
        | .error e => .error e
        | .ok line => .ok (s ++ line))
    (.ok "")

/-! ## Canonical N-Triples (RDF 1.2 N-Triples §canonical form)

https://www.w3.org/TR/rdf12-n-triples/#canonical-ntriples — the form the
W3C `rdf12/rdf-n-triples/c14n` and `rdf12/rdf-n-quads/c14n` suites
compare BYTE FOR BYTE. Port of `RDF.NQuads.Serialize.fst`'s
`nq_canon_*` group (`canon_hex_upper`, `canon_byte_uchar`,
`nq_canon_special_byte`, `nq_canon_escape_byte`, `nq_canon_walk`,
`nq_canon_term`, `nq_canon_line_default`, `canonical_nt_document`).

What canonical form fixes, and what it does NOT:

  * one space between terms, one `" .\n"`-terminated line per triple;
  * the shortest escape for `\b \t \n \f \r \" \\`, an uppercase
    `\u00XX` for every other C0 control and for DEL (U+007F), and
    `￾` / `￿` for the two BMP non-characters;
  * language tags lowercased, the base direction kept as `--ltr` /
    `--rtl`;
  * `xsd:string` written with no datatype;
  * blank-node labels and statement ORDER are preserved. This is
    canonical SERIALISATION, not RDFC-1.0 canonicalisation (which
    relabels blank nodes and sorts — see `RDF/Canonical.lean`).

The F* source walks UTF-8 BYTES; this walks Unicode CHARACTERS. The two
agree: every byte the F* escapes is below 0x80, so it can only be a
one-byte UTF-8 sequence, and the U+FFFE / U+FFFF cases the F* matches as
the byte triples `EF BF BE` / `EF BF BF` are exactly those codepoints. -/

/-- Uppercase hexadecimal digit for a nibble. Port of `canon_hex_upper`. -/
def canonHexUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- `\u00XX` (uppercase hex) for a codepoint below 0x100. Port of
`canon_byte_uchar`. -/
def canonUchar2 (n : Nat) : String :=
  "\\u00" ++ String.ofList [canonHexUpper (n / 16), canonHexUpper (n % 16)]

/-- The canonical escape for one character, `none` when the character
passes through unchanged. Port of `nq_canon_special_byte` +
`nq_canon_escape_byte`, plus the U+FFFE / U+FFFF non-character rule
`nq_canon_walk` applies inline. -/
def canonEscapeChar (c : Char) : Option String :=
  let n := c.toNat
  if n == 0x08 then some "\\b"
  else if n == 0x09 then some "\\t"
  else if n == 0x0A then some "\\n"
  else if n == 0x0C then some "\\f"
  else if n == 0x0D then some "\\r"
  else if n == 0x22 then some "\\\""
  else if n == 0x5C then some "\\\\"
  else if n < 0x20 || n == 0x7F then some (canonUchar2 n)
  else if n == 0xFFFE || n == 0xFFFF then some ("\\u" ++ String.ofList
    [canonHexUpper (n / 4096 % 16), canonHexUpper (n / 256 % 16),
     canonHexUpper (n / 16 % 16), canonHexUpper (n % 16)])
  else none

/-- A literal's lexical form, canonically escaped. Port of
`nq_canon_escape_literal` / `nq_canon_walk`. -/
def canonEscapeLiteral (s : String) : String :=
  String.join (s.toList.map (fun c =>
    match canonEscapeChar c with
    | some e => e
    | none   => String.singleton c))

/-- Canonical form of a term in object position. Port of
`nq_canon_term`. Total: canonical N-Triples IS RDF 1.2, so there is no
mode parameter and no failure case. -/
def Term.toCanonicalNTriples : Term → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .literal wl =>
      let l := wl.val
      let esc := canonEscapeLiteral l.lexicalForm
      match l.langTag with
      | some tag =>
          let dirSuffix := match l.direction with
            | some .ltr => "--ltr"
            | some .rtl => "--rtl"
            | none      => ""
          "\"" ++ esc ++ "\"@" ++ tag.map Char.toLower ++ dirSuffix
      | none =>
          if l.datatype = xsdString then "\"" ++ esc ++ "\""
          else "\"" ++ esc ++ "\"^^<" ++ l.datatype.val ++ ">"
  | .tripleTerm s p o =>
      "<<( " ++ Subject.toNTriples s ++ " <" ++ p.val ++ "> " ++
      Term.toCanonicalNTriples o ++ " )>>"

/-- One canonical line, `" .\n"`-terminated. Port of
`nq_canon_line_default`. -/
def Triple.toCanonicalNTriples (t : Triple) : String :=
  Subject.toNTriples t.s ++ " <" ++ t.p.val ++ "> " ++
  Term.toCanonicalNTriples t.o ++ " .\n"

/-- Canonical N-Triples document: one line per triple, input order.
Port of `canonical_nt_document`. -/
def Graph.toCanonicalNTriples (g : Graph) : String :=
  String.join (g.map Triple.toCanonicalNTriples)

end L4Factoidal.Syntax
