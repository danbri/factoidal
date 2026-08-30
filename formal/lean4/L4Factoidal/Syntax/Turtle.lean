/-
L4Factoidal.Syntax.Turtle — the Turtle 1.1 parser.

Port of `formal/fstar/Parser.Turtle.fst` (+ the token scanner in
`formal/fstar/Parser.TurtleScanner.fst`), built on the character-level
readers already landed in `Syntax.Lexing` and on the RFC 3986 resolver
in `Syntax.IriResolve`.

Grammar productions ported (RDF 1.1 Turtle, https://www.w3.org/TR/turtle/):

  [1]    turtleDoc            ::= statement*
  [2]    statement            ::= directive | triples '.'
  [3]    directive            ::= prefixID | base | sparqlPrefix | sparqlBase
  [4]    prefixID             ::= '@prefix' PNAME_NS IRIREF '.'
  [5]    base                 ::= '@base' IRIREF '.'
  [5s]   sparqlPrefix         ::= "PREFIX" PNAME_NS IRIREF        (case-insensitive)
  [6s]   sparqlBase           ::= "BASE" IRIREF                   (case-insensitive)
  [6]    triples              ::= subject predicateObjectList
                                | blankNodePropertyList predicateObjectList?
  [7]    predicateObjectList  ::= verb objectList (';' (verb objectList)?)*
  [8]    objectList           ::= object (',' object)*
  [9]    verb                 ::= predicate | 'a'
  [10]   subject              ::= iri | BlankNode | collection
  [11]   predicate            ::= iri
  [12]   object               ::= iri | BlankNode | collection
                                | blankNodePropertyList | literal
  [13]   literal              ::= RDFLiteral | NumericLiteral | BooleanLiteral
  [14]   blankNodePropertyList::= '[' predicateObjectList ']'
  [15]   collection           ::= '(' object* ')'
  [16]   NumericLiteral       ::= INTEGER | DECIMAL | DOUBLE
  [128s] RDFLiteral           ::= String (LANGTAG | '^^' iri)?
  [133s] BooleanLiteral       ::= 'true' | 'false'
  [17]   String               ::= STRING_LITERAL_QUOTE
                                | STRING_LITERAL_SINGLE_QUOTE
                                | STRING_LITERAL_LONG_SINGLE_QUOTE
                                | STRING_LITERAL_LONG_QUOTE
  [135s] iri                  ::= IRIREF | PrefixedName
  [136s] PrefixedName         ::= PNAME_LN | PNAME_NS
  [137s] BlankNode            ::= BLANK_NODE_LABEL | ANON
  [139s] PNAME_NS             ::= PN_PREFIX? ':'
  [140s] PNAME_LN             ::= PNAME_NS PN_LOCAL
  [161s] WS, [162s] ANON, [163s] PN_CHARS_BASE, [164s] PN_CHARS_U,
  [166s] PN_CHARS, [167s] PN_PREFIX, [168s] PN_LOCAL,
  [169s] PLX, [170s] PERCENT, [172s] PN_LOCAL_ESC
  plus `#`-to-end-of-line comments (Turtle §2.1).

RDF 1.2 (`.rdf12`; RDF 1.2 Turtle, https://www.w3.org/TR/rdf12-turtle/,
the productions the F* source's `Mode_12` covers), all ported:

  [2]   statement            ::= directive | triples '.'
  [3]   directive            ::= prefixID | base | sparqlPrefix | sparqlBase | version
  [4a]  version              ::= '@version' VERSION_STRING '.'       (port of
        sparqlVersion         ::= "VERSION" VERSION_STRING            `parse_version_directive`)
  [10]  subject              ::= iri | BlankNode | collection | reifiedTriple
  [12]  object               ::= iri | BlankNode | collection
                               | blankNodePropertyList | literal
                               | tripleTerm | reifiedTriple
  [27]  reifiedTriple        ::= '<<' rtSubject verb rtObject reifier? '>>'
  [28]  rtSubject            ::= iri | BlankNode | reifiedTriple
  [29]  rtObject             ::= iri | BlankNode | literal | tripleTerm | reifiedTriple
  [30]  tripleTerm           ::= '<<(' ttSubject verb ttObject ')>>'
  [31]  ttSubject            ::= iri | BlankNode
  [32]  ttObject             ::= iri | BlankNode | literal | tripleTerm
  [33]  reifier              ::= '~' (iri | BlankNode)?
  [34]  annotation           ::= (reifier | annotationBlock)*
  [35]  annotationBlock      ::= '{|' predicateObjectList '|}'
  plus the `@lang--ltr` / `@lang--rtl` base direction on LANG_DIR
  (`Syntax.Lexing.readLangDir12`).

  A reified triple denotes its REIFIER (the `~`-named IRI or blank
  node, or a fresh blank node) and emits
  `reifier rdf:reifies <<( s p o )>>`; the reifier stands in the
  enclosing subject / object position. Ports of `parse_reified_triple`
  / `parse_rt_subject` / `parse_rt_object` / `parse_reifier`,
  `parse_turtle_triple_term` / `parse_tt_object`, `parse_annotations`.
  Every one of them is reachable only under `.rdf12`; under `.rdf11`
  the `<<`, `{|`, `~` and `VERSION` forms are rejected exactly as the
  RDF 1.1 grammar rejects them, and the RDF 1.1 W3C suites' scores are
  unchanged by their presence.

F* → Lean correspondences and the deliberate departures:

  * The F* source indexes BYTES through the `Parser.FastString`
    `assume val` layer (`fs_byte_at` / `fs_byte_index` / `fs_byte_sub`
    / `fs_byte_length` / `fs_cp_at`) and therefore carries an
    ASCII-byte fast path beside a UTF-8 codepoint slow path in every
    scanner (`validate_pname_ns_from`, `validate_pn_local_from`,
    `parse_long_string_body`, `scan_name_body_end`, ...). This port
    walks `List Char` — already Unicode scalar values — so each of
    those pairs collapses to ONE definition, and there is no
    `assume val` beneath any of it. `unescape_pn_local`'s
    raw-byte-fragment workaround (F* issue #325, mojibake on
    `ex:日\-本`) does not arise here at all.
  * FUEL is kept exactly where the F* source needs it: the
    whitespace/comment skipper, the name-body scanner, the string
    bodies, the numeric collector, and the whole mutually-recursive
    term block (`parse_turtle_object` … `parse_trailing_semicolons_rev`).
    Every fuel budget is derived from the remaining input length, so
    it can never bind before the input is consumed.
  * The F* `resolve_iri_hint` short-circuits resolution whenever the
    RAW IRIREF text contains a colon anywhere. That is wrong for a
    relative reference with a colon in a later path segment
    (`<a/b:c>`), which RFC 3986 §4.2 makes relative — it has no
    scheme. This port always routes through `Syntax.IriResolve`
    §5.2, which is a no-op on a genuinely absolute reference and
    correct on `<a/b:c>`. See `PORT_NOTES.md`.
  * BLANK-NODE LABELS. The F* source mints anonymous labels as
    `_anon0`, `_anon1`, … and passes user labels through unchanged, so
    a document writing `_:_anon0` COLLIDES with a generated one. This
    port removes that hazard while KEEPING user labels unchanged (which
    matters: a TriG blank-node graph name `_:G` has to stay comparable
    with the `_:G` of an N-Quads fixture, and `RDF.Dataset` keys named
    graphs by their label string). Generated labels are prefixed with
    `anon` followed by one more consecutive `_` than occurs anywhere in
    the document, so no label the document can write begins with it —
    see `freshBnodePrefix`.
-/

import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.Lexing
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Parser state — port of `turtle_state`

Carries the prefix map, the in-force base IRI, the anonymous-blank-node
counter, and the RDF 1.1/1.2 mode. Threaded explicitly through every
production, exactly as the F* record is; never a global. -/

/-- Port of the F* `turtle_state` record. -/
structure TurtleState where
  /-- `@prefix` / `PREFIX` bindings, most recent first (a re-binding
  shadows the older one, per Turtle §6.3). -/
  prefixes : List (String × String)
  /-- The base IRI currently in force; `""` means "no base", in which
  case a relative reference resolves to itself and then fails
  `RDF.isIri`. -/
  baseIri : String
  /-- Counter behind the generated labels for `[]`, `[ … ]`, and
  collection nodes. -/
  bnodeCounter : Nat
  /-- The prefix generated labels carry — chosen per DOCUMENT so that no
  label the document itself writes can equal a generated one. See
  `freshBnodePrefix`. -/
  bnodePrefix : String
  /-- RDF 1.1 vs RDF 1.2 grammar (port of `ts_mode`). -/
  mode : Mode

/-- The longest run of consecutive `_` characters anywhere in the
document. -/
def maxUnderscoreRun : List Char → Nat → Nat → Nat
  | [],      cur, best => max cur best
  | c :: cs, cur, best =>
      if c == '_' then maxUnderscoreRun cs (cur + 1) (max (cur + 1) best)
      else maxUnderscoreRun cs 0 best

/-- The prefix every GENERATED blank-node label carries for this
document: `anon` followed by one more consecutive `_` than appears
anywhere in the document text. No `_:LABEL` the document writes can
begin with it (a BLANK_NODE_LABEL is a substring of the text, so it
cannot contain a longer underscore run than the text does), so the
generated labels and the document's own labels are disjoint by
construction — and user labels can therefore be passed through
UNCHANGED, which is what keeps a blank-node graph name written `_:G` in
TriG comparable with the `_:G` an N-Quads fixture writes.

The F* source instead mints `_anon<N>` and also passes user labels
through, so a document writing `_:_anon0` collides with a generated
label there. That hazard is removed here at the cost of slightly
longer labels. -/
def freshBnodePrefix (text : String) : String :=
  "anon" ++ String.ofList (List.replicate (maxUnderscoreRun text.toList 0 0 + 1) '_')

/-- Character-list form used by the parser, which already owns a decoded
    document. Keeping this separate avoids a second whole-document
    `String.toList` allocation merely to choose a collision-free generated
    blank-node prefix. -/
def freshBnodePrefixChars (cs : List Char) : String :=
  "anon" ++ String.ofList (List.replicate (maxUnderscoreRun cs 0 0 + 1) '_')

/-- Port of `empty_turtle_state` / `empty_turtle_state_12`, plus the
optional retrieval-IRI base a caller supplies (`parse_turtle_with_base`).
`text` is the whole document, needed only to pick a collision-free
generated-label prefix. -/
def TurtleState.init (text : String) (base : Option String) (mode : Mode) : TurtleState :=
  { prefixes := [], baseIri := base.getD "", bnodeCounter := 0,
    bnodePrefix := freshBnodePrefix text, mode := mode }

/-- Parser-facing state construction from already decoded source characters.
    It has the same state as `TurtleState.init (String.ofList cs)`, while
    avoiding a second materialisation of those characters. -/
def TurtleState.initChars (cs : List Char) (base : Option String) (mode : Mode) : TurtleState :=
  { prefixes := [], baseIri := base.getD "", bnodeCounter := 0,
    bnodePrefix := freshBnodePrefixChars cs, mode := mode }

/-- Mint a fresh anonymous blank-node label. Port of `fresh_bnode`. -/
def TurtleState.freshBnode (st : TurtleState) : BNodeId × TurtleState :=
  (st.bnodePrefix ++ toString st.bnodeCounter,
   { st with bnodeCounter := st.bnodeCounter + 1 })

/-- A document-written `_:LABEL` keeps its label, exactly as the
N-Triples and N-Quads ports do — `freshBnodePrefix` is what keeps the
generated labels out of the way. -/
def userBnodeLabel (l : BNodeId) : BNodeId := l

/-- Look up a prefix. Port of `lookup_prefix` (list order = shadowing
order, most recent binding first). -/
def TurtleState.lookupPrefix (st : TurtleState) (pfx : String) : Option String :=
  match st.prefixes.find? (fun p => p.1 == pfx) with
  | some p => some p.2
  | none   => none

/-! ## Whitespace and comments — Turtle §2.1, production [161s] WS

`WS ::= #x20 | #x9 | #xD | #xA`, and a `#` outside a string or IRIREF
starts a comment running to the next line terminator. -/

/-- Port of `is_turtle_ws`. Unlike N-Triples' `isNtWs` (space/tab only,
because N-Triples is line-structured) Turtle whitespace includes both
line terminators. -/
def isTurtleWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Skip whitespace and `#`-comments without measuring the remaining input.
    The Boolean tracks whether we are consuming comment text; one structural
    recursion thereby avoids the old `cs.length + 1` fuel calculation at every
    whitespace boundary. -/
def skipWsCommentsLoop : Bool → Nat → List Char → Nat × List Char
  | _,          pos, [] => (pos, [])
  | inComment,  pos, c :: rest =>
      if inComment then
        if c == '\n' || c == '\r' then skipWsCommentsLoop false (pos + 1) rest
        else skipWsCommentsLoop true (pos + 1) rest
      else if isTurtleWs c then skipWsCommentsLoop false (pos + 1) rest
      else if c == '#' then skipWsCommentsLoop true (pos + 1) rest
      else (pos, c :: rest)

def skipWsComments (pos : Nat) (cs : List Char) : Nat × List Char :=
  skipWsCommentsLoop false pos cs

/-- `turtle_ws`: skip zero or more whitespace characters and comments.
Fuel is the remaining input length, so it can never bind first. -/
def tws (pos : Nat) (cs : List Char) : Nat × List Char :=
  skipWsComments pos cs

/-! ## Name characters — productions [163s]–[166s]

The Unicode ranges are ALREADY tabulated in `Syntax.Lexing`
(`isBnodeStartChar` = `PN_CHARS_U | [0-9]`, the BLANK_NODE_LABEL start
set; `isBnodeChar` = `PN_CHARS | '.'`, the BLANK_NODE_LABEL body set),
so the three Turtle classes are derived from those rather than
re-tabulated — one table, four consumers. -/

/-- [166s] `PN_CHARS ::= PN_CHARS_U | '-' | [0-9] | #xB7 | [#x300-#x36F] | [#x203F-#x2040]`.
`isBnodeChar` is exactly this set plus `'.'`. -/
def isPnChars (c : Char) : Bool := isBnodeChar c && !(c == '.')

/-- [164s] `PN_CHARS_U ::= PN_CHARS_BASE | '_'`. `isBnodeStartChar` is
exactly this set plus the ASCII digits (BLANK_NODE_LABEL may start with
a digit; PN_CHARS_U may not). -/
def isPnCharsU (c : Char) : Bool := isBnodeStartChar c && !('0' ≤ c ∧ c ≤ '9')

/-- [163s] `PN_CHARS_BASE` — letters and the Unicode name ranges, with
neither `_` nor the digits. -/
def isPnCharsBase (c : Char) : Bool := isPnCharsU c && !(c == '_')

/-- [172s] `PN_LOCAL_ESC ::= '\' ('_' | '~' | '.' | '-' | '!' | '$' |
'&' | "'" | '(' | ')' | '*' | '+' | ',' | ';' | '=' | '/' | '?' | '#' |
'@' | '%')`. Port of `is_pn_local_esc_char`. -/
def isPnLocalEsc (c : Char) : Bool :=
  c == '_' || c == '~' || c == '.' || c == '-' || c == '!' || c == '$' ||
  c == '&' || c == '\'' || c == '(' || c == ')' || c == '*' || c == '+' ||
  c == ',' || c == ';' || c == '=' || c == '/' || c == '?' || c == '#' ||
  c == '@' || c == '%'

/-- ASCII hexadecimal digit — [171s] HEX, used by [170s] PERCENT. Port
of `is_ascii_hex_digit`. -/
def isHexDigit (c : Char) : Bool := (hexVal c).isSome

/-- ASCII decimal digit. Port of `is_digit_char`. -/
def isDigitChar (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'

/-! ## The prefixed-name token scanner — port of
`Parser.TurtleScanner.scan_name_body_end` / `scan_prefixed_name_span`

A prefixed name is scanned as ONE token and only then split at its
first `:` and validated. Scanning has to run ahead of validation
because `PN_LOCAL_ESC` lets a name contain characters (`,`, `;`, `#`,
`(`, …) that otherwise terminate a token: `ex:a\,b` is one name, not
`ex:a\` followed by `,b`. -/

/-- Characters that continue a name token on the ASCII side. Port of
`is_ascii_name_body`. -/
def isAsciiNameBody (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z') || ('0' ≤ c ∧ c ≤ '9') ||
  c == '_' || c == '-' || c == '.' || c == ':' || c == '%' || c == '\\'

/-- Scan one name-token body: ASCII name characters, `\`-escape PAIRS
taken whole, and any non-ASCII character (the F* scanner's
`is_turtle_token_delim` is false on every non-ASCII codepoint, so the
non-ASCII branch always consumes; validation afterwards is what rejects
a character outside `PN_CHARS`). Port of `scan_name_body_end`; fuel is
the F* source's. Every recursive branch consumes one or two input
characters, so the Lean version can use structural recursion and avoid a
full remaining-list-length calculation for every IRI token. Returns
`(token, rest)`. -/
def scanNameBodyLoop : List Char → List Char → List Char × List Char
  | [],               accRev => (accRev.reverse, [])
  | '\\' :: e :: rest, accRev => scanNameBodyLoop rest (e :: '\\' :: accRev)
  | c :: rest, accRev =>
      if c.toNat < 0x80 then
        if isAsciiNameBody c then scanNameBodyLoop rest (c :: accRev)
        else (accRev.reverse, c :: rest)
      else scanNameBodyLoop rest (c :: accRev)

def scanNameBody (cs : List Char) : List Char × List Char :=
  scanNameBodyLoop cs []

/-- Trim trailing UNESCAPED `.` characters off a scanned PN_LOCAL, per
[168s] PN_LOCAL's rule that a local name may contain dots but never end
on one — the trailing dot belongs to the document (`:s :p ex:o.` is a
triple terminator, not a local name `o.`). A dot preceded by `\` is a
PN_LOCAL_ESC and stays. Port of `trim_trailing_dots_pos`. Returns
`(kept, trimmedDots)`, the dots to be pushed back onto the input. -/
def trimDotsRev : List Char → List Char → List Char × List Char
  | [],          acc => ([], acc)
  | '.' :: rest, acc =>
      match rest with
      | '\\' :: _ => ('.' :: rest, acc)
      | _         => trimDotsRev rest ('.' :: acc)
  | l,           acc => (l, acc)

/-- `trimDotsRev` applied to a forward-order character list. -/
def trimTrailingDots (l : List Char) : List Char × List Char :=
  let (revKept, dots) := trimDotsRev l.reverse []
  (revKept.reverse, dots)

/-- [167s] `PN_PREFIX ::= PN_CHARS_BASE ((PN_CHARS | '.')* PN_CHARS)?`
— a valid prefix starts with PN_CHARS_BASE and never ends on `.`. The
empty prefix (bare `:local`) is valid. Port of `validate_pname_ns`,
made grammar-exact: the F* version tests every position against the
same ASCII class and so also accepts a leading digit. -/
def validatePnPrefixTail : List Char → Bool
  | []       => true
  | c :: rest => (isPnChars c || (c == '.' && !rest.isEmpty)) && validatePnPrefixTail rest

def validatePnPrefix : List Char → Bool
  | []        => true
  | c :: rest => isPnCharsBase c && validatePnPrefixTail rest

/-- [168s] `PN_LOCAL ::= (PN_CHARS_U | ':' | [0-9] | PLX)
((PN_CHARS | '.' | ':' | PLX)* (PN_CHARS | ':' | PLX))?`, where
[169s] `PLX ::= PERCENT | PN_LOCAL_ESC`. `isFirst` distinguishes the
first position (no `-`, no `.`). A `.` is legal only when something
follows it — trailing dots have already been trimmed, so "something
follows" is just "`rest` is non-empty". Port of
`validate_pn_local_from`. -/
def validatePnLocal : List Char → Bool → Bool
  | [],                    _       => true
  | '%' :: h1 :: h2 :: rest, _     => isHexDigit h1 && isHexDigit h2 && validatePnLocal rest false
  | '%' :: _,              _       => false
  | '\\' :: e :: rest,     _       => isPnLocalEsc e && validatePnLocal rest false
  | ['\\'],                _       => false
  | c :: rest,             isFirst =>
      (if isFirst then isPnCharsU c || c == ':' || isDigitChar c
       else isPnChars c || c == ':' || (c == '.' && !rest.isEmpty)) &&
      validatePnLocal rest false

/-- Turtle §6.5: a PN_LOCAL_ESC sequence contributes its ESCAPED
character to the IRI; a `%XX` PERCENT sequence is passed through
UNCHANGED (it is already the IRI's own percent-encoding, and decoding
it here would change the IRI). Port of `unescape_pn_local`. -/
def unescapePnLocal : List Char → List Char
  | []                => []
  | '\\' :: e :: rest => e :: unescapePnLocal rest
  | c :: rest         => c :: unescapePnLocal rest

/-- Split a scanned name token at its FIRST `:` — the prefix/local
boundary. `none` when the token has no colon (so it is not a prefixed
name at all). Port of `scan_prefixed_name_span`'s inner `find_colon`. -/
def splitAtFirstColon (l : List Char) : Option (List Char × List Char) :=
  match l.span (fun c => !(c == ':')) with
  | (pre, ':' :: post) => some (pre, post)
  | _                  => none

/-- A character that may open a name token. Port of
`is_ascii_name_start`, widened to accept a non-ASCII PN_CHARS_BASE
character (the F* scanner rejects those outright, so `日本:x` cannot be
a prefixed name there; the Turtle grammar allows it). -/
def isNameStartChar (c : Char) : Bool :=
  if c.toNat < 0x80 then
    ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z') || ('0' ≤ c ∧ c ≤ '9') || c == '_'
  else isPnCharsBase c

/-- [136s] PrefixedName — scan one name token, split it, trim the
trailing dots, validate both halves. Returns the RAW halves (the local
part still carrying its escapes; `unescapePnLocal` runs at
IRI-construction time). Port of `parse_prefixed_name`. -/
def readPrefixedName (pos : Nat) (cs : List Char) :
    Except ParseError ((String × List Char) × Nat × List Char) :=
  let finish (pfx : List Char) (localRaw : List Char) (consumed : Nat) (r : List Char) :
      Except ParseError ((String × List Char) × Nat × List Char) :=
    let (loc, dots) := trimTrailingDots localRaw
    if !validatePnPrefix pfx then .error ⟨"invalid prefix in prefixed name", pos⟩
    else if !validatePnLocal loc true then .error ⟨"invalid prefixed name local part", pos⟩
    else .ok ((String.ofList pfx, loc), pos + consumed - dots.length, dots ++ r)
  match cs with
  | [] => .error ⟨"expected prefixed name", pos⟩
  | ':' :: rest =>
      let (localRaw, r) := scanNameBody rest
      finish [] localRaw (1 + localRaw.length) r
  | c :: _ =>
      if !isNameStartChar c then .error ⟨"expected prefixed name", pos⟩
      else
        let (body, r) := scanNameBody cs
        match splitAtFirstColon body with
        | none => .error ⟨"expected ':' in prefixed name", pos + body.length⟩
        | some (pfx, localRaw) => finish pfx localRaw body.length r

/-- [139s] PNAME_NS alone — the `@prefix` / `PREFIX` directive's
namespace token, which must be a prefix followed by `:` and nothing
else. Port of `parse_pname_ns`. -/
def readPnameNs (pos : Nat) (cs : List Char) : Except ParseError (String × Nat × List Char) :=
  match readPrefixedName pos cs with
  | .error e => .error e
  | .ok ((pfx, loc), pos', rest) =>
      if loc.isEmpty then .ok (pfx, pos', rest)
      else .error ⟨"expected PNAME_NS (prefix followed by ':')", pos⟩

/-! ## IRIs — [135s] iri

`iri ::= IRIREF | PrefixedName`. IRIREF scanning (including UCHAR
escapes and the forbidden-codepoint set) is `Syntax.Lexing.readIriRef`,
already landed for N-Triples; what Turtle adds is RESOLUTION of a
relative reference against the in-force base. -/

/-- Resolve a raw IRIREF against the document base (RFC 3986 §5.2 via
`Syntax.IriResolve`). Port of `resolve_iri` / `resolve_iri_hint` — see
the module header on why the F* colon short-circuit is not reproduced.
With an empty base this is the identity on absolute references and on
relative ones alike, so the "no base" case fails later at `mkIri`, with
a position, exactly as the F* source's `is_iri resolved` check does. -/
def TurtleState.resolve (st : TurtleState) (raw : String) : String :=
  resolveIri st.baseIri raw

/-- Build the IRI a `prefix:local` names: namespace ++ unescaped local.
Port of `resolve_prefixed_name`. `none` = undeclared prefix. -/
def TurtleState.expandPrefixed (st : TurtleState) (pfx : String) (loc : List Char) :
    Option String :=
  match st.lookupPrefix pfx with
  | some ns => some (ns ++ String.ofList (unescapePnLocal loc))
  | none    => none

/-- [135s] iri — an IRIREF (resolved against base) or a PrefixedName
(expanded through the prefix map). Port of `parse_turtle_iri`. -/
def readTurtleIri (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (WfIri × Nat × List Char) :=
  match cs with
  | '<' :: _ =>
      match readIriRef pos cs with
      | .error e => .error e
      | .ok (raw, pos', rest) =>
          match mkIri pos (st.resolve raw) with
          | .error _ => .error ⟨s!"relative IRI <{raw}> with no base to resolve against", pos⟩
          | .ok wi   => .ok (wi, pos', rest)
  | _ =>
      match readPrefixedName pos cs with
      | .error e => .error e
      | .ok ((pfx, loc), pos', rest) =>
          match st.expandPrefixed pfx loc with
          | none   => .error ⟨s!"undefined prefix: {pfx}", pos⟩
          | some s =>
              match mkIri pos s with
              | .error e => .error e
              | .ok wi   => .ok (wi, pos', rest)

/-! ## Blank nodes — [137s] `BlankNode ::= BLANK_NODE_LABEL | ANON`

BLANK_NODE_LABEL scanning is `Syntax.Lexing.readBlankNodeLabel`
(including its trailing-dot rule); ANON (`'[' WS* ']'`) is handled
inside the object/subject productions, where the `[` has to be
distinguished from a blankNodePropertyList anyway. -/

/-- `_:LABEL`, mapped into the parser's user-label namespace. -/
def readTurtleBnode (pos : Nat) (cs : List Char) :
    Except ParseError (BNodeId × Nat × List Char) :=
  match readBlankNodeLabel pos cs with
  | .error e => .error e
  | .ok (l, pos', rest) => .ok (userBnodeLabel l, pos', rest)

/-! ## Strings — [17] String

Four forms, all sharing one escape decoder:
  [22]  STRING_LITERAL_QUOTE             `"…"`
  [23]  STRING_LITERAL_SINGLE_QUOTE      `'…'`
  [24]  STRING_LITERAL_LONG_SINGLE_QUOTE `'''…'''`
  [25]  STRING_LITERAL_LONG_QUOTE        `"""…"""`
Short forms reject raw line terminators; long forms accept them and
accept up to two consecutive quote characters inside. Port of
`parse_turtle_string` / `parse_long_string_body` /
`parse_single_string_body` / (for the double-quoted short form) the
N-Triples `parse_string_body` that `Syntax.Lexing` already ports. -/

/-- [26] UCHAR + [159s] ECHAR, decoded. The argument list starts AFTER
the backslash; `pos` points AT the backslash. Shared by all four string
forms, and identical to the escape table `Syntax.Lexing`'s
`readStringLiteralBody` inlines for N-Triples. -/
def decodeEscape (pos : Nat) : List Char → Except ParseError (Char × Nat × List Char)
  | 't'  :: r => .ok ('\t', pos + 2, r)
  | 'b'  :: r => .ok (Char.ofNat 0x08, pos + 2, r)
  | 'n'  :: r => .ok ('\n', pos + 2, r)
  | 'r'  :: r => .ok ('\r', pos + 2, r)
  | 'f'  :: r => .ok (Char.ofNat 0x0C, pos + 2, r)
  | '"'  :: r => .ok ('"', pos + 2, r)
  | '\'' :: r => .ok ('\'', pos + 2, r)
  | '\\' :: r => .ok ('\\', pos + 2, r)
  | 'u' :: h0 :: h1 :: h2 :: h3 :: r =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3 with
      | some d0, some d1, some d2, some d3 =>
          match codepointToChar (d0 * 4096 + d1 * 256 + d2 * 16 + d3) pos with
          | .error e => .error e
          | .ok c    => .ok (c, pos + 6, r)
      | _, _, _, _ => .error ⟨"invalid hex digit in \\u escape", pos⟩
  | 'u' :: _ => .error ⟨"incomplete \\u escape", pos⟩
  | 'U' :: h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: r =>
      match hexVal h0, hexVal h1, hexVal h2, hexVal h3,
            hexVal h4, hexVal h5, hexVal h6, hexVal h7 with
      | some d0, some d1, some d2, some d3, some d4, some d5, some d6, some d7 =>
          let cp := d0 * 268435456 + d1 * 16777216 + d2 * 1048576 + d3 * 65536
                  + d4 * 4096 + d5 * 256 + d6 * 16 + d7
          match codepointToChar cp pos with
          | .error e => .error e
          | .ok c    => .ok (c, pos + 10, r)
      | _, _, _, _, _, _, _, _ => .error ⟨"invalid hex digit in \\U escape", pos⟩
  | 'U' :: _ => .error ⟨"incomplete \\U escape", pos⟩
  | c :: _   => .error ⟨s!"invalid escape: \\{c}", pos⟩
  | []       => .error ⟨"backslash at end of input", pos⟩

/-- Short-form string body, parametrised by its quote character
(`'"'` or `'\''`). A raw LF or CR is a syntax error. Fuel as in
`parse_single_string_body`. -/
def readShortStringBody (qch : Char) : Nat → Nat → List Char → List Char →
    Except ParseError (String × Nat × List Char)
  | 0,        pos, _,  _   => .error ⟨"string literal too long", pos⟩
  | fuel + 1, pos, cs, acc =>
      match cs with
      | []        => .error ⟨"unterminated string literal", pos⟩
      | '\n' :: _ => .error ⟨"unescaped newline in string literal", pos⟩
      | '\r' :: _ => .error ⟨"unescaped carriage return in string literal", pos⟩
      | '\\' :: rest =>
          match decodeEscape pos rest with
          | .error e => .error e
          | .ok (c, pos', r) => readShortStringBody qch fuel pos' r (c :: acc)
      | c :: rest =>
          if c == qch then .ok (String.ofList acc.reverse, pos + 1, rest)
          else readShortStringBody qch fuel (pos + 1) rest (c :: acc)

/-- Long-form (triple-quoted) string body. Line terminators are
content; one or two consecutive quote characters are content; three end
the literal. Port of `parse_long_string_body`. -/
def readLongStringBody (qch : Char) : Nat → Nat → List Char → List Char →
    Except ParseError (String × Nat × List Char)
  | 0,        pos, _,  _   => .error ⟨"unterminated long string", pos⟩
  | fuel + 1, pos, cs, acc =>
      match cs with
      | []           => .error ⟨"unterminated long string", pos⟩
      | '\\' :: rest =>
          match decodeEscape pos rest with
          | .error e => .error e
          | .ok (c, pos', r) => readLongStringBody qch fuel pos' r (c :: acc)
      | c :: rest =>
          if c == qch then
            match rest with
            | c2 :: c3 :: rest3 =>
                if c2 == qch && c3 == qch then .ok (String.ofList acc.reverse, pos + 3, rest3)
                else readLongStringBody qch fuel (pos + 1) rest (c :: acc)
            | _ => readLongStringBody qch fuel (pos + 1) rest (c :: acc)
          else readLongStringBody qch fuel (pos + 1) rest (c :: acc)

/-- [17] String — dispatch on the opening quote run. Port of
`parse_turtle_string`. -/
def readTurtleString (pos : Nat) (cs : List Char) :
    Except ParseError (String × Nat × List Char) :=
  let fuel := cs.length + 1
  match cs with
  | '"' :: '"' :: '"' :: rest   => readLongStringBody '"' fuel (pos + 3) rest []
  | '\'' :: '\'' :: '\'' :: rest => readLongStringBody '\'' fuel (pos + 3) rest []
  | '"' :: rest                 => readShortStringBody '"' fuel (pos + 1) rest []
  | '\'' :: rest                => readShortStringBody '\'' fuel (pos + 1) rest []
  | _ => .error ⟨"expected string literal", pos⟩

/-! ## Numeric literals — [16] NumericLiteral

```
[19] INTEGER ::= [+-]? [0-9]+
[20] DECIMAL ::= [+-]? [0-9]* '.' [0-9]+
[21] DOUBLE  ::= [+-]? ( [0-9]+ '.' [0-9]* EXPONENT
                       | '.' [0-9]+ EXPONENT
                       | [0-9]+ EXPONENT )
[154s] EXPONENT ::= [eE] [+-]? [0-9]+
```
The LEXICAL FORM is preserved exactly as written (RDF 1.1 Concepts
§3.3: the literal's lexical form is the character string, not a
normalised numeral) and the datatype follows from the shape.

The only subtle case is a `.` after digits: it is the fraction point
when a digit follows, ALSO the fraction point when a genuine EXPONENT
follows (`123.E+1` is a legal DOUBLE with zero fraction digits), and
otherwise the statement terminator — so `123.` is INTEGER `123` plus a
`.`. Port of `parse_numeric_literal` / `is_valid_exponent_at`. -/

/-- Does a well-formed [154s] EXPONENT start here? Port of
`is_valid_exponent_at`. -/
def isValidExponentAt : List Char → Bool
  | e :: rest =>
      (e == 'e' || e == 'E') &&
      (match rest with
       | s :: d :: _ => if s == '+' || s == '-' then isDigitChar d else isDigitChar s
       | [d]         => isDigitChar d
       | []          => false)
  | [] => false

/-- The numeric-character collector. Returns the collected characters,
whether a `.` and an exponent were seen, and the remaining input. Port
of the F* inner `collect_num`, fuel and all. -/
def collectNum : Nat → Nat → List Char → List Char → Bool → Bool →
    (List Char × Bool × Bool × Nat × List Char)
  | 0,        pos, cs, acc, hasDot, hasE => (acc.reverse, hasDot, hasE, pos, cs)
  | fuel + 1, pos, cs, acc, hasDot, hasE =>
      match cs with
      | [] => (acc.reverse, hasDot, hasE, pos, cs)
      | c :: rest =>
          if isDigitChar c then collectNum fuel (pos + 1) rest (c :: acc) hasDot hasE
          else if c == '.' && !hasDot && !hasE then
            match rest with
            | [] => (acc.reverse, hasDot, hasE, pos, cs)
            | n :: _ =>
                if isDigitChar n then collectNum fuel (pos + 1) rest (c :: acc) true hasE
                else if isValidExponentAt rest then
                  collectNum fuel (pos + 1) rest (c :: acc) true hasE
                else (acc.reverse, hasDot, hasE, pos, cs)
          else if (c == 'e' || c == 'E') && !hasE then
            match rest with
            | [] => (acc.reverse, hasDot, hasE, pos, cs)
            | n :: rest2 =>
                if n == '+' || n == '-' then
                  collectNum fuel (pos + 2) rest2 (n :: c :: acc) hasDot true
                else if isDigitChar n then
                  collectNum fuel (pos + 1) rest (c :: acc) hasDot true
                else (acc.reverse, hasDot, hasE, pos, cs)
          else (acc.reverse, hasDot, hasE, pos, cs)

/-- [16] NumericLiteral. Port of `parse_numeric_literal`. -/
def readNumericLiteral (pos : Nat) (cs : List Char) :
    Except ParseError ((String × WfIri) × Nat × List Char) :=
  let (signStr, pos0, cs0) :=
    match cs with
    | '+' :: r => ("+", pos + 1, r)
    | '-' :: r => ("-", pos + 1, r)
    | _        => ("", pos, cs)
  let fuel := cs0.length + 1
  match cs0 with
  | '.' :: rest =>
      match rest with
      | d :: _ =>
          if !isDigitChar d then .error ⟨"expected digit after '.'", pos0⟩
          else
            let (acc, _, hasE, pos', rest') := collectNum fuel (pos0 + 1) rest ['.'] true false
            .ok ((signStr ++ String.ofList acc, if hasE then xsdDouble else xsdDecimal), pos', rest')
      | [] => .error ⟨"expected digit after '.'", pos0⟩
  | _ =>
      let (acc, hasDot, hasE, pos', rest') := collectNum fuel pos0 cs0 [] false false
      if acc.isEmpty then .error ⟨"expected numeric literal", pos⟩
      else
        let dt := if hasE then xsdDouble else if hasDot then xsdDecimal else xsdInteger
        .ok ((signStr ++ String.ofList acc, dt), pos', rest')

/-! ## Boolean literals and the `a` keyword -/

/-- After a bare keyword, a PN_CHARS character means the keyword was
really the head of a longer name (`trueish` is not `true`). Port of
`pn_chars_follows`. -/
def pnCharsFollows : List Char → Bool
  | c :: _ => isPnChars c
  | []     => false

/-- [133s] `BooleanLiteral ::= 'true' | 'false'`. Port of
`parse_boolean_literal`. -/
def readBooleanLiteral (pos : Nat) (cs : List Char) :
    Except ParseError (Literal × Nat × List Char) :=
  let lit (s : String) : Literal :=
    { lexicalForm := s, datatype := xsdBoolean, langTag := none, direction := none }
  match cs with
  | 't' :: 'r' :: 'u' :: 'e' :: rest =>
      if pnCharsFollows rest then .error ⟨"expected boolean literal", pos⟩
      else .ok (lit "true", pos + 4, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest =>
      if pnCharsFollows rest then .error ⟨"expected boolean literal", pos⟩
      else .ok (lit "false", pos + 5, rest)
  | _ => .error ⟨"expected boolean literal", pos⟩

/-- `rdf:type` — what [9] verb's `a` abbreviates. -/
def rdfType : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩
/-- `rdf:first` — [15] collection's element property. -/
def rdfFirst : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#first", rfl⟩
/-- `rdf:rest` — [15] collection's tail property. -/
def rdfRest : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", rfl⟩
/-- `rdf:nil` — the empty collection. -/
def rdfNil : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", rfl⟩
/-- `rdf:reifies` — RDF 1.2's reifier property (`~` and `{| |}`). -/
def rdfReifies : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies", rfl⟩

/-- The `a` of [9] `verb ::= predicate | 'a'`. It is a keyword only
when followed by whitespace, a comment, or end of input — otherwise
`a:b` would lose its prefix. Port of `parse_a_keyword`. -/
def readAKeyword (pos : Nat) (cs : List Char) : Except ParseError (WfIri × Nat × List Char) :=
  match cs with
  | 'a' :: rest =>
      match rest with
      | []     => .ok (rdfType, pos + 1, [])
      | c :: _ =>
          if isTurtleWs c || c == '#' then .ok (rdfType, pos + 1, rest)
          else .error ⟨"expected 'a' keyword", pos⟩
  | _ => .error ⟨"expected 'a'", pos⟩

/-! ## RDFLiteral — [128s] `String (LANGTAG | '^^' iri)?`

Port of `parse_turtle_literal`. Under `.rdf12` the language tag may
carry the `--ltr`/`--rtl` base-direction suffix (`readLangDir12`,
`Syntax.Lexing`); under `.rdf11` it may not. -/

def readRdfLiteral (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (WfLiteral × Nat × List Char) :=
  match readTurtleString pos cs with
  | .error e => .error e
  | .ok (lex, pos1, rest1) =>
      let plain : Literal :=
        { lexicalForm := lex, datatype := xsdString, langTag := none, direction := none }
      match rest1 with
      | '@' :: _ =>
          (match st.mode with
           | .rdf11 =>
               match readLangTag pos1 rest1 with
               | .error e => .error e
               | .ok (tag, pos2, rest2) =>
                   match mkLiteral pos1
                       { lexicalForm := lex, datatype := rdfLangString,
                         langTag := some tag, direction := none } with
                   | .error e => .error e
                   | .ok wl   => .ok (wl, pos2, rest2)
           | .rdf12 =>
               match readLangDir12 pos1 rest1 with
               | .error e => .error e
               | .ok ((tag, dopt), pos2, rest2) =>
                   let dt := match dopt with
                     | none   => rdfLangString
                     | some _ => rdfDirLangString
                   let dir := dopt.map (fun b => if b then TextDirection.rtl else TextDirection.ltr)
                   match mkLiteral pos1
                       { lexicalForm := lex, datatype := dt, langTag := some tag,
                         direction := dir } with
                   | .error e => .error e
                   | .ok wl   => .ok (wl, pos2, rest2))
      | '^' :: '^' :: rest2 =>
          (match readTurtleIri st (pos1 + 2) rest2 with
           | .error e => .error e
           | .ok (dt, pos2, rest3) =>
               match mkLiteral pos1
                   { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
               | .error e => .error e
               | .ok wl   => .ok (wl, pos2, rest3))
      | _ =>
          match mkLiteral pos1 plain with
          | .error e => .error e
          | .ok wl   => .ok (wl, pos1, rest1)

/-! ## The mutually-recursive term block

`object`, `collection`, `objectList`, `predicateObjectList`, `verb`,
`blankNodePropertyList`, and (RDF 1.2) `tripleTerm` / annotations are
all mutually recursive — a collection contains objects, an object may
be a `[ … ]` whose predicateObjectList contains objects, and so on. The
F* source carries one `decreases fuel` block for exactly this set; so
does this port. Fuel is seeded from the remaining input length at the
document level, so it bounds NESTING depth and can never bind before
the input is consumed.

An object production yields more than a term: a `[ … ]` or a `( … )`
also emits SIDE TRIPLES (the property list's own triples, the
collection's `rdf:first`/`rdf:rest` chain) and advances the blank-node
counter. `ObjResult` is the F* `object_result` record. -/

/-- Port of the F* `object_result` record. -/
structure ObjResult where
  term    : Term
  triples : List Triple
  state   : TurtleState

/-- Port of the F* `subject_result` record. `isBnodePropList` records
whether the subject was a `[ … ]` blankNodePropertyList, which [6]
`triples` allows to stand as a whole statement with no
predicateObjectList — a collection may NOT (TriG `trig-syntax-bad-list-03`:
`{ ( 1 2 3 ) }` must be rejected). -/
structure SubjResult where
  subject         : Subject
  triples         : List Triple
  state           : TurtleState
  isBnodePropList : Bool

/-- A term standing in reifier position becomes a subject. -/
def subjectOfTerm : Term → Subject
  | .iri i   => .iri i
  | .bnode b => .bnode b
  | _        => .bnode "reifier-non-node"

/-- [31] `ttSubject ::= iri | BlankNode` — the subject slot of a triple
term: an IRI, a `_:label`, or the anonymous `[]` (never a nested triple
term, never a non-empty `[ … ]`). Port of `parse_tt_subject`, widened
to admit ANON as the grammar does (the F* source rejects `[]` here —
see `PORT_NOTES.md`). -/
def readTtSubject (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (Subject × TurtleState × Nat × List Char) :=
  match cs with
  | '<' :: '<' :: _ =>
      .error ⟨"a triple term's subject may not be a triple term or a reified triple", pos⟩
  | '_' :: ':' :: _ =>
      (match readTurtleBnode pos cs with
       | .error e => .error e
       | .ok (b, pos', rest) => .ok (.bnode b, st, pos', rest))
  | '[' :: rest =>
      let (p2, r2) := tws (pos + 1) rest
      (match r2 with
       | ']' :: r3 =>
           let (b, st') := st.freshBnode
           .ok (.bnode b, st', p2 + 1, r3)
       | _ => .error ⟨"blank node property list not allowed in a triple term", pos⟩)
  | _ =>
      match readTurtleIri st pos cs with
      | .error e => .error e
      | .ok (i, pos', rest) => .ok (.iri i, st, pos', rest)

/-- [9] `verb ::= predicate | 'a'`. Port of `parse_turtle_predicate`. -/
def readVerb (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (WfIri × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"recursion limit in verb", pos⟩
  | _ + 1 =>
    match readAKeyword pos cs with
    | .ok r    => .ok r
    | .error _ => readTurtleIri st pos cs

/-- A literal in one of the three forms [13] admits: an RDFLiteral
(string), a BooleanLiteral, or a NumericLiteral. Shared by the
triple-term and reified-triple object slots, which admit literals but
not the `[ … ]` / `( … )` constructions. -/
def readAnyLiteral (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (WfLiteral × Nat × List Char) :=
  match cs with
  | '"' :: _ | '\'' :: _ => readRdfLiteral st pos cs
  | _ =>
      match readBooleanLiteral pos cs with
      | .ok (l, pos', rest) =>
          (match mkLiteral pos l with
           | .error e => .error e
           | .ok wl => .ok (wl, pos', rest))
      | .error _ =>
          match readNumericLiteral pos cs with
          | .error e => .error e
          | .ok ((lex, dt), pos', rest) =>
              match mkLiteral pos
                  { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
              | .error e => .error e
              | .ok wl => .ok (wl, pos', rest)

/-! ## RDF 1.2 triple terms — [30] tripleTerm, [32] ttObject

`tripleTerm ::= '<<(' ttSubject verb ttObject ')>>'` with
`ttObject ::= iri | BlankNode | literal | tripleTerm`. A triple term
emits NO triples of its own — it is a term. The only recursion is the
object slot nesting another triple term, so this is a self-contained
fuel recursion outside the main mutual block, exactly as the F* source
keeps `parse_tt_object` / `parse_turtle_triple_term` apart. -/

mutual

/-- [32] `ttObject`. Port of `parse_tt_object`; `[]` admitted as the
grammar's ANON (the F* source rejects it). -/
def readTtObject (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (Term × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"triple-term nesting too deep", pos⟩
  | f + 1 =>
    match cs with
    | '<' :: '<' :: '(' :: rest => readTripleTerm f st (pos + 3) rest
    | '<' :: '<' :: _ =>
        .error ⟨"a reified triple is not allowed inside a triple term", pos⟩
    | '<' :: _ =>
        (match readTurtleIri st pos cs with
         | .error e => .error e
         | .ok (i, pos', rest) => .ok (.iri i, st, pos', rest))
    | '_' :: ':' :: _ =>
        (match readTurtleBnode pos cs with
         | .error e => .error e
         | .ok (b, pos', rest) => .ok (.bnode b, st, pos', rest))
    | '[' :: rest =>
        let (p2, r2) := tws (pos + 1) rest
        (match r2 with
         | ']' :: r3 =>
             let (b, st') := st.freshBnode
             .ok (.bnode b, st', p2 + 1, r3)
         | _ => .error ⟨"blank node property list not allowed in a triple term", pos⟩)
    | '(' :: _ => .error ⟨"collection not allowed in a triple term", pos⟩
    | '"' :: _ | '\'' :: _ =>
        (match readRdfLiteral st pos cs with
         | .error e => .error e
         | .ok (l, pos', rest) => .ok (.literal l, st, pos', rest))
    | _ =>
        match readAnyLiteral st pos cs with
        | .ok (l, pos', rest) => .ok (.literal l, st, pos', rest)
        | .error _ =>
            match readTurtleIri st pos cs with
            | .error e => .error e
            | .ok (i, pos', rest) => .ok (.iri i, st, pos', rest)
termination_by fuel

/-- [30] `tripleTerm`, `pos`/`cs` just after the opening `<<(`. Port of
`parse_turtle_triple_term`. Returns the term and the state (ANON
subjects/objects advance the blank-node counter); no side triples. -/
def readTripleTerm (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (Term × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"triple-term nesting too deep", pos⟩
  | f + 1 =>
    let (p1, r1) := tws pos cs
    match readTtSubject st p1 r1 with
    | .error e => .error e
    | .ok (s, st1, p2, r2) =>
        let (p3, r3) := tws p2 r2
        match readVerb f st1 p3 r3 with
        | .error e => .error e
        | .ok (p, p4, r4) =>
            let (p5, r5) := tws p4 r4
            match readTtObject f st1 p5 r5 with
            | .error e => .error e
            | .ok (o, st2, p6, r6) =>
                let (p7, r7) := tws p6 r6
                match r7 with
                | ')' :: '>' :: '>' :: r8 => .ok (.tripleTerm s p o, st2, p7 + 3, r8)
                | _ => .error ⟨"expected ')>>' closing triple term", p7⟩
termination_by fuel

end

/-! ## RDF 1.2 reifiers and reified triples — [27]–[29], [33]

`reifier ::= '~' (iri | BlankNode)?` names the reifier of a reified
triple or of an annotated triple; with nothing after the `~` a fresh
blank node is minted. `reifiedTriple ::= '<<' rtSubject verb rtObject
reifier? '>>'` is SUGAR: it denotes its reifier and emits
`reifier rdf:reifies <<( s p o )>>`. `rtSubject` / `rtObject` are
narrower than [10] / [12]: an IRI, a `_:label`, an EMPTY `[]`, a
nested reified triple, and (object only) a literal or a triple term —
never a collection or a non-empty property list
(turtle12-syntax-bad-06 / bad-07). Like the triple-term block this is
a self-contained fuel recursion that never re-enters the collection /
annotation / object-list machinery. -/

/-- [33] `reifier`, `pos`/`cs` at the `~`. Port of `parse_reifier`:
`_:label`, `[]`, an IRIREF or a prefixed name name the reifier; anything
else (a following `>>`, `{|`, `,`, `;`, `.`, …) means "no explicit
reifier" and a fresh blank node is minted. The F* source does not
accept `[]` here; the grammar's BlankNode does. -/
def readReifier (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (Subject × TurtleState × Nat × List Char) :=
  match cs with
  | '~' :: rest =>
      let (p1, r1) := tws (pos + 1) rest
      let fresh : Except ParseError (Subject × TurtleState × Nat × List Char) :=
        let (b, st') := st.freshBnode
        .ok (.bnode b, st', p1, r1)
      (match r1 with
       | '_' :: ':' :: _ =>
           (match readTurtleBnode p1 r1 with
            | .error e => .error e
            | .ok (b, p2, r2) => .ok (.bnode b, st, p2, r2))
       | '[' :: r2 =>
           let (p3, r3) := tws (p1 + 1) r2
           (match r3 with
            | ']' :: r4 =>
                let (b, st') := st.freshBnode
                .ok (.bnode b, st', p3 + 1, r4)
            | _ => .error ⟨"blank node property list not allowed as a reifier", p1⟩)
       | '<' :: _ =>
           (match readTurtleIri st p1 r1 with
            | .error e => .error e
            | .ok (i, p2, r2) => .ok (.iri i, st, p2, r2))
       | c :: _ =>
           if isNameStartChar c || c == ':' then
             (match readTurtleIri st p1 r1 with
              | .ok (i, p2, r2) => .ok (.iri i, st, p2, r2)
              | .error _ => fresh)
           else fresh
       | [] => fresh)
  | _ => .error ⟨"expected '~'", pos⟩

mutual

/-- [28] `rtSubject ::= iri | BlankNode | reifiedTriple`. Port of
`parse_rt_subject`. -/
def readRtSubject (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (Subject × List Triple × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"reified-triple nesting too deep", pos⟩
  | f + 1 =>
    match cs with
    | [] => .error ⟨"expected reified-triple subject", pos⟩
    | '<' :: '<' :: '(' :: _ =>
        .error ⟨"triple term not allowed as reified-triple subject", pos⟩
    | '<' :: '<' :: _ =>
        (match readReifiedTriple f st pos cs with
         | .error e => .error e
         | .ok (o, pos', rest) => .ok (subjectOfTerm o.term, o.triples, o.state, pos', rest))
    | '_' :: ':' :: _ =>
        (match readTurtleBnode pos cs with
         | .error e => .error e
         | .ok (b, pos', rest) => .ok (.bnode b, [], st, pos', rest))
    | '[' :: rest =>
        let (p2, r2) := tws (pos + 1) rest
        (match r2 with
         | ']' :: r3 =>
             let (b, st') := st.freshBnode
             .ok (.bnode b, [], st', p2 + 1, r3)
         | _ => .error ⟨"blank node property list not allowed in a reified triple", pos⟩)
    | '(' :: _ => .error ⟨"collection not allowed in a reified triple", pos⟩
    | _ =>
        match readTurtleIri st pos cs with
        | .error e => .error e
        | .ok (i, pos', rest) => .ok (.iri i, [], st, pos', rest)
termination_by fuel

/-- [29] `rtObject ::= iri | BlankNode | literal | tripleTerm |
reifiedTriple`. Port of `parse_rt_object`. -/
def readRtObject (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (Term × List Triple × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"reified-triple nesting too deep", pos⟩
  | f + 1 =>
    match cs with
    | [] => .error ⟨"expected reified-triple object", pos⟩
    | '<' :: '<' :: '(' :: rest =>
        (match readTripleTerm f st (pos + 3) rest with
         | .error e => .error e
         | .ok (t, st', pos', rest') => .ok (t, [], st', pos', rest'))
    | '<' :: '<' :: _ =>
        (match readReifiedTriple f st pos cs with
         | .error e => .error e
         | .ok (o, pos', rest) => .ok (o.term, o.triples, o.state, pos', rest))
    | '_' :: ':' :: _ =>
        (match readTurtleBnode pos cs with
         | .error e => .error e
         | .ok (b, pos', rest) => .ok (.bnode b, [], st, pos', rest))
    | '[' :: rest =>
        let (p2, r2) := tws (pos + 1) rest
        (match r2 with
         | ']' :: r3 =>
             let (b, st') := st.freshBnode
             .ok (.bnode b, [], st', p2 + 1, r3)
         | _ => .error ⟨"blank node property list not allowed in a reified triple", pos⟩)
    | '(' :: _ => .error ⟨"collection not allowed in a reified triple", pos⟩
    | '"' :: _ | '\'' :: _ =>
        (match readRdfLiteral st pos cs with
         | .error e => .error e
         | .ok (l, pos', rest) => .ok (.literal l, [], st, pos', rest))
    | _ =>
        match readAnyLiteral st pos cs with
        | .ok (l, pos', rest) => .ok (.literal l, [], st, pos', rest)
        | .error _ =>
            match readTurtleIri st pos cs with
            | .error e => .error e
            | .ok (i, pos', rest) => .ok (.iri i, [], st, pos', rest)
termination_by fuel

/-- [27] `reifiedTriple`, `pos`/`cs` at the opening `<<` (NOT `<<(`).
The result's `term` is the reifier; its `triples` are the nested
reified triples' `rdf:reifies` triples followed by this one's. Port of
`parse_reified_triple`. -/
def readReifiedTriple (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (ObjResult × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"reified-triple nesting too deep", pos⟩
  | f + 1 =>
    match cs with
    | '<' :: '<' :: '(' :: _ => .error ⟨"a triple term is not a reified triple", pos⟩
    | '<' :: '<' :: rest =>
        let (p1, r1) := tws (pos + 2) rest
        match readRtSubject f st p1 r1 with
        | .error e => .error e
        | .ok (s, sTriples, st1, p2, r2) =>
            let (p3, r3) := tws p2 r2
            match readVerb f st1 p3 r3 with
            | .error e => .error e
            | .ok (p, p4, r4) =>
                let (p5, r5) := tws p4 r4
                match readRtObject f st1 p5 r5 with
                | .error e => .error e
                | .ok (o, oTriples, st2, p6, r6) =>
                    let (p7, r7) := tws p6 r6
                    let tt : Term := .tripleTerm s p o
                    let side := sTriples ++ oTriples
                    let finish (r : Subject) (st3 : TurtleState) (p8 : Nat) (r8 : List Char) :
                        Except ParseError (ObjResult × Nat × List Char) :=
                      let (p9, r9) := tws p8 r8
                      match r9 with
                      | '>' :: '>' :: r10 =>
                          .ok (⟨r.toTerm, side ++ [{ s := r, p := rdfReifies, o := tt }], st3⟩,
                               p9 + 2, r10)
                      | _ => .error ⟨"expected '>>' closing reified triple", p9⟩
                    match r7 with
                    | '~' :: _ =>
                        (match readReifier st2 p7 r7 with
                         | .error e => .error e
                         | .ok (r, st3, p8, r8) => finish r st3 p8 r8)
                    | _ =>
                        let (b, st3) := st2.freshBnode
                        finish (.bnode b) st3 p7 r7
    | _ => .error ⟨"expected '<<'", pos⟩
termination_by fuel

end

mutual

/-- [12] object — iri | BlankNode | collection | blankNodePropertyList
| literal, plus (under `.rdf12`) a triple term `<<( s p o )>>`. Port of
`parse_turtle_object`. -/
def readObject (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (ObjResult × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"recursion limit in object", pos⟩
  | f + 1 =>
    match cs with
    | [] => .error ⟨"expected object", pos⟩
    | '<' :: '<' :: '(' :: rest =>
        if st.mode == .rdf12 then
          (match readTripleTerm f st (pos + 3) rest with
           | .error e => .error e
           | .ok (t, st', pos', rest') => .ok (⟨t, [], st'⟩, pos', rest'))
        else .error ⟨"triple term <<( )>> requires RDF 1.2 mode", pos⟩
    | '<' :: '<' :: _ =>
        -- [27] reifiedTriple in object position (RDF 1.2 only).
        if st.mode == .rdf12 then readReifiedTriple f st pos cs
        else .error ⟨"reified triple << >> requires RDF 1.2 mode", pos⟩
    | '<' :: _ =>
        (match readTurtleIri st pos cs with
         | .error e => .error e
         | .ok (i, pos', rest) => .ok (⟨.iri i, [], st⟩, pos', rest))
    | '_' :: ':' :: _ =>
        (match readTurtleBnode pos cs with
         | .error e => .error e
         | .ok (b, pos', rest) => .ok (⟨.bnode b, [], st⟩, pos', rest))
    | '"' :: _ | '\'' :: _ =>
        (match readRdfLiteral st pos cs with
         | .error e => .error e
         | .ok (l, pos', rest) => .ok (⟨.literal l, [], st⟩, pos', rest))
    | '[' :: rest =>
        -- [162s] ANON `[ WS* ]`, or [14] blankNodePropertyList.
        let (b, st1) := st.freshBnode
        let (p2, r2) := tws (pos + 1) rest
        (match r2 with
         | ']' :: r3 => .ok (⟨.bnode b, [], st1⟩, p2 + 1, r3)
         | _ =>
             match readPredicateObjectList f st1 (.bnode b) p2 r2 with
             | .error e => .error e
             | .ok (ts, st2, p3, r3) =>
                 let (p4, r4) := tws p3 r3
                 match r4 with
                 | ']' :: r5 => .ok (⟨.bnode b, ts, st2⟩, p4 + 1, r5)
                 | _ => .error ⟨"expected ']' closing blank node property list", p4⟩)
    | '(' :: rest => readCollection f st (pos + 1) rest
    | _ =>
        -- [133s] BooleanLiteral, then [16] NumericLiteral, then a
        -- PrefixedName. The order is the F* source's and matters:
        -- `true`/`false` would otherwise scan as local names.
        (match readBooleanLiteral pos cs with
         | .ok (l, pos', rest) =>
             (match mkLiteral pos l with
              | .error e => .error e
              | .ok wl => .ok (⟨.literal wl, [], st⟩, pos', rest))
         | .error _ =>
             match readNumericLiteral pos cs with
             | .ok ((lex, dt), pos', rest) =>
                 (match mkLiteral pos
                     { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
                  | .error e => .error e
                  | .ok wl => .ok (⟨.literal wl, [], st⟩, pos', rest))
             | .error _ =>
                 match readTurtleIri st pos cs with
                 | .error e => .error e
                 | .ok (i, pos', rest) => .ok (⟨.iri i, [], st⟩, pos', rest))
termination_by fuel

/-- [15] `collection ::= '(' object* ')'`, encoded as an
`rdf:first`/`rdf:rest` chain terminated by `rdf:nil` (Turtle §2.8). An
EMPTY collection is the IRI `rdf:nil` itself and emits no triples.
`pos`/`cs` start just after the opening `(`. Port of
`parse_collection`. -/
def readCollection (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (ObjResult × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"recursion limit in collection", pos⟩
  | f + 1 =>
    let (p1, r1) := tws pos cs
    match r1 with
    | []        => .error ⟨"unterminated collection (expected ')')", p1⟩
    | ')' :: r2 => .ok (⟨.iri rdfNil, [], st⟩, p1 + 1, r2)
    | _ =>
        match readObject f st p1 r1 with
        | .error e => .error e
        | .ok (first, p2, r2) =>
            let (node, st2) := first.state.freshBnode
            let nodeSubj : Subject := .bnode node
            match readCollectionRest f st2 p2 r2 with
            | .error e => .error e
            | .ok (restTriples, restTerm, st3, p3, r3) =>
                .ok (⟨.bnode node,
                      first.triples ++
                        ({ s := nodeSubj, p := rdfFirst, o := first.term } ::
                         { s := nodeSubj, p := rdfRest,  o := restTerm } :: restTriples),
                      st3⟩, p3, r3)
termination_by fuel

/-- The tail of a collection after its first element. Returns the tail's
triples, the term standing for the tail (`rdf:nil` or the next node's
blank node), and the advanced state. Port of `parse_collection_rest`. -/
def readCollectionRest (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (List Triple × Term × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"recursion limit in collection tail", pos⟩
  | f + 1 =>
    let (p1, r1) := tws pos cs
    match r1 with
    | []        => .error ⟨"unterminated collection (expected ')')", p1⟩
    | ')' :: r2 => .ok ([], .iri rdfNil, st, p1 + 1, r2)
    | _ =>
        match readObject f st p1 r1 with
        | .error e => .error e
        | .ok (next, p2, r2) =>
            let (node, st2) := next.state.freshBnode
            let nodeSubj : Subject := .bnode node
            match readCollectionRest f st2 p2 r2 with
            | .error e => .error e
            | .ok (restTriples, restTerm, st3, p3, r3) =>
                .ok (next.triples ++
                       ({ s := nodeSubj, p := rdfFirst, o := next.term } ::
                        { s := nodeSubj, p := rdfRest,  o := restTerm } :: restTriples),
                     .bnode node, st3, p3, r3)
termination_by fuel

/-- [8] `objectList ::= object (',' object)*`, emitting one triple per
object against the given subject and verb. Under `.rdf12` each object
may be followed by an RDF 1.2 annotation sequence. Port of
`parse_object_list_rev`; the accumulator is reversed by the caller. -/
def readObjectList (fuel : Nat) (st : TurtleState) (subj : Subject) (pred : WfIri)
    (pos : Nat) (cs : List Char) (acc : List Triple) :
    Except ParseError (List Triple × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"recursion limit in object list", pos⟩
  | f + 1 =>
    match readObject f st pos cs with
    | .error e => .error e
    | .ok (o, p1, r1) =>
        let acc0 := acc ++ o.triples ++ [{ s := subj, p := pred, o := o.term }]
        match (if o.state.mode == .rdf12 then
                 readAnnotations f o.state subj pred o.term p1 r1 none
               else .ok ([], o.state, p1, r1)) with
        | .error e => .error e
        | .ok (annTriples, stA, p1a, r1a) =>
            let acc1 := acc0 ++ annTriples
            let (p2, r2) := tws p1a r1a
            match r2 with
            | ',' :: r3 =>
                let (p4, r4) := tws (p2 + 1) r3
                readObjectList f stA subj pred p4 r4 acc1
            | _ => .ok (acc1, stA, p2, r2)
termination_by fuel

/-- RDF 1.2 annotation sequence after an object:
`(reifier | '{|' predicateObjectList '|}')*` with
`reifier ::= '~' (iri | BlankNode)?`. A `~` emits
`reifier rdf:reifies <<( s p o )>>` and becomes the PENDING reifier; an
annotation block reuses a pending reifier or mints one, and hangs its
predicateObjectList off it. Port of `parse_annotations`. -/
def readAnnotations (fuel : Nat) (st : TurtleState) (bs : Subject) (bp : WfIri) (bo : Term)
    (pos : Nat) (cs : List Char) (pending : Option Subject) :
    Except ParseError (List Triple × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .ok ([], st, pos, cs)
  | f + 1 =>
    let (p1, r1) := tws pos cs
    match r1 with
    | '~' :: _ =>
        -- [33] reifier: `~ :r`, `~ <r>`, `~ _:r`, `~ []`, or a bare `~`.
        (match readReifier st p1 r1 with
         | .error e => .error e
         | .ok (rsubj, st1, p3, r3) =>
             let reif : Triple := { s := rsubj, p := rdfReifies, o := .tripleTerm bs bp bo }
             match readAnnotations f st1 bs bp bo p3 r3 (some rsubj) with
             | .error e => .error e
             | .ok (rest, st2, p4, r4) => .ok (reif :: rest, st2, p4, r4))
    | '{' :: '|' :: r2 =>
        let (rsubj, st1, pre) :=
          match pending with
          | some r => (r, st, ([] : List Triple))
          | none =>
              let (b, stb) := st.freshBnode
              ((.bnode b : Subject), stb,
               [{ s := (.bnode b : Subject), p := rdfReifies, o := .tripleTerm bs bp bo }])
        let (p2, r2') := tws (p1 + 2) r2
        (match r2' with
         | '|' :: '}' :: _ => .error ⟨"empty annotation block", p1⟩
         | _ =>
             match readPredicateObjectList f st1 rsubj p2 r2' with
             | .error e => .error e
             | .ok (blk, st2, p3, r3) =>
                 let (p4, r4) := tws p3 r3
                 match r4 with
                 | '|' :: '}' :: r5 =>
                     (match readAnnotations f st2 bs bp bo (p4 + 2) r5 none with
                      | .error e => .error e
                      | .ok (rest, st3, p5, r5') => .ok (pre ++ blk ++ rest, st3, p5, r5'))
                 | _ => .error ⟨"expected '|}' closing annotation block", p4⟩)
    | _ => .ok ([], st, p1, r1)
termination_by fuel

/-- [7] `predicateObjectList ::= verb objectList (';' (verb objectList)?)*`.
Port of `parse_predicate_object_list_rev`. A `;` may be followed by
another verb, by more `;`, or by a terminator — `.` `]` `|}` `}` — the
last of which is TriG's graph-block close (the F* source's issue #434). -/
def readPredicateObjectList (fuel : Nat) (st : TurtleState) (subj : Subject)
    (pos : Nat) (cs : List Char) :
    Except ParseError (List Triple × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"recursion limit in predicate-object list", pos⟩
  | f + 1 =>
    match readVerb f st pos cs with
    | .error e => .error e
    | .ok (pred, p1, r1) =>
        let (p2, r2) := tws p1 r1
        match readObjectList f st subj pred p2 r2 [] with
        | .error e => .error e
        | .ok (ts, st1, p3, r3) =>
            let (p4, r4) := tws p3 r3
            match r4 with
            | ';' :: r5 =>
                let (p6, r6) := tws (p4 + 1) r5
                (match r6 with
                 | [] => .ok (ts, st1, p6, r6)
                 | c :: _ =>
                     if c == ';' then
                       match readPredicateObjectListMore f st1 subj p6 r6 with
                       | .error e => .error e
                       | .ok (more, st2, p7, r7) => .ok (ts ++ more, st2, p7, r7)
                     else if c == '.' || c == ']' || c == '|' || c == '}' then
                       .ok (ts, st1, p6, r6)
                     else
                       match readPredicateObjectList f st1 subj p6 r6 with
                       | .error e => .error e
                       | .ok (more, st2, p7, r7) => .ok (ts ++ more, st2, p7, r7))
            | _ => .ok (ts, st1, p4, r4)
termination_by fuel

/-- Skip a run of `;` separators and, if a verb follows, keep parsing.
Port of `parse_trailing_semicolons_rev`. -/
def readPredicateObjectListMore (fuel : Nat) (st : TurtleState) (subj : Subject)
    (pos : Nat) (cs : List Char) :
    Except ParseError (List Triple × TurtleState × Nat × List Char) :=
  match fuel with
  | 0 => .ok ([], st, pos, cs)
  | f + 1 =>
    match cs with
    | ';' :: rest =>
        let (p2, r2) := tws (pos + 1) rest
        (match r2 with
         | [] => .ok ([], st, p2, r2)
         | c :: _ =>
             if c == ';' || c == '.' || c == ']' || c == '|' || c == '}' then
               if c == ';' then readPredicateObjectListMore f st subj p2 r2
               else .ok ([], st, p2, r2)
             else readPredicateObjectList f st subj p2 r2)
    | _ => .ok ([], st, pos, cs)
termination_by fuel

/-- [10] subject, plus [14] blankNodePropertyList and [15] collection
in subject position. Port of `parse_turtle_subject`. -/
def readSubjectTurtle (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (SubjResult × Nat × List Char) :=
  match fuel with
  | 0 => .error ⟨"recursion limit in subject", pos⟩
  | f + 1 =>
    match cs with
    | [] => .error ⟨"expected subject", pos⟩
    | '<' :: '<' :: '(' :: _ =>
        .error ⟨"triple term is not allowed as a subject", pos⟩
    | '<' :: '<' :: _ =>
        -- [27] reifiedTriple as subject (RDF 1.2 only). Like a `[ … ]`
        -- property list it may stand as a whole statement — just its
        -- `rdf:reifies` triple — with no predicateObjectList
        -- (turtle12-syntax-basic-04: `<<:s :p :o>> .`).
        if st.mode == .rdf12 then
          (match readReifiedTriple f st pos cs with
           | .error e => .error e
           | .ok (o, pos', rest) =>
               .ok (⟨subjectOfTerm o.term, o.triples, o.state, true⟩, pos', rest))
        else .error ⟨"reified triple << >> requires RDF 1.2 mode", pos⟩
    | '<' :: _ =>
        (match readTurtleIri st pos cs with
         | .error e => .error e
         | .ok (i, pos', rest) => .ok (⟨.iri i, [], st, false⟩, pos', rest))
    | '_' :: ':' :: _ =>
        (match readTurtleBnode pos cs with
         | .error e => .error e
         | .ok (b, pos', rest) => .ok (⟨.bnode b, [], st, false⟩, pos', rest))
    | '[' :: rest =>
        let (b, st1) := st.freshBnode
        let (p2, r2) := tws (pos + 1) rest
        (match r2 with
         | ']' :: r3 => .ok (⟨.bnode b, [], st1, false⟩, p2 + 1, r3)
         | _ =>
             match readPredicateObjectList f st1 (.bnode b) p2 r2 with
             | .error e => .error e
             | .ok (ts, st2, p3, r3) =>
                 let (p4, r4) := tws p3 r3
                 match r4 with
                 | ']' :: r5 => .ok (⟨.bnode b, ts, st2, true⟩, p4 + 1, r5)
                 | _ => .error ⟨"expected ']' closing blank node property list", p4⟩)
    | '(' :: rest =>
        (match readCollection f st (pos + 1) rest with
         | .error e => .error e
         | .ok (o, pos', r) =>
             match o.term with
             | .iri i   => .ok (⟨.iri i, o.triples, o.state, false⟩, pos', r)
             | .bnode b => .ok (⟨.bnode b, o.triples, o.state, false⟩, pos', r)
             | _ => .error ⟨"collection did not produce a valid subject", pos⟩)
    | _ =>
        match readTurtleIri st pos cs with
        | .error e => .error e
        | .ok (i, pos', rest) => .ok (⟨.iri i, [], st, false⟩, pos', rest)

end

/-! ## Directives — [3] directive

`[4] prefixID ::= '@prefix' PNAME_NS IRIREF '.'`
`[5] base     ::= '@base' IRIREF '.'`
`[5s] sparqlPrefix ::= "PREFIX" PNAME_NS IRIREF`   (no '.', case-insensitive)
`[6s] sparqlBase   ::= "BASE" IRIREF`              (no '.', case-insensitive)

Both `@prefix`'s namespace IRI and `@base`'s value are resolved against
the base IN FORCE AT THAT POINT (Turtle §6.3/§6.4 — a document may
change its base part-way through, and each `@base` is relative to the
previous one). Port of `parse_at_prefix` / `parse_sparql_prefix` /
`parse_at_base` / `parse_sparql_base`. -/

/-- Match a literal keyword, case-insensitively when asked. Port of
`pstring` / `pstring_ci`. -/
def matchKeyword (ci : Bool) (kw : List Char) (cs : List Char) : Option (List Char) :=
  match kw, cs with
  | [],      rest    => some rest
  | k :: kt, c :: ct => if (if ci then k.toLower == c.toLower else k == c)
                        then matchKeyword ci kt ct else none
  | _ :: _,  []      => none

/-- `@prefix` / `PREFIX`. Returns the binding and the new position. -/
def readPrefixDirective (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError ((String × String) × Nat × List Char) :=
  let body (atForm : Bool) (kwLen : Nat) (rest : List Char) :
      Except ParseError ((String × String) × Nat × List Char) :=
    let (p1, r1) := tws (pos + kwLen) rest
    match readPnameNs p1 r1 with
    | .error e => .error e
    | .ok (ns, p2, r2) =>
        let (p3, r3) := tws p2 r2
        match readIriRef p3 r3 with
        | .error e => .error e
        | .ok (raw, p4, r4) =>
            let iri := st.resolve raw
            if atForm then
              let (p5, r5) := tws p4 r4
              match r5 with
              | '.' :: r6 => .ok ((ns, iri), p5 + 1, r6)
              | _ => .error ⟨"expected '.' after @prefix directive", p5⟩
            else .ok ((ns, iri), p4, r4)
  match matchKeyword false "@prefix".toList cs with
  | some rest => body true 7 rest
  | none =>
      match matchKeyword true "PREFIX".toList cs with
      | some rest => body false 6 rest
      | none => .error ⟨"not a prefix directive", pos⟩

/-- `@base` / `BASE`. -/
def readBaseDirective (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (String × Nat × List Char) :=
  let body (atForm : Bool) (kwLen : Nat) (rest : List Char) :
      Except ParseError (String × Nat × List Char) :=
    let (p1, r1) := tws (pos + kwLen) rest
    match readIriRef p1 r1 with
    | .error e => .error e
    | .ok (raw, p2, r2) =>
        let iri := st.resolve raw
        if atForm then
          let (p3, r3) := tws p2 r2
          match r3 with
          | '.' :: r4 => .ok (iri, p3 + 1, r4)
          | _ => .error ⟨"expected '.' after @base directive", p3⟩
        else .ok (iri, p2, r2)
  match matchKeyword false "@base".toList cs with
  | some rest => body true 5 rest
  | none =>
      match matchKeyword true "BASE".toList cs with
      | some rest => body false 4 rest
      | none => .error ⟨"not a base directive", pos⟩

/-! ## RDF 1.2 `VERSION` directive — [4a] version / sparqlVersion

`@version VERSION_STRING '.'` (at-form, trailing dot REQUIRED) and
`VERSION VERSION_STRING` (keyword form, case-insensitive like
`PREFIX` / `BASE`, NO dot). `VERSION_STRING` is a SHORT string
literal — a long `"""…"""` / `'''…'''` string or an unquoted token is
rejected (turtle12-version-bad-01..06); the string's content is not
validated (turtle12-version-08 accepts `"abc"`). The directive is
state-neutral. Port of `parse_version_short` /
`parse_version_directive`; reachable only under `.rdf12`. -/

/-- Exactly one short string literal, value discarded. -/
def readVersionString (pos : Nat) (cs : List Char) : Except ParseError (Nat × List Char) :=
  match cs with
  | '"' :: '"' :: '"' :: _ | '\'' :: '\'' :: '\'' :: _ =>
      .error ⟨"long string not allowed in VERSION directive", pos⟩
  | '"' :: _ | '\'' :: _ =>
      (match readTurtleString pos cs with
       | .error e => .error e
       | .ok (_, pos', rest) => .ok (pos', rest))
  | _ => .error ⟨"expected string literal in VERSION directive", pos⟩

/-- `@version "…" .` or `VERSION "…"`. Returns the new position. -/
def readVersionDirective (pos : Nat) (cs : List Char) : Except ParseError (Nat × List Char) :=
  match matchKeyword false "@version".toList cs with
  | some rest =>
      let (p1, r1) := tws (pos + 8) rest
      (match readVersionString p1 r1 with
       | .error e => .error e
       | .ok (p2, r2) =>
           let (p3, r3) := tws p2 r2
           match r3 with
           | '.' :: r4 => .ok (p3 + 1, r4)
           | _ => .error ⟨"expected '.' after @version directive", p3⟩)
  | none =>
      match matchKeyword true "VERSION".toList cs with
      | some rest =>
          let (p1, r1) := tws (pos + 7) rest
          readVersionString p1 r1
      | none => .error ⟨"not a version directive", pos⟩

/-! ## Statements and the document — [1] turtleDoc, [2] statement -/

/-- [2] `statement ::= directive | triples '.'`. Returns the statement's
triples and the (possibly updated) state. A statement may also end at a
`}` rather than a `.`, which is what lets TriG reuse this production
verbatim for the last statement of a graph block. Port of
`parse_turtle_statement`. -/
def readStatement (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) :
    Except ParseError (List Triple × TurtleState × Nat × List Char) :=
  let (p1, r1) := tws pos cs
  match r1 with
  | [] => .ok ([], st, p1, [])
  | _ =>
    match readPrefixDirective st p1 r1 with
    | .ok ((pfx, iri), p2, r2) =>
        .ok ([], { st with prefixes := (pfx, iri) :: st.prefixes }, p2, r2)
    | .error _ =>
        match readBaseDirective st p1 r1 with
        | .ok (b, p2, r2) => .ok ([], { st with baseIri := b }, p2, r2)
        | .error _ =>
            -- [4a] RDF 1.2 VERSION directive: state-neutral, `.rdf12` only.
            match (if st.mode == .rdf12 then readVersionDirective p1 r1
                   else .error ⟨"not RDF 1.2", p1⟩) with
            | .ok (p2, r2) => .ok ([], st, p2, r2)
            | .error _ =>
            match readSubjectTurtle fuel st p1 r1 with
            | .error e => .error e
            | .ok (sr, p2, r2) =>
                let (p3, r3) := tws p2 r2
                match r3 with
                | [] =>
                    if sr.isBnodePropList then .ok (sr.triples, sr.state, p3, [])
                    else .error ⟨"expected predicate after subject", p3⟩
                | '.' :: r4 =>
                    if sr.isBnodePropList then .ok (sr.triples, sr.state, p3 + 1, r4)
                    else .error ⟨"expected predicate after subject", p3⟩
                | '}' :: _ =>
                    if sr.isBnodePropList then .ok (sr.triples, sr.state, p3, r3)
                    else
                      (match readPredicateObjectList fuel sr.state sr.subject p3 r3 with
                       | .error e => .error e
                       | .ok (_, _, _, _) => .error ⟨"expected predicate after subject", p3⟩)
                | _ =>
                    match readPredicateObjectList fuel sr.state sr.subject p3 r3 with
                    | .error e => .error e
                    | .ok (ts, st2, p4, r4) =>
                        let all := sr.triples ++ ts
                        let (p5, r5) := tws p4 r4
                        match r5 with
                        | '.' :: r6 => .ok (all, st2, p5 + 1, r6)
                        | '}' :: _  => .ok (all, st2, p5, r5)
                        | _ => .error ⟨"expected '.' after triple", p5⟩

/-- [1] `turtleDoc ::= statement*`. STRICT: the first malformed
statement aborts the whole parse with its `ParseError` (the F* source's
`parse_turtle_*_strict` entry points; its lenient `parse_turtle`, which
returns whatever it managed before the error, is a CLI affordance and
is not ported — same spec/pragmatics split as `Syntax.NTriples`). Fuel
bounds the statement count; every statement consumes at least one
character, and the no-progress guard below turns a hypothetical
zero-width statement into a clean stop rather than a loop. -/
/- `accRev` is kept in reverse source order. Appending the previous complete
   graph for every statement made ordinary one-triple-per-line Turtle
   quadratic; prepend only the newly parsed statement and reverse once at the
   terminal boundary instead. -/
def parseStatements : Nat → TurtleState → Nat → List Char → List Triple →
    Except ParseError (List Triple × TurtleState)
  | 0,        st, _,   _,  accRev => .ok (accRev.reverse, st)
  | fuel + 1, st, pos, cs, accRev =>
      let (p1, r1) := tws pos cs
      match r1 with
      | [] => .ok (accRev.reverse, st)
      | _ =>
          /- `fuel` starts above the document's character count and declines
             once per completed statement. Since every accepted statement
             consumes at least one character, it remains a safe bound for the
             current statement without traversing the complete remaining list
             to compute `r1.length` at every iteration. -/
          match readStatement fuel st p1 r1 with
          | .error e => .error e
          | .ok (ts, st', p2, r2) =>
              let nextAcc := ts.reverse ++ accRev
              /- Positions are absolute character offsets, so this is the
                 previous no-progress guard without another full-list length
                 traversal. -/
              if p2 ≤ p1 then .ok (nextAcc.reverse, st')
              else parseStatements fuel st' p2 r2 nextAcc

/-- Parse complete statements into a caller-supplied pure accumulator. This
    keeps the same grammar/state/error behaviour as `parseStatements`, while
    allowing ingestion code to avoid constructing a second whole-document
    graph merely to repartition its triples. -/
def parseStatementsFold (step : α → List Triple → α) :
    Nat → TurtleState → Nat → List Char → α → Except ParseError (α × TurtleState)
  | 0,        st, _,   _,  acc => .ok (acc, st)
  | fuel + 1, st, pos, cs, acc =>
      let (p1, r1) := tws pos cs
      match r1 with
      | [] => .ok (acc, st)
      | _ =>
          match readStatement fuel st p1 r1 with
          | .error e => .error e
          | .ok (ts, st', p2, r2) =>
              let nextAcc := step acc ts
              if p2 ≤ p1 then .ok (nextAcc, st')
              else parseStatementsFold step fuel st' p2 r2 nextAcc

/-- Parse a complete Turtle document into a `Graph`.

`base` is the retrieval IRI (the W3C suites supply
`http://www.w3.org/2013/TurtleTests/<file>`); `none` means relative
references can only be resolved after an in-document `@base`, and
otherwise fail with a position. `mode` defaults to RDF 1.1 — the RDF 1.2
grammar is still a W3C Working Draft, so 1.1 stays normative, matching
the F* source's `Mode_11` default. Port of
`parse_turtle_with_base_strict_mode`. -/
def parseTurtle (text : String) (base : Option String := none) (mode : Mode := .rdf11) :
    Except ParseError Graph :=
  let cs := text.toList
  match parseStatements (cs.length + 2) (TurtleState.initChars cs base mode) 0 cs [] with
  | .error e     => .error e
  | .ok (ts, _) => .ok ts

/-- Fold complete Turtle statements without first materialising a `Graph`.
    The document is still represented as characters in this first step; a
    byte-streaming host can later drive the same statement/state boundary. -/
def parseTurtleFold (step : α → List Triple → α) (init : α) (text : String)
    (base : Option String := none) (mode : Mode := .rdf11) : Except ParseError α :=
  let cs := text.toList
  match parseStatementsFold step (cs.length + 2) (TurtleState.initChars cs base mode) 0 cs init with
  | .error e => .error e
  | .ok (acc, _) => .ok acc

end L4Factoidal.Syntax
