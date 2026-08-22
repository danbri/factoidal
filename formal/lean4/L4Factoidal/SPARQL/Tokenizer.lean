/-
L4Factoidal.SPARQL.Tokenizer — the SPARQL 1.1 / 1.2 lexer.

Port of `formal/fstar/SPARQL11.Parser.fst` Part 2 (character
classification + lexer helpers, lines 195-560) and Part 3 (the lexer
proper, `next_token` / `tokenize` / `tokenize_12`, lines 560-1190).

WHAT THIS FILE IS. SPARQL 1.1 Query §19.8 gives the grammar in two
layers: terminals ([139] IRIREF … [173] PN_LOCAL_ESC) and productions
([1] QueryUnit … [138] BuiltInCall). This file is the terminal layer.
`SPARQL/Parser.lean` is the production layer.

FAITHFULNESS. The F* lexer is the spec of record here: it passes every
W3C sparql11 syntax suite, so where its character classes are laxer
than §19.8's (see `isPnChar` below) the port keeps the laxness rather
than "fixing" it — a divergence would change which queries are
accepted, which is precisely what the syntax suites measure.

CODEPOINTS VERSUS BYTES — the one structural difference, same as the
XML stage. `SPARQL11.Parser.fst` indexes raw UTF-8 BYTES through
`Parser.FastString`, so it carries `utf8_of_codepoint` (a hand-written
UTF-8 encoder) to turn a `\uXXXX` escape back into bytes. Lean's
`String`/`Char` are codepoint types and a `Char` is a valid Unicode
scalar value by construction, so a resolved codepoint escape is one
`Char.ofNat` and the encoder has no counterpart. Consequences:
  * `PosToken.pos` is a CHARACTER offset, where the F* reports a byte
    offset. Every rejection still names a position; the number differs.
  * A `\uD800`-`\uDFFF` escape inside an IRIREF, which the F* encodes
    as three bytes, is not representable as a Lean `Char`. This port
    DROPS such an escape (the F* itself drops an out-of-Unicode-range
    escape, returning `""` from `utf8_of_codepoint`); inside a STRING
    the F* already rejects surrogates outright and so does this port
    (`decodeStringEscape`).

KEYWORD CASE. §19.8 note: "Keywords are matched in a case-insensitive
manner"; `keywordOfUpper` is the port of `keyword_of_upper`, applied
to the upper-cased lexeme. `a` (rdf:type, [82] VerbSimple) tokenizes
as `Token.a` unconditionally — restricting it to verb position is a
PARSER concern, exactly as in the F*.

VERSION MODE. `SparqlVersion.v12` is the port of the F* `sparql12`
lexer flag: it adds `<<(` / `)>>` triple terms, bare `<<` / `>>`
reified triples, `~`, `{|` / `|}`, the `TRIPLE`/`SUBJECT`/`PREDICATE`/
`OBJECT`/`isTRIPLE` and `VERSION` and lang-direction keywords, the
`@lang--ltr` directional language tags, strict ECHAR-follower
rejection, and the whole-text codepoint-escape preprocessing pass
(`tokenize12`). In `.v11` every one of those is off and the token
stream is the F* 1.1 stream.

TERMINATION. `tokenize` is fuel-bounded exactly as the F*
`tokenize_loop` is (fuel = input length + 1, each round consumes at
least one character or stops). Every scanner is structurally recursive
on the remaining `List Char`. No `partial`, no well-founded recursion.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## Version mode -/

/-- Which SPARQL version's terminal layer to lex. Port of the F*
`sparql12 : bool` flag threaded through `next_token`. -/
inductive SparqlVersion where
  | v11
  | v12
  deriving DecidableEq, Repr

/-- Is this the SPARQL 1.2 lexer? -/
def SparqlVersion.is12 : SparqlVersion → Bool
  | .v11 => false
  | .v12 => true

/-! ## The token type — SPARQL 1.1 Query §19.8 terminals

One constructor per F* `token` case, in the F* source order. The
update keywords ([29] Update … [46] Load and friends) are lexed even
though `Parser.lean` parses queries only: `keyword_of_upper` produces
them, and dropping them would make `INSERT` lex as a prefixed name and
silently change which queries parse. -/

inductive Token where
  -- §19.8 query-form and clause keywords
  | select | ask | construct | describe
  | whereKw | prefixKw | baseKw
  | optional | union | minusKw | filterKw | bind | values
  /-- LATERAL — SPARQL 1.2 track / Jena extension. -/
  | lateral
  | graph | service | silent
  | exists | notKw
  | asKw | distinct | reduced
  | order | by | asc | desc
  | group | having
  | limit | offset
  | fromKw | named
  | inKw | trueKw | falseKw | undef
  /-- `a` — [82] VerbSimple, rdf:type. -/
  | a
  -- punctuation
  | lbrace | rbrace | lparen | rparen
  | lbracket | rbracket
  | dot | semi | comma
  -- operators
  | star | slash | pipe | caret | bang | qmark
  | plus | minusOp
  | eq | ne | lt | gt | le | ge
  | and | or
  /-- `^^` — [147] datatype marker. -/
  | hathat
  -- SPARQL 1.2 triple terms and reification
  /-- `<<(` — triple-term open. -/
  | ttOpen
  /-- `)>>` — triple-term close. -/
  | ttClose
  /-- `<<` — bare reified-triple open. -/
  | ttBareOpen
  /-- `>>` — bare reified-triple close. -/
  | ttBareClose
  /-- `~` — reifier marker. -/
  | tilde
  /-- `{|` — annotation block open. -/
  | annotOpen
  /-- `|}` — annotation block close. -/
  | annotClose
  | tripleKw | subjectKw | predicateKw | objectKw | isTripleKw
  | versionKw
  | hasLangKw | hasLangDirKw | langDirKw | strLangDirKw
  -- terminals carrying text
  /-- [139] IRIREF, escapes already expanded. -/
  | iri       (s : String)
  /-- [140] PNAME_LN / [141] PNAME_NS, pre-expansion. -/
  | pname     (s : String)
  /-- [143] VAR1 / [144] VAR2, without the `?`/`$`. -/
  | var       (s : String)
  /-- [135] String, escapes already expanded. -/
  | str       (s : String)
  /-- [145] LANGTAG, without the `@`. -/
  | langtag   (s : String)
  /-- RDF 1.2 directional language tag `@lang--ltr` / `@lang--rtl`. -/
  | langdir   (s : String) (dir : TextDirection)
  /-- [146] INTEGER. -/
  | integer   (s : String)
  /-- [147] DECIMAL. -/
  | decimal   (s : String)
  /-- [148] DOUBLE. -/
  | double    (s : String)
  /-- [142] BLANK_NODE_LABEL, without the `_:`. -/
  | bnode     (s : String)
  /-- `[]` — [138] ANON. The lexer never emits this; `[` / `]` are
  separate tokens and the parser recognises the pair, exactly as in
  the F*. Kept so the token type matches the F* `token` one-for-one. -/
  | anon
  -- §17 builtin-function keywords
  | strKw | langKw | langMatches | datatype | bound | ifKw
  | iriKw | uriKw | bnodeKw | rand
  | absKw | ceil | floor | roundKw
  | concat | strLen | uCase | lCase
  | encodeForUri | contains | strStarts | strEnds
  | strBefore | strAfter | replaceKw | regexKw
  | substr
  | isIri | isBlank | isLiteral | isNumeric
  | sameTerm | strDt | strLang
  | count | sum | minKw | maxKw | avg
  | groupConcat | sample | separator
  | coalesce | now | uuid | strUuid
  | year | month | day | hours | minutes | seconds
  | timezone | tz
  | md5 | sha1 | sha256 | sha384 | sha512
  -- SPARQL 1.1 Update keywords (lexed, not parsed here)
  | load | clear | drop | create
  | addKw | move | copy
  | insert | delete | data
  | into | to | withKw | using
  | defaultKw | allKw
  /-- A lexical error detected in the terminal layer, carrying the F*
  message text verbatim. -/
  | invalid   (msg : String)
  | eof
  deriving DecidableEq, Repr

/-- A token together with the character offset at which it starts.
The F* `token_stream` is a bare `list token`; positions are added here
so a rejection can name WHERE, which the W3C negative-syntax tests
make a reviewer want. -/
structure PosToken where
  tok : Token
  pos : Nat
  deriving DecidableEq, Repr

/-! ## Character classification — port of the F* `is_*` family -/

/-- `is_alpha`: ASCII letters only. -/
def isAlpha (c : Char) : Bool :=
  ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')

/-- `is_digit`: ASCII `0`-`9`. -/
def isDigitC (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'

/-- `is_alnum`. -/
def isAlnum (c : Char) : Bool := isAlpha c || isDigitC c

/-- `is_ws`: space, tab, LF, CR — §19.8 [162] WS. -/
def isWsC (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- `is_pn_char`. DELIBERATELY LAXER than §19.8 [167] PN_CHARS: the F*
admits every codepoint ≥ 0x80 rather than enumerating the Unicode
ranges, and admits `.` (which [167] excludes, the trailing-dot trim
below putting it back). Kept verbatim — see the module header. -/
def isPnChar (c : Char) : Bool :=
  isAlnum c || c == '_' || c == '-' || c == '.' || c.toNat ≥ 0x80

/-- `is_pn_local_esc`: §19.8 [173] PN_LOCAL_ESC — the characters a
backslash may escape inside a local name. -/
def isPnLocalEscC (c : Char) : Bool :=
  c == '_' || c == '~' || c == '.' || c == '-' ||
  c == '!' || c == '$' || c == '&' || c == '\'' ||
  c == '(' || c == ')' || c == '*' || c == '+' ||
  c == ',' || c == ';' || c == '=' || c == '/' ||
  c == '?' || c == '#' || c == '@' || c == '%'

/-- `char_upper`: ASCII-only upper-casing, the case folding §19.8's
keyword rule needs. -/
def charUpper (c : Char) : Char :=
  if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

/-- `string_upper`, over a character list. -/
def charsUpper (cs : List Char) : List Char := cs.map charUpper

/-- `string_upper`. -/
def stringUpper (s : String) : String :=
  String.ofList (charsUpper s.toList)

/-- `is_hex_digit`. -/
def isHexDigitC (c : Char) : Bool := (hexVal c).isSome

/-! ## Escape processing -/

/-- `read_hex_digits n cs acc`: read exactly `n` hex digits off the
front, or fail. Structural on `n`. -/
def readHexDigits : Nat → List Char → Nat → Option (Nat × List Char)
  | 0,     cs, acc => some (acc, cs)
  | n + 1, cs, acc =>
    match cs with
    | []        => none
    | c :: rest =>
      match hexVal c with
      | none   => none
      | some v => readHexDigits n rest (acc * 16 + v)

/-- Is this codepoint one a Lean `Char` can hold? (Excludes the
surrogate block and everything from 0x110000 up.) -/
def validCodepoint (cp : Nat) : Bool :=
  decide (cp < 0xD800) || (decide (0xDFFF < cp) && decide (cp < 0x110000))

/-- Turn a codepoint into a `Char`, or `none` when no `Char` holds it.
Mirrors `Syntax.codepointToChar` without its error channel — the two
IRIREF call sites below are total by construction, as the F* ones are. -/
def charOfCodepoint? (cp : Nat) : Option Char :=
  if h : cp.isValidChar then some (Char.ofNatAux cp h) else none

/-- `process_iri_escapes_rec`: expand `\uXXXX` / `\UXXXXXXXX` in an
IRIREF lexeme. Total, never fails: an escape that cannot parse leaves
its backslash verbatim (the F*'s stated fallback), and a codepoint no
`Char` can hold is dropped (the F*'s `utf8_of_codepoint` returns `""`
for one out of Unicode range — see the module header on surrogates).
Fuel-bounded so it stays structural; the fuel is the input length,
and every round consumes at least one character. -/
def processIriEscapesRec : Nat → List Char → List Char → List Char
  | 0,     _,  acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | f + 1, c1 :: r1, acc =>
    if c1 == '\\' then
      match r1 with
      | c2 :: r2 =>
        if c2 == 'u' then
          match readHexDigits 4 r2 0 with
          | some (cp, after) =>
            match charOfCodepoint? cp with
            | some ch => processIriEscapesRec f after (ch :: acc)
            | none    => processIriEscapesRec f after acc
          | none => processIriEscapesRec f r1 (c1 :: acc)
        else if c2 == 'U' then
          match readHexDigits 8 r2 0 with
          | some (cp, after) =>
            match charOfCodepoint? cp with
            | some ch => processIriEscapesRec f after (ch :: acc)
            | none    => processIriEscapesRec f after acc
          | none => processIriEscapesRec f r1 (c1 :: acc)
        else processIriEscapesRec f r1 (c1 :: acc)
      | [] => processIriEscapesRec f [] (c1 :: acc)
    else processIriEscapesRec f r1 (c1 :: acc)

/-- `process_iri_escapes`. -/
def processIriEscapes (cs : List Char) : List Char :=
  processIriEscapesRec (cs.length + 1) cs []

/-- `process_codepoint_escapes` — the SPARQL 1.2 whole-text
preprocessing pass. Identical transformation to `processIriEscapes`;
a separate name because the CALL SITE is what carries the meaning
(§19.8's codepoint-escape note lets an escape stand for any character
anywhere in the query, keyword and quote delimiters included, so the
decode cannot be scoped to one token's lexeme). -/
def processCodepointEscapes (cs : List Char) : List Char := processIriEscapes cs

/-- `decode_string_escape`: one ECHAR ([160]) or codepoint escape,
positioned just past the backslash. `strict` (SPARQL 1.2 only) rejects
an unrecognised follower instead of the 1.1 "keep the character, drop
the backslash" fallback. Returns the decoded characters and the
remainder, or `none` for a malformed sequence or a surrogate. -/
def decodeStringEscape (strict : Bool) : List Char →
    Option (List Char × List Char)
  | []        => none
  | c :: rest =>
    if c == 't' then some (['\t'], rest)
    else if c == 'n' then some (['\n'], rest)
    else if c == 'r' then some (['\r'], rest)
    else if c == '\\' then some ([c], rest)
    else if c == '"' then some ([c], rest)
    else if c == '\'' then some ([c], rest)
    else if c == 'b' then some ([Char.ofNat 0x08], rest)
    else if c == 'f' then some ([Char.ofNat 0x0C], rest)
    else if c == 'u' then
      match readHexDigits 4 rest 0 with
      | some (cp, after) =>
        if cp ≥ 0xD800 && cp ≤ 0xDFFF then none
        else (match charOfCodepoint? cp with
               | some ch => some ([ch], after)
               | none    => none)
      | none => none
    else if c == 'U' then
      match readHexDigits 8 rest 0 with
      | some (cp, after) =>
        if cp ≥ 0xD800 && cp ≤ 0xDFFF then none
        else (match charOfCodepoint? cp with
               | some ch => some ([ch], after)
               | none    => none)
      | none => none
    else if strict then none
    else some ([c], rest)

/-- `process_string_escapes_rec`, fuel-bounded so it stays structural.
Fuel is seeded with the input length by `processStringEscapes`; each
round consumes at least one character. -/
def processStringEscapesRec (strict : Bool) : Nat → List Char → List Char →
    Option (List Char)
  | 0,      _,  acc => some acc.reverse
  | _ + 1,  [], acc => some acc.reverse
  | f + 1, c :: rest, acc =>
    if c == '\\' then
      match decodeStringEscape strict rest with
      | none               => none
      | some (dec, after)  =>
        processStringEscapesRec strict f after (dec.reverse ++ acc)
    else processStringEscapesRec strict f rest (c :: acc)

/-- `process_string_escapes_opt`: expand the escapes of a STRING
lexeme, or fail (surrogate, malformed, or — in 1.2 — an unrecognised
ECHAR follower). -/
def processStringEscapes (strict : Bool) (cs : List Char) : Option (List Char) :=
  processStringEscapesRec strict (cs.length + 1) cs []

/-! ## Scanners

Each returns `(lexeme, position after it, remaining characters)`.
Structural on the character list; the F*'s `decreases (length - p)`
becomes plain structural recursion here. -/

/-- Scan while a predicate holds. -/
def scanWhile (p : Char → Bool) : Nat → List Char → List Char →
    List Char × Nat × List Char
  | pos, [],        acc => (acc.reverse, pos, [])
  | pos, c :: rest, acc =>
    if p c then scanWhile p (pos + 1) rest (c :: acc)
    else (acc.reverse, pos, c :: rest)

/-- `skip_ws` / `skip_comment`: whitespace and `#`-comments, fuel-
bounded. §19.8 [161] COMMENT runs to the end of line. -/
def skipWsComments : Nat → Nat → List Char → Nat × List Char
  | 0,     pos, cs => (pos, cs)
  | _ + 1, pos, [] => (pos, [])
  | f + 1, pos, c :: rest =>
    if isWsC c then skipWsComments f (pos + 1) rest
    else if c == '#' then
      let (pos', rest') := scanToEol (pos + 1) rest
      skipWsComments f pos' rest'
    else (pos, c :: rest)
where
  scanToEol : Nat → List Char → Nat × List Char
    | pos, []        => (pos, [])
    | pos, c :: rest =>
      if c == '\n' then (pos + 1, rest) else scanToEol (pos + 1) rest

/-- `skip_ws` at the top level, with fuel seeded from the remaining
input length. -/
def skipWs (pos : Nat) (cs : List Char) : Nat × List Char :=
  skipWsComments (cs.length + 1) pos cs

/-- `scan_iri_end` + `scan_iri`: the content between `<` and `>`, with
a backslash skipping the next character. §19.8 [139] IRIREF. -/
def scanIriBody : Nat → List Char → List Char → List Char × Nat × List Char
  | pos, [],        acc => (acc.reverse, pos, [])
  | pos, c :: rest, acc =>
    if c == '>' then (acc.reverse, pos + 1, rest)
    else if c == '\\' then
      match rest with
      | []        => ((c :: acc).reverse, pos + 1, [])
      | d :: rest' => scanIriBody (pos + 2) rest' (d :: c :: acc)
    else scanIriBody (pos + 1) rest (c :: acc)

/-- `scan_short_string_end`: to the next unescaped delimiter. -/
def scanShortStringBody (q : Char) : Nat → List Char → List Char →
    List Char × Nat × List Char
  | pos, [],        acc => (acc.reverse, pos, [])
  | pos, c :: rest, acc =>
    if c == q then (acc.reverse, pos + 1, rest)
    else if c == '\\' then
      match rest with
      | []         => ((c :: acc).reverse, pos + 1, [])
      | d :: rest' => scanShortStringBody q (pos + 2) rest' (d :: c :: acc)
    else scanShortStringBody q (pos + 1) rest (c :: acc)

/-- `scan_long_string_end`: to the next unescaped TRIPLE delimiter. -/
def scanLongStringBody (q : Char) : Nat → List Char → List Char →
    List Char × Nat × List Char
  | pos, [],        acc => (acc.reverse, pos, [])
  | pos, c :: rest, acc =>
    if c == q then
      match rest with
      | d :: e :: rest' =>
        if d == q && e == q then (acc.reverse, pos + 3, rest')
        else scanLongStringBody q (pos + 1) rest (c :: acc)
      | _ => scanLongStringBody q (pos + 1) rest (c :: acc)
    else if c == '\\' then
      match rest with
      | []         => ((c :: acc).reverse, pos + 1, [])
      | d :: rest' => scanLongStringBody q (pos + 2) rest' (d :: c :: acc)
    else scanLongStringBody q (pos + 1) rest (c :: acc)

/-- `scan_pn_local_end`: PN_LOCAL characters after the colon —
[169] PN_LOCAL, admitting `:`, `%` (PLX) and `\`-escapes. -/
def scanPnLocal : Nat → List Char → List Char → List Char × Nat × List Char
  | pos, [],        acc => (acc.reverse, pos, [])
  | pos, c :: rest, acc =>
    if isPnChar c || c == ':' || c == '%' then
      scanPnLocal (pos + 1) rest (c :: acc)
    else if c == '\\' then
      match rest with
      | []         => (acc.reverse, pos, c :: rest)
      | d :: rest' =>
        if isPnLocalEscC d then scanPnLocal (pos + 2) rest' (d :: c :: acc)
        else (acc.reverse, pos, c :: rest)
    else (acc.reverse, pos, c :: rest)

/-- `trim_trailing_dots`, over the collected lexeme: drop trailing
`.`s, but keep one preceded by a backslash (a `\.` PN_LOCAL_ESC).
Returns the kept lexeme and the dots pushed back into the input. -/
def trimDotsRev : List Char → List Char → List Char × List Char
  | [],       dots => ([], dots)
  | c :: rev, dots =>
    if c == '.' then
      match rev with
      | b :: _ => if b == '\\' then (c :: rev, dots) else trimDotsRev rev (c :: dots)
      | []     => trimDotsRev rev (c :: dots)
    else (c :: rev, dots)

/-- Split a lexeme into (kept, trailing dots). -/
def trimTrailingDots (l : List Char) : List Char × List Char :=
  let (revKept, dots) := trimDotsRev l.reverse []
  (revKept.reverse, dots)

/-! ## Keyword table — §19.8, case-insensitive -/

/-- `keyword_of_upper`: map an UPPER-CASED lexeme to its keyword
token, or `Token.pname` when it is not a keyword. The `v12` guard on
the first ten entries is the F*'s, and is why 1.1 lexing is unchanged
by the 1.2 additions. -/
def keywordOfUpper (v12 : Bool) (upper : String) (original : String) : Token :=
  if v12 && upper == "TRIPLE" then .tripleKw
  else if v12 && upper == "SUBJECT" then .subjectKw
  else if v12 && upper == "PREDICATE" then .predicateKw
  else if v12 && upper == "OBJECT" then .objectKw
  else if v12 && upper == "ISTRIPLE" then .isTripleKw
  else if v12 && upper == "VERSION" then .versionKw
  else if v12 && upper == "HASLANG" then .hasLangKw
  else if v12 && upper == "HASLANGDIR" then .hasLangDirKw
  else if v12 && upper == "LANGDIR" then .langDirKw
  else if v12 && upper == "STRLANGDIR" then .strLangDirKw
  else if upper == "SELECT" then .select
  else if upper == "ASK" then .ask
  else if upper == "CONSTRUCT" then .construct
  else if upper == "DESCRIBE" then .describe
  else if upper == "WHERE" then .whereKw
  else if upper == "PREFIX" then .prefixKw
  else if upper == "BASE" then .baseKw
  else if upper == "OPTIONAL" then .optional
  else if upper == "UNION" then .union
  else if upper == "MINUS" then .minusKw
  else if upper == "LATERAL" then .lateral
  else if upper == "FILTER" then .filterKw
  else if upper == "BIND" then .bind
  else if upper == "VALUES" then .values
  else if upper == "GRAPH" then .graph
  else if upper == "SERVICE" then .service
  else if upper == "SILENT" then .silent
  else if upper == "EXISTS" then .exists
  else if upper == "NOT" then .notKw
  else if upper == "AS" then .asKw
  else if upper == "DISTINCT" then .distinct
  else if upper == "REDUCED" then .reduced
  else if upper == "ORDER" then .order
  else if upper == "BY" then .by
  else if upper == "ASC" then .asc
  else if upper == "DESC" then .desc
  else if upper == "GROUP" then .group
  else if upper == "HAVING" then .having
  else if upper == "LIMIT" then .limit
  else if upper == "OFFSET" then .offset
  else if upper == "FROM" then .fromKw
  else if upper == "NAMED" then .named
  else if upper == "IN" then .inKw
  else if upper == "TRUE" then .trueKw
  else if upper == "FALSE" then .falseKw
  else if upper == "UNDEF" then .undef
  else if upper == "A" then .a
  -- §17 builtin-function keywords
  else if upper == "STR" then .strKw
  else if upper == "LANG" then .langKw
  else if upper == "LANGMATCHES" then .langMatches
  else if upper == "DATATYPE" then .datatype
  else if upper == "BOUND" then .bound
  else if upper == "IF" then .ifKw
  else if upper == "IRI" then .iriKw
  else if upper == "URI" then .uriKw
  else if upper == "BNODE" then .bnodeKw
  else if upper == "RAND" then .rand
  else if upper == "ABS" then .absKw
  else if upper == "CEIL" then .ceil
  else if upper == "FLOOR" then .floor
  else if upper == "ROUND" then .roundKw
  else if upper == "CONCAT" then .concat
  else if upper == "STRLEN" then .strLen
  else if upper == "UCASE" then .uCase
  else if upper == "LCASE" then .lCase
  else if upper == "ENCODE_FOR_URI" then .encodeForUri
  else if upper == "CONTAINS" then .contains
  else if upper == "STRSTARTS" then .strStarts
  else if upper == "STRENDS" then .strEnds
  else if upper == "STRBEFORE" then .strBefore
  else if upper == "STRAFTER" then .strAfter
  else if upper == "REPLACE" then .replaceKw
  else if upper == "REGEX" then .regexKw
  else if upper == "SUBSTR" then .substr
  else if upper == "SUBSTRING" then .substr        -- alias
  else if upper == "ISIRI" then .isIri
  else if upper == "ISURI" then .isIri             -- alias
  else if upper == "ISBLANK" then .isBlank
  else if upper == "ISLITERAL" then .isLiteral
  else if upper == "ISNUMERIC" then .isNumeric
  else if upper == "SAMETERM" then .sameTerm
  else if upper == "STRDT" then .strDt
  else if upper == "STRLANG" then .strLang
  else if upper == "COUNT" then .count
  else if upper == "SUM" then .sum
  else if upper == "MIN" then .minKw
  else if upper == "MAX" then .maxKw
  else if upper == "AVG" then .avg
  else if upper == "GROUP_CONCAT" then .groupConcat
  else if upper == "SAMPLE" then .sample
  else if upper == "SEPARATOR" then .separator
  else if upper == "COALESCE" then .coalesce
  else if upper == "NOW" then .now
  else if upper == "UUID" then .uuid
  else if upper == "STRUUID" then .strUuid
  else if upper == "YEAR" then .year
  else if upper == "MONTH" then .month
  else if upper == "DAY" then .day
  else if upper == "HOURS" then .hours
  else if upper == "MINUTES" then .minutes
  else if upper == "SECONDS" then .seconds
  else if upper == "TIMEZONE" then .timezone
  else if upper == "TZ" then .tz
  else if upper == "MD5" then .md5
  else if upper == "SHA1" then .sha1
  else if upper == "SHA256" then .sha256
  else if upper == "SHA384" then .sha384
  else if upper == "SHA512" then .sha512
  -- SPARQL 1.1 Update keywords
  else if upper == "LOAD" then .load
  else if upper == "CLEAR" then .clear
  else if upper == "DROP" then .drop
  else if upper == "CREATE" then .create
  else if upper == "ADD" then .addKw
  else if upper == "MOVE" then .move
  else if upper == "COPY" then .copy
  else if upper == "INSERT" then .insert
  else if upper == "DELETE" then .delete
  else if upper == "DATA" then .data
  else if upper == "INTO" then .into
  else if upper == "TO" then .to
  else if upper == "WITH" then .withKw
  else if upper == "USING" then .using
  else if upper == "DEFAULT" then .defaultKw
  else if upper == "ALL" then .allKw
  else .pname original

/-- `starts_with_long_string`: look past whitespace for a triple
quote. Used only to reject `VERSION """1.2"""` — §19.8's [4a] Version
declaration takes a plain STRING_LITERAL1/2 (version-bad-01, version-bad-02). -/
def startsWithLongString (cs : List Char) : Bool :=
  let (_, cs') := skipWs 0 cs
  match cs' with
  | q :: d :: e :: _ => (q == '"' || q == '\'') && d == q && e == q
  | _                => false

/-- `scan_pname_or_keyword`: a prefixed name ([140] PNAME_LN) or a
keyword. -/
def scanPnameOrKeyword (v12 : Bool) (pos : Nat) (cs : List Char) :
    Token × Nat × List Char :=
  let (word, pos1, rest1) := scanWhile isPnChar pos cs []
  match rest1 with
  | ':' :: after =>
    let (locRaw, pos2, rest2) := scanPnLocal (pos1 + 1) after []
    let whole := word ++ [':'] ++ locRaw
    let (kept, dots) := trimTrailingDots whole
    (.pname (String.ofList kept), pos2 - dots.length, dots ++ rest2)
  | _ =>
    let tok := keywordOfUpper v12 (String.ofList (charsUpper word)) (String.ofList word)
    match tok with
    | .versionKw =>
      if startsWithLongString rest1 then
        (.invalid "VERSION requires a plain string literal, not a triple-quoted long string",
         pos1, rest1)
      else (tok, pos1, rest1)
    | _ => (tok, pos1, rest1)

/-- `scan_number`: §19.8 [146] INTEGER / [147] DECIMAL / [148] DOUBLE.
A `.` counts only when a digit follows it; an `e`/`E` makes the whole
lexeme a DOUBLE. -/
def scanNumber (pos : Nat) (cs : List Char) : Token × Nat × List Char :=
  let (int1, pos1, rest1) := scanWhile isDigitC pos cs []
  let hasDot : Bool :=
    match rest1 with
    | '.' :: d :: _ => isDigitC d
    | _             => false
  let (fracPart, pos2, rest2) :=
    if hasDot then
      match rest1 with
      | _ :: rest1' =>
        let (fr, p, r) := scanWhile isDigitC (pos1 + 1) rest1' []
        ('.' :: fr, p, r)
      | []          => ([], pos1, rest1)
    else ([], pos1, rest1)
  let hasExp : Bool :=
    match rest2 with
    | e :: _ => e == 'e' || e == 'E'
    | []     => false
  let (expPart, pos3, rest3) :=
    if hasExp then
      match rest2 with
      | e :: rest2' =>
        let (signPart, posS, restS) :=
          match rest2' with
          | s :: rest2'' => if s == '+' || s == '-' then ([s], pos2 + 2, rest2'') else ([], pos2 + 1, rest2')
          | []           => ([], pos2 + 1, [])
        let (ds, p, r) := scanWhile isDigitC posS restS []
        (e :: signPart ++ ds, p, r)
      | []          => ([], pos2, rest2)
    else ([], pos2, rest2)
  let text := String.ofList (int1 ++ fracPart ++ expPart)
  if hasExp then (.double text, pos3, rest3)
  else if hasDot then (.decimal text, pos3, rest3)
  else (.integer text, pos3, rest3)

/-- `scan_bnode_label`: [142] BLANK_NODE_LABEL after `_:`, with the
trailing-dot trim. -/
def scanBnodeLabel (pos : Nat) (cs : List Char) : String × Nat × List Char :=
  let (raw, pos', rest) := scanWhile isPnChar pos cs []
  let (kept, dots) := trimTrailingDots raw
  (String.ofList kept, pos' - dots.length, dots ++ rest)

/-- `scan_var_name`: [166] VARNAME after `?`/`$` — the F* admits
`[A-Za-z0-9_]`. -/
def scanVarName (pos : Nat) (cs : List Char) : String × Nat × List Char :=
  let (raw, pos', rest) := scanWhile (fun c => isAlnum c || c == '_') pos cs []
  (String.ofList raw, pos', rest)

/-- `scan_langtag`: [145] LANGTAG after `@`. -/
def scanLangTag (pos : Nat) (cs : List Char) : String × Nat × List Char :=
  let (raw, pos', rest) := scanWhile (fun c => isAlnum c || c == '-') pos cs []
  (String.ofList raw, pos', rest)

/-- `sparql_lang_valid_subtags`: every hyphen-separated subtag is 1-8
characters (RDF 1.2 Concepts §3.3, the direction-tag split rule). -/
def langValidSubtags : List Char → Nat → Bool
  | [],       cur => cur ≥ 1 && cur ≤ 8
  | c :: rest, cur =>
    if c == '-' then (cur ≥ 1 && cur ≤ 8) && langValidSubtags rest 0
    else langValidSubtags rest (cur + 1)

/-- `sparql_split_lang_dir`: split at the FIRST `--`. -/
def splitLangDir : List Char → List Char → List Char × Option (List Char)
  | c1 :: c2 :: rest, acc =>
    if c1 == '-' && c2 == '-' then (acc.reverse, some rest)
    else splitLangDir (c2 :: rest) (c1 :: acc)
  | [c], acc => ((c :: acc).reverse, none)
  | [],  acc => (acc.reverse, none)

/-- `has_gt_before_terminator`: does a `>` appear before whitespace or
a closing bracket? The lookahead that lets `<?x>` lex as an IRIREF
while `?a < ?b` lexes as a comparison. -/
def hasGtBeforeTerminator : List Char → Bool
  | []        => false
  | c :: rest =>
    if c == '>' then true
    else if isWsC c || c == ')' || c == '}' || c == ']' then false
    else hasGtBeforeTerminator rest

/-! ## `next_token` — one token from the current position -/

/-- Port of `next_token`. Skips whitespace and comments first, then
dispatches on the leading character. Returns the token, the position
it starts at, the position after it, and the remaining input. -/
def nextToken (v12 : Bool) (pos0 : Nat) (cs0 : List Char) :
    Token × Nat × Nat × List Char :=
  let (pos, cs) := skipWs pos0 cs0
  match cs with
  | [] => (.eof, pos, pos, [])
  | c :: rest =>
    if c == '<' then
      match rest with
      | '<' :: '(' :: r  => if v12 then (.ttOpen, pos, pos + 3, r) else ltCase pos c rest
      | '<' :: r         => if v12 then (.ttBareOpen, pos, pos + 2, r) else ltCase pos c rest
      | '=' :: r         => (.le, pos, pos + 2, r)
      | _                => ltCase pos c rest
    else if c == '>' then
      match rest with
      | '>' :: r => if v12 then (.ttBareClose, pos, pos + 2, r) else (.gt, pos, pos + 1, rest)
      | '=' :: r => (.ge, pos, pos + 2, r)
      | _        => (.gt, pos, pos + 1, rest)
    else if c == '{' then
      match rest with
      | '|' :: r => if v12 then (.annotOpen, pos, pos + 2, r) else (.lbrace, pos, pos + 1, rest)
      | _        => (.lbrace, pos, pos + 1, rest)
    else if c == '}' then (.rbrace, pos, pos + 1, rest)
    else if c == '(' then (.lparen, pos, pos + 1, rest)
    else if c == ')' then
      match rest with
      | '>' :: '>' :: r => if v12 then (.ttClose, pos, pos + 3, r) else (.rparen, pos, pos + 1, rest)
      | _               => (.rparen, pos, pos + 1, rest)
    else if c == '[' then (.lbracket, pos, pos + 1, rest)
    else if c == ']' then (.rbracket, pos, pos + 1, rest)
    else if c == '.' then (.dot, pos, pos + 1, rest)
    else if c == ';' then (.semi, pos, pos + 1, rest)
    else if c == ',' then (.comma, pos, pos + 1, rest)
    else if c == '*' then (.star, pos, pos + 1, rest)
    else if c == '/' then (.slash, pos, pos + 1, rest)
    else if c == '|' then
      match rest with
      | '}' :: r => if v12 then (.annotClose, pos, pos + 2, r) else (.pipe, pos, pos + 1, rest)
      | '|' :: r => (.or, pos, pos + 2, r)
      | _        => (.pipe, pos, pos + 1, rest)
    else if c == '^' then
      match rest with
      | '^' :: r => (.hathat, pos, pos + 2, r)
      | _        => (.caret, pos, pos + 1, rest)
    else if c == '!' then
      match rest with
      | '=' :: r => (.ne, pos, pos + 2, r)
      | _        => (.bang, pos, pos + 1, rest)
    else if c == '=' then (.eq, pos, pos + 1, rest)
    else if c == '&' then
      -- The F* maps both `&&` and a lone `&` to Tok_AND, advancing by
      -- two either way; kept, so a lone `&` behaves identically.
      match rest with
      | _ :: r => (.and, pos, pos + 2, r)
      | []     => (.and, pos, pos + 2, [])
    else if c == '?' || c == '$' then
      let (name, pos', rest') := scanVarName (pos + 1) rest
      if name.length == 0 then (.qmark, pos, pos + 1, rest)
      else (.var name, pos, pos', rest')
    else if c == '"' || c == '\'' then
      let isLong : Bool :=
        match rest with
        | d :: e :: _ => d == c && e == c
        | _           => false
      let (raw, pos', rest') :=
        if isLong then
          match rest with
          | _ :: _ :: r => scanLongStringBody c (pos + 3) r []
          | _           => ([], pos + 1, [])
        else scanShortStringBody c (pos + 1) rest []
      match processStringEscapes v12 raw with
      | some s => (.str (String.ofList s), pos, pos', rest')
      | none   => (.invalid "invalid string escape (surrogate or malformed)", pos, pos', rest')
    else if c == '@' then
      let (tag, pos', rest') := scanLangTag (pos + 1) rest
      if v12 then
        match splitLangDir tag.toList [] with
        | (ltChars, some dchars) =>
          if !langValidSubtags ltChars 0 then
            (.invalid "invalid language tag before base direction", pos, pos', rest')
          else if dchars == ['l', 't', 'r'] then
            (.langdir (String.ofList ltChars) .ltr, pos, pos', rest')
          else if dchars == ['r', 't', 'l'] then
            (.langdir (String.ofList ltChars) .rtl, pos, pos', rest')
          else
            (.invalid "invalid base direction (expected ltr or rtl)", pos, pos', rest')
        | (_, none) => (.langtag tag, pos, pos', rest')
      else (.langtag tag, pos, pos', rest')
    else if c == '+' then (.plus, pos, pos + 1, rest)
    else if c == '-' then (.minusOp, pos, pos + 1, rest)
    else if c == '_' then
      match rest with
      | ':' :: r =>
        let (label, pos', rest') := scanBnodeLabel (pos + 2) r
        (.bnode label, pos, pos', rest')
      | _ =>
        let (t, p', r') := scanPnameOrKeyword v12 pos (c :: rest)
        (t, pos, p', r')
    else if v12 && c == '~' then (.tilde, pos, pos + 1, rest)
    else if isDigitC c then
      let (t, p', r') := scanNumber pos (c :: rest)
      (t, pos, p', r')
    else if isAlpha c || c == ':' || c.toNat ≥ 0x80 then
      let (t, p', r') := scanPnameOrKeyword v12 pos (c :: rest)
      (t, pos, p', r')
    else (.eof, pos, pos + 1, rest)   -- skip unknown character
where
  /-- The `<` disambiguation: `<IRI>` versus the less-than operator.
  An IRIREF is recognised when the next character is a letter, `>`,
  `_`, `/`, `#`, or a `?`/`$` with a `>` ahead of any terminator. -/
  ltCase (pos : Nat) (c : Char) (rest : List Char) : Token × Nat × Nat × List Char :=
    match rest with
    | [] => (.lt, pos, pos + 1, [])
    | d :: _ =>
      if isAlpha d || d == '>' || d == '_' || d == '/' || d == '#' ||
         ((d == '?' || d == '$') && hasGtBeforeTerminator rest) then
        let (body, pos', rest') := scanIriBody (pos + 1) rest []
        (.iri (String.ofList (processIriEscapes body)), pos, pos', rest')
      else (.lt, pos, pos + 1, rest)

/-! ## `tokenize` -/

/-- `tokenize_loop`: repeat `nextToken` until EOF, fuel-bounded. The
`pos' ≤ pos` no-progress stop of the F* is not needed here (the
remaining list shrinks or the loop ends), but the fuel bound is kept
because it is what makes the definition structural. -/
def tokenizeLoop (v12 : Bool) : Nat → Nat → List Char → List PosToken →
    List PosToken
  | 0,     pos, _,  acc => (⟨.eof, pos⟩ :: acc).reverse
  | f + 1, pos, cs, acc =>
    let (tok, start, pos', rest) := nextToken v12 pos cs
    match tok with
    | .eof => (⟨Token.eof, start⟩ :: acc).reverse
    | _    =>
      if rest.length ≥ cs.length then (⟨Token.eof, start⟩ :: acc).reverse
      else tokenizeLoop v12 f pos' rest (⟨tok, start⟩ :: acc)

/-- SPARQL 1.1 tokenizer — port of `tokenize`. -/
def tokenize (s : String) : List PosToken :=
  tokenizeLoop false (s.toList.length + 1) 0 s.toList []

/-- SPARQL 1.2 tokenizer — port of `tokenize_12`. Decodes codepoint
escapes over the WHOLE text first (§19.8's codepoint-escape note),
then lexes in 1.2 mode. -/
def tokenize12 (s : String) : List PosToken :=
  let decoded := processCodepointEscapes s.toList
  tokenizeLoop true (decoded.length + 1) 0 decoded []

/-- Tokenize at the requested version. -/
def tokenizeAt : SparqlVersion → String → List PosToken
  | .v11, s => tokenize s
  | .v12, s => tokenize12 s

/-- The token list without positions — the shape the F* `tokenize`
returns, and the convenient one for the case-insensitivity guards in
`ParserTheorems.lean`. -/
def tokensOf (ts : List PosToken) : List Token := ts.map PosToken.tok

end L4Factoidal.SPARQL
