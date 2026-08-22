/-
L4Factoidal.CSVW.UriTemplate — the RFC 6570 subset CSVW needs,
ported from `formal/fstar/CSVW.URITemplate.fst`.

Scope, matching the F* module exactly: level-1 simple expansion
`{var}` and level-2 fragment expansion `{#var}`. No query form
`{?var}`, no path segments `{/var}`, no multi-variable lists, no
prefix or explode modifiers. Extend the grammar if a fixture needs
more, rather than reaching for a general RFC 6570 library.

CSVW's row-scoped variables (`_row`, `_sourceRow`, `_name` — the
leading underscore is a CSVW convention, not RFC 6570) resolve through
the caller's `lookup`, so this module needs no CSVW knowledge. The
conversion step builds that closure per row and column.
-/

namespace L4Factoidal.CSVW
namespace UriTemplate

inductive Segment where
  | literal (s : String)
  | var     (name : String)
deriving Repr, DecidableEq

/-- Split a template into literal runs and `{...}` references. RFC
    6570 defines no brace escaping, so neither does this. -/
def parse (raw : String) : List Segment :=
  let rec go (cur : List Char) (acc : List Segment) (inBrace : Bool)
      : List Char → List Segment
    | [] =>
        if cur.isEmpty then acc
        else acc ++ [if inBrace then .var (String.ofList cur.reverse)
                     else .literal (String.ofList cur.reverse)]
    | c :: rest =>
        if !inBrace && c == '{' then
          let acc := if cur.isEmpty then acc
                     else acc ++ [.literal (String.ofList cur.reverse)]
          go [] acc true rest
        else if inBrace && c == '}' then
          go [] (acc ++ [.var (String.ofList cur.reverse)]) false rest
        else go (c :: cur) acc inBrace rest
  go [] [] false raw.toList

/-- RFC 3986 unreserved: ALPHA / DIGIT / "-" / "." / "_" / "~". -/
def isUnreserved (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') ||
  c == '-' || c == '.' || c == '_' || c == '~'

/-- RFC 3986 reserved (gen-delims + sub-delims), which fragment
    expansion passes through unencoded. -/
def isReserved (c : Char) : Bool :=
  ":/?#[]@".contains c || "!$&'()*+,;=".contains c

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)

/-- Percent-encode one character's UTF-8 bytes. -/
def encodeChar (c : Char) : String :=
  String.ofList (
    (String.mk [c]).toUTF8.toList.flatMap (fun b =>
      ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]))

/-- Simple expansion `{var}`: everything but unreserved is encoded. -/
def encodeSimple (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if isUnreserved c then String.mk [c] else encodeChar c)) ""

/-- Fragment expansion `{#var}`: reserved characters pass through. -/
def encodeFragment (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ (if isUnreserved c || isReserved c then String.mk [c] else encodeChar c)) ""

/-- Is this a `{#var}` reference? -/
def varIsFragment (v : String) : Bool := v.startsWith "#"

/-- The variable name with any operator character stripped. -/
def varName (v : String) : String := if varIsFragment v then String.ofList (v.toList.drop 1) else v

/-- Expand one segment.

    THE FRAGMENT RULE, and the reason it is spelled out: RFC 6570
    §3.2.4 says a DEFINED variable under `{#var}` is prefixed with a
    literal `'#'`, while an UNDEFINED one produces no output at all —
    not even a stray `'#'`. Dropping that prefix made
    `countries.csv{#countryCode}` expand to `countries.csvAD` instead
    of `countries.csv#AD`, which broke every aboutUrl/valueUrl
    fragment template in the csv2rdf corpus. The F* module carries
    that fix; this port carries it with a regression guard. -/
def expandSegment (lookup : String → Option String) : Segment → String
  | .literal l => l
  | .var v =>
      match lookup (varName v) with
      | none     => ""
      | some raw =>
          if varIsFragment v then "#" ++ encodeFragment raw
          else encodeSimple raw

/-- Expand a whole template against a row/column-scoped lookup. The
    result may still be a relative reference; resolving it against the
    document base IRI belongs to the conversion step. -/
def expand (lookup : String → Option String) (raw : String) : String :=
  (parse raw).foldl (fun acc s => acc ++ expandSegment lookup s) ""

end UriTemplate
end L4Factoidal.CSVW
