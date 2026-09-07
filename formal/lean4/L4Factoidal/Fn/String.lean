/-
L4Factoidal.Fn.String — the string part of XQuery 1.0 and XPath 2.0
Functions and Operators (https://www.w3.org/TR/xpath-functions/), §5.

RIF-DTB 4.7 cites these by name; SPARQL 1.1 §17.4.3 cites the same
ones under SPARQL spellings (`SUBSTR`, `STRBEFORE`, `ENCODE_FOR_URI`,
`UCASE`, ...); XSLT reaches them through the XPath 1.0 function
library. The semantics is written HERE and the three front ends call
it.

Where the three specifications DISAGREE, the disagreement is a
separate function with both spellings kept, not a reconciliation. The
disagreements are listed in
`docs/designissues/2026-09-07-function-library.md` §4 and witnessed by
theorems in `L4Factoidal/Fn/Theorems.lean`.
-/

namespace L4Factoidal.Fn.String

/-! ## §5.4.5-5.4.7 — the three URI escapers

They differ only in WHICH characters they leave alone; every one of
them encodes the rest as the percent-escaped UTF-8 bytes of the
character. -/

def hexDigitUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

def pctByte (b : Nat) : String :=
  "%" ++ String.singleton (hexDigitUpper (b / 16)) ++ String.singleton (hexDigitUpper (b % 16))

/-- The UTF-8 bytes of one codepoint. -/
def utf8Bytes (c : Char) : List Nat :=
  let n := c.toNat
  if n < 0x80 then [n]
  else if n < 0x800 then [0xC0 + n / 64, 0x80 + n % 64]
  else if n < 0x10000 then [0xE0 + n / 4096, 0x80 + (n / 64) % 64, 0x80 + n % 64]
  else [0xF0 + n / 262144, 0x80 + (n / 4096) % 64, 0x80 + (n / 64) % 64, 0x80 + n % 64]

def pctEncodeWith (keep : Char → Bool) (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if keep c then String.singleton c
    else String.join ((utf8Bytes c).map pctByte)))

/-- RFC 3986 §2.3 unreserved: `ALPHA / DIGIT / "-" / "." / "_" / "~"`.
    `Char.isAlpha` is Lean's Unicode predicate, so it would keep an
    accented letter that RFC 3986 does not name; the set is written
    with explicit code-point ranges instead. -/
def isUnreserved (c : Char) : Bool :=
  let n := c.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57)
    || n == 45 || n == 46 || n == 95 || n == 126

/-- §5.4.5 `fn:encode-for-uri`, which SPARQL 1.1 §17.4.3.15
    `ENCODE_FOR_URI` and RIF-DTB 4.7 `func:encode-for-uri` both cite
    unchanged. One definition, three callers. -/
def encodeForUri (s : String) : String := pctEncodeWith isUnreserved s

/-- §5.4.6 `fn:iri-to-uri`: the unreserved AND reserved US-ASCII
    characters survive; everything else, non-ASCII included, is
    encoded. -/
def iriToUri (s : String) : String :=
  pctEncodeWith (fun c =>
    isUnreserved c || "!*'();:@&=+$,/?#[]%".toList.contains c) s

/-- §5.4.7 `fn:escape-html-uri`: every PRINTABLE US-ASCII character
    survives. -/
def escapeHtmlUri (s : String) : String :=
  pctEncodeWith (fun c => 32 ≤ c.toNat && c.toNat ≤ 126) s

/-! ## §5.4.1-5.4.4 — substrings -/

/-- The character index of the first occurrence of `needle` in
    `hay`, or `none`. An EMPTY needle occurs at index 0. -/
def indexOfSub (hay needle : String) : Option Nat :=
  let h := hay.toList
  let n := needle.toList
  let rec go (i : Nat) (rest : List Char) : Option Nat :=
    if n.isPrefixOf rest then some i
    else match rest with
      | []      => none
      | _ :: tl => go (i + 1) tl
  go 0 h

/-- §5.4.2 `fn:substring-before`: the empty string when the needle does
    not occur. XPath 1.0 §4.2 `substring-before()` and SPARQL 1.1
    §17.4.3.8 `STRBEFORE` agree with F&O here. -/
def substringBefore (hay needle : String) : String :=
  match indexOfSub hay needle with
  | some i => String.ofList (hay.toList.take i)
  | none   => ""

/-- §5.4.3 `fn:substring-after`. -/
def substringAfter (hay needle : String) : String :=
  match indexOfSub hay needle with
  | some i => String.ofList (hay.toList.drop (i + needle.toList.length))
  | none   => ""

/-- §5.4.4 `fn:substring` with a start and a length, 1-BASED: the
    window keeps every position `p` with `start <= p < start + length`.
    A start of 0 therefore loses the first character. SPARQL 1.1
    §17.4.3.3 `SUBSTR` cites this rule with `xs:integer` arguments;
    XPath 1.0 §4.2 cites it with `round()`ed doubles. -/
def substringFromLen (s : String) (start len : Int) : String :=
  String.ofList ((s.toList.zipIdx).filterMap (fun (c, i) =>
    let p : Int := Int.ofNat i + 1
    if start ≤ p && p < start + len then some c else none))

/-- §5.4.4 with a start only: every position from `start` on. -/
def substringFrom (s : String) (start : Int) : String :=
  String.ofList ((s.toList.zipIdx).filterMap (fun (c, i) =>
    let p : Int := Int.ofNat i + 1
    if start ≤ p then some c else none))

/-- The RIF Core Approved `Builtins_String` fixture asserts
    `substring("foobar" 3) = "bar"`, which is 0-BASED, while the same
    fixture's 3-argument line `substring("foobar" 0 3) = "fo"` is
    1-based. The two forms disagree on their base inside one fixture.
    This is the 2-argument form the RIF front end uses, kept separate
    from `substringFrom` so the disagreement is visible rather than
    averaged away. -/
def substringFromRif (s : String) (start : Int) : String :=
  if start ≤ 0 then s else String.ofList (s.toList.drop start.toNat)

/-! ## §5.3 — comparison, and §5.2 — assembly -/

/-- §5.3.6 `fn:compare` under the Unicode codepoint collation: -1, 0
    or 1. -/
def compare (a b : String) : Int :=
  match Ord.compare a.toList b.toList with
  | .lt => -1 | .eq => 0 | .gt => 1

/-- §5.4.1 `fn:concat`, variadic. XPath 1.0 `concat()` requires at
    least two arguments; that arity rule belongs to the front end, not
    here. -/
def concat (xs : List String) : String := String.join xs

/-- §5.4.6 `fn:string-join`. -/
def stringJoin (xs : List String) (sep : String) : String :=
  String.intercalate sep xs

/-- §5.3.1 `fn:contains`. An empty needle is contained in every
    string. -/
def contains (hay needle : String) : Bool := (indexOfSub hay needle).isSome

def startsWith (hay needle : String) : Bool := hay.startsWith needle
def endsWith (hay needle : String) : Bool := hay.endsWith needle

/-- §5.3.2 `fn:string-length`, in CODEPOINTS. -/
def stringLength (s : String) : Nat := s.toList.length

def upperCase (s : String) : String := s.toUpper
def lowerCase (s : String) : String := s.toLower

/-! ## RFC 4647 language-range matching

Two different filtering algorithms, and the front ends do not agree on
which one they use: RIF-DTB 4.10.2 `pred:matches-language-range` is
EXTENDED filtering (§3.3.2), SPARQL 1.1 §17.4.3.10 `langMatches` is
BASIC filtering (§3.3.1). Both are here, named for their algorithm. -/

/-- §3.3.2, the recursive part: the first range subtag has already
    matched. Each later range subtag must appear in order, `*` matches
    any one subtag, and a tag subtag that is skipped may not be a
    singleton. -/
def extendedRest : List String → List String → Bool
  | [],          _   => true
  | _ :: _,      []  => false
  | "*" :: rs,   ts  => extendedRest rs ts
  | r :: rs,  t :: ts =>
      if t == r then extendedRest rs ts
      else if t.length == 1 then false
      else extendedRest (r :: rs) ts

/-- RFC 4647 §3.3.2 EXTENDED filtering. -/
def matchesLanguageRange (tag range : String) : Bool :=
  let lc := fun (x : String) => x.toLower
  match (lc range).splitOn "-", (lc tag).splitOn "-" with
  | r :: rs, t :: ts => (r == "*" || r == t) && extendedRest rs ts
  | _, _             => false

/-- RFC 4647 §3.3.1 BASIC filtering: `*` matches any non-empty tag;
    otherwise the tag equals the range or extends it at a hyphen. -/
def langMatchesBasic (tag range : String) : Bool :=
  let t := tag.toLower
  let r := range.toLower
  if r == "*" then !t.isEmpty
  else t == r || t.startsWith (r ++ "-")

/-! ## Pins -/

-- The RIF-DTB 4.7 examples, which the Approved `Builtins_String`
-- fixture writes out.
#guard compare "bar" "foo" = -1
#guard compare "bar" "bar" = 0
#guard stringJoin ["foo", "bar"] "," = "foo,bar"
#guard substringFromRif "foobar" 3 = "bar"
#guard substringFromLen "foobar" 0 3 = "fo"
#guard substringBefore "foobar" "bar" = "foo"
#guard substringAfter "foobar" "foo" = "bar"
#guard encodeForUri "RIF Basic Logic Dialect" = "RIF%20Basic%20Logic%20Dialect"
#guard iriToUri "http://www.example.com/~bébé"
     = "http://www.example.com/~b%C3%A9b%C3%A9"
#guard escapeHtmlUri "a bé" = "a b%C3%A9"

-- F&O 5.4.4's own examples.
#guard substringFromLen "motor car" 6 3 = " ca"
#guard substringFromLen "metadata" 4 3 = "ada"
#guard substringFrom "motor car" 6 = " car"

-- RFC 4647 §3.3.2, the examples the specification lists, and the pair
-- that separates extended from basic filtering.
#guard matchesLanguageRange "de-at" "de-*" = true
#guard matchesLanguageRange "de-DE-1996" "de-de" = true
#guard matchesLanguageRange "de-Latn-DE" "de-*-DE" = true
#guard matchesLanguageRange "de-a-DE" "de-*-DE" = false
#guard matchesLanguageRange "en-GB" "de-*" = false
#guard langMatchesBasic "de-Latn-DE" "de-*-DE" = false
#guard langMatchesBasic "de-DE-1996" "de-DE" = true

end L4Factoidal.Fn.String
