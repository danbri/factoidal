/-
L4Factoidal.Regex.XSDPattern — the XSD-flavour regular-expression PARSER.

Port of `formal/fstar/Regex.XSDPattern.fst` (issue #304, phase 2). Parses
XML Schema Part 2 Appendix F pattern syntax
(https://www.w3.org/TR/xmlschema-2/#regexs), plus the XPath `^` / `$`
anchors, into the `Re` AST over codepoints.

Constructs implemented (the F* source derived this set by measuring the
fixture corpora it feeds — OWL, CSVW, SHACL, ShEx): literals (any
codepoint), `.`, character classes `[...]` with ranges and the
`\d \D \s \S \w \W` escapes, negated classes `[^...]`, single-char
escapes (`\n \r \t \f \\ \. \- \/ \^ \$ \( \) \[ \] \{ \} \| \* \+ \?`),
Unicode escapes `\uHHHH` / `\UHHHHHHHH`, quantifiers `?` `*` `+` `{n}`
`{n,}` `{n,m}` (a trailing lazy `?` is accepted and ignored — lazy vs
greedy does not change the LANGUAGE), groups `(...)` and `(?:...)`,
alternation `|`, and the anchors `^` / `$`, parsed as no-ops because
this parser's reading is WHOLE-STRING membership (the XPath layer in
`Regex.XPath` turns them into real anchors before calling it).

Constructs that cleanly return `none` (outside the fragment):
lookahead / lookbehind / flag groups `(?=` `(?!` `(?<` `(?i)`, category
escapes `\p{...}` / `\P{...}`, and backreferences `\1` (not regular).
`\w` / `\W` use the ECMAScript definition `[A-Za-z0-9_]`; the XSD
category-table definition is not ported (no fixture needs it), as in
the F*.

Totality: recursive descent over `List Nat`, terminated by an explicit
fuel that decreases on every call (`parseCps` sets it to a multiple of
the input length, so no real pattern exhausts it). The F* class scanner
recurses on the input length; here it carries the same fuel.
-/
import L4Factoidal.Regex.Syntax

namespace L4Factoidal.Regex.XSDPattern

/-! ## Codepoint constants for the metacharacters -/

def cpLparen   : Nat := 0x28
def cpRparen   : Nat := 0x29
def cpLbracket : Nat := 0x5B
def cpRbracket : Nat := 0x5D
def cpLbrace   : Nat := 0x7B
def cpRbrace   : Nat := 0x7D
def cpPipe     : Nat := 0x7C
def cpStar     : Nat := 0x2A
def cpPlus     : Nat := 0x2B
def cpQuestion : Nat := 0x3F
def cpDot      : Nat := 0x2E
def cpCaret    : Nat := 0x5E
def cpDollar   : Nat := 0x24
def cpBackslash: Nat := 0x5C
def cpHyphen   : Nat := 0x2D
def cpComma    : Nat := 0x2C
def cpColon    : Nat := 0x3A
def cp0        : Nat := 0x30
def cp9        : Nat := 0x39
def cpU        : Nat := 0x75   -- `u`
def cpUU       : Nat := 0x55   -- `U`

/-! ## Leaf builders -/

/-- A single-codepoint literal class (F* `single`). -/
def single (c : Nat) : Re := .ranges [(c, c)]

/-- XSD `.`: any character except newline (#xA) and carriage return (#xD)
(F* `dot_regex`). -/
def dotRegex : Re := .ranges (complementRanges [(0x0A, 0x0A), (0x0D, 0x0D)])

/-! ## Escapes -/

def hexVal (c : Nat) : Option Nat :=
  if c ≥ 0x30 && c ≤ 0x39 then some (c - 0x30)
  else if c ≥ 0x61 && c ≤ 0x66 then some (c - 0x61 + 10)
  else if c ≥ 0x41 && c ≤ 0x46 then some (c - 0x41 + 10)
  else none

/-- Read exactly `n` hex digits, accumulating the value (F* `read_hex_n`). -/
def readHexN : Nat → List Nat → Nat → Option (Nat × List Nat)
  | 0, input, acc => some (acc, input)
  | n + 1, input, acc =>
    match input with
    | [] => none
    | c :: t =>
      match hexVal c with
      | none => none
      | some v => readHexN n t (acc * 16 + v)

/-- Single-character escapes: control chars and escaped metacharacters
(F* `char_escape`). -/
def charEscape (letter : Nat) : Option Nat :=
  if letter = 0x6E then some 0x0A          -- \n
  else if letter = 0x72 then some 0x0D     -- \r
  else if letter = 0x74 then some 0x09     -- \t
  else if letter = 0x66 then some 0x0C     -- \f
  else if letter = cpBackslash then some 0x5C
  else if letter = cpDot then some 0x2E
  else if letter = cpHyphen then some 0x2D
  else if letter = 0x2F then some 0x2F     -- \/
  else if letter = cpCaret then some 0x5E
  else if letter = cpDollar then some 0x24
  else if letter = cpLparen then some 0x28
  else if letter = cpRparen then some 0x29
  else if letter = cpLbracket then some 0x5B
  else if letter = cpRbracket then some 0x5D
  else if letter = cpLbrace then some 0x7B
  else if letter = cpRbrace then some 0x7D
  else if letter = cpPipe then some 0x7C
  else if letter = cpStar then some 0x2A
  else if letter = cpPlus then some 0x2B
  else if letter = cpQuestion then some 0x3F
  else none

/-- Multi-character class escapes `\d \D \s \S \w \W` as codepoint ranges
(F* `class_escape_ranges`). `\s = {#x9 #xA #xD #x20}` (XSD);
`\w = [A-Za-z0-9_]` (ECMAScript); `\D \S \W` are the complements. -/
def classEscapeRanges (letter : Nat) : Option (List (Nat × Nat)) :=
  if letter = 0x64 then some [(0x30, 0x39)]                                          -- \d
  else if letter = 0x44 then some (complementRanges [(0x30, 0x39)])                  -- \D
  else if letter = 0x73 then some [(0x09, 0x0A), (0x0D, 0x0D), (0x20, 0x20)]         -- \s
  else if letter = 0x53 then
    some (complementRanges [(0x09, 0x0A), (0x0D, 0x0D), (0x20, 0x20)])              -- \S
  else if letter = 0x77 then some [(0x30, 0x39), (0x41, 0x5A), (0x5F, 0x5F), (0x61, 0x7A)]  -- \w
  else if letter = 0x57 then
    some (complementRanges [(0x30, 0x39), (0x41, 0x5A), (0x5F, 0x5F), (0x61, 0x7A)]) -- \W
  else none

/-- Escape as an ATOM (top-level `\...`) (F* `parse_escape_atom`). -/
def parseEscapeAtom (letter : Nat) (t2 : List Nat) : Option (Re × List Nat) :=
  match classEscapeRanges letter with
  | some rs => some (.ranges rs, t2)
  | none =>
    if letter = cpU then
      match readHexN 4 t2 0 with
      | some (cp, rest) => if cp ≤ maxCodepoint then some (single cp, rest) else none
      | none => none
    else if letter = cpUU then
      match readHexN 8 t2 0 with
      | some (cp, rest) => if cp ≤ maxCodepoint then some (single cp, rest) else none
      | none => none
    else match charEscape letter with
      | some cp => some (single cp, t2)
      | none => none

/-- Escape INSIDE a character class: the ranges it contributes
(F* `class_escape_item`). -/
def classEscapeItem (letter : Nat) (t2 : List Nat) : Option (List (Nat × Nat) × List Nat) :=
  match classEscapeRanges letter with
  | some rs => some (rs, t2)
  | none =>
    if letter = cpU then
      match readHexN 4 t2 0 with
      | some (cp, rest) => if cp ≤ maxCodepoint then some ([(cp, cp)], rest) else none
      | none => none
    else if letter = cpUU then
      match readHexN 8 t2 0 with
      | some (cp, rest) => if cp ≤ maxCodepoint then some ([(cp, cp)], rest) else none
      | none => none
    else match charEscape letter with
      | some cp => some ([(cp, cp)], t2)
      | none => none

/-! ## Character classes `[...]` -/

/-- Scan class items up to the closing `]` (F* `parse_class_items`).
Range items `a-z` need plain-codepoint endpoints with `lo ≤ hi`. The F*
recurses on the input length; the fuel here is set to that length by
`parseClass`. -/
def parseClassItems : Nat → List Nat → List (Nat × Nat) → Option (List (Nat × Nat) × List Nat)
  | 0, _, _ => none
  | _ + 1, [], _ => none                                     -- unterminated class
  | fuel + 1, h :: t, acc =>
    if h = cpRbracket then some (acc, t)                      -- end of class
    else if h = cpBackslash then
      match t with
      | [] => none
      | letter :: t2 =>
        match classEscapeItem letter t2 with
        | none => none
        | some (rs, t3) => parseClassItems fuel t3 (acc ++ rs)
    else
      match t with
      | d :: c2 :: t2 =>
        if d = cpHyphen && c2 ≠ cpRbracket && c2 ≠ cpBackslash && h ≤ c2 then
          parseClassItems fuel t2 (acc ++ [(h, c2)])         -- range h-c2
        else parseClassItems fuel t (acc ++ [(h, h)])        -- literal h
      | _ => parseClassItems fuel t (acc ++ [(h, h)])

/-- Insertion sort of an interval list by lower bound (F* `insert_range`
/ `sort_ranges`): `complementRanges` needs SORTED input, and a negated
class like `[^a-z0-9]` supplies its ranges in source order. -/
def insertRange (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: t => if x.1 ≤ y.1 then x :: y :: t else y :: insertRange x t

def sortRanges : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | y :: t => insertRange y (sortRanges t)

/-- Entry after the opening `[` (F* `parse_class`). A negated class
`[^...]` takes the complement (over `[0, maxCodepoint]`) of its sorted
ranges; exact for disjoint ranges. -/
def parseClass (input : List Nat) : Option (Re × List Nat) :=
  match input with
  | [] => none
  | h :: t =>
    if h = cpCaret then
      match parseClassItems (t.length + 1) t [] with
      | none => none
      | some (ranges, rest) => some (.ranges (complementRanges (sortRanges ranges)), rest)
    else
      match parseClassItems (input.length + 1) input [] with
      | none => none
      | some (ranges, rest) => some (.ranges ranges, rest)

/-! ## Quantifiers -/

/-- `r^n` (F* `repeat_exact`). -/
def repeatExact (r : Re) : Nat → Re
  | 0 => .eps
  | n + 1 => .cat r (repeatExact r n)

/-- `(r?)^k`, the `{n,m}` upper slack (F* `repeat_opt`). -/
def repeatOpt (r : Re) : Nat → Re
  | 0 => .eps
  | k + 1 => .cat (.alt r .eps) (repeatOpt r k)

/-- Read a (possibly empty) run of decimal digits (F* `read_digits_acc`). -/
def readDigitsAcc : List Nat → Nat → Bool → Nat × List Nat × Bool
  | c :: t, acc, seen =>
    if c ≥ cp0 && c ≤ cp9 then readDigitsAcc t (acc * 10 + (c - cp0)) true
    else (acc, c :: t, seen)
  | [], acc, seen => (acc, [], seen)

def readUint (input : List Nat) : Option (Nat × List Nat) :=
  let (v, rest, seen) := readDigitsAcc input 0 false
  if seen then some (v, rest) else none

/-- Parse a `{...}` quantifier body; `t` is AFTER the `{` (F* `parse_brace`). -/
def parseBrace (r : Re) (t : List Nat) : Option (Re × List Nat) :=
  match readUint t with
  | none => none
  | some (n, t1) =>
    match t1 with
    | c :: t2 =>
      if c = cpRbrace then some (repeatExact r n, t2)                               -- {n}
      else if c = cpComma then
        match t2 with
        | c2 :: t3 =>
          if c2 = cpRbrace then some (.cat (repeatExact r n) (.star r), t3)         -- {n,}
          else
            match readUint t2 with
            | none => none
            | some (m, t3') =>
              match t3' with
              | c3 :: t4 =>
                if c3 = cpRbrace && m ≥ n then
                  some (.cat (repeatExact r n) (repeatOpt r (m - n)), t4)           -- {n,m}
                else none
              | [] => none
        | [] => none
      else none
    | [] => none

/-- Drop a trailing lazy `?` (`*?`, `+?`, `??`): same language (F* `skip_lazy`). -/
def skipLazy : List Nat → List Nat
  | c :: t2 => if c = cpQuestion then t2 else c :: t2
  | [] => []

/-- Apply a postfix quantifier, if any, to a parsed atom (F* `parse_quant`). -/
def parseQuant (r : Re) (rest : List Nat) : Option (Re × List Nat) :=
  match rest with
  | [] => some (r, [])
  | q :: t =>
    if q = cpStar then some (.star r, skipLazy t)
    else if q = cpPlus then some (.cat r (.star r), skipLazy t)
    else if q = cpQuestion then some (.alt r .eps, skipLazy t)
    else if q = cpLbrace then
      match parseBrace r t with
      | none => none
      | some (r', t') => some (r', skipLazy t')
    else some (r, q :: t)

/-- Metacharacters that may not begin an atom (F* `is_atom_meta`). -/
def isAtomMeta (h : Nat) : Bool :=
  h = cpStar || h = cpPlus || h = cpQuestion || h = cpLbrace ||
  h = cpRbrace || h = cpRbracket || h = cpPipe || h = cpRparen

/-! ## Recursive-descent core (alt > seq > rep > atom > group), fuel-terminated -/

mutual
  /-- F* `parse_alt`. -/
  def parseAlt : Nat → List Nat → Option (Re × List Nat)
    | 0, _ => none
    | fuel + 1, input =>
      match parseSeq fuel input with
      | none => none
      | some (r1, rest) =>
        match rest with
        | c :: t =>
          if c = cpPipe then
            match parseAlt fuel t with
            | none => none
            | some (r2, rest2) => some (.alt r1 r2, rest2)
          else some (r1, c :: t)
        | [] => some (r1, [])

  /-- F* `parse_seq`. -/
  def parseSeq : Nat → List Nat → Option (Re × List Nat)
    | 0, _ => none
    | fuel + 1, input =>
      match input with
      | [] => some (.eps, [])
      | h :: _ =>
        if h = cpPipe || h = cpRparen then some (.eps, input)
        else
          match parseRep fuel input with
          | none => none
          | some (r1, rest) =>
            match rest with
            | [] => some (r1, [])
            | h2 :: _ =>
              if h2 = cpPipe || h2 = cpRparen then some (r1, rest)
              else
                match parseSeq fuel rest with
                | none => none
                | some (r2, rest2) => some (.cat r1 r2, rest2)

  /-- F* `parse_rep`. -/
  def parseRep : Nat → List Nat → Option (Re × List Nat)
    | 0, _ => none
    | fuel + 1, input =>
      match parseAtom fuel input with
      | none => none
      | some (r, rest) => parseQuant r rest

  /-- F* `parse_atom`. `^` / `$` parse to `eps` (whole-string reading). -/
  def parseAtom : Nat → List Nat → Option (Re × List Nat)
    | 0, _ => none
    | fuel + 1, input =>
      match input with
      | [] => none
      | h :: t =>
        if h = cpLparen then parseGroup fuel t
        else if h = cpLbracket then parseClass t
        else if h = cpDot then some (dotRegex, t)
        else if h = cpCaret then some (.eps, t)
        else if h = cpDollar then some (.eps, t)
        else if h = cpBackslash then
          match t with
          | [] => none
          | letter :: t2 => parseEscapeAtom letter t2
        else if isAtomMeta h then none
        else some (single h, t)

  /-- F* `parse_group`: `(?:` non-capturing, any other `(?` unsupported. -/
  def parseGroup : Nat → List Nat → Option (Re × List Nat)
    | 0, _ => none
    | fuel + 1, t =>
      match t with
      | q :: c :: t2 =>
        if q = cpQuestion && c = cpColon then parseGroupClose fuel t2
        else if q = cpQuestion then none
        else parseGroupClose fuel t
      | q :: _ =>
        if q = cpQuestion then none
        else parseGroupClose fuel t
      | [] => parseGroupClose fuel t

  /-- F* `parse_group_close`. -/
  def parseGroupClose : Nat → List Nat → Option (Re × List Nat)
    | 0, _ => none
    | fuel + 1, t =>
      match parseAlt fuel t with
      | none => none
      | some (r, rest) =>
        match rest with
        | c :: t2 => if c = cpRparen then some (r, t2) else none
        | [] => none
end

/-! ## Public API -/

/-- Parse a pattern given as a codepoint list; succeeds only if the ENTIRE
input is consumed (F* `parse_cps`). -/
def parseCps (cps : List Nat) : Option Re :=
  let fuel := 16 * (cps.length + 4)
  match parseAlt fuel cps with
  | some (r, []) => some r
  | _ => none

/-- Parse an XSD-flavour pattern string, or `none` if it uses a construct
outside the supported fragment (F* `parse_xsd_pattern`). -/
def parseXsdPattern (s : String) : Option Re := parseCps (cpsOfString s)

end L4Factoidal.Regex.XSDPattern
