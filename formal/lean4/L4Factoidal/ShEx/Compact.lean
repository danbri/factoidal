/-
L4Factoidal.ShEx.Compact — a ShExC (ShEx compact syntax) parser that
builds the SAME `Schema` the ShExJ reader builds.

Port of `formal/fstar/Parser.ShExC.fst`. Spec: ShEx 2.1
(http://shex.io/shex-semantics/) Appendix A, whose terminals
(IRIREF, PNAME, STRING, NUMBER) it borrows from Turtle and SPARQL by
the specification's own grammar credits.

Two phases, as in the F* module and for the same reason: a
character-level TOKENIZER, then a recursive-descent parser over the
token list. ShExC's shape-expression algebra — OR/AND/NOT precedence,
EachOf/OneOf grouping, cardinality suffixes, the shape-definition
modifiers — is a deeper non-terminal graph than Turtle's, and
keyword case-insensitivity, comments and whitespace are each handled
ONCE at tokenize time instead of at every grammar rule.

## Everything unsupported is a LOUD refusal

`parseShExC` returns `Except String Schema`. A construct outside the
grammar below stops the parse with a message naming what was found.
That is the property that makes a partial parser safe to ship: an
unparsed schema is visibly unparsed, never a schema that validates
the wrong graphs. The differential runner counts a refusal apart from
a mismatch for exactly that reason.

## What this parser reads

Directives `PREFIX` / `BASE` / `IMPORT` (SPARQL-style, keywords
case-insensitive); `start = …`; shape declarations with an IRI,
prefixed-name or blank-node label; the shape-expression algebra
`OR` / `AND` / `NOT` with parentheses; shape references `@label`; the
wildcard `.`; shape definitions `{ … }` with `CLOSED`, `EXTRA` and
`EXTENDS`; triple expressions separated by `;` and `|`; triple
constraints with `^` inverse, the Turtle `a` shorthand, cardinality
`*` `+` `?` `{m,n}` `{m,}`; node constraints with a node kind, a
datatype, a value set, and the numeric and string facets.
-/
import L4Factoidal.ShEx.Schema
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.ShEx.Compact

open L4Factoidal.ShEx

/-! ## Tokens -/

inductive Tok where
  /-- `<iri>`, unresolved. -/
  | iri   (raw : String)
  /-- `ns:local`; `local` is empty for a bare `ns:`. -/
  | pname (ns : String) (localPart : String)
  | bnode (label : String)
  /-- A string literal with an optional language tag or datatype. -/
  | str   (lex : String) (lang : Option String) (dt : Option String)
  /-- A numeric literal, with the datatype its lexical form implies. -/
  | num   (lex : String) (dt : String)
  /-- A keyword, UPPERCASED — ShExC keywords are case-insensitive. -/
  | kw    (k : String)
  | punct (p : String)
  /-- `/pattern/flags`. -/
  | regex (pattern : String) (flags : String)
  /-- `@fr`, `@fr-be`: a LANGTAG in a value set. Kept apart from
      `punct "@"` (the shape-reference marker) because the two carry
      different things and only the tokenizer can see which is which:
      a shape reference's label always has a colon or angle brackets,
      a language tag never does. -/
  | lang  (tag : String)
deriving Repr, DecidableEq, Inhabited

abbrev Chars := Array Char

def charAt (s : Chars) (i : Nat) : Option Char := s[i]?

/-- A character READ at an index is a character IN RANGE. This is the
    whole termination argument of every index-walking scanner below:
    the walker only steps past an index it has read, so `s.size - i`
    decreases at every step. -/
theorem charAt_lt {s : Chars} {i : Nat} {c : Char} (h : charAt s i = some c) :
    i < s.size := by
  rcases Nat.lt_or_ge i s.size with hlt | hge
  . exact hlt
  . rw [charAt, Array.getElem?_eq_none hge] at h
    simp at h
def isAt (s : Chars) (i : Nat) (c : Char) : Bool := charAt s i == some c

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-! ### Trivia

`skipTrivia` skips whitespace, `#` line comments and `/* … */` block
comments. A `/` is only a comment opener when the next character is
`*`; otherwise it opens a regular expression, which is why this cannot
be a plain character class. -/

/-- Skip to just past the next newline, ending a `#` comment.

    The result is packaged with the proof that it did not go BACKWARDS.
    `skipTrivia` restarts at that index, so without the bound its own
    recursion has no measure; carrying the bound in the return type
    avoids a separate induction over this function. -/
def skipToEol (s : Chars) (j : Nat) : { k : Nat // j ≤ k } :=
  match h : charAt s (j) with
  | none => ⟨j, Nat.le_refl j⟩
  | some d =>
      if d == '\n' then ⟨j + 1, Nat.le_succ j⟩
      else
        let r := skipToEol s (j + 1)
        ⟨r.1, Nat.le_trans (Nat.le_succ j) r.2⟩
  termination_by s.size - j
  decreasing_by (have hlt := charAt_lt h; omega)

/-- Skip to just past the closing `*/` of a block comment, with the
    same non-decreasing bound. -/
def skipToBlockEnd (s : Chars) (j : Nat) : { k : Nat // j ≤ k } :=
  match hA : charAt s (j) with
  | none => ⟨j, Nat.le_refl j⟩
  | some a =>
      match charAt s (j+1) with
      | none => ⟨j + 1, Nat.le_succ j⟩
      | some b =>
          if a == '*' && b == '/' then ⟨j + 2, by omega⟩
          else
            let r := skipToBlockEnd s (j + 1)
            ⟨r.1, Nat.le_trans (Nat.le_succ j) r.2⟩
  termination_by s.size - j
  decreasing_by (have hlt := charAt_lt hA; omega)

def skipTrivia (s : Chars) (i : Nat) : Nat :=
  match h : charAt s (i) with
  | none   => i
  | some c =>
    if isWs c then skipTrivia s (i + 1)
    else if c == '#' then
      skipTrivia s (skipToEol s (i + 1)).1
    else if c == '/' && charAt s (i+1) == some '*' then
      skipTrivia s (skipToBlockEnd s (i + 2)).1
    else i
  termination_by s.size - i
  decreasing_by
    all_goals
      (have hlt := charAt_lt h
       first
         | omega
         | (have hb := (skipToEol s (i + 1)).2; omega)
         | (have hb := (skipToBlockEnd s (i + 2)).2; omega))

/-! ### Name characters

`PN_CHARS_BASE` and friends, restricted to what the corpus uses plus
the non-ASCII range, which is admitted wholesale: a name character
test that rejected non-ASCII would reject legal ShExC, and admitting
it cannot make an illegal document parse as a DIFFERENT legal one. -/

def isPnCharsBase (c : Char) : Bool :=
  c.isAlpha || c.toNat ≥ 0x80

def isPnChars (c : Char) : Bool :=
  isPnCharsBase c || c.isDigit || c == '_' || c == '-' || c == '·'

def isPnCharsU (c : Char) : Bool := isPnCharsBase c || c == '_'

/-- Scan `PN_LOCAL`, which admits `.` and `:` INSIDE but not at the
    end — a trailing dot is the statement separator, not part of the
    name. -/
def scanPnLocal (s : Chars) (i : Nat) : String × Nat :=
  let rec go (j : Nat) (acc : List Char) : List Char × Nat :=
    match h : charAt s (j) with
    | none   => (acc, j)
    | some c =>
        if isPnChars c || c == ':' || c == '%' then go (j + 1) (c :: acc)
        else if c == '\\' then
          match charAt s (j+1) with
          | some d => go (j + 2) (d :: acc)
          | none   => (acc, j)
        else if c == '.' then
          -- A dot belongs to the name only when a name character
          -- follows it.
          match charAt s (j+1) with
          | some d => if isPnChars d || d == ':' then go (j + 1) (c :: acc) else (acc, j)
          | none   => (acc, j)
        else (acc, j)
  termination_by s.size - j
  decreasing_by all_goals (have hlt := charAt_lt h; omega)
  let (acc, j) := go i []
  (String.ofList acc.reverse, j)

def scanPnPrefix (s : Chars) (i : Nat) : String × Nat :=
  let rec go (j : Nat) (acc : List Char) : List Char × Nat :=
    match h : charAt s (j) with
    | none   => (acc, j)
    | some c =>
        if isPnChars c then go (j + 1) (c :: acc)
        else if c == '.' then
          match charAt s (j+1) with
          | some d => if isPnChars d then go (j + 1) (c :: acc) else (acc, j)
          | none   => (acc, j)
        else (acc, j)
  termination_by s.size - j
  decreasing_by all_goals (have hlt := charAt_lt h; omega)
  let (acc, j) := go i []
  (String.ofList acc.reverse, j)

/-! ### String escapes -/

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexRun (s : Chars) (i n : Nat) : Option Nat :=
  (List.range n).foldl (fun acc k =>
    acc.bind (fun v => ((charAt s (i + k)).bind hexVal).map (fun d => v * 16 + d))) (some 0)

/-- One escape after a backslash: the six ShExC/Turtle short escapes
    and the two `\uXXXX` / `\UXXXXXXXX` forms. -/
def readEscape (s : Chars) (i : Nat) : Option (Char × Nat) :=
  match charAt s (i) with
  | none => none
  | some c =>
    if c == 't' then some ('\t', i + 1)
    else if c == 'b' then some ((Char.ofNat 8), i + 1)
    else if c == 'n' then some ('\n', i + 1)
    else if c == 'r' then some ('\r', i + 1)
    else if c == 'f' then some ((Char.ofNat 12), i + 1)
    else if c == '"' then some ('"', i + 1)
    else if c == '\'' then some ('\'', i + 1)
    else if c == '\\' then some ('\\', i + 1)
    else if c == 'u' then (hexRun s (i + 1) 4).map (fun v => (Char.ofNat v, i + 5))
    else if c == 'U' then (hexRun s (i + 1) 8).map (fun v => (Char.ofNat v, i + 9))
    else none

/-- An escape CONSUMES at least one character. The string scanner
    restarts at the index this returns, so the strict increase is its
    whole termination argument. -/
theorem readEscape_lt {s : Chars} {i : Nat} {d : Char} {k : Nat}
    (h : readEscape s i = some (d, k)) : i < k := by
  unfold readEscape at h
  split at h
  . simp at h
  . repeat' split at h
    all_goals simp_all
    all_goals omega


/-! ### Scanning one token -/

/-- The keywords, uppercased. Recognised by a case-insensitive
    comparison of a whole identifier run, so a shape called
    `ORDER` is a label and not the operator `OR`. -/
def keywords : List String :=
  ["PREFIX", "BASE", "IMPORT", "START", "EXTERNAL", "CLOSED", "EXTRA",
   "EXTENDS", "ABSTRACT", "RESTRICTS", "AND", "OR", "NOT",
   "IRI", "BNODE", "NONLITERAL", "LITERAL",
   "MININCLUSIVE", "MAXINCLUSIVE", "MINEXCLUSIVE", "MAXEXCLUSIVE",
   "TOTALDIGITS", "FRACTIONDIGITS", "LENGTH", "MINLENGTH", "MAXLENGTH",
   "PATTERN", "TRUE", "FALSE"]

def xsdIri (localName : String) : String :=
  "http://www.w3.org/2001/XMLSchema#" ++ localName

/-- Scan a quoted string. Handles the single- and triple-quoted forms
    with either quote character. -/
def scanString (s : Chars) (i : Nat) (q : Char) : Option (String × Nat) :=
  let triple := charAt s (i) == some q && charAt s (i+1) == some q && charAt s (i+2) == some q
  let start := if triple then i + 3 else i + 1
  let rec go (j : Nat) (acc : List Char) : Option (String × Nat) :=
    match h : charAt s (j) with
    | none => none
    | some c =>
      if c == '\\' then
        match h2 : readEscape s (j + 1) with
        | some (d, k) => go k (d :: acc)
        | none        => none
      else if c == q then
        if triple then
          if charAt s (j+1) == some q && charAt s (j+2) == some q then
            some (String.ofList acc.reverse, j + 3)
          else go (j + 1) (c :: acc)
        else some (String.ofList acc.reverse, j + 1)
      else go (j + 1) (c :: acc)
  termination_by s.size - j
  decreasing_by
    all_goals
      (have hlt := charAt_lt h
       first
         | omega
         | (have he := readEscape_lt h2; omega))
  go start []

/-- Scan a regular-expression literal `/pattern/flags`. A backslash
    always consumes the next character, so `\/` denotes a slash; every
    OTHER escape is kept VERBATIM, backslash included, because the
    pattern is handed to a regular-expression engine that reads its
    own escapes. -/
def scanRegex (s : Chars) (i : Nat) : Option (String × String × Nat) :=
  let rec body (j : Nat) (acc : List Char) : Option (List Char × Nat) :=
    match h : charAt s j with
    | none => none
    | some c =>
      if c == '\\' then
        match charAt s (j + 1) with
        | some '/' => body (j + 2) ('/' :: acc)
        -- A UCHAR is a way of WRITING a character, so it is decoded;
        -- every other backslash escape belongs to the regular
        -- expression and is carried through untouched. Decoding all
        -- of them turned `\t` into a tab and `\-` into `-`, changing
        -- what the pattern matches; decoding none of them left
        -- `\u0061` where the ShExJ twin has `a`
        -- (1literalPattern_with_REGEXP_escapes).
        | some 'u' =>
            (match hexRun s (j + 2) 4 with
             | some v => body (j + 6) (Char.ofNat v :: acc)
             | none   => body (j + 2) ('u' :: '\\' :: acc))
        | some 'U' =>
            (match hexRun s (j + 2) 8 with
             | some v => body (j + 10) (Char.ofNat v :: acc)
             | none   => body (j + 2) ('U' :: '\\' :: acc))
        | some d   => body (j + 2) (d :: '\\' :: acc)
        | none     => none
      else if c == '/' then some (acc.reverse, j + 1)
      else body (j + 1) (c :: acc)
  termination_by s.size - j
  decreasing_by all_goals (have hlt := charAt_lt h; omega)
  match body (i + 1) [] with
  | none => none
  | some (pat, j) =>
      let rec flags (k : Nat) (acc : List Char) : List Char × Nat :=
        match h : charAt s k with
        | some c => if c.isAlpha then flags (k + 1) (c :: acc) else (acc, k)
        | none   => (acc, k)
      termination_by s.size - k
      decreasing_by all_goals (have hlt := charAt_lt h; omega)
      let (fl, k) := flags j []
      some (String.ofList pat, String.ofList fl.reverse, k)

/-- Scan a numeric literal, DOUBLE-AWARE first: `1e3` must not be read
    as the integer `1` followed by a name `e3` (anti-pattern 8). -/
def scanNumber (s : Chars) (i : Nat) : Option (String × String × Nat) :=
  let rec digits (j : Nat) (acc : List Char) : List Char × Nat :=
    match h : charAt s j with
    | some c => if c.isDigit then digits (j + 1) (c :: acc) else (acc, j)
    | none   => (acc, j)
  termination_by s.size - j
  decreasing_by all_goals (have hlt := charAt_lt h; omega)
  let (sign, i0) := match charAt s i with
    | some '+' => (['+'], i + 1)
    | some '-' => (['-'], i + 1)
    | _        => ([], i)
  let (ipRev, i1) := digits i0 []
  let ip := ipRev.reverse
  let (fp, i2) := match charAt s i1 with
    | some '.' =>
        let (dRev, k) := digits (i1 + 1) []
        if dRev.isEmpty && ip.isEmpty then ([], i1) else ('.' :: dRev.reverse, k)
    | _ => ([], i1)
  if ip.isEmpty && fp.isEmpty then none
  else
    let mant := sign ++ ip ++ fp
    let plainDt := xsdIri (if fp.isEmpty then "integer" else "decimal")
    match charAt s i2 with
    | some e =>
      if e == 'e' || e == 'E' then
        let (esign, j0) := match charAt s (i2 + 1) with
          | some '+' => (['+'], i2 + 2)
          | some '-' => (['-'], i2 + 2)
          | _        => ([], i2 + 1)
        let (edRev, j1) := digits j0 []
        if edRev.isEmpty then some (String.ofList mant, plainDt, i2)
        else some (String.ofList (mant ++ [e] ++ esign ++ edRev.reverse),
                   xsdIri "double", j1)
      else some (String.ofList mant, plainDt, i2)
    | none => some (String.ofList mant, plainDt, i2)

/-- Punctuation, LONGEST FIRST so `^^` is not read as two `^`. -/
def punctTable : List String :=
  ["^^", "//", "{", "}", "(", ")", "[", "]", ";", "|", ",", "@", "^", "$",
   "&", "=", "-", "~", "*", "+", "?", "!", ".", "%"]

/-- Read the IRI between angle brackets. -/
def scanAngle (s : Chars) (i : Nat) : Option (String × Nat) :=
  let rec go (j : Nat) (acc : List Char) : Option (String × Nat) :=
    match h : charAt s j with
    | none   => none
    | some d =>
      if d == '>' then some (String.ofList acc.reverse, j + 1)
      else if d == '\\' then
        -- An IRIREF carries `\uXXXX` / `\UXXXXXXXX` UCHARs. Keeping
        -- them verbatim gave a predicate spelled
        -- `http://a.example/p\u0031` where the ShExJ twin has
        -- `.../p1` (1IRI_with_UCHAR.1dot) — a different IRI, so a
        -- different schema.
        (match charAt s (j + 1) with
         | some 'u' => (hexRun s (j + 2) 4).bind (fun v => go (j + 6) (Char.ofNat v :: acc))
         | some 'U' => (hexRun s (j + 2) 8).bind (fun v => go (j + 10) (Char.ofNat v :: acc))
         | _        => go (j + 1) (d :: acc))
      else go (j + 1) (d :: acc)
  termination_by s.size - j
  decreasing_by all_goals (have hlt := charAt_lt h; omega)
  go i []
/-! ### The token loop -/

/-- A datatype written as a prefixed name is carried through the token
    stream tagged, because it cannot be resolved until the parser
    knows the prefix map — directives may appear anywhere among ShExC
    statements, so resolving eagerly at tokenize time would be
    wrong. -/
def pnameTag : String := " pname:"
def bareTag : String := " bare"

def tokenize (s : Chars) : Except String (List Tok) :=
  let rec go (i : Nat) (acc : List Tok) (fuel : Nat) : Except String (List Tok) :=
    match fuel with
    | 0     => .error "tokenizer fuel exhausted"
    | f + 1 =>
      let i := skipTrivia s i
      match charAt s i with
      | none   => .ok acc
      | some c =>
        if c == '<' then
          match scanAngle s (i + 1) with
          | none          => .error "unterminated IRI reference"
          | some (raw, j) => go j (acc ++ [.iri raw]) f
        else if c == '"' || c == '\'' then
          match scanString s i c with
          | none => .error "unterminated string literal"
          | some (lex, j) =>
            if charAt s j == some '@' then
              let rec tag (k : Nat) (a : List Char) : List Char × Nat :=
                match h : charAt s k with
                | some d => if d.isAlphanum || d == '-' then tag (k + 1) (d :: a) else (a, k)
                | none   => (a, k)
              termination_by s.size - k
              decreasing_by all_goals (have hlt := charAt_lt h; omega)
              let (t, k) := tag (j + 1) []
              if t.isEmpty then .error "empty language tag"
              else
                -- RDF 1.1 Concepts 3.3: the VALUE of a language tag is
                -- its lowercase form. `"x"@en-UK` and `"x"@en-uk` are
                -- one literal, and the ShExJ twins write the lowercase
                -- form (1val1STRING_LITERAL2_with_subtag).
                go k (acc ++ [.str lex (some (String.ofList t.reverse).toLower) none]) f
            else if charAt s j == some '^' && charAt s (j + 1) == some '^' then
              let k := skipTrivia s (j + 2)
              match charAt s k with
              | some '<' =>
                  (match scanAngle s (k + 1) with
                   | none         => .error "unterminated datatype IRI"
                   | some (dt, m) => go m (acc ++ [.str lex none (some dt)]) f)
              | some d =>
                  if isPnCharsU d || d == ':' then
                    let (ns, m) := scanPnPrefix s k
                    if charAt s m == some ':' then
                      let (lp, m2) := scanPnLocal s (m + 1)
                      go m2 (acc ++ [.str lex none (some (pnameTag ++ ns ++ ":" ++ lp))]) f
                    else .error "malformed datatype prefixed name"
                  else .error "malformed datatype"
              | none => .error "truncated datatype"
            else go j (acc ++ [.str lex none none]) f
        else if c == '_' && charAt s (i + 1) == some ':' then
          let (lp, j) := scanPnLocal s (i + 2)
          go j (acc ++ [.bnode lp]) f
        else if c.isDigit ||
                ((c == '+' || c == '-') &&
                 ((charAt s (i + 1)).map Char.isDigit == some true)) then
          match scanNumber s i with
          | none              => .error "malformed numeric literal"
          | some (lex, dt, j) => go j (acc ++ [.num lex dt]) f
        else if c == '%' then
          -- A SEMANTIC ACTION: `%iri%` or `%iri{ code %}`. Both
          -- readers ignore semantic actions, so this consumes one and
          -- emits NO token — recording it on one side only would make
          -- every schema carrying one differ.
          let k := skipTrivia s (i + 1)
          let k2 := (match charAt s k with
            | some '<' => (match scanAngle s (k + 1) with
                           | some (_, m) => m
                           | none        => k)
            | _ => let (ns, m) := scanPnPrefix s k
                   let _ := ns
                   if charAt s m == some ':' then (scanPnLocal s (m + 1)).2 else m)
          let k3 := skipTrivia s k2
          (match charAt s k3 with
           | some '%' => go (k3 + 1) acc f
           | some '{' =>
             -- Scan to the closing `%}`, honouring `\` escapes so a
             -- `\%` inside the code body does not end it early.
             let rec toEnd (m : Nat) : Nat :=
               match h : charAt s m with
               | none     => m
               | some '\\' => toEnd (m + 2)
               | some '%'  => if charAt s (m + 1) == some '}' then m + 2 else toEnd (m + 1)
               | some _    => toEnd (m + 1)
             termination_by s.size - m
             decreasing_by all_goals (have hlt := charAt_lt h; omega)
             go (toEnd (k3 + 1)) acc f
           | _ => .error "malformed semantic action")
        else if c == '/' && charAt s (i + 1) == some '/' then
          -- `//` OPENS AN ANNOTATION. Reaching the regex scanner
          -- first, it read an EMPTY regex `//` and left the
          -- annotation's predicate and object as loose tokens, so
          -- every annotated schema died at the closing brace
          -- ("expected '}', found //" — 1inversedotAnnot3,
          -- kitchenSink, _all and 11 more).
          go (i + 2) (acc ++ [.punct "//"]) f
        else if c == '/' then
          match scanRegex s i with
          | none              => .error "unterminated regular expression"
          | some (pat, fl, j) => go j (acc ++ [.regex pat fl]) f
        else if isPnCharsU c then
          let (ns, j) := scanPnPrefix s i
          if charAt s j == some ':' then
            let (lp, k) := scanPnLocal s (j + 1)
            go k (acc ++ [.pname ns lp]) f
          else
            let up := ns.toUpper
            if keywords.contains up then go j (acc ++ [.kw up]) f
            else go j (acc ++ [.pname bareTag ns]) f
        else if c == '@' then
          -- `@` begins a shape reference (`@<iri>`, `@ex:S1`, `@:S1`,
          -- `@_:b`) or a LANGTAG (`@fr`, `@fr-be`). Only a letter can
          -- start a langtag, and only a colon after the name means a
          -- prefixed shape label, so one character of lookahead
          -- separates them.
          (match charAt s (i + 1) with
           | some d =>
             if d.isAlpha then
               let (nm, k) := scanPnPrefix s (i + 1)
               if charAt s k == some ':' then go (i + 1) (acc ++ [.punct "@"]) f
               else go k (acc ++ [.lang nm.toLower]) f
             else go (i + 1) (acc ++ [.punct "@"]) f
           | none => go (i + 1) (acc ++ [.punct "@"]) f)
        else if c == ':' then
          let (lp, j) := scanPnLocal s (i + 1)
          go j (acc ++ [.pname "" lp]) f
        else
          match punctTable.find? (fun p =>
            (p.toList.zipIdx).all (fun (ch, k) => charAt s (i + k) == some ch)) with
          | some p => go (i + p.length) (acc ++ [.punct p]) f
          | none   => .error s!"unexpected character in ShExC: {c}"
  go 0 [] (s.size * 4 + 16)

/-! ## Parsing

A hand-written recursive descent over the token list. Every function
takes the parse STATE (the prefix map and the base IRI, which a
directive anywhere in the document may extend) and the remaining
tokens, and returns a value with the tokens left. -/

structure PState where
  prefixes : List (String × String) := []
  base     : String := ""
deriving Repr, Inhabited

abbrev Res (a : Type) := Except String (a × List Tok)

def fail (msg : String) : Res a := .error msg

def showTok : Tok → String
  | .iri r       => "<" ++ r ++ ">"
  | .pname ns lp => if ns == bareTag then lp else ns ++ ":" ++ lp
  | .bnode b     => "_:" ++ b
  | .str l _ _   => "\"" ++ l ++ "\""
  | .num l _     => l
  | .kw k        => k
  | .punct p     => p
  | .regex p _   => "/" ++ p ++ "/"
  | .lang t      => "@" ++ t

def expectPunct (p : String) : List Tok → Res Unit
  | .punct q :: r => if q == p then .ok ((), r) else fail s!"expected '{p}', found '{q}'"
  | t :: _        => fail s!"expected '{p}', found {showTok t}"
  | []            => fail s!"expected '{p}', found end of input"

def peekPunct : List Tok → Option String
  | .punct p :: _ => some p
  | _             => none

def peekKw : List Tok → Option String
  | .kw k :: _ => some k
  | _          => none

/-- Resolve a lexical term to an absolute IRI. An UNDECLARED prefix is
    an error, not a guessed expansion: a schema whose labels came out
    of a prefix nobody declared would validate against IRIs nobody
    wrote. -/
def resolveTerm (st : PState) : Tok → Except String String
  | .iri raw =>
      .ok (if st.base == "" then raw else L4Factoidal.Syntax.resolveIri st.base raw)
  | .pname ns lp =>
      if ns == bareTag then .error s!"bare name '{lp}' where an IRI was expected"
      else match st.prefixes.find? (fun (p, _) => p == ns) with
        | some (_, iri) => .ok (iri ++ lp)
        | none          => .error s!"undeclared prefix '{ns}:'"
  | .bnode b => .ok ("_:" ++ b)
  | t        => .error s!"expected an IRI, found {showTok t}"

/-- The datatype tag a literal token carries, resolved. -/
def resolveDt (st : PState) (dt : String) : Except String String :=
  if dt.startsWith pnameTag then
    let rest := String.ofList (dt.toList.drop pnameTag.length)
    match rest.splitOn ":" with
    | [ns, lp] => resolveTerm st (.pname ns lp)
    | _        => .error "malformed datatype prefixed name"
  else .ok (if st.base == "" then dt else L4Factoidal.Syntax.resolveIri st.base dt)

/-- The `ObjectValue` a value-set member denotes. -/
def objectValueOfTok (st : PState) : Tok → Except String ObjectValue
  | .str lex lang dt =>
      (match dt with
       | none    => .ok (ObjectValue.literal lex lang none)
       | some d  => (resolveDt st d).map (fun i => ObjectValue.literal lex lang (some i)))
  | .num lex dt => .ok (ObjectValue.literal lex none (some dt))
  | .kw "TRUE"  => .ok (ObjectValue.literal "true" none (some (xsdIri "boolean")))
  | .kw "FALSE" => .ok (ObjectValue.literal "false" none (some (xsdIri "boolean")))
  | t           => (resolveTerm st t).map ObjectValue.iri

/-! ### Cardinality -/

def digitsOf (s : String) : Option Int :=
  if s.isEmpty then none
  else s.toList.foldl (fun acc c =>
    acc.bind (fun n => if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat : Int)) else none))
    (some (0 : Int))

/-- `*` `+` `?` `{m}` `{m,n}` `{m,*}` `{m,}`. Absent is `(1, 1)`, and
    UNBOUNDED is `-1`, matching the ShExJ encoding the JSON reader
    produces. -/
def parseCardinality (ts : List Tok) : Option (Int × Int) × List Tok :=
  match ts with
  | .punct "*" :: r => (some (0, -1), r)
  | .punct "+" :: r => (some (1, -1), r)
  | .punct "?" :: r => (some (0, 1), r)
  | .punct "{" :: .num m _ :: rest =>
      (match digitsOf m, rest with
       | some mi, .punct "}" :: r2 => (some (mi, mi), r2)
       | some mi, .punct "," :: .punct "*" :: .punct "}" :: r2 => (some (mi, -1), r2)
       | some mi, .punct "," :: .punct "}" :: r2 => (some (mi, -1), r2)
       | some mi, .punct "," :: .num n _ :: .punct "}" :: r2 =>
           (match digitsOf n with
            | some ni => (some (mi, ni), r2)
            | none    => (none, ts))
       | _, _ => (none, ts))
  | _ => (none, ts)
/-! ### Facets and value sets -/

def isNumericFacetKw (k : String) : Bool :=
  ["MININCLUSIVE", "MAXINCLUSIVE", "MINEXCLUSIVE", "MAXEXCLUSIVE",
   "TOTALDIGITS", "FRACTIONDIGITS"].contains k

def isStringFacetKw (k : String) : Bool :=
  ["LENGTH", "MINLENGTH", "MAXLENGTH", "PATTERN"].contains k

def isNodeKindKw (k : String) : Bool :=
  ["IRI", "BNODE", "NONLITERAL", "LITERAL"].contains k

def nodeKindOfKw : String → Option NodeKind
  | "IRI"        => some .iri
  | "BNODE"      => some .bnode
  | "NONLITERAL" => some .nonLiteral
  | "LITERAL"    => some .literal
  | _            => none

/-- Apply one facet to the constraint being built. -/
def applyFacet (nc : NodeConstraint) (k : String) : Tok → Except String NodeConstraint
  | .num lex _ =>
      -- The numeric facets keep their VALUE, not their spelling —
      -- see `canonNumericLexeme`.
      let cn := canonNumericLexeme lex
      (match k with
       | "MININCLUSIVE"   => .ok { nc with minInclusive := some cn }
       | "MAXINCLUSIVE"   => .ok { nc with maxInclusive := some cn }
       | "MINEXCLUSIVE"   => .ok { nc with minExclusive := some cn }
       | "MAXEXCLUSIVE"   => .ok { nc with maxExclusive := some cn }
       | "TOTALDIGITS"    => (match digitsOf lex with
                              | some n => .ok { nc with totalDigits := some n }
                              | none   => .error "TOTALDIGITS needs an integer")
       | "FRACTIONDIGITS" => (match digitsOf lex with
                              | some n => .ok { nc with fractionDigits := some n }
                              | none   => .error "FRACTIONDIGITS needs an integer")
       | "LENGTH"         => (match digitsOf lex with
                              | some n => .ok { nc with length := some n }
                              | none   => .error "LENGTH needs an integer")
       | "MINLENGTH"      => (match digitsOf lex with
                              | some n => .ok { nc with minLength := some n }
                              | none   => .error "MINLENGTH needs an integer")
       | "MAXLENGTH"      => (match digitsOf lex with
                              | some n => .ok { nc with maxLength := some n }
                              | none   => .error "MAXLENGTH needs an integer")
       | _ => .error s!"facet {k} does not take a number")
  | .str lex _ _ =>
      if k == "PATTERN" then .ok { nc with pattern := some lex }
      else .error s!"facet {k} does not take a string"
  | t => .error s!"facet {k} does not take {showTok t}"

/-- One `- value` exclusion of a stem range, with the KIND its form
    implies. The kind travels with the exclusion because a WILDCARD
    stem (`[. - "v1"]`) has nothing else to say what family it
    restricts: the ShExJ twin writes `LiteralStemRange` there, and a
    reader that assumed `IriStemRange` disagreed with the JSON on
    every wildcard range whose exclusions were not IRIs
    (1val1dotMinusliteral3 and its language and stem variants). -/
def parseOneExclusion (st : PState) (r : List Tok)
    : Except String (Option ((VsvKind × Exclusion) × List Tok)) :=
  match r with
  | .punct "-" :: .lang tg :: rest =>
      (match rest with
       | .punct "~" :: rest2 => .ok (some ((.language, .stem tg), rest2))
       | _                   => .ok (some ((.language, .lang tg), rest)))
  | .punct "-" :: t :: rest =>
      (match objectValueOfTok st t with
       | .error e => .error e
       | .ok ov =>
         let kind : VsvKind := match ov with
           | .iri _                => .iri
           | .literal _ (some _) _ => .language
           | .literal ..           => .literal
         match rest with
         | .punct "~" :: rest2 =>
             let stemStr : String := match ov with
               | .iri v         => v
               | .literal l _ _ => l
             .ok (some ((kind, .stem stemStr), rest2))
         | _ => .ok (some ((kind, .value ov), rest)))
  | _ => .ok none

/-- Every `- value` exclusion that follows a stem. -/
def parseExclusions (st : PState) (ts : List Tok)
    : Except String (List (VsvKind × Exclusion) × List Tok) :=
  let rec go (r : List Tok) (acc : List (VsvKind × Exclusion)) (fuel : Nat)
      : Except String (List (VsvKind × Exclusion) × List Tok) :=
    match fuel with
    | 0     => .error "too many exclusions"
    | f + 1 =>
      match parseOneExclusion st r with
      | .error e            => .error e
      | .ok none            => .ok (acc, r)
      | .ok (some (e, r2))  => go r2 (acc ++ [e]) f
  go ts [] (ts.length + 1)

/-- The kind a WILDCARD stem range restricts, read off its exclusions:
    a language exclusion makes it a `LanguageStemRange`, a literal one
    a `LiteralStemRange`, and anything else an `IriStemRange`. -/
def wildcardKind (es : List (VsvKind × Exclusion)) : VsvKind :=
  if es.any (fun e => e.1 == .language) then .language
  else if es.any (fun e => e.1 == .literal) then .literal
  else .iri

/-- The `~` STEM forms. A bare stem is a `Stem`; a stem with
    exclusions is a `StemRange`, and the difference is what the ShExJ
    reader also makes, so the two front doors agree. -/
def parseValueSetValue (st : PState) (ts : List Tok)
    : Except String (ValueSetValue × List Tok) :=
  match ts with
  | .punct "." :: rest =>
      -- `. - v ~?` : a wildcard stem range with exclusions.
      (match parseExclusions st rest with
       | .error e     => .error e
       | .ok (es, r2) =>
           .ok (.stemRange (wildcardKind es) .wildcard (es.map Prod.snd), r2))
  | .lang tg :: rest =>
      -- `@fr` is an exact language, `@fr~` a language stem.
      (match rest with
       | .punct "~" :: rest2 =>
           (match parseExclusions st rest2 with
            | .error e      => .error e
            | .ok ([], r2)  => .ok (.stem .language (.plain tg), r2)
            | .ok (es, r2)  =>
                .ok (.stemRange .language (.plain tg) (es.map Prod.snd), r2))
       | _ => .ok (.language tg, rest))
  | .punct "@" :: .punct "~" :: rest =>
      -- `@~` : EVERY language, i.e. a language stem whose stem is the
      -- empty string. The tokenizer cannot make a `.lang` token here
      -- because there is no tag to carry.
      (match parseExclusions st rest with
       | .error e     => .error e
       | .ok ([], r2) => .ok (.stem .language (.plain ""), r2)
       | .ok (es, r2) =>
           .ok (.stemRange .language (.plain "") (es.map Prod.snd), r2))
  | t :: rest =>
      match objectValueOfTok st t with
      | .error e => .error e
      | .ok ov =>
        match rest with
        | .punct "~" :: rest2 =>
            -- A stem, possibly with `- …` exclusions.
            let kind : VsvKind := match ov with
              | .iri _                => .iri
              | .literal _ (some _) _ => .language
              | .literal ..           => .literal
            let stemStr : String := match ov with
              | .iri v         => v
              | .literal l _ _ => l
            (match parseExclusions st rest2 with
             | .error e     => .error e
             | .ok ([], r2) => .ok (.stem kind (.plain stemStr), r2)
             | .ok (es, r2) =>
                 .ok (.stemRange kind (.plain stemStr) (es.map Prod.snd), r2))
        | _ => .ok (.object ov, rest)
  | [] => .error "unterminated value set"

def parseValueSet (st : PState) (ts : List Tok)
    : Except String (List ValueSetValue × List Tok) :=
  let rec go (r : List Tok) (acc : List ValueSetValue) (fuel : Nat)
      : Except String (List ValueSetValue × List Tok) :=
    match fuel with
    | 0 => .error "value set is too long"
    | f + 1 =>
      match r with
      | .punct "]" :: rest => .ok (acc, rest)
      | []                 => .error "unterminated value set"
      | _ =>
        match parseValueSetValue st r with
        | .error e      => .error e
        | .ok (v, rest) => go rest (acc ++ [v]) f
  go ts [] (ts.length + 1)
/-! ### Node constraints -/

/-- Read a node constraint: a node kind, a datatype, a value set, or a
    run of facets — each followed by any number of further facets.
    `none` when the tokens do not begin one, which is how the caller
    tells a node constraint from a shape reference. -/
def parseNodeConstraint (st : PState) (ts : List Tok)
    : Except String (Option (NodeConstraint × List Tok)) :=
  let rec facets (nc : NodeConstraint) (r : List Tok) (fuel : Nat)
      : Except String (NodeConstraint × List Tok) :=
    match fuel with
    | 0 => .error "too many facets"
    | f + 1 =>
      match r with
      | .kw k :: v :: rest =>
          if isNumericFacetKw k || (isStringFacetKw k && k != "PATTERN") then
            match applyFacet nc k v with
            | .error e   => .error e
            | .ok nc2    => facets nc2 rest f
          else if k == "PATTERN" then
            match applyFacet nc k v with
            | .error e => .error e
            | .ok nc2  =>
              -- An optional FLAGS string may follow a PATTERN.
              (match rest with
               | .str fl _ _ :: rest2 => facets { nc2 with flags := some fl } rest2 f
               | _                    => facets nc2 rest f)
          else .ok (nc, r)
      | .regex pat fl :: rest =>
          facets { nc with pattern := some pat,
                           flags := if fl.isEmpty then none else some fl } rest f
      | _ => .ok (nc, r)
  match ts with
  | .kw k :: rest =>
      if isNodeKindKw k then
        (match facets { nodeKind := nodeKindOfKw k } rest (ts.length + 1) with
         | .error e => .error e
         | .ok p    => .ok (some p))
      else if isNumericFacetKw k || isStringFacetKw k then
        (match facets {} ts (ts.length + 1) with
         | .error e => .error e
         | .ok p    => .ok (some p))
      else .ok none
  | .regex _ _ :: _ =>
      (match facets {} ts (ts.length + 1) with
       | .error e => .error e
       | .ok p    => .ok (some p))
  | .punct "[" :: rest =>
      (match parseValueSet st rest with
       | .error e => .error e
       | .ok (vs, r2) =>
         match facets { values := vs } r2 (ts.length + 1) with
         | .error e => .error e
         | .ok p    => .ok (some p))
  | t :: rest =>
      -- A bare IRI or prefixed name in this position is a DATATYPE.
      -- A bare `a` is not: `a` is the predicate shorthand and never a
      -- datatype, so it is left for the caller.
      (match t with
       | .iri _ => match resolveTerm st t with
           | .error e => .error e
           | .ok d    => (match facets { datatype := some d } rest (ts.length + 1) with
                          | .error e => .error e
                          | .ok p    => .ok (some p))
       | .pname ns _ =>
           if ns == bareTag then .ok none
           else (match resolveTerm st t with
                 | .error e => .error e
                 | .ok d    => (match facets { datatype := some d } rest (ts.length + 1) with
                                | .error e => .error e
                                | .ok p    => .ok (some p)))
       | _ => .ok none)
  | [] => .ok none
/-! ### The shape-expression algebra and triple expressions

`none` from an atom marks the WILDCARD `.`. Alone it means "no
constraint at all", and a triple constraint then omits its
`valueExpr` entirely; COMBINED with anything it reifies as an empty
Shape. That distinction is what the ShExJ twins in the corpus record,
so a reader that collapsed the two would disagree with the JSON on
documents that are otherwise identical. -/

def emptyShape : ShapeExpr := .shape (.mk false [] none [] [] [])

/-- Consume `// predicate object` annotations. BOTH readers ignore
    annotations — the ShExJ reader sets the field to the empty list
    unconditionally — so skipping them here keeps the two front doors
    agreeing. Recording them on one side only would make every
    annotated schema differ. -/
def skipAnnotations (ts : List Tok) : List Tok :=
  match ts with
  | .punct "//" :: _ :: obj :: r =>
      (match obj with
       | .punct _ => ts        -- not an object: leave the tokens alone
       | _        => skipAnnotations r)
  | _ => ts

def combineAnd : List (Option ShapeExpr) → Option ShapeExpr
  | []     => none
  | [x]    => x
  | xs     => some (.shapeAnd (xs.map (fun o => o.getD emptyShape)))

def combineOr : List (Option ShapeExpr) → Option ShapeExpr
  | []     => none
  | [x]    => x
  | xs     => some (.shapeOr (xs.map (fun o => o.getD emptyShape)))

mutual

/-- `shapeOr ::= shapeAnd (OR shapeAnd)*` -/
partial def parseShapeExpr (st : PState) (ts : List Tok)
    : Except String (Option ShapeExpr × List Tok) :=
  let rec go (r : List Tok) (acc : List (Option ShapeExpr)) (fuel : Nat)
      : Except String (Option ShapeExpr × List Tok) :=
    match fuel with
    | 0 => .error "shape expression is too deep"
    | f + 1 =>
      match parseShapeAnd st r with
      | .error e => .error e
      | .ok (x, r2) =>
        match r2 with
        | .kw "OR" :: r3 => go r3 (acc ++ [x]) f
        | _              => .ok (combineOr (acc ++ [x]), r2)
  go ts [] (ts.length + 1)

/-- `shapeAnd ::= shapeNot (AND shapeNot)*`, with the IMPLICIT AND of a
    node constraint and a following shape reference flattened into the
    same list. -/
partial def parseShapeAnd (st : PState) (ts : List Tok)
    : Except String (Option ShapeExpr × List Tok) :=
  let rec go (r : List Tok) (acc : List (Option ShapeExpr)) (fuel : Nat)
      : Except String (Option ShapeExpr × List Tok) :=
    match fuel with
    | 0 => .error "shape expression is too deep"
    | f + 1 =>
      match parseShapeNot st r with
      | .error e => .error e
      | .ok (xs, r2) =>
        match r2 with
        | .kw "AND" :: r3 => go r3 (acc ++ xs) f
        | _               => .ok (combineAnd (acc ++ xs), r2)
  go ts [] (ts.length + 1)

/-- `shapeNot ::= NOT? shapeAtom`. Returns the OPERANDS, so that a node
    constraint with a shape reference contributes two of them and
    flattens into an enclosing AND. -/
partial def parseShapeNot (st : PState) (ts : List Tok)
    : Except String (List (Option ShapeExpr) × List Tok) :=
  match ts with
  | .kw "NOT" :: r =>
      (match parseShapeNot st r with
       | .error e     => .error e
       | .ok (xs, r2) => .ok ([some (.shapeNot ((combineAnd xs).getD emptyShape))], r2))
  | _ => parseShapeAtom st ts

partial def parseShapeAtom (st : PState) (ts : List Tok)
    : Except String (List (Option ShapeExpr) × List Tok) :=
  match ts with
  | .punct "(" :: r =>
      (match parseShapeExpr st r with
       | .error e => .error e
       | .ok (x, r2) =>
         match expectPunct ")" r2 with
         | .error e     => .error e
         | .ok (_, r3)  => .ok ([x], r3))
  | .punct "." :: r => .ok ([none], r)
  | _ =>
    match parseNodeConstraint st ts with
    | .error e => .error e
    | .ok (some (nc, r2)) =>
        -- A shape reference or definition may follow, combined by an
        -- IMPLICIT AND that flattens into an enclosing one.
        (match parseShapeOrRef st r2 with
         | .error e            => .error e
         | .ok (none, r3)      => .ok ([some (.nodeConstraint nc)], r3)
         | .ok (some sr, r3)   => .ok ([some (.nodeConstraint nc), some sr], r3))
    | .ok none =>
        (match parseShapeOrRef st ts with
         | .error e          => .error e
         | .ok (some sr, r2) => .ok ([some sr], r2)
         | .ok (none, _)     =>
             (match ts with
              | t :: _ => .error s!"expected a shape expression, found {showTok t}"
              | []     => .error "expected a shape expression, found end of input"))

/-- `shapeOrRef ::= shapeDefinition | '@' shapeExprLabel`. `none` when
    the tokens begin neither. -/
partial def parseShapeOrRef (st : PState) (ts : List Tok)
    : Except String (Option ShapeExpr × List Tok) :=
  match ts with
  | .punct "@" :: t :: r =>
      (match resolveTerm st t with
       | .error e => .error e
       | .ok lbl  => .ok (some (.ref lbl), r))
  -- `{` after a node constraint is a REPEAT RANGE, not a shape
  -- definition, when a number follows it. Reading `ex:literal
  -- ["a" "b"]{2,3}` as a shape definition made `2` a predicate and
  -- refused the whole schema (kitchenSink).
  | .punct "{" :: .num _ _ :: _ => .ok (none, ts)
  | .kw "CLOSED" :: _ | .kw "EXTRA" :: _ | .kw "EXTENDS" :: _ | .punct "{" :: _ =>
      parseShapeDefinition st ts
  | _ => .ok (none, ts)

/-- `shapeDefinition ::= (EXTRA p+ | CLOSED | EXTENDS label)* '{' … '}'` -/
partial def parseShapeDefinition (st : PState) (ts : List Tok)
    : Except String (Option ShapeExpr × List Tok) :=
  let rec mods (r : List Tok) (closed : Bool) (extra : List String)
      (ext : List String) (fuel : Nat)
      : Except String (Bool × List String × List String × List Tok) :=
    match fuel with
    | 0 => .error "too many shape modifiers"
    | f + 1 =>
      match r with
      | .kw "CLOSED" :: r2 => mods r2 true extra ext f
      | .kw "EXTENDS" :: .punct "@" :: t :: r2 =>
          (match resolveTerm st t with
           | .error e => .error e
           | .ok lbl  => mods r2 closed extra (ext ++ [lbl]) f)
      | .kw "EXTENDS" :: t :: r2 =>
          (match resolveTerm st t with
           | .error e => .error e
           | .ok lbl  => mods r2 closed extra (ext ++ [lbl]) f)
      | .kw "EXTRA" :: r2 =>
          -- EXTRA takes ONE OR MORE predicates; the run ends at the
          -- next keyword or the opening brace.
          let rec preds (q : List Tok) (acc : List String) (g : Nat)
              : Except String (List String × List Tok) :=
            match g with
            | 0 => .error "too many EXTRA predicates"
            | h + 1 =>
              match q with
              | .pname ns lp :: q2 =>
                  if ns == bareTag then
                    if lp == "a" then
                      preds q2 (acc ++ ["http://www.w3.org/1999/02/22-rdf-syntax-ns#type"]) h
                    else .ok (acc, q)
                  else (match resolveTerm st (.pname ns lp) with
                        | .error e => .error e
                        | .ok p    => preds q2 (acc ++ [p]) h)
              | .iri raw :: q2 =>
                  (match resolveTerm st (.iri raw) with
                   | .error e => .error e
                   | .ok p    => preds q2 (acc ++ [p]) h)
              | _ => .ok (acc, q)
          (match preds r2 [] (r2.length + 1) with
           | .error e => .error e
           | .ok (ps, r3) =>
               if ps.isEmpty then .error "EXTRA needs at least one predicate"
               else mods r3 closed (extra ++ ps) ext f)
      | _ => .ok (closed, extra, ext, r)
  match mods ts false [] [] (ts.length + 1) with
  | .error e => .error e
  | .ok (closed, extra, ext, r) =>
    match r with
    -- A shape definition may carry its own `// p o` annotations after
    -- the closing brace. Leaving them made the statement reader see a
    -- loose `//` where the next shape label belonged
    -- (1dotShapeAnnotIRIREF and three more).
    | .punct "{" :: .punct "}" :: r2 =>
        .ok (some (.shape (.mk closed extra none [] [] ext)), skipAnnotations r2)
    | .punct "{" :: r2 =>
        (match parseTripleExpr st r2 with
         | .error e => .error e
         | .ok (te, r3) =>
           match expectPunct "}" r3 with
           | .error e    => .error e
           | .ok (_, r4) =>
               .ok (some (.shape (.mk closed extra (some te) [] [] ext)),
                    skipAnnotations r4))
    | _ => .ok (none, ts)

/-- `oneOfTripleExpr ::= groupTripleExpr ('|' groupTripleExpr)*` -/
partial def parseTripleExpr (st : PState) (ts : List Tok)
    : Except String (TripleExpr × List Tok) :=
  let rec go (r : List Tok) (acc : List TripleExpr) (fuel : Nat)
      : Except String (TripleExpr × List Tok) :=
    match fuel with
    | 0 => .error "triple expression is too deep"
    | f + 1 =>
      match parseGroupTripleExpr st r with
      | .error e => .error e
      | .ok (x, r2) =>
        match r2 with
        | .punct "|" :: r3 => go r3 (acc ++ [x]) f
        | _ =>
          -- A GROUP wrapper is added only when there are two or more
          -- members. A lone member is left unwrapped, which is what
          -- the ShExJ twins record.
          (match acc ++ [x] with
           | [one] => .ok (one, r2)
           | xs    => .ok (.oneOf (.mk none xs none none [] []), r2))
  go ts [] (ts.length + 1)

/-- `groupTripleExpr ::= unaryTripleExpr (';' unaryTripleExpr)* ';'?` -/
partial def parseGroupTripleExpr (st : PState) (ts : List Tok)
    : Except String (TripleExpr × List Tok) :=
  let rec go (r : List Tok) (acc : List TripleExpr) (fuel : Nat)
      : Except String (TripleExpr × List Tok) :=
    match fuel with
    | 0 => .error "triple expression is too deep"
    | f + 1 =>
      match parseUnaryTripleExpr st r with
      | .error e => .error e
      | .ok (x, r2) =>
        match r2 with
        | .punct ";" :: r3 =>
            -- A TRAILING `;` ends the group rather than promising
            -- another member.
            (match r3 with
             | .punct "}" :: _ | .punct ")" :: _ | .punct "|" :: _ | [] =>
                 (match acc ++ [x] with
                  | [one] => .ok (one, r3)
                  | xs    => .ok (.eachOf (.mk none xs none none [] []), r3))
             | _ => go r3 (acc ++ [x]) f)
        | _ =>
            (match acc ++ [x] with
             | [one] => .ok (one, r2)
             | xs    => .ok (.eachOf (.mk none xs none none [] []), r2))
  go ts [] (ts.length + 1)

partial def parseUnaryTripleExpr (st : PState) (ts : List Tok)
    : Except String (TripleExpr × List Tok) :=
  match ts with
  | .punct "&" :: t :: r =>
      (match resolveTerm st t with
       | .error e => .error e
       | .ok lbl  => .ok (.ref lbl, r))
  | .punct "$" :: t :: r =>
      (match resolveTerm st t with
       | .error e => .error e
       | .ok lbl  =>
         match parseUnaryTripleExpr st r with
         | .error e => .error e
         | .ok (te, r2) =>
           .ok (match te with
                | .tripleConstraint (.mk _ i p v mn mx sa an) =>
                    .tripleConstraint (.mk (some lbl) i p v mn mx sa an)
                | .eachOf (.mk _ es mn mx sa an) => .eachOf (.mk (some lbl) es mn mx sa an)
                | .oneOf  (.mk _ es mn mx sa an) => .oneOf  (.mk (some lbl) es mn mx sa an)
                | other => other, r2))
  | .punct "(" :: r =>
      (match parseTripleExpr st r with
       | .error e => .error e
       | .ok (te, r2) =>
         match expectPunct ")" r2 with
         | .error e    => .error e
         | .ok (_, r3) =>
           let (card, r4) := parseCardinality r3
           let r5 := skipAnnotations r4
           -- An ABSENT cardinality leaves the group UNWRAPPED and its
           -- min/max unset. Writing `min: 1, max: 1` instead is a
           -- different document: the ShExJ twins omit both, and a
           -- reader that supplied them disagreed with the JSON on
           -- every parenthesised group (open2dotclose and 40 more).
           .ok (match card with
                | none => te
                | some (mn, mx) =>
                  match te with
                  | .eachOf (.mk i es _ _ sa an) =>
                      .eachOf (.mk i es (some mn) (some mx) sa an)
                  | .oneOf (.mk i es _ _ sa an) =>
                      .oneOf (.mk i es (some mn) (some mx) sa an)
                  -- A bracketed SINGLE member takes the cardinality
                  -- ITSELF rather than gaining a wrapper
                  -- (open1dotclosecardOpt).
                  | .tripleConstraint (.mk i inv p v _ _ sa an) =>
                      .tripleConstraint (.mk i inv p v mn mx sa an)
                  | other => .eachOf (.mk none [other] (some mn) (some mx) [] []), r5))
  | _ => parseTripleConstraint st ts

partial def parseTripleConstraint (st : PState) (ts : List Tok)
    : Except String (TripleExpr × List Tok) :=
  let (inverse, r0) := match ts with
    | .punct "^" :: r => (true, r)
    | _               => (false, ts)
  let predRes : Except String (String × List Tok) :=
    match r0 with
    | .pname ns lp :: r =>
        if ns == bareTag then
          if lp == "a" then .ok ("http://www.w3.org/1999/02/22-rdf-syntax-ns#type", r)
          else .error s!"expected a predicate, found the bare name '{lp}'"
        else (resolveTerm st (.pname ns lp)).map (fun p => (p, r))
    | .iri raw :: r => (resolveTerm st (.iri raw)).map (fun p => (p, r))
    | t :: _        => .error s!"expected a predicate, found {showTok t}"
    | []            => .error "expected a predicate, found end of input"
  match predRes with
  | .error e => .error e
  | .ok (p, r1) =>
    match parseShapeExpr st r1 with
    | .error e => .error e
    | .ok (v, r2) =>
      let r2 := skipAnnotations r2
      let (card, r3) := parseCardinality r2
      let (mn, mx) := card.getD (1, 1)
      .ok (.tripleConstraint (.mk none inverse p v mn mx [] []), skipAnnotations r3)

end
/-! ## The document -/

/-- One statement: a directive, `start = …`, or a shape declaration.
    A directive may appear ANYWHERE among the statements, so the state
    is threaded rather than collected in a prologue pass. -/
def parseStatement (st : PState) (sch : Schema) (ts : List Tok)
    : Except String (PState × Schema × List Tok) :=
  match ts with
  | .kw "PREFIX" :: .pname ns lp :: .iri iri :: r =>
      if !lp.isEmpty then .error "a PREFIX declaration takes a bare prefix name"
      else
        let full := if st.base == "" then iri else L4Factoidal.Syntax.resolveIri st.base iri
        .ok ({ st with prefixes := (ns, full) :: st.prefixes }, sch, r)
  | .kw "BASE" :: .iri iri :: r =>
      .ok ({ st with base :=
               if st.base == "" then iri else L4Factoidal.Syntax.resolveIri st.base iri },
           sch, r)
  | .kw "IMPORT" :: t :: r =>
      (match resolveTerm st t with
       | .error e => .error e
       | .ok i    => .ok (st, { sch with imports := sch.imports ++ [i] }, r))
  | .kw "START" :: .punct "=" :: r =>
      (match parseShapeExpr st r with
       | .error e     => .error e
       | .ok (se, r2) => .ok (st, { sch with start := se.orElse (fun _ => sch.start) }, r2))
  | .kw "ABSTRACT" :: r =>
      (match parseStatement st sch r with
       | .error e => .error e
       | .ok (st2, sch2, r2) =>
         -- Mark the declaration this ABSTRACT introduced.
         .ok (st2, { sch2 with shapes := match sch2.shapes.reverse with
                       | d :: rest => (rest.reverse ++ [{ d with isAbstract := true }])
                       | []        => sch2.shapes }, r2))
  | t :: r =>
      -- A shape declaration: a label, then a shape expression or
      -- EXTERNAL.
      (match resolveTerm st t with
       | .error e  => .error s!"expected a statement: {e}"
       | .ok label =>
         match r with
         | .kw "EXTERNAL" :: r2 =>
             .ok (st, { sch with shapes := sch.shapes ++
                          [{ id := label, expr := .external }] }, r2)
         | _ =>
           match parseShapeExpr st r with
           | .error e => .error e
           | .ok (se, r2) =>
               .ok (st, { sch with shapes := sch.shapes ++
                            [{ id := label, expr := se.getD emptyShape }] }, r2))
  | [] => .error "unexpected end of input"

/-- Read a whole ShExC document. `Except` with a MESSAGE, never a
    partial schema: a schema missing a declaration validates the wrong
    graphs, and nothing downstream could tell. -/
def parseShExC (text : String) : Except String Schema :=
  match tokenize text.toList.toArray with
  | .error e => .error ("ShExC tokenizer: " ++ e)
  | .ok toks =>
    let rec go (st : PState) (sch : Schema) (ts : List Tok) (fuel : Nat)
        : Except String Schema :=
      match fuel with
      | 0 => .error "ShExC document is too long"
      | f + 1 =>
        match ts with
        | [] => .ok sch
        | _  =>
          match parseStatement st sch ts with
          | .error e => .error e
          | .ok (st2, sch2, ts2) =>
              if ts2.length ≥ ts.length then
                .error "ShExC parser made no progress"
              else go st2 sch2 ts2 f
    go {} {} toks (toks.length + 2)

end L4Factoidal.ShEx.Compact
