/-
L4Factoidal.CSVW.Formats — cell value formats, ported from
`formal/fstar/CSVW.Formats.fst`.

Spec: tabular-metadata §5.11.3 (`format` on a datatype) plus the
tabular-data-model §6.4 parsing rules.

SCOPE OF THIS SLICE, stated rather than implied: boolean formats,
numeric formats (group/decimal separators, percent and per-mille
scaling, pattern-implied grouping) and DATE/TIME patterns. The
regex-valued duration `format` facet is NOT here — it needs the XSD
regex engine — so a duration format returns `noFormat`, which the
caller treats as "keep the cell as written" rather than as a
rejection. That is the conservative direction: a format we cannot
read must never reject a value it might have accepted.
-/
import L4Factoidal.Regex.XPath

namespace L4Factoidal.CSVW

/-- The result of applying a format to a cell.

    Three outcomes, not two: `noFormat` means "no format applied,
    use the cell as-is", which is DIFFERENT from `invalid` ("a format
    was applied and the cell failed it"). Collapsing them would turn
    an unported format into a validation failure. -/
inductive FmtOutcome where
  | valid    (lexical : String)
  | invalid
  | noFormat
deriving Repr, DecidableEq, Inhabited

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Split on the first occurrence of a character. -/
def splitFirst (sep : Char) (l : List Char) : Option (List Char × List Char) :=
  match l.findIdx? (· == sep) with
  | some i => some (l.take i, l.drop (i + 1))
  | none   => none

/-- §5.11.3 boolean format: `"trueValue|falseValue"`. With no format,
    the XSD lexical space applies (`true`/`1`, `false`/`0`). A format
    with no `|` is MALFORMED and rejects everything — it does not
    silently fall back to the XSD space. -/
def parseBool (fmt : Option String) (v : String) : FmtOutcome :=
  match fmt with
  | none =>
      if v == "true" || v == "1" then .valid "true"
      else if v == "false" || v == "0" then .valid "false"
      else .invalid
  | some f =>
      match splitFirst '|' f.toList with
      | none => .invalid
      | some (tv, fv) =>
          if v.toList == tv then .valid "true"
          else if v.toList == fv then .valid "false"
          else .invalid

/-! ### Decimal PATTERNS (UAX #35 number patterns, §5.11.3)

A `pattern` is not just a hint about grouping: it constrains how many
digits the value may have on each side of the point, and where the
grouping separators must fall. Sixteen tests in the csv2rdf corpus
(288–303 plus 160) supply a value that is a perfectly good number and
expect it REJECTED because it does not match its column's pattern —
`1` against `#,#00`, `12.34` against `#0.#`, `1,234,567` against
`#,##,#00`. Reading the pattern only for its grouping character let
every one of them through with the column's datatype attached.

Supported: `#` and `0` digit places, `,` grouping (primary and
secondary group sizes), `.` with minimum and maximum fraction digits,
and an `E` exponent. Prefixes, suffixes, quoting and the second
(negative) subpattern are NOT read — none appears in the corpus, and
guessing at them would reject values a real pattern accepts.
-/

structure NumPattern where
  minInt         : Nat := 0
  minFrac        : Nat := 0
  maxFrac        : Nat := 0
  primaryGroup   : Option Nat := none
  secondaryGroup : Option Nat := none
  /-- The exponent marker the pattern uses, if any. `none` means the
      value must NOT carry an exponent. -/
  expChar        : Option Char := none
deriving Repr, Inhabited

/-- Does the pattern call for an exponent at all? -/
def NumPattern.hasExp (p : NumPattern) : Bool := p.expChar.isSome

/-- Read a number pattern. Only the digit-place characters are
    significant here; anything else is a prefix or suffix. -/
def parseNumPattern (pat : String) (grp dec : Char) : NumPattern :=
  let cs := pat.toList.filter (fun c => c == '#' || c == '0' || c == grp || c == dec
                                        || c == 'E' || c == 'e')
  -- The exponent marker is LITERAL: a pattern written with `E`
    -- requires an `E` in the value, and `10.10e10` does not match
    -- `0.00E0` (test157).
  let (mant, expChar) := match splitFirst 'E' cs with
    | some (m, _) => (m, some 'E')
    | none => match splitFirst 'e' cs with
      | some (m, _) => (m, some 'e')
      | none        => (cs, none)
  let (ip, fp) := match splitFirst dec mant with
    | some (a, b) => (a, b)
    | none        => (mant, [])
  -- Group sizes are counted from the RIGHT: the primary group is the
  -- run after the last separator, the secondary the run before it.
  let groups := (String.ofList ip).splitOn (String.mk [grp])
  let sizes := groups.map (·.length)
  -- A SECONDARY group size exists only when the pattern has TWO or
  -- more separators. With one, the run before it is not a group-size
  -- declaration — it is the "and any further digits" placeholder —
  -- so the secondary size equals the primary. `#,#00` says groups of
  -- three, and `1,234,567` matches it; reading the leading `#` as a
  -- secondary size of ONE demanded `1,2,3,4,567` and rejected the
  -- value the corpus expects (test282). `#,##,#00` is the case with a
  -- genuine secondary size: primary 3, secondary 2, so `12,34,567`.
  let (primary, secondary) := match sizes.reverse with
    | last :: prev :: _ :: _ => (some last, some prev)
    | last :: _ :: []        => (some last, some last)
    | [_]                    => (none, none)
    | []                     => (none, none)
  { minInt := (ip.filter (· == '0')).length
    minFrac := (fp.filter (· == '0')).length
    maxFrac := fp.length
    primaryGroup := primary
    secondaryGroup := secondary
    expChar := expChar }

/-- Chop a digit run from the RIGHT into `sec`-sized pieces. `fuel` is
    the run length, so the bound is exact. -/
def chopFromRight : Nat → Nat → List Char → List (List Char)
  | 0,        _,   cs => [cs]
  | _,        0,   cs => [cs]
  | fuel + 1, sec, cs =>
      if cs.length ≤ sec then [cs]
      else chopFromRight fuel sec (cs.take (cs.length - sec)) ++ [cs.drop (cs.length - sec)]

/-- Insert grouping separators into a digit string, primary group
    first (from the right), then repeated secondary groups. -/
def regroup (digits : String) (primary secondary : Nat) (grp : Char) : String :=
  if primary == 0 then digits
  else
    let ds := digits.toList
    let n := ds.length
    if n ≤ primary then digits
    else
      let head := ds.take (n - primary)
      let tail := ds.drop (n - primary)
      let sec := if secondary == 0 then primary else secondary
      let parts := chopFromRight (head.length + 1) sec head
      String.intercalate (String.mk [grp]) ((parts.map String.ofList) ++ [String.ofList tail])

/-- Does the value, AS WRITTEN, match the pattern? -/
def matchesNumPattern (p : NumPattern) (grp dec : Char) (v : String) : Bool :=
  let body := if v.startsWith "-" || v.startsWith "+"
              then String.ofList (v.toList.drop 1) else v
  let body := String.ofList (body.toList.filter (fun c => c != '%' && c != '‰'))
  let (mant, expPart) := match p.expChar with
    | some ec => match splitFirst ec body.toList with
      | some (m, e) => (String.ofList m, some (String.ofList e))
      | none        => (body, none)
    | none => (body, none)
  -- With no exponent in the pattern the value must carry none EITHER
  -- marker; with one, it must carry that exact marker.
  let valueHasExp := body.toList.contains 'E' || body.toList.contains 'e'
  if p.hasExp != expPart.isSome || (!p.hasExp && valueHasExp) then false
  else
    let (ip, fp) := match splitFirst dec mant.toList with
      | some (a, b) => (String.ofList a, String.ofList b)
      | none        => (mant, "")
    let digits := String.ofList (ip.toList.filter (· != grp))
    let fracLen := fp.length
    if digits.length < p.minInt then false
    else if fracLen < p.minFrac || fracLen > p.maxFrac then false
    else
      match p.primaryGroup with
      | none   => !ip.toList.contains grp
      | some g => ip == regroup digits g (p.secondaryGroup.getD g) grp

/-- A numeric format: the grouping and decimal characters, and the
    scaling implied by a trailing `%` or `‰`. -/
structure NumFmt where
  groupChar   : Char := ','
  decimalChar : Char := '.'
  percent     : Bool := false
  permille    : Bool := false
  /-- The digit-place constraints, when a pattern was given. -/
  pattern     : Option NumPattern := none
  /-- May the value carry grouping characters at all? A PATTERN that
      does not itself contain the grouping character forbids them:
      `##0` says "no grouping", so `1,234` is not a number in that
      format and must not be silently regrouped into `1234`
      (test286). With no pattern, grouping is allowed. -/
  grouping    : Bool := true
deriving Repr, Inhabited

/-- Read the scaling suffix and the grouping permission out of a
    number pattern. -/
def parseNumFmt (pat : Option String) (grp dec : Char) : NumFmt :=
  match pat with
  | none   => { groupChar := grp, decimalChar := dec }
  | some p =>
      { groupChar := grp, decimalChar := dec,
        pattern := some (parseNumPattern p grp dec),
        percent := p.endsWith "%" || p.startsWith "%",
        permille := p.endsWith "‰" || p.startsWith "‰",
        grouping := p.toList.contains grp }

/-- The numeric bases a `format` may scale. -/
def isNumericBase (b : String) : Bool :=
  ["decimal", "integer", "long", "int", "short", "byte", "double",
   "float", "number", "nonNegativeInteger", "positiveInteger",
   "nonPositiveInteger", "negativeInteger", "unsignedLong",
   "unsignedInt", "unsignedShort", "unsignedByte"].contains b

def isDateBase (b : String) : Bool :=
  ["date", "dateTime", "datetime", "time", "gYear", "gYearMonth",
   "gMonth", "gMonthDay", "gDay", "dateTimeStamp"].contains b

def isDurationBase (b : String) : Bool :=
  ["duration", "dayTimeDuration", "yearMonthDuration"].contains b

/-- Shift a decimal string by `n` places to the LEFT (dividing by a
    power of ten), used for percent and per-mille. Done on the digit
    string rather than by float arithmetic, so `12.5%` becomes exactly
    `0.125` and not a binary approximation. -/
def shiftPoint (s : String) (byRight : Int) : String :=
  let neg := s.startsWith "-"
  let body := if neg then String.ofList (s.toList.drop 1) else s
  let body := if body.startsWith "+" then String.ofList (body.toList.drop 1) else body
  let (ip, fp) := match splitFirst '.' body.toList with
    | some (a, b) => (a, b)
    | none        => (body.toList, [])
  let digits := ip ++ fp
  let pointPos : Int := (ip.length : Int) + byRight
  -- Pad on the LEFT when the point lands before the first digit.
  let (digits, pointPos) :=
    if pointPos ≤ 0 then
      (List.replicate (1 - pointPos).toNat '0' ++ digits, (1 : Int))
    else (digits, pointPos)
  -- ...and on the RIGHT when it lands past the last one, which a
  -- POSITIVE shift can do and a negative one cannot. `shiftLeft`
  -- never needed this case.
  let digits :=
    if pointPos > (digits.length : Int)
    then digits ++ List.replicate (pointPos - (digits.length : Int)).toNat '0'
    else digits
  let cut := pointPos.toNat
  let ipOut := String.ofList (digits.take cut)
  let fpOut := String.ofList (digits.drop cut)
  (if neg then "-" else "") ++ ipOut ++ (if fpOut == "" then "" else "." ++ fpOut)

/-- Move the decimal point LEFT by `n` places — the `%` / `‰` scaling. -/
def shiftLeft (s : String) (n : Nat) : String := shiftPoint s (-(n : Int))

/-- The three doubles that are NOT numbers. -/
def isSpecialDouble (s : String) : Bool :=
  s == "NaN" || s == "INF" || s == "-INF" || s == "+INF"

/-- A numeric lexical form with its EXPONENT resolved into the digits:
    `10.10e1` becomes `101.0`, `0.0e0` becomes `0.0`.

    csv2json emits a numeric cell as a JSON NUMBER, and JSON has no
    lexical space to preserve — `10.10e1` and `101.0` are the same
    number, and the corpus writes the second (test155). The RDF output
    keeps the lexical form, because an RDF literal's lexical form is
    part of its identity; the JSON output cannot, because a JSON
    number's is not. -/
def resolveExponent (s : String) : String :=
  if isSpecialDouble s then s
  else
    match splitFirst 'e' s.toList, splitFirst 'E' s.toList with
    | some (m, e), _ | none, some (m, e) =>
        (match (String.ofList e).toInt? with
         | some n => shiftPoint (String.ofList m) n
         | none   => s)
    | none, none => s

/-! ## Value constraints (§5.11.2) and the remaining lexical spaces

Three gaps the corpus exposes once formats work:

  * the `minimum` / `maximum` / `min|maxInclusive` / `min|maxExclusive`
    facets were never checked, so a cell outside its own stated range
    still carried the column's datatype (test203);
  * `duration` had no lexical space, so `Foo` came out as an
    `xsd:duration` (test279);
  * a date/time column with NO format was unchecked, so any text at
    all took the date datatype.

Each of these produced a triple whose datatype asserts something the
value does not support — the failure a triple count cannot see.
-/

/-- Compare two decimal numerals EXACTLY, without going through a
    float. Returns `none` if either is not a decimal numeral. -/
def decimalCompare (a b : String) : Option Ordering :=
  let split := fun (s : String) =>
    let neg := s.startsWith "-"
    let body := if neg || s.startsWith "+" then String.ofList (s.toList.drop 1) else s
    match splitFirst '.' body.toList with
    | some (i, f) => (neg, String.ofList i, String.ofList f)
    | none        => (neg, body, "")
  let (an, ai, af) := split a
  let (bn, bi, bf) := split b
  if !(ai ++ af).toList.all isDigit || !(bi ++ bf).toList.all isDigit then none
  else if (ai ++ af) == "" || (bi ++ bf) == "" then none
  else
    -- Pad both to a common shape so a plain string comparison is a
    -- numeric one.
    let iw := Nat.max ai.length bi.length
    let fw := Nat.max af.length bf.length
    let padL := fun (s : String) => String.ofList (List.replicate (iw - s.length) '0') ++ s
    let padR := fun (s : String) => s ++ String.ofList (List.replicate (fw - s.length) '0')
    let ka := padL ai ++ padR af
    let kb := padL bi ++ padR bf
    let magnitude := compare ka kb
    -- `-0` and `0` are the SAME value. Reading the sign first made
    -- `"-0"^^xsd:nonNegativeInteger` fall below the type's lower
    -- bound and leave its lexical space (ShEx `nonNegativeInteger-n0`).
    let aZero := ka.toList.all (· == '0')
    let bZero := kb.toList.all (· == '0')
    some (
      if aZero && bZero then .eq
      else if an && !bn then .lt
      else if !an && bn then .gt
      else if an && bn then magnitude.swap
      else magnitude)

/-- Ordering for a facet comparison: numeric where both sides are
    decimal numerals, plain lexicographic otherwise — which is the
    right thing for the canonical XSD date and time forms, since they
    are fixed-width and big-endian by construction. -/
def facetCompare (a b : String) : Ordering :=
  match decimalCompare a b with
  | some o => o
  | none   => compare a b

/-- The §5.11.2 value constraints. -/
structure Facets where
  length       : Option Int := none
  minLength    : Option Int := none
  maxLength    : Option Int := none
  minimum      : Option String := none
  maximum      : Option String := none
  minInclusive : Option String := none
  maxInclusive : Option String := none
  minExclusive : Option String := none
  maxExclusive : Option String := none
deriving Repr, Inhabited

/-- The LENGTH a `length` / `minLength` / `maxLength` facet counts.
    §5.11.2 measures the VALUE, not its lexical form, so a binary type
    counts decoded BYTES: `base64Binary` with `length: 19` describes
    the nineteen bytes of "Send reinforcements", whose base64 text is
    twenty-eight characters, and `hexBinary` with `length: 2` describes
    two bytes written as four hex digits (test195). -/
def facetLength (base : String) (lex : String) : Int :=
  if base == "hexBinary" then (lex.length + 1) / 2
  else if base == "base64Binary" then
    -- 4 base64 characters carry 3 bytes, less one per `=` of padding.
    let pad := (lex.toList.filter (· == '=')).length
    (lex.length / 4) * 3 - pad
  else lex.length

/-- Does the (already normalised) lexical form satisfy every stated
    constraint? -/
def satisfiesFacetsFor (base : String) (f : Facets) (lex : String) : Bool :=
  let len : Int := facetLength base lex
  let ge := fun (b : String) => (facetCompare lex b) != .lt
  let le := fun (b : String) => (facetCompare lex b) != .gt
  let gt := fun (b : String) => (facetCompare lex b) == .gt
  let lt := fun (b : String) => (facetCompare lex b) == .lt
  (f.length.all (· == len)) &&
  (f.minLength.all (· ≤ len)) &&
  (f.maxLength.all (len ≤ ·)) &&
  (f.minimum.all ge) && (f.minInclusive.all ge) &&
  (f.maximum.all le) && (f.maxInclusive.all le) &&
  (f.minExclusive.all gt) && (f.maxExclusive.all lt)

/-- The same check with no base-specific length rule. -/
def satisfiesFacets (f : Facets) (lex : String) : Bool :=
  satisfiesFacetsFor "string" f lex

/-- One `nnU` component of a duration: digits, an optional fractional
    part, and a unit letter legal in this half of the value. -/
private def durationStep (inTime : Bool) (cs : List Char)
    : Option (List Char) :=
  let digits := cs.takeWhile isDigit
  if digits.isEmpty then none
  else
    let after := cs.dropWhile isDigit
    let after := match after with
      | '.' :: t => if (t.takeWhile isDigit).isEmpty then after else t.dropWhile isDigit
      | t        => t
    match after with
    | u :: t =>
        let ok := if inTime then u == 'H' || u == 'M' || u == 'S'
                  else u == 'Y' || u == 'M' || u == 'D'
        if ok then some t else none
    | [] => none

/-- Walk a duration body. `fuel` is the remaining character count, so
    the bound is exact; every step consumes at least one character. -/
private def durationWalk : Nat → List Char → Bool → Nat → Bool
  | 0,        _,       _,      n => n > 0
  | _ + 1,    [],      _,      n => n > 0
  | fuel + 1, c :: tl, inTime, n =>
      if c == 'T' then
        if inTime || tl.isEmpty then false else durationWalk fuel tl true n
      else
        match durationStep inTime (c :: tl) with
        | some rest => durationWalk fuel rest inTime (n + 1)
        | none      => false

/-- `xsd:duration` and its two restrictions: `-?PnYnMnDTnHnMnS` with at
    least one component present, and `T` present only when a time
    component follows. -/
def isDurationLexical (s : String) : Bool :=
  let cs := (if s.startsWith "-" then s.toList.drop 1 else s.toList)
  match cs with
  | 'P' :: rest => durationWalk (rest.length + 1) rest false 0
  | _           => false

/-! ### XSD lexical spaces for the numeric bases

A numeric column validates its cells even with NO `format`: `3.2` is
not an `xsd:integer` and `123.456E7` is not an `xsd:decimal`, whatever
the metadata says about grouping. Before this the numeric path
returned `noFormat` whenever no pattern, `groupChar` or `decimalChar`
was stated, so nothing was checked and every such cell got its base's
datatype — asserting that `NaN` is a decimal (measured 2026-08-22,
tests 161 and 163–167). -/

private def stripSign (s : String) : String :=
  if s.startsWith "-" || s.startsWith "+" then String.ofList (s.toList.drop 1) else s

def isIntegerLexical (s : String) : Bool :=
  let core := stripSign s
  core != "" && core.toList.all isDigit

def isDecimalLexical (s : String) : Bool :=
  let core := stripSign s
  let parts := core.splitOn "."
  core != "" && parts.length ≤ 2 &&
  parts.all (fun p => p.toList.all isDigit) && parts.any (fun p => p != "")

/-- `xsd:double` / `xsd:float`: a decimal mantissa with an optional
    exponent, or one of the three special values. -/
def isDoubleLexical (s : String) : Bool :=
  if s == "NaN" || s == "INF" || s == "-INF" || s == "+INF" then true
  else
    match splitFirst 'e' s.toList, splitFirst 'E' s.toList with
    | some (m, e), _ =>
        isDecimalLexical (String.ofList m) && isIntegerLexical (String.ofList e)
    | none, some (m, e) =>
        isDecimalLexical (String.ofList m) && isIntegerLexical (String.ofList e)
    | none, none => isDecimalLexical s

/-- The inclusive range of an integer base, where XSD bounds one.
    `none` means unbounded on that side.

    A range is part of the LEXICAL SPACE decision here, not a separate
    facet: `1234` is not an `xsd:byte` at all, and emitting it with
    that datatype asserts a value the type does not contain
    (test172). -/
def integerBounds (base : String) : Option String × Option String :=
  match base with
  | "byte"               => (some "-128", some "127")
  | "unsignedByte"       => (some "0", some "255")
  | "short"              => (some "-32768", some "32767")
  | "unsignedShort"      => (some "0", some "65535")
  | "int"                => (some "-2147483648", some "2147483647")
  | "unsignedInt"        => (some "0", some "4294967295")
  | "long"               => (some "-9223372036854775808", some "9223372036854775807")
  | "unsignedLong"       => (some "0", some "18446744073709551615")
  | "nonNegativeInteger" => (some "0", none)
  | "positiveInteger"    => (some "1", none)
  | "nonPositiveInteger" => (none, some "0")
  | "negativeInteger"    => (none, some "-1")
  | _                    => (none, none)

/-- The lexical form a `double` / `float` value carries in the RDF
    output: the same digits, with the exponent marker written `e`.

    This follows the corpus, and the corpus is not XSD-canonical here.
    XSD's canonical mapping for `double` writes `E` and normalises the
    mantissa to one digit before the point, so `10.10E1` would be
    `1.010E2`. Every expected file in the CSVW suite instead keeps the
    mantissa as parsed and writes a lowercase `e` — `"0.0e0"^^xsd:double`
    in test158.ttl — and no expected file anywhere in the corpus uses
    `E`. Conformance is measured against those files, so this
    normalisation matches them and says plainly that it is a
    deviation from the XSD canonical mapping rather than an instance
    of it. The VALUE is the same either way; only the lexical form
    differs, and RDF literal equality is lexical, which is why the
    difference is visible at all. -/
def normalizeDoubleLexical (s : String) : String :=
  if s == "NaN" || s == "INF" || s == "-INF" || s == "+INF" then s
  else String.ofList (s.toList.map (fun c => if c == 'E' then 'e' else c))

/-- Which lexical space a numeric base uses. -/
def isXsdNumericLexical (base : String) (s : String) : Bool :=
  if base == "decimal" then isDecimalLexical s
  else if base == "double" || base == "float" || base == "number" then
    isDoubleLexical s
  else if !isIntegerLexical s then false
  else
    let (lo, hi) := integerBounds base
    (lo.all (fun b => decimalCompare s b != some .lt)) &&
    (hi.all (fun b => decimalCompare s b != some .gt))


/-- Apply a numeric format: strip grouping characters, normalise the
    decimal character to `.`, apply percent / per-mille scaling, and
    check the result against the base's XSD lexical space.

    Grouping characters must SEPARATE digits. Two in a row, or one at
    either end, is a validation error the corpus states outright:
    "Implementations MUST add a validation error … if the string being
    parsed contains two consecutive groupChar strings." Filtering them
    out unconditionally turned `123,,456.789` into a valid decimal. -/
def groupingWellPlaced (grp : Char) (v : String) : Bool :=
  let cs := v.toList
  let adjacent := (cs.zip (cs.drop 1)).any (fun (a, b) => a == grp && b == grp)
  let atEdge := (cs.head? == some grp) || (cs.reverse.head? == some grp)
  !adjacent && !atEdge

def parseNumber (base : String) (nf : NumFmt) (v : String) : FmtOutcome :=
  let hasGroup := v.toList.contains nf.groupChar
  if nf.pattern.any (fun p => !matchesNumPattern p nf.groupChar nf.decimalChar v) then .invalid
  else if hasGroup && !nf.grouping then .invalid
  else if !groupingWellPlaced nf.groupChar v then .invalid
  else
  -- The scaling suffix may be on the VALUE as well as on the pattern:
  -- §6.4.2 lets a cell carry its own `%` / `‰`, and `123456.789%`
  -- under a bare `{"groupChar": ","}` must still divide by a hundred
  -- (test170). Reading the suffix only from the pattern left the
  -- value a hundred times too large with the right datatype on it.
  let percent := nf.percent || v.toList.contains '%'
  let permille := nf.permille || v.toList.contains '‰'
  let body := v.toList.filter (fun c => c != nf.groupChar && c != '%' && c != '‰')
  let body := body.map (fun c => if c == nf.decimalChar then '.' else c)
  let s := String.ofList body
  if !isXsdNumericLexical base s then .invalid
  else
    -- A leading `+` is dropped only where SCALING rebuilds the number
    -- anyway. With no scaling the value passes through AS WRITTEN:
    -- `+` is in the `xsd:decimal` lexical space, and the corpus keeps
    -- it — the `+0` column of test283 expects `"+1"^^xsd:decimal`,
    -- while its `%000` column expects `%+123` to become `1.23`.
    -- Stripping unconditionally lost the sign the document wrote.
    let stripPlus := fun (x : String) =>
      if x.startsWith "+" then String.ofList (x.toList.drop 1) else x
    let norm := fun (x : String) =>
      if base == "double" || base == "float" || base == "number"
      then normalizeDoubleLexical x else x
    if percent then .valid (norm (shiftLeft (stripPlus s) 2))
    else if permille then .valid (norm (shiftLeft (stripPlus s) 3))
    else .valid (norm s)


/-! ## Date and time formats (§5.11.3, tabular-data-model §6.4.2)

A `format` on a date/time datatype is a pattern in the subset
tabular-metadata §5.11.3 lists — `yyyy`, `M`/`MM`, `d`/`dd`, `HH`,
`mm`, `ss`, a fractional-second run after a dot, and the `X`/`x`
timezone forms. The cell is read THROUGH the pattern and rewritten in
the XSD canonical lexical form, which is what the RDF output must
carry.

This matters more than it looks: without it every date column in the
CSVW corpus emits its SOURCE text under an `xsd:date` datatype —
`"10/18/2010"^^xsd:date` instead of `"2010-10-18"^^xsd:date`. The
triple count is right, the predicate is right, and the value is
wrong. That single gap accounted for a whole family of csv2rdf
conformance failures (measured 2026-08-22).
-/

/-- The fields a date/time pattern can fill. Kept as strings rather
    than numbers because the canonical form is a matter of DIGITS and
    padding, and a round trip through `Nat` would silently accept a
    year like `0000012`. -/
structure DateParts where
  year   : Option String := none
  month  : Option String := none
  day    : Option String := none
  hour   : Option String := none
  minute : Option String := none
  second : Option String := none
  frac   : Option String := none
  /-- Already canonical: `Z` or `+HH:MM` / `-HH:MM`. -/
  tz     : Option String := none
deriving Repr, Inhabited

private def pad (n : Nat) (s : String) : String :=
  if s.length ≥ n then s else String.ofList (List.replicate (n - s.length) '0') ++ s

/-- Read exactly `n` digits. -/
private def takeDigits (n : Nat) (cs : List Char) : Option (String × List Char) :=
  let d := cs.take n
  if d.length == n && d.all isDigit then some (String.ofList d, cs.drop n) else none

/-- Read one or two digits — the variable-width `M` and `d` fields. -/
private def takeFlex (cs : List Char) : Option (String × List Char) :=
  match cs with
  | a :: b :: rest =>
      if !isDigit a then none
      else if isDigit b then some (String.ofList [a, b], rest)
      else some (String.ofList [a], b :: rest)
  | [a] => if isDigit a then some (String.ofList [a], []) else none
  | []  => none

/-- Read a run of digits (the fractional-second field). -/
private def takeRun (cs : List Char) : String × List Char :=
  let d := cs.takeWhile isDigit
  (String.ofList d, cs.dropWhile isDigit)

/-- Read a timezone in one of the `X` / `x` widths, returning it in the
    canonical XSD form. `allowZ` distinguishes `X` (which accepts the
    literal `Z` for UTC) from `x` (which does not). -/
private def takeTz (allowZ : Bool) (width : Nat) (cs : List Char)
    : Option (Option String × List Char) :=
  match cs with
  | 'Z' :: rest => if allowZ then some (some "Z", rest) else none
  | sign :: rest =>
      if sign != '+' && sign != '-' then none
      else
        match takeDigits 2 rest with
        | none => none
        | some (hh, r1) =>
            if width == 1 then
              -- `X` is the ISO 8601 BASIC form: hours, with the
              -- minutes field OPTIONAL. `+0800` and `+08` are both
              -- `X`; reading only the hours left `+0800` with a
              -- trailing `00` the pattern could not match (test190).
              match takeDigits 2 r1 with
              | some (mm, r2) =>
                  some (some (String.ofList [sign] ++ hh ++ ":" ++ mm), r2)
              | none =>
                  some (some (String.ofList [sign] ++ hh ++ ":00"), r1)
            else
              let r1 := if width == 3 then
                  (match r1 with | ':' :: t => t | t => t)
                else r1
              match takeDigits 2 r1 with
              | none => none
              | some (mm, r2) =>
                  some (some (String.ofList [sign] ++ hh ++ ":" ++ mm), r2)
  | [] => none

/-- Walk the pattern and the cell together. `fuel` is the pattern
    length: every step consumes at least one pattern character, so the
    bound is exact and never truncates a real pattern. -/
private def matchDatePattern : Nat → List Char → List Char → DateParts → Option DateParts
  | 0,        _,   _,   _ => none
  | _ + 1,    [],  inp, p => if inp.isEmpty then some p else none
  | fuel + 1, pat, inp, p =>
      let step (n : Nat) (rest : List Char) (v : String) (inp' : List Char)
          (upd : DateParts → String → DateParts) : Option DateParts :=
        let _ := n
        matchDatePattern fuel rest inp' (upd p v)
      if pat.take 4 == ['y','y','y','y'] then
        match takeDigits 4 inp with
        | some (v, r) => step 4 (pat.drop 4) v r (fun q x => { q with year := some x })
        | none => none
      else if pat.take 2 == ['M','M'] then
        match takeDigits 2 inp with
        | some (v, r) => step 2 (pat.drop 2) v r (fun q x => { q with month := some x })
        | none => none
      else if pat.take 1 == ['M'] then
        match takeFlex inp with
        | some (v, r) => step 1 (pat.drop 1) v r (fun q x => { q with month := some x })
        | none => none
      else if pat.take 2 == ['d','d'] then
        match takeDigits 2 inp with
        | some (v, r) => step 2 (pat.drop 2) v r (fun q x => { q with day := some x })
        | none => none
      else if pat.take 1 == ['d'] then
        match takeFlex inp with
        | some (v, r) => step 1 (pat.drop 1) v r (fun q x => { q with day := some x })
        | none => none
      else if pat.take 2 == ['H','H'] then
        match takeDigits 2 inp with
        | some (v, r) => step 2 (pat.drop 2) v r (fun q x => { q with hour := some x })
        | none => none
      else if pat.take 2 == ['m','m'] then
        match takeDigits 2 inp with
        | some (v, r) => step 2 (pat.drop 2) v r (fun q x => { q with minute := some x })
        | none => none
      else if pat.take 2 == ['s','s'] then
        match takeDigits 2 inp with
        | some (v, r) => step 2 (pat.drop 2) v r (fun q x => { q with second := some x })
        | none => none
      else if pat.take 2 == ['.','S'] then
        -- A dot followed by a run of `S`: an OPTIONAL fractional part.
        let sRun := (pat.drop 1).takeWhile (· == 'S')
        let rest := pat.drop (1 + sRun.length)
        match inp with
        | '.' :: t =>
            let (v, r) := takeRun t
            -- The number of `S`s is the number of fractional digits,
            -- exactly. `HH:mm:ss.S` does not accept `15:02:37.143`
            -- (test247); reading the whole digit run regardless let
            -- three digits through a one-digit pattern.
            if v == "" || v.length != sRun.length then none
            else matchDatePattern fuel rest r { p with frac := some v }
        | _ => matchDatePattern fuel rest inp p
      else
        let xs := pat.takeWhile (· == 'X')
        let xls := pat.takeWhile (· == 'x')
        if xs.length > 0 then
          match takeTz true xs.length inp with
          | some (tz, r) => matchDatePattern fuel (pat.drop xs.length) r { p with tz := tz }
          | none => none
        else if xls.length > 0 then
          match takeTz false xls.length inp with
          | some (tz, r) => matchDatePattern fuel (pat.drop xls.length) r { p with tz := tz }
          | none => none
        else
          match pat, inp with
          | c :: prest, i :: irest => if c == i then matchDatePattern fuel prest irest p else none
          | _, _ => none

/-- Rebuild the canonical XSD lexical form for `base` from the parsed
    fields. A field the base needs but the pattern never filled makes
    this fail rather than substitute a zero — a missing month is a
    pattern that does not match the datatype, not a January. -/
def canonicalDate (base : String) (p : DateParts) : Option String :=
  let tz := p.tz.getD ""
  let timePart : Option String :=
    match p.hour, p.minute with
    | some h, some m =>
        some (pad 2 h ++ ":" ++ pad 2 m ++ ":" ++ pad 2 (p.second.getD "00")
              ++ (match p.frac with | some f => "." ++ f | none => ""))
    | _, _ => none
  match base with
  | "date" =>
      match p.year, p.month, p.day with
      | some y, some m, some d => some (pad 4 y ++ "-" ++ pad 2 m ++ "-" ++ pad 2 d ++ tz)
      | _, _, _ => none
  | "dateTime" | "datetime" | "dateTimeStamp" =>
      match p.year, p.month, p.day, timePart with
      | some y, some m, some d, some t =>
          some (pad 4 y ++ "-" ++ pad 2 m ++ "-" ++ pad 2 d ++ "T" ++ t ++ tz)
      | _, _, _, _ => none
  | "time" => timePart.map (fun t => t ++ tz)
  | "gYear" => p.year.map (fun y => pad 4 y ++ tz)
  | "gYearMonth" =>
      match p.year, p.month with
      | some y, some m => some (pad 4 y ++ "-" ++ pad 2 m ++ tz)
      | _, _ => none
  | "gMonth" => p.month.map (fun m => "--" ++ pad 2 m ++ tz)
  | "gMonthDay" =>
      match p.month, p.day with
      | some m, some d => some ("--" ++ pad 2 m ++ "-" ++ pad 2 d ++ tz)
      | _, _ => none
  | "gDay" => p.day.map (fun d => "---" ++ pad 2 d ++ tz)
  | _ => none

/-- Apply a date/time `format` to a cell. -/
def parseDate (base : String) (fmt : String) (v : String) : FmtOutcome :=
  let pat := fmt.toList
  match matchDatePattern (pat.length + 1) pat v.toList {} with
  | none   => .invalid
  | some p => match canonicalDate base p with
    | some lex => .valid lex
    | none     => .invalid

/-- The CANONICAL patterns for a date/time base — what a column with no
    `format` must already be written in. The timezone is optional, so
    each base offers its patterns with and without one.

    Without this a date column with no format accepted any text at all
    and stamped `xsd:date` on it. -/
def canonicalDatePatterns (base : String) : List String :=
  let withTz := fun (p : String) => [p, p ++ "XXX", p ++ "X"]
  -- A canonical `xsd:dateTime` may carry ANY number of fractional
  -- second digits. `matchDatePattern` reads an `S` run as an EXACT
  -- digit count, deliberately (CSVW test247 requires `HH:mm:ss.S` to
  -- reject `15:02:37.143`), so the no-format canonical form offers
  -- one pattern per width instead. With only `.S` on offer,
  -- `"2012-01-02T12:34:56.78Z"` was not a `dateTime` at all.
  let fracRuns : List String :=
    (List.range 9).map (fun n => String.ofList (List.replicate (n + 1) 'S'))
  match base with
  | "date"       => withTz "yyyy-MM-dd"
  | "dateTime" | "datetime" | "dateTimeStamp" =>
      withTz "yyyy-MM-ddTHH:mm:ss" ++ fracRuns.flatMap (fun f =>
        withTz ("yyyy-MM-ddTHH:mm:ss." ++ f))
  | "time"       => withTz "HH:mm:ss" ++ fracRuns.flatMap (fun f =>
        withTz ("HH:mm:ss." ++ f))
  | "gYear"      => withTz "yyyy"
  | "gYearMonth" => withTz "yyyy-MM"
  | "gMonth"     => withTz "--MM"
  | "gMonthDay"  => withTz "--MM-dd"
  | "gDay"       => withTz "---dd"
  | _            => []

/-- A date/time cell with NO format: it must already be in the
    canonical XSD lexical form. -/
def parseCanonicalDate (base : String) (v : String) : FmtOutcome :=
  match (canonicalDatePatterns base).findSome? (fun p =>
      match parseDate base p v with
      | .valid lex => some lex
      | _          => none) with
  | some lex => .valid lex
  | none     => .invalid

/-- Top-level dispatch, mirroring the F* module's. A DURATION format
    returns `noFormat` in this slice — see the module header. -/
def formatConvert (baseName : String) (formatStr pattern groupChar decimalChar : Option String)
    (txt : String) : FmtOutcome :=
  if baseName == "boolean" then parseBool formatStr txt
  else if isNumericBase baseName then
    let pat := pattern.orElse (fun _ => formatStr)
    -- No early `noFormat` exit: the XSD lexical space applies even
    -- with no format stated. The default grouping character is the
    -- comma only when a format asks for grouping; with none stated a
    -- comma is just a character the lexical check will reject.
    let grp := (groupChar.bind (·.toList.head?)).getD
      (if groupChar.isNone && pat.isNone then '\u0000' else ',')
    let dec := (decimalChar.bind (·.toList.head?)).getD '.'
    parseNumber baseName (parseNumFmt pat grp dec) txt
  else if isDateBase baseName then
    match formatStr with
    | some f => parseDate baseName f txt
    | none   => parseCanonicalDate baseName txt
  else if isDurationBase baseName then
    -- The `format` facet on a duration is a REGULAR EXPRESSION
    -- (tabular-metadata §5.11.3: "the datatype format annotation
    -- provides a regular expression for the string values"), matched
    -- the way `fn:matches` matches — a search, with `^` and `$` as
    -- anchors. The tree HAS that engine, so the format is now
    -- CHECKED rather than treated as unknowable.
    --
    -- Before this the format branch returned `.invalid` outright, on
    -- the ground that satisfaction could not be shown. That was the
    -- right call while there was no engine, and it was still wrong
    -- about nine rows of test193, whose formats every cell matches.
    -- Refusing to decide and deciding NO are the same output here —
    -- a plain literal — which is exactly why the shortcut survived:
    -- the count was right and the datatype was missing.
    --
    -- The lexical space is checked as well as the format. A cell must
    -- BE a duration and match the pattern; test194 states
    -- `"format": "^.$"`, which no duration matches, and expects every
    -- cell plain.
    if !isDurationLexical txt then .invalid
    else match formatStr with
      | none   => .valid txt
      | some f => if L4Factoidal.Regex.regexMatch txt f "" then .valid txt else .invalid
  else .noFormat

end L4Factoidal.CSVW
