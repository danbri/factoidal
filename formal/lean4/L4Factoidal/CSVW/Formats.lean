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

/-- A numeric format: the grouping and decimal characters, and the
    scaling implied by a trailing `%` or `‰`. -/
structure NumFmt where
  groupChar   : Char := ','
  decimalChar : Char := '.'
  percent     : Bool := false
  permille    : Bool := false
deriving Repr, Inhabited

/-- Read the scaling suffix out of a number pattern. -/
def parseNumFmt (pat : Option String) (grp dec : Char) : NumFmt :=
  match pat with
  | none   => { groupChar := grp, decimalChar := dec }
  | some p =>
      { groupChar := grp, decimalChar := dec,
        percent := p.endsWith "%" || p.startsWith "%",
        permille := p.endsWith "‰" || p.startsWith "‰" }

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
def shiftLeft (s : String) (n : Nat) : String :=
  let neg := s.startsWith "-"
  let body := if neg then String.ofList (s.toList.drop 1) else s
  let (ip, fp) := match splitFirst '.' body.toList with
    | some (a, b) => (a, b)
    | none        => (body.toList, [])
  let digits := ip ++ fp
  let pointPos : Int := (ip.length : Int) - (n : Int)
  let (digits, pointPos) :=
    if pointPos ≤ 0 then
      (List.replicate (1 - pointPos).toNat '0' ++ digits, (1 : Int))
    else (digits, pointPos)
  let cut := pointPos.toNat
  let ipOut := String.ofList (digits.take cut)
  let fpOut := String.ofList (digits.drop cut)
  (if neg then "-" else "") ++ ipOut ++ (if fpOut == "" then "" else "." ++ fpOut)

/-- Apply a numeric format: strip grouping characters, normalise the
    decimal character to `.`, and apply percent / per-mille scaling.
    Rejects anything that is not a well-formed number afterwards. -/
def parseNumber (nf : NumFmt) (v : String) : FmtOutcome :=
  let body := v.toList.filter (fun c => c != nf.groupChar && c != '%' && c != '‰')
  let body := body.map (fun c => if c == nf.decimalChar then '.' else c)
  let s := String.ofList body
  let core := if s.startsWith "-" || s.startsWith "+"
              then String.ofList (s.toList.drop 1) else s
  let parts := core.splitOn "."
  let wellFormed :=
    core != "" && parts.length ≤ 2 &&
    parts.all (fun p => p.toList.all isDigit) &&
    parts.any (fun p => p != "")
  if !wellFormed then .invalid
  else
    let s := if s.startsWith "+" then String.ofList (s.toList.drop 1) else s
    if nf.percent then .valid (shiftLeft s 2)
    else if nf.permille then .valid (shiftLeft s 3)
    else .valid s


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
              -- `X` with no minutes still canonicalises to HH:MM.
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
            if v == "" then none
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

/-- Top-level dispatch, mirroring the F* module's. A DURATION format
    returns `noFormat` in this slice — see the module header. -/
def formatConvert (baseName : String) (formatStr pattern groupChar decimalChar : Option String)
    (txt : String) : FmtOutcome :=
  if baseName == "boolean" then parseBool formatStr txt
  else if isNumericBase baseName then
    let pat := pattern.orElse (fun _ => formatStr)
    if pat.isNone && groupChar.isNone && decimalChar.isNone then .noFormat
    else
      let grp := (groupChar.bind (·.toList.head?)).getD ','
      let dec := (decimalChar.bind (·.toList.head?)).getD '.'
      parseNumber (parseNumFmt pat grp dec) txt
  else if isDateBase baseName then
    match formatStr with
    | some f => parseDate baseName f txt
    | none   => .noFormat
  else .noFormat

end L4Factoidal.CSVW
