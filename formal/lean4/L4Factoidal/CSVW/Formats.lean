/-
L4Factoidal.CSVW.Formats — cell value formats, ported from
`formal/fstar/CSVW.Formats.fst`.

Spec: tabular-metadata §5.11.3 (`format` on a datatype) plus the
tabular-data-model §6.4 parsing rules.

SCOPE OF THIS SLICE, stated rather than implied: boolean formats and
numeric formats (group/decimal separators, percent and per-mille
scaling, pattern-implied grouping). Date/time patterns and the
regex-valued duration `format` facet are NOT here yet — the F* module
carries both, and the duration one needs the XSD regex engine. Until
they land, a date or duration format returns `noFormat`, which the
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

/-- Top-level dispatch, mirroring the F* module's. Date and duration
    formats return `noFormat` in this slice — see the module header. -/
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
  else .noFormat

end L4Factoidal.CSVW
