/-
L4Factoidal.CSVW.FormatsTests — build-time checks for CSVW value
formats.
-/
import L4Factoidal.CSVW.Formats

namespace L4Factoidal.CSVW

-- Boolean, no format: the XSD lexical space.
#guard parseBool none "true" == .valid "true"
#guard parseBool none "1" == .valid "true"
#guard parseBool none "0" == .valid "false"
#guard parseBool none "YES" == .invalid

-- Boolean with a format.
#guard parseBool (some "YES|NO") "YES" == .valid "true"
#guard parseBool (some "YES|NO") "NO" == .valid "false"
#guard parseBool (some "YES|NO") "maybe" == .invalid

-- A boolean format with NO '|' is malformed and rejects everything;
-- it does NOT silently fall back to the XSD space.
#guard parseBool (some "YN") "true" == .invalid
#guard parseBool (some "YN") "Y" == .invalid

-- Grouping and decimal characters.
private def euro : NumFmt := { groupChar := '.', decimalChar := ',' }
#guard parseNumber euro "1.234,56" == .valid "1234.56"
#guard parseNumber {} "1,234.56" == .valid "1234.56"
#guard parseNumber {} "42" == .valid "42"
#guard parseNumber {} "-42" == .valid "-42"
#guard parseNumber {} "+42" == .valid "42"

-- Malformed numbers are rejected.
#guard parseNumber {} "abc" == .invalid
#guard parseNumber {} "" == .invalid
#guard parseNumber {} "1.2.3" == .invalid
#guard parseNumber {} "." == .invalid

-- Percent and per-mille scale EXACTLY, on the digit string — no
-- float arithmetic, so 12.5% is 0.125 rather than a binary
-- approximation.
#guard parseNumber { percent := true } "12.5%" == .valid "0.125"
#guard parseNumber { percent := true } "50%" == .valid "0.50"
#guard parseNumber { permille := true } "125‰" == .valid "0.125"
#guard parseNumber { percent := true } "-25%" == .valid "-0.25"

-- The three-way outcome: a numeric base with NO format at all is
-- `noFormat`, which is not the same as `invalid`.
#guard formatConvert "integer" none none none none "42" == .noFormat
#guard formatConvert "integer" (some "#,##0") none none none "1,234" == .valid "1234"
#guard formatConvert "integer" (some "#,##0") none none none "oops" == .invalid

-- Date and duration formats are not in this slice; they return
-- `noFormat` so the caller keeps the cell rather than rejecting it.
#guard formatConvert "date" (some "yy-MM-dd") none none none "10-18-25" == .noFormat
#guard formatConvert "duration" (some "^.$") none none none "P1D" == .noFormat

-- Base classification.
#guard isNumericBase "decimal"
#guard isDateBase "dateTime"
#guard isDurationBase "dayTimeDuration"
#guard !(isNumericBase "string")

end L4Factoidal.CSVW
