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

-- DATE formats are read through the pattern and rewritten in the XSD
-- canonical lexical form. This is what stops a date column emitting
-- its source text under an `xsd:date` datatype.
#guard formatConvert "date" (some "M/d/yyyy") none none none "10/18/2010"
       == .valid "2010-10-18"
#guard formatConvert "date" (some "dd.MM.yyyy") none none none "02.06.2010"
       == .valid "2010-06-02"
#guard formatConvert "date" (some "yyyy-MM-dd") none none none "2010-06-02"
       == .valid "2010-06-02"
-- A cell that does not match its own pattern is INVALID, not
-- `noFormat`: a format WAS applied and the cell failed it.
#guard formatConvert "date" (some "M/d/yyyy") none none none "2010-10-18" == .invalid
-- With no format the XSD lexical space applies as written.
#guard formatConvert "date" none none none none "2010-10-18" == .noFormat

-- Time, dateTime, and the timezone forms.
#guard formatConvert "time" (some "HH:mm:ss") none none none "12:34:56"
       == .valid "12:34:56"
#guard formatConvert "time" (some "HH:mm") none none none "12:34" == .valid "12:34:00"
#guard formatConvert "dateTime" (some "yyyy-MM-ddTHH:mm:ss") none none none
         "2010-06-02T12:34:56" == .valid "2010-06-02T12:34:56"
#guard formatConvert "dateTime" (some "yyyy-MM-ddTHH:mm:ssX") none none none
         "2010-06-02T12:34:56Z" == .valid "2010-06-02T12:34:56Z"
#guard formatConvert "dateTime" (some "yyyy-MM-ddTHH:mm:ssXXX") none none none
         "2010-06-02T12:34:56+01:00" == .valid "2010-06-02T12:34:56+01:00"
-- `x` does not accept the literal `Z`; `X` does. Getting this wrong
-- silently widens the format.
#guard formatConvert "dateTime" (some "yyyy-MM-ddTHH:mm:ssxxx") none none none
         "2010-06-02T12:34:56Z" == .invalid
-- The fractional-second run is OPTIONAL, so a pattern with `.S` also
-- reads a value without one.
#guard formatConvert "dateTime" (some "yyyy-MM-ddTHH:mm:ss.S") none none none
         "2010-06-02T12:34:56.5" == .valid "2010-06-02T12:34:56.5"
#guard formatConvert "dateTime" (some "yyyy-MM-ddTHH:mm:ss.S") none none none
         "2010-06-02T12:34:56" == .valid "2010-06-02T12:34:56"
-- The g* bases produce their own canonical forms.
#guard formatConvert "gYear" (some "yyyy") none none none "1960" == .valid "1960"
#guard formatConvert "gMonthDay" (some "M/d") none none none "6/2" == .valid "--06-02"
#guard formatConvert "gDay" (some "d") none none none "2" == .valid "---02"
-- A pattern that never fills a field the base needs FAILS rather than
-- substituting a zero: a missing month is a mismatched pattern, not a
-- January.
#guard formatConvert "date" (some "yyyy") none none none "1960" == .invalid

-- The duration `format` facet still needs the XSD regex engine.
#guard formatConvert "duration" (some "^.$") none none none "P1D" == .noFormat

-- Base classification.
#guard isNumericBase "decimal"
#guard isDateBase "dateTime"
#guard isDurationBase "dayTimeDuration"
#guard !(isNumericBase "string")

end L4Factoidal.CSVW
