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
#guard parseNumber "decimal" euro "1.234,56" == .valid "1234.56"
#guard parseNumber "decimal" {} "1,234.56" == .valid "1234.56"
#guard parseNumber "decimal" {} "42" == .valid "42"
#guard parseNumber "decimal" {} "-42" == .valid "-42"
#guard parseNumber "decimal" {} "+42" == .valid "42"

-- Malformed numbers are rejected.
#guard parseNumber "decimal" {} "abc" == .invalid
#guard parseNumber "decimal" {} "" == .invalid
#guard parseNumber "decimal" {} "1.2.3" == .invalid
-- A numeric column validates its cells with NO format at all: the XSD
-- lexical space still applies.
#guard parseNumber "integer" {} "3.2" == .invalid
#guard parseNumber "decimal" {} "123.456E7" == .invalid
#guard parseNumber "double" {} "123.456E7" == .valid "123.456E7"
#guard parseNumber "decimal" {} "NaN" == .invalid
#guard parseNumber "double" {} "NaN" == .valid "NaN"
#guard parseNumber "double" {} "-INF" == .valid "-INF"
-- Grouping characters must SEPARATE digits. Two in a row is a
-- validation error the corpus states outright.
#guard parseNumber "decimal" {} "123,,456.789" == .invalid
#guard parseNumber "decimal" {} "123,456.789" == .valid "123456.789"
#guard parseNumber "decimal" {} "." == .invalid

-- Percent and per-mille scale EXACTLY, on the digit string — no
-- float arithmetic, so 12.5% is 0.125 rather than a binary
-- approximation.
#guard parseNumber "decimal" { percent := true } "12.5%" == .valid "0.125"
#guard parseNumber "decimal" { percent := true } "50%" == .valid "0.50"
#guard parseNumber "decimal" { permille := true } "125‰" == .valid "0.125"
#guard parseNumber "decimal" { percent := true } "-25%" == .valid "-0.25"

-- The three-way outcome: a numeric base with NO format at all is
-- A NUMERIC base is checked even with no format: the XSD lexical
-- space applies regardless. (This guard used to expect `noFormat`;
-- returning that meant `3.2` reached the output as an `xsd:integer`.)
#guard formatConvert "integer" none none none none "42" == .valid "42"
#guard formatConvert "integer" none none none none "3.2" == .invalid
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
-- With no format the CANONICAL XSD lexical form is required, and
-- checked. (This guard used to expect `noFormat`, which meant any
-- text at all took the date datatype.)
#guard formatConvert "date" none none none none "2010-10-18"
       == .valid "2010-10-18"
#guard formatConvert "date" none none none none "10/18/2010" == .invalid
#guard formatConvert "dateTime" none none none none "2010-06-02T12:34:56Z"
       == .valid "2010-06-02T12:34:56Z"

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

-- The duration `format` facet is an XSD REGEX and needs an engine this
-- slice does not have, so a value under one cannot be SHOWN valid and
-- gets no datatype. With NO format the lexical space is still
-- checkable, which is what stops `Foo` becoming an xsd:duration.
#guard formatConvert "duration" (some "^.$") none none none "P1D" == .invalid
#guard formatConvert "duration" none none none none "P1D" == .valid "P1D"
#guard formatConvert "duration" none none none none "Foo" == .invalid
#guard isDurationLexical "P1Y2M3DT4H5M6S"
#guard isDurationLexical "-P1D"
#guard isDurationLexical "PT1.5S"
#guard !isDurationLexical "P"
#guard !isDurationLexical "P1DT"
#guard !isDurationLexical "1D"

-- Decimal PATTERNS constrain digit counts and grouping positions, not
-- just the separator characters. Sixteen corpus tests supply a
-- perfectly good number and expect it REJECTED for not matching its
-- column's pattern.
private def pat (p : String) : NumPattern := parseNumPattern p ',' '.'
#guard (pat "#,#00").minInt == 2
#guard (pat "#0.0#").minFrac == 1
#guard (pat "#0.0#").maxFrac == 2
#guard (pat "#,##,#00").primaryGroup == some 3
#guard (pat "#,##,#00").secondaryGroup == some 2
#guard (pat "0.0E0").hasExp

#guard regroup "1234567" 3 2 ',' == "12,34,567"
#guard regroup "1234567" 3 3 ',' == "1,234,567"
#guard regroup "12" 3 3 ',' == "12"

-- Too few integer digits for `#,#00`.
#guard !matchesNumPattern (pat "#,#00") ',' '.' "1"
-- Right digits, but the grouping the pattern demands is absent.
#guard !matchesNumPattern (pat "#,#00") ',' '.' "1234"
#guard matchesNumPattern (pat "#,#00") ',' '.' "1,234"
-- Secondary group size 2, so `1,234,567` is the wrong shape.
#guard !matchesNumPattern (pat "#,##,#00") ',' '.' "1,234,567"
#guard matchesNumPattern (pat "#,##,#00") ',' '.' "12,34,567"
-- Fraction-digit bounds.
#guard !matchesNumPattern (pat "#0.#") ',' '.' "12.34"
#guard matchesNumPattern (pat "#0.#") ',' '.' "12.3"
#guard !matchesNumPattern (pat "#0.0") ',' '.' "1"
#guard !matchesNumPattern (pat "#0.0#") ',' '.' "12.345"
-- An exponent is required exactly when the pattern has one.
#guard !matchesNumPattern (pat "0.0") ',' '.' "1.0E3"
#guard matchesNumPattern (pat "0.0E0") ',' '.' "1.0E3"

-- Value constraints (section 5.11.2), compared EXACTLY rather than
-- through a float.
#guard decimalCompare "4" "5" == some .lt
#guard decimalCompare "5" "5" == some .eq
#guard decimalCompare "-2" "1" == some .lt
#guard decimalCompare "10.5" "10.50" == some .eq
#guard decimalCompare "2" "10" == some .lt
#guard satisfiesFacets { minimum := some "5" } "5"
#guard !satisfiesFacets { minimum := some "5" } "4"
#guard !satisfiesFacets { minExclusive := some "5" } "5"
#guard satisfiesFacets { maxExclusive := some "5" } "4"
#guard satisfiesFacets { minLength := some 2, maxLength := some 4 } "abc"
#guard !satisfiesFacets { maxLength := some 2 } "abc"

-- Base classification.
#guard isNumericBase "decimal"
#guard isDateBase "dateTime"
#guard isDurationBase "dayTimeDuration"
#guard !(isNumericBase "string")

end L4Factoidal.CSVW
