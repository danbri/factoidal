/-
L4Factoidal.XSD.DatatypesTests — the `#guard` battery for
`XSD/Datatypes.lean`, taken from the examples XML Schema 1.1 Part 2
prints in its own datatype sections.

Every literal below is quoted from the specification section named in
the comment above it. A `#guard` that fails is a build failure, so the
battery is a gate and not documentation.
-/
import L4Factoidal.XSD.SimpleType

namespace L4Factoidal.XSD

/-! ## §3.3.1 `string`, §3.4.1-§3.4.2 the normalized forms -/

#guard (lexicalMapWs .string "  a  b  ") == some (.str .string "  a  b  ")
#guard (lexicalMapWs .normalizedString "a\tb") == some (.str .string "a b")
#guard (lexicalMapWs .token "  a   b  ") == some (.str .string "a b")
#guard wsCollapse "  a \t b \n c  " == "a b c"
#guard wsReplace "a\tb\nc" == "a b c"

/-! ## §3.3.2 `boolean` — "true", "false", "1", "0" -/

#guard (lexicalMapWs .boolean "true") == some (.bool true)
#guard (lexicalMapWs .boolean "1") == some (.bool true)
#guard (lexicalMapWs .boolean "0") == some (.bool false)
#guard (lexicalMapWs .boolean "TRUE") == none
#guard canonicalMap .boolean (.bool true) == "true"
-- whiteSpace is `collapse`, so a padded literal IS in the lexical space.
#guard (lexicalMapWs .boolean " true ") == some (.bool true)

/-! ## §3.3.3 `decimal` — the section's own examples
"3.0", "-1.23", "12678967.543233", "+100000.00", "210" -/

#guard (lexicalMapWs .decimal "3.0") == some (.dec ⟨3, 0⟩)
#guard (lexicalMapWs .decimal "-1.23") == some (.dec ⟨-123, 2⟩)
#guard (lexicalMapWs .decimal "12678967.543233").isSome
#guard (lexicalMapWs .decimal "+100000.00") == some (.dec ⟨100000, 0⟩)
#guard (lexicalMapWs .decimal "210") == some (.dec ⟨210, 0⟩)
#guard (lexicalMapWs .decimal "1E2") == none
#guard (lexicalMapWs .decimal "") == none
#guard (lexicalMapWs .decimal ".") == none
-- §3.3.3.2: an integral value has no decimal point in canonical form.
#guard canonicalMap .decimal (.dec ⟨3, 0⟩) == "3"
#guard canonicalMap .decimal (.dec ⟨-123, 2⟩) == "-1.23"
#guard canonicalMap .decimal (.dec ⟨5, 3⟩) == "0.005"
#guard Dec.cmp ⟨30, 1⟩ ⟨3, 0⟩ == .eq
#guard (Dec.norm ⟨100, 2⟩) == ⟨1, 0⟩

/-! ## §3.3.13 `integer` and the §3.4 bounded types -/

#guard (lexicalMapWs .integer "-1") == some (.dec ⟨-1, 0⟩)
#guard (lexicalMapWs .integer "+00000000000012678967543233").isSome
#guard (lexicalMapWs .integer "1.0") == none
#guard canonicalMap .integer (.dec ⟨100000, 0⟩) == "100000"
#guard (lexicalMapWs .byte "127").isSome
#guard (lexicalMapWs .byte "128") == none
#guard (lexicalMapWs .byte "-128").isSome
#guard (lexicalMapWs .byte "-129") == none
#guard (lexicalMapWs .unsignedByte "255").isSome
#guard (lexicalMapWs .unsignedByte "256") == none
#guard (lexicalMapWs .int "2147483647").isSome
#guard (lexicalMapWs .int "2147483648") == none
#guard (lexicalMapWs .long "9223372036854775807").isSome
#guard (lexicalMapWs .long "9223372036854775808") == none
#guard (lexicalMapWs .unsignedLong "18446744073709551615").isSome
#guard (lexicalMapWs .unsignedLong "18446744073709551616") == none
#guard (lexicalMapWs .positiveInteger "0") == none
#guard (lexicalMapWs .negativeInteger "0") == none
#guard (lexicalMapWs .nonNegativeInteger "0").isSome
#guard (lexicalMapWs .nonPositiveInteger "0").isSome
#guard derivedFrom .byte .integer
#guard derivedFrom .byte .decimal
#guard !derivedFrom .decimal .integer

/-! ## §3.3.4 `float` and §3.3.5 `double` — the section's examples
"-1E4", "1267.43233E12", "12.78e-2", "12", "-0", "0", "INF" -/

#guard (lexicalMapWs .float "-1E4").isSome
#guard (lexicalMapWs .float "1267.43233E12").isSome
#guard (lexicalMapWs .float "12.78e-2").isSome
#guard (lexicalMapWs .float "12").isSome
#guard (lexicalMapWs .float "-0").isSome
#guard (lexicalMapWs .float "INF").isSome
#guard (lexicalMapWs .float "NaN").isSome
#guard (lexicalMapWs .float "+INF").isSome
#guard (lexicalMapWs .double "-INF").isSome
#guard (lexicalMapWs .float "Infinity") == none
#guard (lexicalMapWs .float "nan") == none
#guard (lexicalMapWs .float "1e") == none
-- NaN is incomparable with everything, itself included (§3.3.4).
#guard (valCompare (.flt ⟨false, .nan⟩) (.flt ⟨false, .nan⟩)) == none
-- but it is IDENTICAL to itself, which is what `enumeration` tests.
#guard valIdentical (.flt ⟨false, .nan⟩) (.flt ⟨false, .nan⟩)
-- `-0` and `+0` are equal in the order and distinct in identity.
#guard (valCompare (.flt ⟨true, .zero⟩) (.flt ⟨false, .zero⟩)) == some .eq
#guard !valIdentical (.flt ⟨true, .zero⟩) (.flt ⟨false, .zero⟩)
#guard canonicalMap .float (.flt ⟨false, .inf⟩) == "INF"
#guard canonicalMap .double (.dbl ⟨true, .inf⟩) == "-INF"
#guard canonicalMap .double (.dbl ⟨false, .nan⟩) == "NaN"

/-! ## §3.3.6 `duration` — "P1Y2M3DT10H30M", "-P120D", "P1347Y" -/

#guard (lexicalMapWs .duration "P1Y2M3DT10H30M").isSome
#guard (lexicalMapWs .duration "-P120D").isSome
#guard (lexicalMapWs .duration "P1347Y").isSome
#guard (lexicalMapWs .duration "P0Y1347M").isSome
#guard (lexicalMapWs .duration "P0Y1347M0D").isSome
-- §3.3.6: these are NOT in the lexical space.
#guard (lexicalMapWs .duration "P-1347M") == none
#guard (lexicalMapWs .duration "P1Y2MT") == none
#guard (lexicalMapWs .duration "P") == none
#guard (lexicalMapWs .duration "1Y") == none
#guard (lexicalMapWs .duration "PT") == none
-- §3.4.27 / §3.4.28: the two 1.1 sub-types.
#guard (lexicalMapWs .yearMonthDuration "P1Y2M").isSome
#guard (lexicalMapWs .yearMonthDuration "P1D") == none
#guard (lexicalMapWs .dayTimeDuration "P1DT2H").isSome
#guard (lexicalMapWs .dayTimeDuration "P1Y") == none
#guard canonicalMap .duration (.dur ⟨14, Dec.ofInt 0⟩) == "P1Y2M"
#guard canonicalMap .duration (.dur ⟨0, Dec.ofInt 0⟩) == "PT0S"
-- §3.3.6.2: P1M and P30D are INCOMPARABLE.
#guard (valCompare (.dur ⟨1, Dec.ofInt 0⟩) (.dur ⟨0, Dec.ofInt 2592000⟩)) == none
#guard (valCompare (.dur ⟨0, Dec.ofInt 60⟩) (.dur ⟨0, Dec.ofInt 61⟩)) == some .lt

/-! ## §3.3.7-§3.3.14 the date/time family -/

#guard (lexicalMapWs .dateTime "2002-10-10T12:00:00-05:00").isSome
#guard (lexicalMapWs .dateTime "2002-10-10T17:00:00Z").isSome
-- §3.3.8: the two above denote the SAME instant.
#guard valIdentical
  ((lexicalMapWs .dateTime "2002-10-10T12:00:00-05:00").getD (.bool false))
  ((lexicalMapWs .dateTime "2002-10-10T17:00:00Z").getD (.bool true))
#guard (lexicalMapWs .dateTime "2002-10-10T12:00:00").isSome
#guard (lexicalMapWs .dateTime "2002-13-10T12:00:00Z") == none
#guard (lexicalMapWs .dateTime "2002-02-30T12:00:00Z") == none
#guard (lexicalMapWs .dateTime "2004-02-29T12:00:00Z").isSome
#guard (lexicalMapWs .dateTime "2003-02-29T12:00:00Z") == none
-- §3.3.8: 24:00:00 is the start of the next day.
#guard (lexicalMapWs .dateTime "2002-10-10T24:00:00Z") ==
       (lexicalMapWs .dateTime "2002-10-11T00:00:00Z")
#guard (lexicalMapWs .dateTime "2002-10-10T24:00:01Z") == none
-- §3.3.7.1: the timezone window is [-14:00, +14:00].
#guard (lexicalMapWs .dateTime "2002-10-10T12:00:00+14:00").isSome
#guard (lexicalMapWs .dateTime "2002-10-10T12:00:00+14:01") == none
#guard (lexicalMapWs .dateTime "2002-10-10T12:00:00+15:00") == none
#guard (lexicalMapWs .date "2002-10-10").isSome
#guard (lexicalMapWs .date "2002-10-10Z").isSome
#guard (lexicalMapWs .time "13:20:00-05:00").isSome
#guard (lexicalMapWs .time "13:20:00.5").isSome
#guard (lexicalMapWs .time "25:00:00") == none
#guard (lexicalMapWs .gYearMonth "1999-05").isSome
#guard (lexicalMapWs .gYear "1999").isSome
#guard (lexicalMapWs .gYear "99") == none
#guard (lexicalMapWs .gMonthDay "--05-31").isSome
#guard (lexicalMapWs .gMonthDay "--02-29").isSome
#guard (lexicalMapWs .gMonthDay "--02-30") == none
#guard (lexicalMapWs .gDay "---31").isSome
#guard (lexicalMapWs .gMonth "--05").isSome
#guard (lexicalMapWs .gMonth "--13") == none
-- §3.4.29 `dateTimeStamp` requires the timezone.
#guard (lexicalMapWs .dateTimeStamp "2002-10-10T12:00:00Z").isSome
#guard (lexicalMapWs .dateTimeStamp "2002-10-10T12:00:00") == none
#guard canonicalMap .dateTime
  ((lexicalMapWs .dateTime "2002-10-10T12:00:00-05:00").getD (.bool false))
  == "2002-10-10T12:00:00-05:00"
#guard canonicalMap .date ((lexicalMapWs .date "2002-10-10Z").getD (.bool false))
  == "2002-10-10Z"
-- §3.2.7.4: an untimezoned value and a timezoned one inside the
-- ±14:00 window are INCOMPARABLE.
#guard (valCompare
  ((lexicalMapWs .dateTime "2002-10-10T12:00:00").getD (.bool false))
  ((lexicalMapWs .dateTime "2002-10-10T13:00:00Z").getD (.bool true))) == none
#guard (valCompare
  ((lexicalMapWs .dateTime "2002-10-10T12:00:00").getD (.bool false))
  ((lexicalMapWs .dateTime "2010-01-01T00:00:00Z").getD (.bool true))) == some .lt

/-! ## §3.3.15 `hexBinary` and §3.3.16 `base64Binary` -/

#guard (lexicalMapWs .hexBinary "0FB7") == some (.bin true [15, 183])
#guard (lexicalMapWs .hexBinary "0fb7") == some (.bin true [15, 183])
#guard (lexicalMapWs .hexBinary "0FB") == none
#guard (lexicalMapWs .hexBinary "0FGB") == none
#guard (lexicalMapWs .hexBinary "") == some (.bin true [])
-- §3.3.15.2: the canonical form uses upper-case digits.
#guard canonicalMap .hexBinary (.bin true [15, 183]) == "0FB7"
#guard (lexicalMapWs .base64Binary "MTIz") == some (.bin false [49, 50, 51])
#guard canonicalMap .base64Binary (.bin false [49, 50, 51]) == "MTIz"
#guard (lexicalMapWs .base64Binary "MQ==") == some (.bin false [49])
#guard canonicalMap .base64Binary (.bin false [49]) == "MQ=="
#guard (lexicalMapWs .base64Binary "MTI=") == some (.bin false [49, 50])
#guard canonicalMap .base64Binary (.bin false [49, 50]) == "MTI="
-- §3.3.16.1: the padding characters constrain the preceding digit.
#guard (lexicalMapWs .base64Binary "MB==") == none
#guard (lexicalMapWs .base64Binary "MTB=") == none
#guard (lexicalMapWs .base64Binary "MTIz=") == none

/-! ## §3.3.17-§3.3.20 and the §3.4 string family -/

#guard (lexicalMapWs .anyURI "http://example.org/a?b=c#d").isSome
#guard (lexicalMapWs .anyURI "relative/path").isSome
#guard (lexicalMapWs .anyURI "http://example.org/a%zz") == none
#guard (lexicalMapWs .anyURI "a#b#c") == none
#guard (lexicalMapWs .qname "xs:string") == some (.qname "xs" "string" false)
#guard (lexicalMapWs .qname "string") == some (.qname "" "string" false)
#guard (lexicalMapWs .qname "a:b:c") == none
#guard (lexicalMapWs .qname "1a") == none
#guard (lexicalMapWs .language "en").isSome
#guard (lexicalMapWs .language "en-GB").isSome
#guard (lexicalMapWs .language "abcdefghi") == none
#guard (lexicalMapWs .language "en-") == none
#guard (lexicalMapWs .ncname "a.b-c").isSome
#guard (lexicalMapWs .ncname "a:b") == none
#guard (lexicalMapWs .name "a:b").isSome
#guard (lexicalMapWs .nmtoken "123").isSome
#guard (lexicalMapWs .ncname "123") == none
-- §3.4.5: `NMTOKENS` is a list, and its value is a sequence.
#guard (lexicalMapWs .nmtokens "a b c") ==
       some (.seq [.str .string "a", .str .string "b", .str .string "c"])
#guard (lexicalMapWs .nmtokens "") == none
#guard canonicalMap .nmtokens
  (.seq [.str .string "a", .str .string "b"]) == "a b"

/-! ## §4.3 — the constraining facets -/

private def strLen (lo hi : Nat) : SimpleType :=
  .atomic .string { minLength := some lo, maxLength := some hi }

#guard validate (strLen 2 4) "abc"
#guard !validate (strLen 2 4) "a"
#guard !validate (strLen 2 4) "abcde"
#guard validate (.atomic .string { length := some 3 }) "abc"
#guard !validate (.atomic .string { length := some 3 }) "ab"
-- §4.3.1: on `hexBinary` the unit is OCTETS, not characters.
#guard validate (.atomic .hexBinary { length := some 2 }) "0FB7"
#guard !validate (.atomic .hexBinary { length := some 4 }) "0FB7"
-- §4.3.7-§4.3.10, on the value space.
#guard validate (.atomic .integer { minInclusive := some "0" }) "0"
#guard !validate (.atomic .integer { minExclusive := some "0" }) "0"
#guard validate (.atomic .decimal { maxInclusive := some "3.0" }) "3"
#guard !validate (.atomic .decimal { maxExclusive := some "3.0" }) "3"
-- §4.3.11 / §4.3.12.
#guard validate (.atomic .decimal { totalDigits := some 3 }) "1.23"
#guard !validate (.atomic .decimal { totalDigits := some 2 }) "1.23"
#guard validate (.atomic .decimal { fractionDigits := some 2 }) "1.23"
#guard !validate (.atomic .decimal { fractionDigits := some 1 }) "1.23"
-- §4.3.5 `enumeration` tests IDENTITY, so a different lexical form of
-- the same value is admitted.
#guard validate (.atomic .decimal { enumeration := some ["1.0", "2.0"] }) "1"
#guard !validate (.atomic .decimal { enumeration := some ["1.0", "2.0"] }) "3"
-- §4.3.4 `pattern`, on the whiteSpace-normalized literal.
#guard validate (.atomic .string { patterns := [["[a-z]+"]] }) "abc"
#guard !validate (.atomic .string { patterns := [["[a-z]+"]] }) "abc1"
#guard validate (.atomic .string { patterns := [["[a-z]+", "[0-9]+"]] }) "123"
#guard !validate (.atomic .string { patterns := [["[a-z]+"], ["a.*"]] }) "bcd"
-- §4.3.13 `explicitTimezone`, new in 1.1.
#guard validate (.atomic .dateTime { explicitTimezone := some .required })
  "2002-10-10T12:00:00Z"
#guard !validate (.atomic .dateTime { explicitTimezone := some .required })
  "2002-10-10T12:00:00"
#guard !validate (.atomic .dateTime { explicitTimezone := some .prohibited })
  "2002-10-10T12:00:00Z"
-- §4.1.1 list and union varieties.
#guard validate (.list (.atomic .integer {}) { maxLength := some 3 }) "1 2 3"
#guard !validate (.list (.atomic .integer {}) { maxLength := some 3 }) "1 2 3 4"
#guard !validate (.list (.atomic .integer {}) {}) "1 x"
#guard validate (.union [.atomic .integer {}, .atomic .boolean {}] {}) "true"
#guard validate (.union [.atomic .integer {}, .atomic .boolean {}] {}) "42"
#guard !validate (.union [.atomic .integer {}, .atomic .boolean {}] {}) "x"

end L4Factoidal.XSD
