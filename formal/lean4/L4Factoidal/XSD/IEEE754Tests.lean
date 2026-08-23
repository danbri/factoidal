/-
L4Factoidal.XSD.IEEE754Tests — the port against an independent
correctly-rounded implementation.

`IEEE754.lean` computes the IEEE-754 value of a decimal lexical in exact
big-integer rational arithmetic. A test that restates that algorithm
proves nothing. The table below is the same 66 lexicals converted by
CPython's `float()`, which goes through a correctly-rounded `strtod`,
with the resulting bit patterns read out by `struct.pack('>d', …)` and
`struct.pack('>f', …)`. Each row is `(lexical, binary64 bits, binary32
bits)`.

The binary32 column is the DOUBLE-ROUNDED value (decimal → binary64 →
binary32), which is what `struct.pack('>f', float(s))` computes and what
`IEEE754.lean`'s `canonFloat` specifies.

Coverage the table is chosen for, and not by accident:

- the 2^53 boundary (`9007199254740993` is not representable; the four
  consecutive integers around it pin the ties-to-even direction);
- the 2^24 boundary for binary32 (`16777217`, `16777219`);
- one-ulp neighbours (`1.0000000000000001` vs `1.0000000000000002`);
- the smallest subnormal and its halfway point (`5e-324`, `2.5e-324`,
  `2.4e-324`) — the ties-to-even case at the very bottom of the grid;
- `2.2250738585072011e-308`, the decimal that hung PHP's `strtod` in
  2011, and its normal neighbour;
- overflow to infinity at both magnitudes (`1.8e308`, `1e400`);
- underflow to zero below the subnormal grid (`1e-46`);
- the same value written several ways (`1000`, `1e3`, `0.001e6`,
  `100000e-2`);
- a 60-digit exact decimal expansion of a double;
- signed zero, both infinities, and NaN.

Generated 2026-08-23. Regenerate by running the same lexicals through
`float()` if a row is ever disputed; do not hand-edit an expected value.
-/
import L4Factoidal.XSD.IEEE754

namespace L4Factoidal.XSD

/-- `(lexical, expected binary64 bits, expected binary32 bits)`. -/
def oracle : List (String × UInt64 × UInt32) := [
  ("0", 0x0000000000000000, 0x00000000),
  ("0.0", 0x0000000000000000, 0x00000000),
  ("-0.0", 0x8000000000000000, 0x80000000),
  ("1", 0x3FF0000000000000, 0x3F800000),
  ("1.0", 0x3FF0000000000000, 0x3F800000),
  ("-1", 0xBFF0000000000000, 0xBF800000),
  ("1.5", 0x3FF8000000000000, 0x3FC00000),
  ("2", 0x4000000000000000, 0x40000000),
  ("3", 0x4008000000000000, 0x40400000),
  ("10", 0x4024000000000000, 0x41200000),
  ("100", 0x4059000000000000, 0x42C80000),
  ("0.5", 0x3FE0000000000000, 0x3F000000),
  ("0.25", 0x3FD0000000000000, 0x3E800000),
  ("0.1", 0x3FB999999999999A, 0x3DCCCCCD),
  ("0.2", 0x3FC999999999999A, 0x3E4CCCCD),
  ("0.3", 0x3FD3333333333333, 0x3E99999A),
  ("1e0", 0x3FF0000000000000, 0x3F800000),
  ("1E0", 0x3FF0000000000000, 0x3F800000),
  ("1e1", 0x4024000000000000, 0x41200000),
  ("1e-1", 0x3FB999999999999A, 0x3DCCCCCD),
  ("+1.0", 0x3FF0000000000000, 0x3F800000),
  ("-1.5", 0xBFF8000000000000, 0xBFC00000),
  ("1000", 0x408F400000000000, 0x447A0000),
  ("1e3", 0x408F400000000000, 0x447A0000),
  ("1.0e3", 0x408F400000000000, 0x447A0000),
  ("10e2", 0x408F400000000000, 0x447A0000),
  ("0.001e6", 0x408F400000000000, 0x447A0000),
  ("100000e-2", 0x408F400000000000, 0x447A0000),
  ("9007199254740992", 0x4340000000000000, 0x5A000000),
  ("9007199254740993", 0x4340000000000000, 0x5A000000),
  ("9007199254740994", 0x4340000000000001, 0x5A000000),
  ("9007199254740995", 0x4340000000000002, 0x5A000000),
  ("1.0000000000000002", 0x3FF0000000000001, 0x3F800000),
  ("1.0000000000000001", 0x3FF0000000000000, 0x3F800000),
  ("1.00000000000000011", 0x3FF0000000000000, 0x3F800000),
  ("16777216", 0x4170000000000000, 0x4B800000),
  ("16777217", 0x4170000010000000, 0x4B800000),
  ("16777219", 0x4170000030000000, 0x4B800002),
  ("1.0000001", 0x3FF000001AD7F29B, 0x3F800001),
  ("3.4028235e38", 0x47EFFFFFE54DAFF8, 0x7F7FFFFF),
  ("3.4028236e38", 0x47EFFFFFF514A7BC, 0x7F800000),
  ("5e-324", 0x0000000000000001, 0x00000000),
  ("2.5e-324", 0x0000000000000001, 0x00000000),
  ("2.4e-324", 0x0000000000000000, 0x00000000),
  ("1e-323", 0x0000000000000002, 0x00000000),
  ("4.9406564584124654e-324", 0x0000000000000001, 0x00000000),
  ("2.2250738585072011e-308", 0x000FFFFFFFFFFFFF, 0x00000000),
  ("2.2250738585072014e-308", 0x0010000000000000, 0x00000000),
  ("1e-310", 0x000012688B70E62B, 0x00000000),
  ("1e-45", 0x3696D601AD376AB9, 0x00000001),
  ("1.4e-45", 0x369FF868BF4D956A, 0x00000001),
  ("7e-46", 0x368FF868BF4D956A, 0x00000000),
  ("1e-46", 0x366244CE242C5561, 0x00000000),
  ("1e308", 0x7FE1CCF385EBC8A0, 0x7F800000),
  ("1.7976931348623157e308", 0x7FEFFFFFFFFFFFFF, 0x7F800000),
  ("1.8e308", 0x7FF0000000000000, 0x7F800000),
  ("1e309", 0x7FF0000000000000, 0x7F800000),
  ("1e400", 0x7FF0000000000000, 0x7F800000),
  ("-1e400", 0xFFF0000000000000, 0xFF800000),
  ("0.100000000000000005551115123125782702118158340454101562500000", 0x3FB999999999999A, 0x3DCCCCCD),
  ("123456789012345678901234567890", 0x45F8EE90FF6C373E, 0x6FC77488),
  ("0.000000000000000000000000000000123456789", 0x39840831C2FCAE11, 0x0C20418E),
  ("INF", 0x7FF0000000000000, 0x7F800000),
  ("+INF", 0x7FF0000000000000, 0x7F800000),
  ("-INF", 0xFFF0000000000000, 0xFF800000),
  ("NaN", 0x7FF8000000000000, 0x7FC00000)]

/-- Rows where this module's bits differ from the oracle's. -/
def mismatches : List (String × UInt64 × UInt32) :=
  oracle.filter (fun (s, b64, b32) =>
    match bitsOfLexical s with
    | none          => true
    | some (g64, g32) => g64 != b64 || g32 != b32)

#guard oracle.length == 66
#guard mismatches == []

/-! Every lexical in the table is in the datatype's lexical space, so a
    `none` from `parseLexical` is a failure rather than a skip. Checked
    separately, because `mismatches` counts a `none` as a mismatch and
    that would read as a rounding difference. -/

#guard oracle.all (fun (s, _, _) => (parseLexical s).isSome)

/-! ## Value equality follows from the bits

The public API compares canonical records, not bit patterns, so these
check the two agree on the cases where the distinction is visible. -/

#guard doubleValueEq "1000" "1e3"
#guard doubleValueEq "0.001e6" "100000e-2"
#guard doubleValueEq "9007199254740992" "9007199254740993"   -- both round to 2^53
#guard !doubleValueEq "9007199254740992" "9007199254740994"
#guard doubleValueEq "1e400" "1e500"                          -- both overflow to +INF
#guard !doubleValueEq "1e400" "-1e400"                        -- signed infinities differ
#guard !doubleValueEq "0.0" "-0.0"                            -- signed zeros differ
#guard !doubleValueEq "NaN" "NaN"                             -- NaN equals nothing
#guard doubleValueEq "1e-400" "0.0"                           -- underflow to +0
#guard !doubleValueEq "1e-400" "-0.0"

/-! `xsd:float` is coarser than `xsd:double`: two lexicals can be
    distinct binary64 values and the same binary32 value. -/

#guard !doubleValueEq "16777216" "16777217"
#guard floatValueEq "16777216" "16777217"
#guard !floatValueEq "16777216" "16777219"
#guard floatValueEq "3.4028236e38" "INF"                      -- above the binary32 maximum
#guard !doubleValueEq "3.4028236e38" "INF"

/-! `rdf:JSON` numbers are binary64. -/

#guard jsonNumberEq "1.0" "1"
#guard jsonNumberEq "1e3" "1000"

/-! A lexical outside the lexical space has no value, so the API falls
    back to string equality — the F\* source's behaviour. -/

#guard (parseLexical "").isNone
#guard (parseLexical "abc").isNone
#guard (parseLexical "1.2.3").isNone
#guard (parseLexical "1e").isNone
#guard (parseLexical ".").isNone
#guard doubleValueEq "abc" "abc"
#guard !doubleValueEq "abc" "abd"

/-! `.5` and `5.` ARE in the XSD lexical space for double. -/

#guard doubleValueEq ".5" "0.5"
#guard doubleValueEq "5." "5"

end L4Factoidal.XSD
