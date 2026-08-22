/-
L4Factoidal.XPath.NumberTests — build-time checks for the XPath 1.0
number type, including the IEEE special values.
-/
import L4Factoidal.XPath.Number

namespace L4Factoidal.XPath
open Num

-- Exact decimals: 0.1 + 0.2 is 0.3, which a float never manages.
#guard eq (add (.finite 1 1) (.finite 2 1)) (.finite 3 1)
#guard eq (.finite 1 1) (.finite 10 2)          -- 0.1 = 0.10
#guard eq (mul (.finite 5 1) (.finite 2 1)) (.finite 1 1)   -- 0.5 * 0.2 = 0.1

-- NaN compares unequal to EVERYTHING, including itself.
#guard cmp .nan .nan == none
#guard !(eq .nan .nan)
#guard !(lt .nan (ofInt 1))

-- Infinity arithmetic follows IEEE.
#guard add .posInf .negInf == .nan
#guard add .posInf (ofInt 5) == .posInf
#guard mul (.finite 0 0) .posInf == .nan       -- 0 x inf is NaN
#guard mul .negInf .negInf == .posInf
#guard mul .posInf (ofInt (-2)) == .negInf

-- Division by zero is an IEEE value, NOT an error.
#guard div (ofInt 1) (ofInt 0) == .posInf
#guard div (ofInt (-1)) (ofInt 0) == .negInf
#guard div (ofInt 0) (ofInt 0) == .nan
#guard eq (div (ofInt 10) (ofInt 4)) (.finite 2500000000000000000 18)

-- Ordering across the special values.
#guard lt .negInf (ofInt 0)
#guard lt (ofInt 0) .posInf
#guard le (ofInt 3) (ofInt 3)

-- boolean(): zero and NaN are FALSE, everything else TRUE. NaN being
-- false is the rule that surprises people.
#guard !(Num.toBool Num.nan)
#guard !(toBool (ofInt 0))
#guard toBool (ofInt 1)
#guard Num.toBool Num.posInf
#guard Num.toBool Num.negInf

-- number() on a string: anything unparseable is NaN, not an error.
#guard eq (ofString "42") (ofInt 42)
#guard eq (ofString "  1.5  ") (.finite 15 1)
#guard eq (ofString "-0.25") (.finite (-25) 2)
#guard ofString "abc" == .nan
#guard ofString "" == .nan
#guard ofString "1.2.3" == .nan
-- XPath 1.0 number() does NOT accept exponent notation.
#guard ofString "1e5" == .nan

end L4Factoidal.XPath
