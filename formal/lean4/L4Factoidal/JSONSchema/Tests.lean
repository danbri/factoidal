/-
L4Factoidal.JSONSchema.Tests — build-time checks, with the
three-valued result and the exact-rational arithmetic pinned.
-/
import L4Factoidal.JSONSchema.Validate

namespace L4Factoidal.JSONSchema
open L4Factoidal.JSON

-- The three-valued lattice. A definite failure dominates an
-- unsupported sibling; a definite pass dominates one in a disjunction.
#guard vand .fail .unsupported == .fail
#guard vand .pass .unsupported == .unsupported
#guard vor .pass .unsupported == .pass
#guard vor .fail .unsupported == .unsupported
#guard vand .pass .pass == .pass

-- Exact rationals from lexemes — including exponents.
#guard parseRat "1" == some (1, 1)
#guard parseRat "1.5" == some (15, 10)
#guard parseRat "-0.25" == some (-25, 100)
#guard parseRat "1e2" == some (100, 1)
#guard parseRat "1.5e2" == some (150, 1)
#guard parseRat "1e-2" == some (1, 100)
#guard parseRat "abc" == none

-- Value comparison, not lexeme comparison: 1.0 equals 1.
#guard ratEq (1, 1) (10, 10)
#guard jsonEq (.number "1.0") (.number "1")
#guard !(jsonEq (.number "1.0") (.number "1.1"))

-- multipleOf is exact: 0.3 is a multiple of 0.1, which a float-based
-- check famously gets wrong.
#guard isMultiple (3, 10) (1, 10)
#guard !(isMultiple (35, 100) (1, 10))
#guard isMultiple (10, 1) (5, 1)

-- `integer` accepts a number whose VALUE is integral, so 1.0 counts.
#guard checkType (.string "integer") (.number "1") == .pass
#guard checkType (.string "integer") (.number "1.0") == .pass
#guard checkType (.string "integer") (.number "1.5") == .fail
#guard checkType (.string "string") (.string "x") == .pass
#guard checkType (.array [.string "string", .string "null"]) (.null) == .pass

-- Range keywords.
#guard validate (.object [("minimum", .number "5")]) (.number "5") == .pass
#guard validate (.object [("exclusiveMinimum", .number "5")]) (.number "5") == .fail
#guard validate (.object [("maximum", .number "5")]) (.number "6") == .fail
-- A non-number ignores numeric keywords rather than failing them.
#guard validate (.object [("minimum", .number "5")]) (.string "x") == .pass

-- Boolean schemas.
#guard validate (.bool true) (.number "1") == .pass
#guard validate (.bool false) (.number "1") == .fail

-- Objects: required and properties.
private def personSchema : Json :=
  .object [("type", .string "object"),
           ("required", .array [.string "name"]),
           ("properties", .object [("name", .object [("type", .string "string")])])]
#guard validate personSchema (.object [("name", .string "Alice")]) == .pass
#guard validate personSchema (.object [("name", .number "1")]) == .fail
#guard validate personSchema (.object []) == .fail

-- Arrays.
#guard validate (.object [("items", .object [("type", .string "number")])])
         (.array [.number "1", .number "2"]) == .pass
#guard validate (.object [("items", .object [("type", .string "number")])])
         (.array [.number "1", .string "x"]) == .fail
#guard validate (.object [("minItems", .number "2")]) (.array [.number "1"]) == .fail

-- Combinators, including `not`.
#guard validate (.object [("allOf", .array [.bool true, .bool true])]) .null == .pass
#guard validate (.object [("allOf", .array [.bool true, .bool false])]) .null == .fail
#guard validate (.object [("anyOf", .array [.bool false, .bool true])]) .null == .pass
#guard validate (.object [("not", .bool false)]) .null == .pass
#guard validate (.object [("not", .bool true)]) .null == .fail

-- An UNKNOWN keyword makes the verdict undetermined rather than
-- silently passing — the honest answer, and the one that keeps the
-- score truthful.
#guard validate (.object [("unknownKeyword", .number "1")]) .null == .unsupported
-- ...but a definite failure alongside it still fails.
#guard validate (.object [("type", .string "string"), ("unknownKeyword", .number "1")])
         (.number "1") == .fail

-- Annotation keywords never affect the verdict.
#guard validate (.object [("title", .string "T"), ("type", .string "null")]) .null == .pass

-- const and enum compare by value.
#guard validate (.object [("const", .number "1.0")]) (.number "1") == .pass
#guard validate (.object [("enum", .array [.string "a", .string "b"])]) (.string "b") == .pass
#guard validate (.object [("enum", .array [.string "a"])]) (.string "z") == .fail

end L4Factoidal.JSONSchema
