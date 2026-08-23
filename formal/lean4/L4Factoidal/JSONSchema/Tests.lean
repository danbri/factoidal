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

/-! ## `$id` and the base URI (draft-07 §8.2)

Every check below pins a case the validator used to leave
UNDETERMINED: it could not resolve the `$ref`, so it returned no
verdict. That is the honest failure mode, and it is still a gap — 44
of the suite's 770 tests sat in it. -/

-- The base a subschema sees composes with the NEAREST enclosing base,
-- not with the document's.
#guard baseInside "" (.object [("$id", .string "http://example.com/a.json")])
       == "http://example.com/a.json"
#guard baseInside "http://example.com/a.json" (.object [("$id", .string "b/c.json")])
       == "http://example.com/b/c.json"
#guard baseInside "http://example.com/b/c.json" (.object [("$id", .string "d.json")])
       == "http://example.com/b/d.json"

-- A PLAIN-FRAGMENT `$id` is an anchor: it names this position and
-- leaves the base where it was.
#guard baseInside "http://example.com/a.json" (.object [("$id", .string "#foo")])
       == "http://example.com/a.json"

-- §8.3: a sibling `$ref` makes `$id` inert, so the ref resolves
-- against the OUTER base.
#guard baseInside "http://localhost:1234/sibling_id/base/"
         (.object [("$id", .string "foo.json"), ("$ref", .string "foo.json")])
       == "http://localhost:1234/sibling_id/base/"

-- A URN base takes an absolute reference whole. RFC 3986 relative
-- resolution is not defined against a URN, and treating one as a path
-- would mangle it.
#guard resolveAgainst "urn:uuid:deadbeef-1234-ffff-ffff-4321feebdaed"
         "urn:uuid:deadbeef-1234-ffff-ffff-4321feebdaed"
       == "urn:uuid:deadbeef-1234-ffff-ffff-4321feebdaed"
#guard hasScheme "urn:uuid:deadbeef"
#guard hasScheme "http://example.com/"
#guard !(hasScheme "foo.json")
#guard !(hasScheme "/absref/foobar.json")

-- An absolute-path reference keeps the authority and replaces the path.
#guard resolveAgainst "http://example.com/ref/absref.json" "/absref/foobar.json"
       == "http://example.com/absref/foobar.json"

-- Every `$id` in the document is registered, subschemas included --
-- a `$ref` may name one directly.
private def nestedIds : Json :=
  .object [("$id", .string "http://example.com/root"),
           ("definitions", .object [
             ("A", .object [("$id", .string "#anchorA"), ("type", .string "string")]),
             ("B", .object [("$id", .string "nested.json"),
                            ("type", .string "integer")])])]

#guard (collectIds 32 "" nestedIds).map (·.1) ==
       ["http://example.com/root", "http://example.com/root#anchorA",
        "http://example.com/nested.json"]

-- ...and the refs that name them resolve, in both directions.
#guard validate (.object [("$id", .string "http://example.com/root"),
                          ("$ref", .string "#anchorA"),
                          ("definitions", .object [
                            ("A", .object [("$id", .string "#anchorA"),
                                           ("type", .string "string")])])])
         (.string "s") == .pass
#guard validate (.object [("$id", .string "http://example.com/root"),
                          ("$ref", .string "#anchorA"),
                          ("definitions", .object [
                            ("A", .object [("$id", .string "#anchorA"),
                                           ("type", .string "string")])])])
         (.number "1") == .fail

-- A `$ref` is validated in the referenced schema's OWN scope, so a
-- pointer written there points into ITS document. Keeping the
-- POINTING document's scope is the classic wrong answer: here it
-- would resolve `#/definitions/y` in `a.json`, which has no `y`.
--
-- The inner `$ref` sits under an `allOf` rather than beside the
-- `$id`, and that placement is forced: §8.3 makes a sibling `$ref`
-- cancel its `$id`, so `{"$id": "b.json", "$ref": …}` would never
-- publish `b.json` at all. The first draft of this check made that
-- mistake and the guard caught it.
private def scopedRefDoc : Json :=
  .object [("$id", .string "http://example.com/a.json"),
           ("$ref", .string "b.json"),
           ("definitions", .object [
             ("x", .object [("$id", .string "b.json"),
                            ("allOf", .array [.object [("$ref", .string "#/definitions/y")]]),
                            ("definitions", .object [
                              ("y", .object [("type", .string "boolean")])])])])]

#guard validate scopedRefDoc (.bool true) == .pass
#guard validate scopedRefDoc (.number "1") == .fail

/-! ## A count bound may be written as a decimal

`{"maxItems": 2.0}` is `2`. Requiring a denominator of 1 made six
groups of the suite UNDETERMINED — no verdict on an ordinary schema.
The comparison stays exact: the count is scaled by the denominator
rather than the bound turned into a float. -/

#guard validate (.object [("maxItems", .number "2.0")])
         (.array [.number "1", .number "2", .number "3"]) == .fail
#guard validate (.object [("maxItems", .number "2.0")])
         (.array [.number "1"]) == .pass
#guard validate (.object [("minLength", .number "2.0")]) (.string "a") == .fail
#guard validate (.object [("minLength", .number "2.0")]) (.string "ab") == .pass
#guard validate (.object [("minProperties", .number "1.0")]) (.object []) == .fail
#guard validate (.object [("maxProperties", .number "1.0")])
         (.object [("a", .null), ("b", .null)]) == .fail
-- A NON-number bound is still undetermined, not a pass.
#guard validate (.object [("maxItems", .string "2")]) (.array []) == .unsupported

end L4Factoidal.JSONSchema
