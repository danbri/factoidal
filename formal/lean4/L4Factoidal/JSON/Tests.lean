/-
L4Factoidal.JSON.Tests — compile-time executable checks.

Every `#guard` below is evaluated during `lake build`: a wrong answer
is a BUILD FAILURE (same discipline as `L4Factoidal/Tests.lean`).
Covers RFC 8259 examples, every escape form (§7), number-lexeme
preservation (§6), rejection cases, key-order/duplicate preservation,
and parse∘serialize round-trips.
-/
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.JSON.Tests

open L4Factoidal.JSON

/-! ### RFC 8259 §13 example object (adapted) -/

def rfcExample : Json :=
  .object [
    ("Image", .object [
      ("Width", .number "800"),
      ("Height", .number "600"),
      ("Title", .string "View from 15th Floor"),
      ("Thumbnail", .object [
        ("Url", .string "http://www.example.com/image/481989943"),
        ("Height", .number "125"),
        ("Width", .number "100")
      ]),
      ("Animated", .bool false),
      ("IDs", .array [.number "116", .number "943", .number "234", .number "38793"])
    ])
  ]

#guard parseJson rfcExample.toString == .ok rfcExample

/-! ### Literal forms -/

#guard parseJson "null" == .ok Json.null
#guard parseJson "true" == .ok (Json.bool true)
#guard parseJson "false" == .ok (Json.bool false)
#guard parseJson "  null  " == .ok Json.null   -- leading/trailing whitespace (§2)
#guard parseJson "\t\n\rnull\r\n\t" == .ok Json.null

/-! ### Numbers (§6) — lexical preservation -/

#guard parseJson "0" == .ok (Json.number "0")
#guard parseJson "-0" == .ok (Json.number "-0")
#guard parseJson "-0.0" == .ok (Json.number "-0.0")
#guard parseJson "123" == .ok (Json.number "123")
#guard parseJson "-123" == .ok (Json.number "-123")
#guard parseJson "1.5" == .ok (Json.number "1.5")
#guard parseJson "1e10" == .ok (Json.number "1e10")
#guard parseJson "1E10" == .ok (Json.number "1E10")
#guard parseJson "1e+10" == .ok (Json.number "1e+10")
#guard parseJson "1e-10" == .ok (Json.number "1e-10")
#guard parseJson "1.5E-3" == .ok (Json.number "1.5E-3")
#guard parseJson "3.14159" == .ok (Json.number "3.14159")

/-! ### Strings — the full escape set (§7) -/

#guard parseJson "\"\"" == .ok (Json.string "")
#guard parseJson "\"hello\"" == .ok (Json.string "hello")
#guard parseJson "\"\\\"\"" == .ok (Json.string "\"")       -- \"
#guard parseJson "\"\\\\\"" == .ok (Json.string "\\")       -- \\
#guard parseJson "\"\\/\"" == .ok (Json.string "/")         -- \/
#guard parseJson "\"\\b\"" == .ok (Json.string "\x08")      -- \b
#guard parseJson "\"\\f\"" == .ok (Json.string "\x0C")      -- \f
#guard parseJson "\"\\n\"" == .ok (Json.string "\n")        -- \n
#guard parseJson "\"\\r\"" == .ok (Json.string "\r")        -- \r
#guard parseJson "\"\\t\"" == .ok (Json.string "\t")        -- \t
#guard parseJson "\"\\u0041\"" == .ok (Json.string "A")     -- \u ASCII
#guard parseJson "\"\\u00e9\"" == .ok (Json.string "é")     -- \u non-ASCII BMP
#guard parseJson "\"\\uD83D\\uDE00\"" == .ok (Json.string "😀")  -- surrogate pair
#guard parseJson "\"raw utf8 café ☺\"" == .ok (Json.string "raw utf8 café ☺")  -- raw pass-through

/-! ### Nested structures -/

#guard parseJson "[]" == .ok (Json.array [])
#guard parseJson "{}" == .ok (Json.object [])
#guard parseJson "[1,2,3]" ==
  .ok (Json.array [Json.number "1", Json.number "2", Json.number "3"])
#guard parseJson "[[1,2],[3,4]]" ==
  .ok (Json.array [Json.array [Json.number "1", Json.number "2"],
                    Json.array [Json.number "3", Json.number "4"]])
#guard parseJson "{\"a\":{\"b\":{\"c\":1}}}" ==
  .ok (Json.object [("a", Json.object [("b", Json.object [("c", Json.number "1")])])])
#guard parseJson "[{\"a\":1},{\"b\":2}]" ==
  .ok (Json.array [Json.object [("a", Json.number "1")], Json.object [("b", Json.number "2")]])

/-! ### Key order and duplicate keys are preserved (Value.lean's module header) -/

#guard parseJson "{\"z\":1,\"a\":2,\"m\":3}" ==
  .ok (Json.object [("z", Json.number "1"), ("a", Json.number "2"), ("m", Json.number "3")])
#guard parseJson "{\"a\":1,\"a\":2}" ==
  .ok (Json.object [("a", Json.number "1"), ("a", Json.number "2")])
-- first-match lookup on a duplicate-keyed object (Json.field?):
#guard (Json.object [("a", Json.number "1"), ("a", Json.number "2")]).field? "a" ==
  some (Json.number "1")

/-! ### Rejection cases -/

#guard (parseJson "").isError                       -- empty input
#guard (parseJson "01").isError                      -- leading zero
#guard (parseJson "-01").isError                     -- leading zero, negative
#guard (parseJson "{a:1}").isError                   -- unquoted key
#guard (parseJson "{\"a\":1,}").isError               -- trailing comma, object
#guard (parseJson "[1,2,]").isError                  -- trailing comma, array
#guard (parseJson "\"\\uD800\"").isError              -- lone high surrogate
#guard (parseJson "\"\\uDC00\"").isError              -- lone low surrogate
#guard (parseJson "\"\\uD800\\u0041\"").isError       -- high surrogate not followed by low
#guard (parseJson "\"a\nb\"").isError                 -- raw control character (unescaped LF)
#guard (parseJson "[1,2").isError                    -- truncated: unterminated array
#guard (parseJson "\"abc").isError                    -- truncated: unterminated string
#guard (parseJson "tru").isError                      -- truncated keyword
#guard (parseJson "null extra").isError               -- trailing content after value
#guard (parseJson "\"\\x\"").isError                  -- invalid escape letter
#guard (parseJson "1.").isError                       -- dot with no fraction digit
#guard (parseJson "1e").isError                       -- exponent with no digit
#guard (parseJson "+1").isError                       -- leading '+' not permitted

/-! ### parse ∘ serialize round-trips on every positive fixture above -/

def fixtures : List Json := [
  Json.null, Json.bool true, Json.bool false,
  Json.number "0", Json.number "-0", Json.number "-0.0", Json.number "123",
  Json.number "1.5E-3", Json.number "1e+10",
  Json.string "", Json.string "hello", Json.string "\"", Json.string "\\",
  Json.string "/", Json.string "\x08", Json.string "\x0C", Json.string "\n",
  Json.string "\r", Json.string "\t", Json.string "A", Json.string "é",
  Json.string "😀", Json.string "raw utf8 café ☺",
  Json.array [], Json.object [],
  Json.array [Json.number "1", Json.number "2", Json.number "3"],
  Json.object [("z", Json.number "1"), ("a", Json.number "2")],
  Json.object [("a", Json.number "1"), ("a", Json.number "2")],
  rfcExample
]

#guard fixtures.all (fun j => parseJson j.toString == .ok j)
#guard fixtures.all (fun j => parseJson j.toStringPretty == .ok j)

end L4Factoidal.JSON.Tests
