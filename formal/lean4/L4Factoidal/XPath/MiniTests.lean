/-
L4Factoidal.XPath.MiniTests — build-time checks for the XPath subset.

Every `#guard` below that names a bug pins a WRONG DEFINITE ANSWER,
not a crash. Both bugs the Schematron corpus caught made the evaluator
return a confident value at the right type, so the runner counted them
as decided and the score stayed silent about them.
-/
import L4Factoidal.XPath.Mini

namespace L4Factoidal.XPath

open L4Factoidal.XML

/-! ## Bug 1: `::` is not a name character

`takeName` used `takeWhile isNameC`, and `:` is a name character
because a QName writes `sch:pattern`. So `preceding-sibling::row`
came back as ONE name and parsed as a CHILD step looking for an
element literally called `preceding-sibling::row`. No document has
one, so `count(...)` was 0, `0 < 1` was TRUE, and an assertion that
should have fired reported a clean document. -/

private def precPath : Option XExpr :=
  parseXPath "count(preceding-sibling::row) < 1"

#guard (match precPath with
        | some (.binop "<" (.call "count" [.path [st]]) (.num 1)) =>
            st.axis == Axis.precedingSibling && st.test == "row"
        | _ => false)

-- A single `:` is STILL a name character: a QName must survive.
#guard (match parseXPath "sch:pattern" with
        | some (.path [st]) => st.axis == Axis.child && st.test == "sch:pattern"
        | _ => false)

/-! ## Bug 2: a sibling position is identity, not a value

`stepFrom` located the context node among its parent's children with
`findIdx? (· == ctx)` — a STRUCTURAL comparison. `<row/><row/>` are
equal values, so the second row was found at index 0 and both rows
reported zero preceding siblings. -/

private def twoRows : Node :=
  .element "table" [] [.element "row" [] [], .element "row" [] []]

-- The first row has no preceding sibling; the second has one.
#guard evalTestAt twoRows "count(preceding-sibling::row) = 0" "/table[1]/row[1]"
       == Sum.inl (some true)
#guard evalTestAt twoRows "count(preceding-sibling::row) = 1" "/table[1]/row[2]"
       == Sum.inl (some true)
-- and following-sibling is the mirror image, on the same identity.
#guard evalTestAt twoRows "count(following-sibling::row) = 1" "/table[1]/row[1]"
       == Sum.inl (some true)
#guard evalTestAt twoRows "count(following-sibling::row) = 0" "/table[1]/row[2]"
       == Sum.inl (some true)

/-! ## Paths address nodes, and the addressing round-trips -/

#guard documentPaths twoRows == ["/table[1]", "/table[1]/row[1]", "/table[1]/row[2]"]

/-! ## The corpus's own shapes -/

private def shop : Node :=
  .element "shop" []
    [ .element "book" [⟨"discount", "yes"⟩, ⟨"clearance", "yes"⟩] [.text "Both"]
    , .element "book" [⟨"discount", "yes"⟩] [.text "Discount"]
    , .element "book" [] [.text "Plain"] ]

#guard evalTestAt shop "@discount and @clearance" "/shop[1]/book[1]" == Sum.inl (some true)
#guard evalTestAt shop "@discount and @clearance" "/shop[1]/book[2]" == Sum.inl (some false)
#guard evalTestAt shop "@discount and @clearance" "/shop[1]/book[3]" == Sum.inl (some false)
#guard evalTestAt shop "count(book) = 3" "/shop[1]" == Sum.inl (some true)
#guard evalTestAt shop "false()" "/shop[1]" == Sum.inl (some false)
#guard evalTestAt shop "not(false())" "/shop[1]" == Sum.inl (some true)

private def payments : Node :=
  .element "payments" []
    [ .element "payment" [⟨"type", "card"⟩] [.element "card-number" [] [.text "4111"]]
    , .element "payment" [⟨"type", "card"⟩] []
    , .element "payment" [⟨"type", "cash"⟩] [] ]

#guard evalTestAt payments "not(@type = 'card') or card-number" "/payments[1]/payment[1]"
       == Sum.inl (some true)
#guard evalTestAt payments "not(@type = 'card') or card-number" "/payments[1]/payment[2]"
       == Sum.inl (some false)
#guard evalTestAt payments "not(@type = 'card') or card-number" "/payments[1]/payment[3]"
       == Sum.inl (some true)

/-! ## A context pattern selects on the element name, `*` on any -/

#guard contextSelects shop "book" "/shop[1]/book[1]"
#guard !(contextSelects shop "book" "/shop[1]")
#guard contextSelects shop "*" "/shop[1]"
#guard !(contextSelects shop "book" "/shop[1]/absent[1]")

/-! ## OUTSIDE the subset is `undecided`, never `false`

This is the property that keeps the score truthful: a construct the
evaluator cannot read is refused with a reason, so the runner counts
it apart instead of scoring an invented verdict. -/

#guard (match evalTestAt shop "substring-before(@x, '-')" "/shop[1]" with
        | Sum.inr _ => true | _ => false)
#guard (match evalTestAt shop "book[1]" "/shop[1]" with
        | Sum.inr _ => true | _ => false)
#guard (match evalTestAt shop "count(book) < 'x'" "/shop[1]" with
        | Sum.inr _ => true | _ => false)
-- A node the path does not name is refused too, not reported false.
#guard (match evalTestAt shop "true()" "/shop[1]/book[9]" with
        | Sum.inr _ => true | _ => false)

end L4Factoidal.XPath
