/-
L4Factoidal.Fn.Boolean — XQuery 1.0 and XPath 2.0 Functions and
Operators §9, the `xs:boolean` operators.

RIF-DTB 4.6 cites `fn:not`, `op:boolean-equal`, `op:boolean-less-than`
and `op:boolean-greater-than`. The value space is `{false, true}`
ordered `false < true` (XML Schema Part 2 §3.3.2.3).
-/

namespace L4Factoidal.Fn.Boolean

/-- §9.3.1 `fn:not`. -/
def not (b : Bool) : Bool := !b

/-- §9.2.1 `op:boolean-equal`. -/
def equal (a b : Bool) : Bool := a == b

/-- §9.2.2 `op:boolean-less-than`: `false` precedes `true`. -/
def lessThan (a b : Bool) : Bool := !a && b

/-- §9.2.3 `op:boolean-greater-than`. -/
def greaterThan (a b : Bool) : Bool := a && !b

/-- The `xs:boolean` lexical mapping (XML Schema Part 2 §3.3.2.2):
    `true`, `false`, `1`, `0`. `1` and `true` are the SAME value, which
    is why the RIF corpus's
    `pred:boolean-less-than("0"^^xs:boolean "1"^^xs:boolean)` holds. -/
def ofLexical (s : String) : Option Bool :=
  if s == "true" || s == "1" then some true
  else if s == "false" || s == "0" then some false
  else none

/-- §3.3.2.2, the canonical mapping. -/
def canonical (b : Bool) : String := if b then "true" else "false"

#guard lessThan false true = true
#guard lessThan true false = false
#guard greaterThan true false = true
#guard ofLexical "1" = some true
#guard ofLexical "0" = some false
#guard ofLexical "yes" = none

/-- The order is total and antisymmetric, checked over the whole
    two-element value space rather than asserted. -/
theorem lessThan_asymm (a b : Bool) : ¬(lessThan a b ∧ lessThan b a) := by
  cases a <;> cases b <;> simp [lessThan]

theorem trichotomy (a b : Bool) : lessThan a b ∨ equal a b ∨ greaterThan a b := by
  cases a <;> cases b <;> simp [lessThan, equal, greaterThan]

end L4Factoidal.Fn.Boolean
