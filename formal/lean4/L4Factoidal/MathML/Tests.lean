/-
L4Factoidal.MathML.Tests — build-time checks for exact rational
evaluation and Presentation rendering.
-/
import L4Factoidal.MathML.Core

namespace L4Factoidal.MathML

private def noEnv : String → Option (Int × Int) := fun _ => none
private def env1 : String → Option (Int × Int)
  | "x" => some (2, 1)
  | _   => none

-- Exact rationals: thirds sum to exactly one.
#guard eval noEnv (.app "plus" [.rat 1 3, .rat 1 3, .rat 1 3]) == some (.num (1, 1))
#guard eval noEnv (.app "plus" [.int 1, .int 2]) == some (.num (3, 1))
#guard eval noEnv (.app "times" [.rat 1 2, .rat 2 3]) == some (.num (1, 3))
#guard eval noEnv (.app "minus" [.int 5, .int 3]) == some (.num (2, 1))
#guard eval noEnv (.app "minus" [.int 5]) == some (.num (-5, 1))
#guard eval noEnv (.app "power" [.int 2, .int 10]) == some (.num (1024, 1))

-- Normalisation to lowest terms with a positive denominator.
#guard normRat 2 4 == (1, 2)
#guard normRat 1 (-2) == (-1, 2)
#guard normRat (-2) (-4) == (1, 2)

-- Division by zero REFUSES rather than inventing an infinity —
-- Content MathML has no such value.
#guard eval noEnv (.app "divide" [.int 1, .int 0]) == none
#guard divRat (1, 1) (0, 1) == none
#guard eval noEnv (.app "divide" [.int 1, .int 4]) == some (.num (1, 4))

-- An unbound symbol refuses; a bound one resolves.
#guard eval noEnv (.sym "x") == none
#guard eval env1 (.sym "x") == some (.num (2, 1))
#guard eval env1 (.app "plus" [.sym "x", .int 1]) == some (.num (3, 1))

-- An unknown operator refuses rather than defaulting.
#guard eval noEnv (.app "frobnicate" [.int 1]) == none

-- Relations produce booleans.
#guard eval noEnv (.app "lt" [.int 1, .int 2]) == some (.bool true)
#guard eval noEnv (.app "geq" [.int 2, .int 2]) == some (.bool true)
#guard eval noEnv (.app "neq" [.rat 1 2, .rat 2 4]) == some (.bool false)

-- Precedence table.
#guard prec (.int 1) == 4
#guard prec (.int (-1)) == 1        -- a negative literal binds loosely
#guard prec (.app "plus" [.int 1]) == 1
#guard prec (.app "times" [.int 1]) == 2
#guard prec (.app "power" [.int 1]) == 3
#guard prec (.app "eq" [.int 1]) == 0

-- Rendering fences a looser child inside a tighter parent.
#guard render (.int 2) == "<mn>2</mn>"
#guard render (.app "times" [.app "plus" [.int 1, .int 2], .int 3])
       == "<mrow><mrow><mo>(</mo><mrow><mn>1</mn><mo>+</mo><mn>2</mn></mrow><mo>)</mo></mrow><mo>&#x22C5;</mo><mn>3</mn></mrow>"
-- ...and does NOT fence when it is already tighter.
#guard render (.app "plus" [.app "times" [.int 1, .int 2], .int 3])
       == "<mrow><mrow><mn>1</mn><mo>&#x22C5;</mo><mn>2</mn></mrow><mo>+</mo><mn>3</mn></mrow>"

-- XML escaping in symbol names.
#guard escapeXml "a<b&c" == "a&lt;b&amp;c"
#guard render (.sym "a<b") == "<mi>a&lt;b</mi>"

-- Content vs Presentation detection: CONTENT wins when both appear,
-- since that is the vocabulary carrying meaning.
#guard kindOf ["apply", "cn"] == .content
#guard kindOf ["mrow", "mi"] == .presentation
#guard kindOf ["apply", "mrow"] == .content
#guard kindOf ["div", "span"] == .unknown

end L4Factoidal.MathML
