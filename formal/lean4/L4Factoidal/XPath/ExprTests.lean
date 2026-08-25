/-
L4Factoidal.XPath.ExprTests — build-time checks for the XPath 1.0
tokenizer, parser and evaluator.

Every `#guard` here pins a rule the XSLT corpus caught this module
getting wrong, with the case that caught it named beside it. A rule
with no war story beside it is one nobody has paid for yet.
-/
import L4Factoidal.XPath.Eval
import L4Factoidal.XML.Parser

namespace L4Factoidal.XPath.Full

open L4Factoidal.XPath

open L4Factoidal.XML

/-! ## Tokenizing -/

/-! `[5] QName` carries AT MOST ONE colon, so `::` ends the name.
    Taking every colon into the name made `self::a` a single token
    that `pNodeTest` read as a CHILD name test called `self::a` — a
    pattern that parsed cleanly and matched nothing. -/
#guard tokenize "self::a".toList == some [.name "self", .op "::", .name "a"]
#guard tokenize "attribute::*".toList == some [.name "attribute", .op "::", .op "*"]
#guard tokenize "p:x".toList == some [.name "p:x"]
#guard tokenize "p:*".toList == some [.name "p", .op ":", .op "*"]

/-! `*` is the multiplication operator after a name, a number, a
    literal, `)`, `]` or `*`, and the wildcard everywhere else
    (§3.7). -/
#guard (parseExpr "count(*)").isSome
#guard (parseExpr "a * b").isSome
#guard (parseExpr "attribute::*").isSome
#guard (parseExpr "xhtml:*").isSome
#guard (parseExpr "@xhtml:*").isSome

/-! A partial parse is a wrong answer wearing the shape of a right
    one, so leftover tokens are a failure. -/
#guard (parseExpr "a b").isNone

/-! ## The XPath 2.0 value comparisons and the double literal

Neither is XPath 1.0. Both are here because the vendored corpus
exercises them and the F* engine this module ports implements them;
they are named apart so that no reader takes them for 1.0. -/

#guard (parseExpr "1 eq 1").isSome
#guard (parseExpr "'a' lt 'b'").isSome
/-! An element may be CALLED `eq`, and `eq` is an operator only where
    an operator can stand — the same rule as `and`, `or`, `div`. -/
#guard (parseExpr "eq").isSome
#guard (parseExpr "a/eq").isSome

/-! Two numbers compare numerically; anything else compares as
    strings by codepoint, so `'20' lt '180.3'` is FALSE. -/
#guard valueCmp "lt" (.num (Num.finite 20 0)) (.num (Num.finite 1803 1))
#guard !(valueCmp "lt" (.str "20") (.str "180.3"))
#guard valueCmp "eq" (.num (Num.finite 1 0)) (.num (Num.finite 10 1))
#guard !(valueCmp "eq" (.str "1") (.str "1.0"))

/-! `1e3` is the XPath 2.0 double LITERAL. XPath 1.0's `number()` has
    no exponent, so `ofString` keeps saying NaN — changing that would
    change what `number(.)` says about a string. -/
#guard Num.ofLexeme "1e3" == Num.finite 1000 0
#guard Num.ofLexeme "1.0e2" == Num.finite 100 0
#guard Num.ofLexeme "1.5E-2" == Num.finite 15 3
#guard Num.ofString "1e3" == Num.nan

/-! ## Numbers -/

/-! §4.2 `string()` on a number: `NaN`, `Infinity` spelled out, an
    integer with no decimal point, a fraction with no trailing
    zeroes. -/
#guard Num.toXString (Num.finite 2 0) == "2"
#guard Num.toXString (Num.finite 150 2) == "1.5"
#guard Num.toXString (Num.finite 0 3) == "0"
#guard Num.toXString (Num.finite (-125) 2) == "-1.25"
#guard Num.toXString Num.nan == "NaN"
#guard Num.toXString Num.posInf == "Infinity"

/-! §4.4 `round()` is half to POSITIVE infinity, so `round(-0.5)` is
    `0` and not `-1`. -/
#guard Num.roundN (Num.finite 5 1) == Num.finite 1 0
#guard Num.roundN (Num.finite (-5) 1) == Num.finite 0 0
#guard Num.roundN (Num.finite (-15) 1) == Num.finite (-1) 0
#guard Num.floorN (Num.finite (-15) 1) == Num.finite (-2) 0
#guard Num.ceilingN (Num.finite 15 1) == Num.finite 2 0
/-! `mod` takes the sign of the DIVIDEND (§3.5). -/
#guard Num.modN (Num.finite 5 0) (Num.finite 3 0) == Num.finite 2 0
#guard Num.modN (Num.finite (-5) 0) (Num.finite 3 0) == Num.finite (-2) 0

/-! ## Evaluating against a document -/

private def docOf (s : String) : Doc :=
  match parseXML s with
  | .ok d    => d.prolog ++ (d.root :: d.epilog)
  | .error _ => []

private def sample : Doc := docOf
  "<doc><a id='x1'>one</a><a>two</a><b><c>three</c></b><!--k--><?pi dat?></doc>"

private def ask (e : String) : String :=
  match evalText { doc := sample, item := .doc sample } e with
  | some v => v.toStr
  | none   => "<unreadable>"

private def askN (e : String) : Nat :=
  match evalText { doc := sample, item := .doc sample } e with
  | some (.nodes ns) => (normalize ns).length
  | _                => 9999

#guard ask "count(/doc/a)" == "2"
#guard ask "/doc/a[1]" == "one"
#guard ask "/doc/a[2]" == "two"
#guard ask "string(/doc/b/c)" == "three"
#guard ask "/doc/a/@id" == "x1"
#guard ask "name(/doc/b/c)" == "c"
#guard ask "count(/doc/comment())" == "1"
#guard ask "count(/doc/processing-instruction())" == "1"
-- `//node()` is `/descendant-or-self::node()/child::node()`: every
-- node except the document node itself, and attributes and namespace
-- nodes, which are not children.
#guard ask "count(//node())" == "10"

/-! A comment contributes NOTHING to an element's string-value, and
    neither does a processing instruction (§5.7). -/
#guard ask "string(/doc)" == "onetwothree"

/-! The `|` union is a SET in document order, so a node reached twice
    is counted once. -/
#guard askN "/doc/a | /doc/a" == 2
#guard askN "//a | //c" == 3

/-! A FILTER expression's predicate sees the whole filtered set, so
    `last()` is that set's size. Encoding it as a `self::node()` step
    gave every node a one-element context, and `(a|b|c)[last()]` then
    kept everything (XSLT position-6901). -/
#guard askN "(//a | //c)[last()]" == 1
#guard ask "(//a | //c)[last()]" == "three"
#guard ask "(//a | //c)[1]" == "one"

/-! §3.3: a NUMERIC predicate is a position test, not a boolean. -/
#guard askN "//a[1]" == 1
#guard askN "//a[@id]" == 1

/-! A reverse axis counts positions along ITS OWN direction, so
    `ancestor::*[1]` is the parent. -/
#guard ask "name(/doc/b/c/ancestor::*[1])" == "b"

/-! An unimplemented function is `none`, never a wrong value. -/
#guard ask "key('k', 'v')" == "<unreadable>"

end L4Factoidal.XPath.Full
