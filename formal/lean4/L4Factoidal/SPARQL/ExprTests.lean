/-
L4Factoidal.SPARQL.ExprTests — compile-time executable checks for the
expression language.

Every `#guard` here is evaluated during `lake build`, so a wrong answer
is a BUILD FAILURE. The cases are drawn from the intent of the W3C
SPARQL 1.1 expression tests (the `expr-builtin`, `expr-equals`,
`expr-ops`, `functions` and `lang-basedir` families) rather than from
their files: these are unit checks of the semantics. The CONFORMANCE
score comes from `Harness/` (`lake exe l4w3c` over the sparql11
manifests — iron rule #6), not from a green build of this file.
-/
import L4Factoidal.SPARQL.Expr
import L4Factoidal.Tests

namespace L4Factoidal.SPARQL.ExprTests

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ### Fixtures -/

def iriE (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

def litInt (s : String) : WfLiteral := mkTypedLiteral s xsdInteger
def litDec (s : String) : WfLiteral := mkTypedLiteral s xsdDecimal
def litStr (s : String) : WfLiteral := Literal.string s
def litLang (s tag : String) : WfLiteral := Literal.langString s tag

/-- A solution mapping binding two integer-typed literals with
different lexical forms for the same value, and one plain string. -/
def muNums : Binding :=
  [("a", .literal (litInt "1")),
   ("b", .literal (litInt "01")),
   ("d", .literal (litDec "1.0")),
   ("s", .literal (litStr "Alice"))]

/-! ### §17.2.2 — the effective boolean value table -/

#guard ebv (.bool true) == some true
#guard ebv (.bool false) == some false
#guard ebv (.num 0) == some false
#guard ebv (.num 42) == some true
#guard ebv (.dec "0.0") == some false
#guard ebv (.dbl "NaN") == some false
#guard ebv (.term (.literal (litStr ""))) == some false
#guard ebv (.term (.literal (litStr "x"))) == some true
#guard ebv (.term (.literal (mkTypedLiteral "true" xsdBoolean))) == some true
#guard ebv (.term (.literal (mkTypedLiteral "1" xsdBoolean))) == some true
-- A language-tagged literal is "any other argument": a TYPE ERROR, not
-- `true`. (The table's String row is the un-tagged case only.)
#guard ebv (.term (.literal (litLang "chat" "fr"))) == none
-- An IRI is a type error too.
#guard ebv (.term (.iri (iriE "http://example.org/a"))) == none
#guard ebv .error == none

/-! ### §17.4.1.1 BOUND -/

#guard (Expr.bound "a").eval muNums == .bool true
#guard (Expr.bound "zz").eval muNums == .bool false
-- An unbound variable used as a VALUE is a type error, unlike BOUND.
#guard (Expr.var "zz").eval muNums == .error

/-! ### §17.1 numeric promotion — the open-world value comparisons -/

-- 1 = 1.0 : integer against decimal, exactly equal in the scaled model.
#guard (Expr.compare .eq (.numericLit 1) (.decimalLit "1.0")).eval [] == .bool true
-- 1 = 1.0E0 : integer against double.
#guard (Expr.compare .eq (.numericLit 1) (.doubleLit "1.0E0")).eval [] == .bool true
-- Mixed-type ordering across all three numeric types.
#guard (Expr.compare .lt (.numericLit 1) (.decimalLit "1.5")).eval [] == .bool true
#guard (Expr.compare .lt (.decimalLit "1.5") (.doubleLit "2.0E0")).eval [] == .bool true
#guard (Expr.compare .gt (.doubleLit "2.0E0") (.numericLit 1)).eval [] == .bool true
#guard (Expr.compare .le (.numericLit 2) (.decimalLit "2.00")).eval [] == .bool true
-- Negative and fractional lexical forms parse exactly.
#guard (Expr.compare .lt (.decimalLit "-0.5") (.numericLit 0)).eval [] == .bool true

-- "1"^^xsd:integer and "01"^^xsd:integer are the same VALUE: a variable
-- lookup promotes the literal, so `=` compares numbers.
#guard (Expr.compare .eq (.var "a") (.var "b")).eval muNums == .bool true
#guard (Expr.compare .eq (.var "a") (.var "d")).eval muNums == .bool true

-- RDF/SPARQL language tags compare case-insensitively for `=`; this is not
-- the strict spelling-sensitive `sameTerm` relation.
#guard (Expr.compare .eq (.lit (litLang "xyz" "en")) (.lit (litLang "xyz" "EN"))).eval [] == .bool true
#guard (Expr.compare .ne (.lit (litLang "xyz" "en")) (.lit (litLang "xyz" "EN"))).eval [] == .bool false
-- ...but they are different TERMS, so sameTerm on the terms is false.
#guard (Expr.sameTerm (.lit (litInt "1")) (.lit (litInt "01"))).eval [] == .bool false
-- A literal written directly in the expression is NOT promoted (the F*
-- `E_Literal` arm returns the term as-is), so `=` on two typed literals
-- compares them by datatype + lexical form. Recorded here because it is
-- a real fidelity edge, not an accident.
#guard (Expr.compare .eq (.lit (litInt "1")) (.lit (litInt "01"))).eval [] == .bool false

-- Two literals of DIFFERENT, unknown datatypes are a type error under
-- `<` — the open-world rule. Under `=` on the same datatype but
-- different language tags, `=` is definitely false.
#guard (Expr.compare .lt (.lit (litLang "a" "en")) (.lit (litLang "b" "fr"))).eval []
  == .error
#guard (Expr.compare .eq (.lit (litLang "a" "en")) (.lit (litLang "a" "fr"))).eval []
  == .bool false

/-! ### §17.3 — error propagation through the connectives -/

/-- An expression that evaluates to a type error. -/
def errE : Expr := .var "unbound"

-- A determinate `false` dominates an erroring co-operand (tolerant)...
#guard (Expr.and (.boolLit false) errE).eval [] == .bool false
#guard (Expr.and errE (.boolLit false)).eval [] == .bool false
-- ...but nothing dominates here, so the error survives (preserving).
#guard (Expr.and (.boolLit true) errE).eval [] == .error
#guard (Expr.and errE errE).eval [] == .error
#guard (Expr.and (.boolLit true) (.boolLit true)).eval [] == .bool true

#guard (Expr.or (.boolLit true) errE).eval [] == .bool true
#guard (Expr.or errE (.boolLit true)).eval [] == .bool true
#guard (Expr.or (.boolLit false) errE).eval [] == .error
#guard (Expr.or (.boolLit false) (.boolLit false)).eval [] == .bool false

#guard (Expr.not errE).eval [] == .error
#guard (Expr.not (.boolLit false)).eval [] == .bool true

/-! ### §17.4.1 arithmetic -/

#guard (Expr.arith .add (.numericLit 2) (.numericLit 3)).eval [] == .num 5
#guard (Expr.arith .sub (.numericLit 2) (.numericLit 3)).eval [] == .num (-1)
#guard (Expr.arith .mul (.numericLit 2) (.numericLit 3)).eval [] == .num 6
-- integer ÷ integer is an xsd:DECIMAL, never an integer (§17.4.1).
#guard (Expr.arith .div (.numericLit 1) (.numericLit 2)).eval [] == .dec "0.5"
-- Division by zero is a type error, in every numeric type.
#guard (Expr.arith .div (.numericLit 1) (.numericLit 0)).eval [] == .error
#guard (Expr.arith .div (.numericLit 1) (.decimalLit "0.0")).eval [] == .error
-- Decimal addition is exact in the scaled model.
#guard (Expr.arith .add (.decimalLit "0.1") (.decimalLit "0.2")).eval [] == .dec "0.3"
#guard (Expr.arith .mul (.decimalLit "1.5") (.numericLit 2)).eval [] == .dec "3.0"
#guard (Expr.unaryMinus (.numericLit 3)).eval [] == .num (-3)
#guard (Expr.unaryMinus (.decimalLit "1.5")).eval [] == .dec "-1.5"
#guard (Expr.unaryPlus (.numericLit 3)).eval [] == .num 3
-- Arithmetic on a non-number is a type error.
#guard (Expr.arith .add (.numericLit 1) (.lit (litStr "x"))).eval [] == .error

/-! ### §17.4.4 ABS / ROUND / CEIL / FLOOR -/

#guard (Expr.abs (.numericLit (-4))).eval [] == .num 4
#guard (Expr.abs (.decimalLit "-1.5")).eval [] == .dec "1.5"
#guard (Expr.floor (.decimalLit "-1.5")).eval [] == .dec "-2"
#guard (Expr.ceil (.decimalLit "1.5")).eval [] == .dec "2"
#guard (Expr.round (.decimalLit "1.5")).eval [] == .dec "2"
#guard (Expr.round (.decimalLit "-1.5")).eval [] == .dec "-2"
#guard (Expr.round (.decimalLit "1.4")).eval [] == .dec "1"

/-! ### §17.4.2 node tests and accessors -/

#guard (Expr.isIri (.iri (iriE "http://example.org/a"))).eval [] == .bool true
#guard (Expr.isLiteral (.lit (litStr "x"))).eval [] == .bool true
#guard (Expr.isNumeric (.numericLit 1)).eval [] == .bool true
#guard (Expr.isNumeric (.lit (litStr "1"))).eval [] == .bool false
#guard (Expr.isNumeric (.var "a")).eval muNums == .bool true
#guard (Expr.isBlank (.iri (iriE "http://example.org/a"))).eval [] == .bool false

#guard (Expr.str (.iri (iriE "http://example.org/a"))).eval []
  == .term (.literal (litStr "http://example.org/a"))
#guard (Expr.str (.lit (litLang "chat" "fr"))).eval [] == .term (.literal (litStr "chat"))
#guard (Expr.lang (.lit (litLang "chat" "fr"))).eval [] == .term (.literal (litStr "fr"))
#guard (Expr.lang (.lit (litStr "x"))).eval [] == .term (.literal (litStr ""))
#guard (Expr.lang (.iri (iriE "http://example.org/a"))).eval [] == .error
#guard (Expr.datatype (.lit (litStr "x"))).eval [] == .term (.iri xsdString)
#guard (Expr.datatype (.numericLit 1)).eval [] == .term (.iri xsdInteger)

-- IRI() on an absolute IRI string.
#guard (Expr.iriFn (.lit (litStr "http://example.org/a"))).eval []
  == .term (.iri (iriE "http://example.org/a"))
-- A relative reference is an error with no BASE in the environment…
#guard (Expr.iriFn (.lit (litStr "relative"))).eval [] == .error
-- …and resolves (RFC 3986) against `EvalEnv.base` when there is one
-- (W3C `iri01`: `BASE <http://example.org/> … IRI("iri")`).
#guard (Expr.iriFn (.lit (litStr "iri"))).evalIn { base := some "http://example.org/" } []
  == .term (.iri (iriE "http://example.org/iri"))
#guard (Expr.iriFn (.lit (litStr "../x"))).evalIn { base := some "http://example.org/a/b" } []
  == .term (.iri (iriE "http://example.org/x"))
-- An absolute lexical form is unchanged by BASE.
#guard (Expr.iriFn (.lit (litStr "http://other.org/z"))).evalIn { base := some "http://example.org/" } []
  == .term (.iri (iriE "http://other.org/z"))

-- STRDT / STRLANG.
#guard (Expr.strDt (.lit (litStr "1")) (.iri xsdInteger)).eval []
  == .term (.literal (litInt "1"))
#guard (Expr.strLang (.lit (litStr "chat")) (.lit (litStr "fr"))).eval []
  == .term (.literal (litLang "chat" "fr"))
-- STRLANG on an already-tagged literal is an error.
#guard (Expr.strLang (.lit (litLang "chat" "en")) (.lit (litStr "fr"))).eval [] == .error

/-! ### RDF 1.2 direction family (RDF 1.2 Concepts §3.3) -/

def litDir : WfLiteral := mkDirLangLiteral "مرحبا" "ar" .rtl

#guard (Expr.hasLang (.lit (litLang "chat" "fr"))).eval [] == .bool true
#guard (Expr.hasLang (.lit (litStr "x"))).eval [] == .bool false
-- hasLANG never errors on a bound value: an IRI just answers `false`.
#guard (Expr.hasLang (.iri (iriE "http://example.org/a"))).eval [] == .bool false
#guard (Expr.hasLangDir (.lit litDir)).eval [] == .bool true
#guard (Expr.hasLangDir (.lit (litLang "chat" "fr"))).eval [] == .bool false
#guard (Expr.langDir (.lit litDir)).eval [] == .term (.literal (litStr "rtl"))
#guard (Expr.langDir (.lit (litLang "chat" "fr"))).eval [] == .term (.literal (litStr ""))
#guard (Expr.strLangDir (.lit (litStr "x")) (.lit (litStr "he")) (.lit (litStr "rtl"))).eval []
  == .term (.literal (mkDirLangLiteral "x" "he" .rtl))
-- The direction argument is lowercase-only.
#guard (Expr.strLangDir (.lit (litStr "x")) (.lit (litStr "he")) (.lit (litStr "RTL"))).eval []
  == .error

/-! ### §17.4.3 string functions -/

-- STRLEN counts codepoints, and works on a language-tagged literal.
#guard (Expr.strLen (.lit (litStr "foobar"))).eval [] == .num 6
#guard (Expr.strLen (.lit (litLang "chat" "fr"))).eval [] == .num 4
#guard (Expr.strLen (.iri (iriE "http://example.org/a"))).eval [] == .num 20

-- SUBSTR is ONE-BASED (§17.4.3.3): SUBSTR("foobar", 4) = "bar".
#guard (Expr.substr (.lit (litStr "foobar")) (.numericLit 4) none).eval []
  == .term (.literal (litStr "bar"))
#guard (Expr.substr (.lit (litStr "foobar")) (.numericLit 4) (some (.numericLit 1))).eval []
  == .term (.literal (litStr "b"))
#guard (Expr.substr (.lit (litStr "foobar")) (.numericLit 1) (some (.numericLit 3))).eval []
  == .term (.literal (litStr "foo"))
-- SUBSTR preserves a language tag.
#guard (Expr.substr (.lit (litLang "foobar" "en")) (.numericLit 4) none).eval []
  == .term (.literal (litLang "bar" "en"))

#guard (Expr.uCase (.lit (litStr "abc"))).eval [] == .term (.literal (litStr "ABC"))
#guard (Expr.lCase (.lit (litStr "ABC"))).eval [] == .term (.literal (litStr "abc"))
-- UCASE preserves the language tag.
#guard (Expr.uCase (.lit (litLang "chat" "fr"))).eval []
  == .term (.literal (litLang "CHAT" "fr"))

#guard (Expr.strStarts (.lit (litStr "foobar")) (.lit (litStr "foo"))).eval [] == .bool true
#guard (Expr.strEnds (.lit (litStr "foobar")) (.lit (litStr "bar"))).eval [] == .bool true
#guard (Expr.contains (.lit (litStr "foobar")) (.lit (litStr "oob"))).eval [] == .bool true
#guard (Expr.contains (.lit (litStr "foobar")) (.lit (litStr "zzz"))).eval [] == .bool false

#guard (Expr.strBefore (.lit (litStr "abc")) (.lit (litStr "b"))).eval []
  == .term (.literal (litStr "a"))
#guard (Expr.strAfter (.lit (litStr "abc")) (.lit (litStr "b"))).eval []
  == .term (.literal (litStr "c"))
-- No occurrence: both return the empty SIMPLE literal (§17.4.3.13/14).
#guard (Expr.strAfter (.lit (litStr "abc")) (.lit (litStr "z"))).eval []
  == .term (.literal (litStr ""))

-- CONCAT keeps a language tag both arguments agree on...
#guard (Expr.concat [.lit (litLang "foo" "en"), .lit (litLang "bar" "en")]).eval []
  == .term (.literal (litLang "foobar" "en"))
-- ...drops to xsd:string when they disagree...
#guard (Expr.concat [.lit (litLang "foo" "en"), .lit (litLang "bar" "fr")]).eval []
  == .term (.literal (litStr "foobar"))
-- ...and keeps xsd:string for plain arguments.
#guard (Expr.concat [.lit (litStr "foo"), .lit (litStr "bar")]).eval []
  == .term (.literal (litStr "foobar"))
#guard (Expr.concat ([] : List Expr)).eval [] == .term (.literal (litStr ""))

#guard (Expr.encodeForUri (.lit (litStr "a b"))).eval []
  == .term (.literal (litStr "a%20b"))
#guard (Expr.encodeForUri (.lit (litStr "http://x/y"))).eval []
  == .term (.literal (litStr "http%3A%2F%2Fx%2Fy"))

/-! ### §17.4.3.10 langMatches — RFC 4647 basic filtering -/

def langMatches (a b : Expr) : Expr := .functionCall langMatchesIri [a, b]

#guard (langMatches (.lit (litStr "en-US")) (.lit (litStr "en"))).eval [] == .bool true
#guard (langMatches (.lit (litStr "en")) (.lit (litStr "en"))).eval [] == .bool true
#guard (langMatches (.lit (litStr "EN-us")) (.lit (litStr "en"))).eval [] == .bool true
#guard (langMatches (.lit (litStr "fr")) (.lit (litStr "en"))).eval [] == .bool false
-- The "*" range matches any non-empty tag.
#guard (langMatches (.lit (litStr "en-US")) (.lit (litStr "*"))).eval [] == .bool true
#guard (langMatches (.lit (litStr "")) (.lit (litStr "*"))).eval [] == .bool false
-- "en" must not match the range "en-US" (matching is one-directional).
#guard (langMatches (.lit (litStr "en")) (.lit (litStr "en-US"))).eval [] == .bool false

/-! ### §17.4.1 functional forms: IF / COALESCE / IN / NOT IN / sameTerm -/

#guard (Expr.cond (.boolLit true) (.numericLit 1) (.numericLit 2)).eval [] == .num 1
#guard (Expr.cond (.boolLit false) (.numericLit 1) (.numericLit 2)).eval [] == .num 2
-- §17.4.1.2: a type error in the condition PROPAGATES (W3C `if02`,
-- `IF(1/0, false, true)` is unbound) — it is not folded to the else arm.
#guard (Expr.cond errE (.numericLit 1) (.numericLit 2)).eval [] == .error
#guard (Expr.cond (.arith .div (.numericLit 1) (.numericLit 0)) (.boolLit false) (.boolLit true)).eval []
  == .error

#guard (Expr.coalesce [errE, .numericLit 3]).eval [] == .num 3
#guard (Expr.coalesce [errE, errE]).eval [] == .error

#guard (Expr.inList (.numericLit 1) [.numericLit 2, .decimalLit "1.0"]).eval [] == .bool true
#guard (Expr.inList (.numericLit 1) [.numericLit 2, .numericLit 3]).eval [] == .bool false
#guard (Expr.notInList (.numericLit 1) [.numericLit 2, .numericLit 3]).eval [] == .bool true

#guard (Expr.sameTerm (.lit (litStr "x")) (.lit (litStr "x"))).eval [] == .bool true
#guard (Expr.sameTerm (.lit (litStr "x")) (.lit (litLang "x" "en"))).eval [] == .bool false

/-! ### SPARQL 1.2 triple terms: `=` is value equality, sameTerm is not -/

def ttInt : Term :=
  .tripleTerm (.iri (iriE "http://example.org/a")) (iriE "http://example.org/b")
    (.literal (litInt "123"))
def ttDec : Term :=
  .tripleTerm (.iri (iriE "http://example.org/a")) (iriE "http://example.org/b")
    (.literal (litDec "123.0"))

#guard (Expr.compare .eq (.lit (litInt "1")) (.lit (litInt "1"))).eval [] == .bool true
#guard (Expr.isTriple (.lit (litStr "x"))).eval [] == .bool false
-- `<<( :a :b 123 )>> = <<( :a :b 123.0 )>>` holds (value equality)...
#guard valueCompare (.term ttInt) (.term ttDec) .eq == some true
-- ...but the two triple terms are not the SAME term.
#guard (Expr.sameTerm (.lit (litInt "1")) (.lit (litDec "1.0"))).eval [] == .bool false
-- Triple terms have no ordering: `<` on them is a type error.
#guard valueCompare (.term ttInt) (.term ttDec) .lt == none

/-! ### §17.4.3.14 REGEX / §17.4.3.15 REPLACE over the pure engine -/

-- Unanchored search: "a." matches inside "abc".
#guard (Expr.regex (.lit (litStr "abc")) (.lit (litStr "a.")) none).eval [] == .bool true
#guard (Expr.regex (.lit (litStr "abc")) (.lit (litStr "^b")) none).eval [] == .bool false
-- The `i` flag.
#guard (Expr.regex (.lit (litStr "ABC")) (.lit (litStr "b")) (some (.lit (litStr "i")))).eval []
  == .bool true
-- An unknown flag is an error (FORX0001), as is an invalid pattern (FORX0002).
#guard (Expr.regex (.lit (litStr "abc")) (.lit (litStr "b")) (some (.lit (litStr "z")))).eval []
  == .error
#guard (Expr.regex (.lit (litStr "abc")) (.lit (litStr "(")) none).eval [] == .error
-- A non-string text argument is an error.
#guard (Expr.regex (.lit (litInt "1")) (.lit (litStr "1")) none).eval [] == .error
-- REPLACE keeps the text's language tag and replaces every match.
#guard (Expr.replace (.lit (litStr "abcb")) (.lit (litStr "b")) (.lit (litStr "z")) none).eval []
  == erString "azcz"
#guard (Expr.replace (.lit (litLang "abc" "en")) (.lit (litStr "b")) (.lit (litStr "z")) none).eval []
  == (Expr.lit (litLang "azc" "en")).eval []
-- A pattern that matches the empty string is an error (FORX0003).
#guard (Expr.replace (.lit (litStr "abc")) (.lit (litStr "x*")) (.lit (litStr "z")) none).eval []
  == .error

/-! ### Scoped-out operators return the type error, not a wrong answer -/

#guard Expr.now.eval [] == .error
#guard (Expr.aggregate .count false (.var "a")).eval muNums == .error
-- §17.6: an unregistered extension-function IRI is the spec-required error.
#guard (Expr.functionCall (iriE "http://example.org/f") [.numericLit 1]).eval [] == .error

/-! ### The purity doctrine in action: host services as INPUTS

`NOW()` and §17.6 extension functions are not effects here — they are
arguments. Supplying them makes the same expression evaluate. -/

def envWithNow : EvalEnv := { now := some "2026-08-22T00:00:00Z" }

#guard Expr.evalIn envWithNow [] .now
  == .term (.literal (mkTypedLiteral "2026-08-22T00:00:00Z" xsdDateTime))
#guard Expr.evalIn envWithNow [] (.year .now) == .num 2026
#guard Expr.evalIn envWithNow [] (.month .now) == .num 8
#guard Expr.evalIn envWithNow [] (.day .now) == .num 22

/-- A host that registers one §17.6 extension function, `ex:double`. -/
def envWithExt : EvalEnv :=
  { ext := fun iri args =>
      if iri == "http://example.org/double" then
        match args with
        | [.num n] => some (.num (2 * n))
        | _ => some .error
      else none }

#guard Expr.evalIn envWithExt []
    (.functionCall (iriE "http://example.org/double") [.numericLit 21]) == .num 42
#guard Expr.evalIn envWithExt []
    (.functionCall (iriE "http://example.org/other") [.numericLit 21]) == .error

-- §18.6 EXISTS is not an expression-layer operation: the pattern
-- layer substitutes every EXISTS by its boolean before evaluation
-- (`substituteExistentials`, Query.lean — exercised in
-- `QueryTests.lean`). One that reaches this evaluator un-substituted is
-- the F* `E_Exists _ -> ER_Error`.
#guard Expr.evalIn emptyEnv [] (.existsPat (.bgp L4Factoidal.Tests.qNames)) == .error
#guard Expr.evalIn emptyEnv [] (.notExistsPat (.bgp L4Factoidal.Tests.qNames)) == .error

/-! ### §18.5 FILTER — the bridge into the algebra

`Expr.toCond` turns an expression into the row predicate the
algebra's `filter`/`leftJoin` take (under a `fun _ =>` for the active
graph they also receive), collapsing a type error to `false`
because §18.5 drops the row either way. Run against the `Tests.lean`
fixture graph (two people, Alice 30 and Bob 7). -/

section AlgebraBridge
open L4Factoidal.Tests

-- FILTER(?n = "Alice") keeps one of the two rows.
#guard ((GraphPattern.filter
    (fun _ => Expr.toCond (.compare .eq (.var "n") (.lit (litStr "Alice"))))
    (.bgp qNameAge)).eval g).length == 1

-- The same filter written through the expression-level constructor.
#guard ((GraphPattern.filterExpr
    (.compare .eq (.var "n") (.lit (litStr "Alice")))
    (.bgp qNameAge)).eval g).length == 1

-- FILTER(STRLEN(?n) > 3) keeps Alice (5) and drops Bob (3).
#guard (((GraphPattern.filterExpr
    (.compare .gt (.strLen (.var "n")) (.numericLit 3))
    (.bgp qNames)).eval g).map (fun mu => mu.lookup "n"))
  == [some (Term.literal (litStr "Alice"))]

-- The fixture's ages are xsd:STRING literals, so a numeric comparison
-- against them is a TYPE ERROR — and §18.5 drops every row rather than
-- guessing. A filter that removes everything is the correct answer
-- here, not a bug: this is the open-world discipline the promoted-type
-- model exists to keep visible.
#guard ((GraphPattern.filterExpr
    (.compare .gt (.var "a") (.numericLit 18))
    (.bgp qNameAge)).eval g).length == 0

-- FINDING, shared with the F* source: STRDT builds a TERM, and terms
-- are not promoted (only a variable lookup promotes), so
-- `STRDT(STR(?a), xsd:integer) > 18` is still a type error and drops
-- every row. Recorded as behaviour, not asserted as correct — SPARQL
-- 1.1 §17.1's operand mapping would compare these numerically.
#guard ((GraphPattern.filterExpr
    (.compare .gt (.strDt (.str (.var "a")) (.iri xsdInteger)) (.numericLit 18))
    (.bgp qNameAge)).eval g).length == 0

-- With xsd:integer ages IN THE DATA, the variable lookup promotes and
-- the numeric filter works end to end: Alice (30) survives, Bob (7)
-- does not.
def gTyped : Graph :=
  [{ s := alice, p := exName, o := .literal (litStr "Alice") },
   { s := alice, p := exAge,  o := .literal (litInt "30") },
   { s := bob,   p := exName, o := .literal (litStr "Bob") },
   { s := bob,   p := exAge,  o := .literal (litInt "7") }]

#guard (((GraphPattern.filterExpr
    (.compare .gt (.var "a") (.numericLit 18))
    (.bgp qNameAge)).eval gTyped).map (fun mu => mu.lookup "n"))
  == [some (Term.literal (litStr "Alice"))]

-- ...and an OPTIONAL whose filter uses an expression keeps every left
-- row, extending only the ones that pass (SPARQL 1.1 §18.5 LeftJoin).
#guard (((GraphPattern.leftJoinExpr (.bgp qNames)
      (.bgp [{ s := .var "s", p := .iri exAge, o := .var "a" }])
      (.compare .gt (.var "a") (.numericLit 18))).eval gTyped).map
    (fun mu => (mu.lookup "a").isSome))
  == [true, false]

end AlgebraBridge

/-! ### §17.4.4.7–11 hash builtins — the W3C `functions` fixture values -/

#guard (Expr.md5 (.lit (litStr "foo"))).eval [] == erString "acbd18db4cc2f85cedef654fccc4a4d8"
#guard (Expr.md5 (.lit (litStr "abc"))).eval [] == erString "900150983cd24fb0d6963f7d28e17f72"
#guard (Expr.sha1 (.lit (litStr "foo"))).eval [] == erString "0beec7b5ea3f0fdbc95d0dd47f3c5bc275da8a33"
#guard (Expr.sha256 (.lit (litStr "foo"))).eval []
  == erString "2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae"
#guard (Expr.sha384 (.lit (litStr "foo"))).eval []
  == erString "98c11ffdfdd540676b1a137cb1a22b2a70350c9a44171d6b1180c6be5cbb2ee3f79d532c8a1dd9ef2e8e08e752a3babb"
#guard (Expr.sha512 (.lit (litStr "foo"))).eval []
  == erString "f7fbba6e0636f890e56fbbf3283e524c6fa3204ae298382d624741d0dc6638326e282c41be5e4254d8820772c5518a2c5a8c0c7f7eda19594a7eb539453e1ed7"
-- Unicode input hashes its UTF-8 bytes (W3C `md5-02`).
#guard (Expr.md5 (.lit (litLang "食べ物" "ja"))).eval [] == erString "e7ada485d13b1decf628c9211bc3a97b"
-- A hash of a promoted number uses its canonical lexical form; an
-- unbound variable or a blank node is a type error.
#guard (Expr.md5 (.numericLit 1)).eval [] == erString "c4ca4238a0b923820dcc509a6f75849b"
#guard (Expr.sha256 errE).eval [] == .error
#guard (Expr.sha1 (.var "b")).eval [("b", .bnode "x")] == .error

/-! ### §17.4.5 SECONDS / TIMEZONE / TZ (W3C `seconds01`, `timezone01`, `tz01`) -/

def dtLit (s : String) : Expr := .lit (mkTypedLiteral s xsdDateTime)

#guard (Expr.seconds (dtLit "2010-06-21T11:28:01Z")).eval [] == .dec "1"
#guard (Expr.seconds (dtLit "2008-06-20T23:59:00Z")).eval [] == .dec "0"
#guard (Expr.seconds (dtLit "2010-12-21T15:38:02.5-08:00")).eval [] == .dec "2.5"
#guard (Expr.timezone (dtLit "2010-06-21T11:28:01Z")).eval []
  == .term (.literal (mkTypedLiteral "PT0S" xsdDayTimeDuration))
#guard (Expr.timezone (dtLit "2010-12-21T15:38:02-08:00")).eval []
  == .term (.literal (mkTypedLiteral "-PT8H" xsdDayTimeDuration))
#guard (Expr.timezone (dtLit "2010-12-21T15:38:02+05:30")).eval []
  == .term (.literal (mkTypedLiteral "PT5H30M" xsdDayTimeDuration))
-- No timezone: TIMEZONE is a type error, TZ is the empty string.
#guard (Expr.timezone (dtLit "2011-02-01T01:02:03")).eval [] == .error
#guard (Expr.tz (dtLit "2011-02-01T01:02:03")).eval [] == erString ""
#guard (Expr.tz (dtLit "2010-06-21T11:28:01Z")).eval [] == erString "Z"
#guard (Expr.tz (dtLit "2010-12-21T15:38:02-08:00")).eval [] == erString "-08:00"
-- A non-dateTime argument is a type error.
#guard (Expr.tz (.lit (litStr "2010-06-21T11:28:01Z"))).eval [] == .error

/-! ### §17.4.3.1 string-literal arguments (W3C `concat02`, `strbefore01a`, `strbefore02`) -/

-- CONCAT / STRBEFORE / STRAFTER require string literals: a number is
-- a type error.
#guard (Expr.concat [.lit (litStr "abc"), .numericLit 7]).eval [] == .error
#guard (Expr.concat [.numericLit 7]).eval [] == .error
#guard (Expr.strBefore (.numericLit 7) (.lit (litStr "b"))).eval [] == .error
#guard (Expr.strAfter (.numericLit 7) (.lit (litStr "b"))).eval [] == .error
-- A simple first argument with a TAGGED second is not compatible…
#guard (Expr.strBefore (.lit (litStr "abc")) (.lit (litLang "b" "cy"))).eval [] == .error
#guard (Expr.strAfter (.lit (litStr "abc")) (.lit (litLang "" "en"))).eval [] == .error
-- …a tagged first with a simple second is; the tag is preserved…
#guard (Expr.strBefore (.lit (litLang "abc" "en")) (.lit (litStr "b"))).eval []
  == .term (.literal (litLang "a" "en"))
-- …two tags must agree…
#guard (Expr.strAfter (.lit (litLang "abc" "en")) (.lit (litLang "b" "en"))).eval []
  == .term (.literal (litLang "c" "en"))
#guard (Expr.strAfter (.lit (litLang "abc" "en")) (.lit (litLang "b" "cy"))).eval [] == .error
-- …an empty tagged separator returns the tagged empty string / the
-- whole string (W3C `strbefore02` row s2: `?ben = ""@en`).
#guard (Expr.strBefore (.lit (litLang "abc" "en")) (.lit (litLang "" "en"))).eval []
  == .term (.literal (litLang "" "en"))
-- A separator that does not occur gives the SIMPLE empty literal.
#guard (Expr.strBefore (.lit (litLang "abc" "en")) (.lit (litStr "xyz"))).eval []
  == erString ""

/-! ### §17.4.2.3 STRDT takes a simple literal only (W3C `strdt01`, `strdt03`) -/

#guard (Expr.strDt (.lit (litLang "bar" "en")) (.iri xsdString)).eval [] == .error
#guard (Expr.strDt (.lit (litInt "-2")) (.iri xsdString)).eval [] == .error
#guard (Expr.strDt (.numericLit 3) (.iri xsdString)).eval [] == .error
#guard (Expr.strDt (.lit (litStr "abc")) (.iri xsdString)).eval []
  == .term (.literal (litStr "abc"))

/-! ### §17.5 XSD constructor functions (the W3C `cast` suite's rules) -/

def xsdFn (t : String) (e : Expr) (h : isIri (xsdNamespace ++ t) := by rfl) : Expr :=
  .functionCall ⟨xsdNamespace ++ t, h⟩ [e]

-- From a STRING: the lexical form must be in the target's lexical space.
#guard (xsdFn "integer" (.lit (litStr "13"))).eval [] == .num 13
#guard (xsdFn "integer" (.lit (litStr "+13"))).eval [] == .num 13
#guard (xsdFn "integer" (.lit (litStr "1.5"))).eval [] == .error
#guard (xsdFn "integer" (.lit (litStr "1E0"))).eval [] == .error
#guard (xsdFn "integer" (.lit (litStr "string"))).eval [] == .error
#guard (xsdFn "decimal" (.lit (litStr "+33.3300"))).eval [] == .dec "33.33"
#guard (xsdFn "decimal" (.lit (litStr "0"))).eval [] == .dec "0.0"
#guard (xsdFn "decimal" (.lit (litStr "1E0"))).eval [] == .error
#guard (xsdFn "double" (.lit (litStr "-10.2E3"))).eval [] == .dbl "-10.2E3"
#guard (xsdFn "double" (.lit (litStr "true"))).eval [] == .error
#guard (xsdFn "float" (.lit (litStr "1.5"))).eval []
  == .term (.literal (mkTypedLiteral "1.5" xsdFloat))
#guard (xsdFn "boolean" (.lit (litStr "1"))).eval [] == .bool true
#guard (xsdFn "boolean" (.lit (litStr "false"))).eval [] == .bool false
#guard (xsdFn "boolean" (.lit (litStr "0.0"))).eval [] == .error
#guard (xsdFn "boolean" (.lit (litStr "13"))).eval [] == .error
#guard (xsdFn "string" (.iri (iriE "http://example.org/z"))).eval []
  == erString "http://example.org/z"
-- From a NUMBER or BOOLEAN: the VALUE converts.
#guard (xsdFn "integer" (.decimalLit "-7.875")).eval [] == .num (-7)
#guard (xsdFn "integer" (.doubleLit "1E0")).eval [] == .num 1
#guard (xsdFn "integer" (.boolLit true)).eval [] == .num 1
#guard (xsdFn "decimal" (.numericLit 1)).eval [] == .dec "1.0"
#guard (xsdFn "decimal" (.doubleLit "0E1")).eval [] == .dec "0.0"
#guard (xsdFn "decimal" (.doubleLit "1.25")).eval [] == .dec "1.25"
#guard (xsdFn "boolean" (.decimalLit "0.0")).eval [] == .bool false
#guard (xsdFn "boolean" (.doubleLit "1.25")).eval [] == .bool true
#guard (xsdFn "float" (.boolLit false)).eval []
  == .term (.literal (mkTypedLiteral "0E0" xsdFloat))
#guard (xsdFn "float" (.doubleLit "1E0")).eval []
  == .term (.literal (mkTypedLiteral "1.0" xsdFloat))
#guard (xsdFn "string" (.decimalLit "1.0")).eval [] == erString "1"
#guard (xsdFn "string" (.doubleLit "1E0")).eval [] == erString "1"
#guard (xsdFn "string" (.boolLit false)).eval [] == erString "false"
-- Any other XSD datatype builds a typed literal; a blank node or an
-- unbound variable is a type error; the arity is one.
#guard (xsdFn "dateTime" (.lit (litStr "2002-10-10T17:00:00Z"))).eval []
  == .term (.literal (mkTypedLiteral "2002-10-10T17:00:00Z" xsdDateTime))
#guard (xsdFn "integer" errE).eval [] == .error
#guard (Expr.functionCall (iriE "http://www.w3.org/2001/XMLSchema#integer")
          [.numericLit 1, .numericLit 2]).eval [] == .error

/-! ### §17.4.2.9/12/13 fresh values, reproducibly (W3C `bnode01`, `bnode02`, `uuid02`, `rand01`) -/

def fnCall (n : String) (args : List Expr) (h : isIri (fnNamespace ++ n) := by rfl) : Expr :=
  .functionCall ⟨fnNamespace ++ n, h⟩ args

def muRow (row occ : String) : Binding := Binding.withFreshnessCtx row occ []

-- RAND(): a double in [0, 1).
#guard (fnCall "rand" []).eval [] == .dbl "0.5"
-- UUID(): an IRI of the `urn:uuid:` shape, STRUUID() the bare string.
#guard (match (fnCall "uuid" []).eval (muRow "0" "u1") with
        | .term (.iri i) => "urn:uuid:".isPrefixOf i.val && i.val.length == 45
        | _ => false)
#guard (match (fnCall "struuid" []).eval (muRow "0" "u1") with
        | .term (.literal l) => l.val.lexicalForm.length == 36 && l.val.datatype == xsdString
        | _ => false)
-- Two call sites in one row differ; the same call site across rows differs.
#guard (fnCall "uuid" []).eval (muRow "0" "u1") != (fnCall "uuid" []).eval (muRow "0" "u2")
#guard (fnCall "uuid" []).eval (muRow "0" "u1") != (fnCall "uuid" []).eval (muRow "1" "u1")
-- Deterministic: the same context gives the same value.
#guard (fnCall "uuid" []).eval (muRow "0" "u1") == (fnCall "uuid" []).eval (muRow "0" "u1")
-- BNODE(): a blank node, distinct per call site and per row.
#guard (match (fnCall "bnode" []).eval (muRow "0" "b1") with | .term (.bnode _) => true | _ => false)
#guard (fnCall "bnode" []).eval (muRow "0" "b1") != (fnCall "bnode" []).eval (muRow "0" "b2")
-- BNODE(str): the same label for the same string within a row, a
-- different one across rows, and distinct for different strings.
#guard (fnCall "bnode" [.lit (litStr "foo")]).eval (muRow "2" "b1")
  == (fnCall "bnode" [.lit (litStr "foo")]).eval (muRow "2" "b2")
#guard (fnCall "bnode" [.lit (litStr "foo")]).eval (muRow "2" "b1")
  != (fnCall "bnode" [.lit (litStr "foo")]).eval (muRow "3" "b1")
#guard (fnCall "bnode" [.lit (litStr "foo")]).eval (muRow "2" "b1")
  != (fnCall "bnode" [.lit (litStr "BAZ")]).eval (muRow "2" "b1")
#guard (fnCall "bnode" [errE]).eval (muRow "0" "b1") == .error
#guard (fnCall "bnode" [.numericLit 1, .numericLit 2]).eval (muRow "0" "b1") == .error
-- The reserved context keys never reach an expression's variables.
#guard (Expr.bound fxKeyRow).eval [] == .bool false

end L4Factoidal.SPARQL.ExprTests
