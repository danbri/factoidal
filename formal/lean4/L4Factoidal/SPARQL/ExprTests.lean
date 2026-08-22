/-
L4Factoidal.SPARQL.ExprTests — compile-time executable checks for the
expression language.

Every `#guard` here is evaluated during `lake build`, so a wrong answer
is a BUILD FAILURE. The cases are drawn from the intent of the W3C
SPARQL 1.1 expression tests (the `expr-builtin`, `expr-equals`,
`expr-ops`, `functions` and `lang-basedir` families) rather than from
their files: this port has no query parser and no manifest reader yet,
so it cannot claim a CONFORMANCE score — these are unit checks of the
semantics, and the project's iron rule #6 ("run the real W3C test
files") is satisfied only when a Lean runner reads those manifests.
Said plainly so no reader mistakes a green build for a suite result.
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
-- A relative reference is an error here (no BASE resolution is ported).
#guard (Expr.iriFn (.lit (litStr "relative"))).eval [] == .error

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
-- IF's condition uses the FILTER-style collapse: an error acts as false.
#guard (Expr.cond errE (.numericLit 1) (.numericLit 2)).eval [] == .num 2

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

/-! ### Scoped-out operators return the type error, not a wrong answer -/

#guard (Expr.regex (.lit (litStr "abc")) (.lit (litStr "a.")) none).eval [] == .error
#guard (Expr.replace (.lit (litStr "abc")) (.lit (litStr "b")) (.lit (litStr "z")) none).eval []
  == .error
#guard (Expr.md5 (.lit (litStr "abc"))).eval [] == .error
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

/-- A host that supplies §18.6 EXISTS by pattern evaluation. Here the
graph is fixed to the `Tests` fixture, which is exactly the shape the
pattern-evaluation layer will provide. -/
def envWithExists : EvalEnv :=
  { existsHook := some (fun p mu =>
      !(SPARQL.join [mu] (p.eval L4Factoidal.Tests.g)).isEmpty) }

#guard Expr.evalIn envWithExists []
    (.existsPat (.bgp L4Factoidal.Tests.qNames)) == .bool true
#guard Expr.evalIn envWithExists []
    (.notExistsPat (.bgp L4Factoidal.Tests.qNames)) == .bool false
#guard Expr.evalIn emptyEnv [] (.existsPat (.bgp L4Factoidal.Tests.qNames)) == .error

/-! ### §18.5 FILTER — the bridge into the algebra

`Expr.toCond` turns an expression into the `Binding → Bool` the
algebra's `filter`/`leftJoin` take, collapsing a type error to `false`
because §18.5 drops the row either way. Run against the `Tests.lean`
fixture graph (two people, Alice 30 and Bob 7). -/

open L4Factoidal.Tests in
/-- FILTER(?n = "Alice") keeps one of the two rows. -/
#guard ((GraphPattern.filter
    (Expr.toCond (.compare .eq (.var "n") (.lit (litStr "Alice"))))
    (.bgp qNameAge)).eval g).length == 1

open L4Factoidal.Tests in
/-- The same filter written through the expression-level constructor. -/
#guard ((GraphPattern.filterExpr
    (.compare .eq (.var "n") (.lit (litStr "Alice")))
    (.bgp qNameAge)).eval g).length == 1

open L4Factoidal.Tests in
/-- FILTER(STRLEN(?n) > 3) keeps Alice (5) and drops Bob (3). -/
#guard ((GraphPattern.filterExpr
    (.compare .gt (.strLen (.var "n")) (.numericLit 3))
    (.bgp qNames)).eval g).map (fun mu => mu.lookup "n")
  == [some (.literal (litStr "Alice"))]

open L4Factoidal.Tests in
/-- The fixture's ages are xsd:STRING literals, so a numeric comparison
against them is a TYPE ERROR — and §18.5 drops every row rather than
guessing. A filter that removes everything is the correct answer here,
not a bug: this is the open-world discipline the promoted-type model
exists to keep visible. -/
#guard ((GraphPattern.filterExpr
    (.compare .gt (.var "a") (.numericLit 18))
    (.bgp qNameAge)).eval g).length == 0

open L4Factoidal.Tests in
/-- With the age read as an integer (STRDT), the same filter keeps
Alice's row. -/
#guard ((GraphPattern.filterExpr
    (.compare .gt (.strDt (.str (.var "a")) (.iri xsdInteger)) (.numericLit 18))
    (.bgp qNameAge)).eval g).map (fun mu => mu.lookup "n")
  == [some (.literal (litStr "Alice"))]

end L4Factoidal.SPARQL.ExprTests
