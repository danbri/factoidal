# One function library for RIF-DTB, XPath, XSLT and SPARQL

Date: 2026-09-07. Branch `wt/rif-dtb`.
Tracking: <https://github.com/danbri/factoidal/issues/664>

Owner, 2026-09-07, verbatim: "it looks like we should implement all of the
latest version of RIF-DTB. Do so in a way that assures us of its integrity
using Lean theorems (and F\* equiv is possible) and aim for tight integrations
with other pieces of Factoidal - from XSLT/XPath/XML to SPARQL."

Specifications:

* [RIF-DTB 1.0, 2nd Edition](https://www.w3.org/TR/rif-dtb/) — the built-in
  names, their signatures, their symbol spaces and their error conditions.
* [XQuery 1.0 and XPath 2.0 Functions and Operators](https://www.w3.org/TR/xpath-functions/)
  — the SEMANTICS. RIF-DTB defines almost every built-in by citing an F&O
  function; SPARQL 1.1 §17 cites the same ones; XPath 1.0 §4 predates them and
  defines its own, which agree on some and differ on others.
* [XML Schema Part 2: Datatypes](https://www.w3.org/TR/xmlschema11-2/) — the
  value spaces every one of these functions computes over.

## 1. The problem this record answers

The same F&O function is written more than once in the Lean tree today. Three
front ends carry their own copy of the string and numeric semantics:

| function | RIF | SPARQL | XPath 1.0 |
| --- | --- | --- | --- |
| percent-encoding (`fn:encode-for-uri`) | `RIF/Builtins.lean` `encodeForUri`, `pctEncodeWith`, `utf8Bytes`, `pctByte` | `SPARQL/Expr.lean` `strEncodeUri`, `encodeUriChars`, `percentEncodeChar`, `percentEncodeByte`, `nibbleToHex` | absent |
| substring | `substring2`, `substring3` | `substrSpec` | `substrChars` (double-valued, XPath 1.0 §4.2) |
| substring-before/after | `evalFunc "substring-before"` | `strBefore`/`strAfter` | `substring-before` in the function table |
| upper/lower case | `evalFunc` | `.ucase`/`.lcase` | absent (XPath 1.0 has neither) |
| string length | `evalFunc` | `.strlen` | `string-length` |
| decimal arithmetic | `decParts`, `decRender`, `addDec`, `subDec`, `mulDec`, `divDec` | `Scaled` | `Num` (XPath 1.0 doubles — a different specification, not a duplicate) |
| `daysFromCivil` | private copy | — | — |
| dateTime lexical to timeline | `dateTimeSecsOfLex` | `valueCompare` compares LEXICAL strings | — |

`XSD/Datatypes.lean` already carries the value spaces, the lexical mappings,
the canonical mappings and the orders (`Dec`, `DTValue`, `DurValue`,
`parseDateTimeLex`, `parseDurationLex`, `timeOnTimeline`, `dtCompare`,
`durCompare`, `canonicalDateTime`, `canonicalDuration`). What is missing is a
layer ABOVE it: the F&O functions themselves.

Design: `L4Factoidal/Fn/` holds the F&O semantics once, over the
`XSD.Datatypes` value spaces. RIF, SPARQL and XPath become signature layers —
each keeps its own argument typing, its own coercions and its own error
discipline, and none of them reimplements the function.

The XPath 1.0 number grammar (`XPath/Number.lean`) is NOT consolidated. XPath
1.0 §3.5 defines its own lexical space and its own IEEE 754 double semantics;
that is a different specification, not a duplicate of XSD's, and the
2026-09-07 XSD audit §8 already records it as out of scope.

## 2. The complete RIF-DTB built-in list

Counted from RIF-DTB 1.0 2nd Edition section 4. "Today" is the state of
`L4Factoidal/RIF/Builtins.lean` at commit `709f3c49c`.

| DTB § | title | names | today | after |
| ---: | --- | ---: | ---: | ---: |
| 4.1 | Comparison for literals | 1 | 1 | 1 |
| 4.2 | Guard predicates | 35 | 33 | 35 |
| 4.3 | Negative guard predicates | 35 | 33 | 35 |
| 4.4 | Casting (33 `xs:`, `rdf:XMLLiteral`, `rdf:PlainLiteral`, `pred:iri-string`) | 36 | 30 | 36 |
| 4.5 | Numeric | 12 | 12 | 12 |
| 4.6 | Boolean | 4 | 3 | 4 |
| 4.7 | Strings | 17 | 17 | 17 |
| 4.8 | Dates, times and durations | 72 | 2 | 72 |
| 4.9 | `rdf:XMLLiteral` | 2 | 0 | 2 |
| 4.10 | `rdf:PlainLiteral` | 6 | 5 | 6 |
| 4.11 | RIF lists | 16 | 16 | 16 |
| | **total** | **236** | **152** | **236** |

The header comment in `RIF/Builtins.lean` says "RIF-DTB defines 197
built-ins". That figure was never sourced; 236 is the count of the names
listed in section 4 of the specification, and it is what this record uses.

### 2.1 Names the specification and the corpus disagree on

* DTB 4.5.1 names `func:numeric-mod`. Every fixture in
  `third_party/testing/rif-core-suite` writes `func:numeric-integer-mod`.
  Both names are accepted, and the second is noted as the corpus spelling.
* `Builtins_Time-premise.rifps` writes
  `External( func:add-dayTimeDuration-to-dateTime(...) ) = "2000-11-02T12:27:00"^^xs:dayTime`.
  There is no `xs:dayTime` datatype. It is a typo for `xs:dateTime` in the
  Approved fixture. The F\* tree skips the whole test rather than decide it.
  This work decides the test and records the accommodation at its single site
  (`RIF/Builtins.lean`, `xsdFamily`), naming the fixture line.

## 3. The inventory, function by function

Column (a) is the F&O function RIF-DTB cites; (b) is where the same semantics
already existed in the Lean tree before this work; (c) is the XSD value space
it computes over.

### 4.1 / 4.2 / 4.3 — literal comparison and the guards

| DTB name | (a) F&O | (b) already in tree | (c) value space |
| --- | --- | --- | --- |
| `pred:literal-not-identical` | — (RIF-specific: identity of symbol AND symbol space) | `RIF/Builtins.lean` | every |
| `pred:is-literal-T` (35) | — (RIF-specific: value-space membership) | `RIF/Builtins.lean` `inLexicalSpace`, `xsdFamily`; `XSD.lexicalMap` is the same decision written properly | the named datatype |
| `pred:is-literal-not-T` (35) | — | the negation of the above | the named datatype |

The two guards missing before this work are `pred:is-literal-time` /
`-not-time` reaching a `time` lexical space that `CSVW.parseCanonicalDate`
does not model, and `dateTimeStamp` (a `dateTime` with the timezone
REQUIRED). Both are decided by `XSD.parseDateTimeLex`.

### 4.4 — casting

| DTB name | (a) F&O | (b) already in tree | (c) value space |
| --- | --- | --- | --- |
| `xs:T(...)` (33) | F&O 17 casting | `RIF/Builtins.lean` `evalFunc "cast-…"` over `inLexicalSpace`; `SPARQL/Expr.lean` §17.1 casts; `XSD.lexicalMap` | the named datatype |
| `rdf:XMLLiteral`, `rdf:PlainLiteral` | — (RDF Concepts) | `RIF/Builtins.lean` | — |
| `pred:iri-string` | — | `RIF/Builtins.lean` + `iriStringBind` | `xs:string` / IRI |

### 4.5 — numeric

| DTB name | (a) F&O | (b) already in tree | (c) value space |
| --- | --- | --- | --- |
| `func:numeric-add` | `op:numeric-add` | `addDec`; SPARQL `Scaled` add | `xs:decimal` (exact) |
| `func:numeric-subtract` | `op:numeric-subtract` | `subDec` | `xs:decimal` |
| `func:numeric-multiply` | `op:numeric-multiply` | `mulDec` | `xs:decimal` |
| `func:numeric-divide` | `op:numeric-divide` | `divDec` | `xs:decimal` |
| `func:numeric-integer-divide` | `op:numeric-integer-divide` | `evalFunc` | `xs:integer` |
| `func:numeric-mod` / `-integer-mod` | `op:numeric-mod` | `evalFunc` | `xs:integer` |
| `pred:numeric-*` (6) | `op:numeric-equal`, `-less-than`, `-greater-than` | `cmpNum` over `CSVW.decimalCompare`; SPARQL §17.4.1.7 | `xs:decimal` order |

### 4.6 — boolean

| DTB name | (a) F&O | (b) already in tree | (c) value space |
| --- | --- | --- | --- |
| `func:not` | `fn:not` | XPath `"not"` in the function table; SPARQL `.not` | `xs:boolean` |
| `pred:boolean-equal` | `op:boolean-equal` | `boolValue` + `evalPred` | `xs:boolean` |
| `pred:boolean-less-than` | `op:boolean-less-than` | `evalPred` | `xs:boolean` |
| `pred:boolean-greater-than` | `op:boolean-greater-than` | `evalPred` | `xs:boolean` |

### 4.7 — strings

| DTB name | (a) F&O | (b) already in tree | (c) value space |
| --- | --- | --- | --- |
| `func:compare` | `fn:compare` | `evalFunc "compare"` | `xs:string` codepoint order |
| `func:concat` | `fn:concat` | `evalFunc`; SPARQL `.concat`; XPath `"concat"` | `xs:string` |
| `func:string-join` | `fn:string-join` | `evalFunc` | `xs:string` |
| `func:substring` | `fn:substring` | `substring2`, `substring3`; SPARQL `substrSpec`; XPath `substrChars` — **all three differ** (§4 below) | `xs:string` |
| `func:string-length` | `fn:string-length` | `evalFunc`; SPARQL `.strlen`; XPath `"string-length"` | `xs:string` |
| `func:upper-case` / `lower-case` | `fn:upper-case` / `fn:lower-case` | `evalFunc`; SPARQL `.ucase` / `.lcase` | `xs:string` |
| `func:encode-for-uri` | `fn:encode-for-uri` | `encodeForUri`; SPARQL `strEncodeUri` — **two copies of one function** | `xs:string` |
| `func:iri-to-uri` | `fn:iri-to-uri` | `iriToUri` | `xs:string` |
| `func:escape-html-uri` | `fn:escape-html-uri` | `escapeHtmlUri` | `xs:string` |
| `func:substring-before` / `-after` | `fn:substring-before` / `-after` | `evalFunc`; SPARQL `strBefore`/`strAfter`; XPath function table | `xs:string` |
| `func:replace` | `fn:replace` | `evalFunc` over `Regex.XPath` | `xs:string` |
| `pred:contains`, `starts-with`, `ends-with` | `fn:contains`, `fn:starts-with`, `fn:ends-with` | `evalPred`; SPARQL; XPath (no `ends-with` in XPath 1.0) | `xs:string` |
| `pred:matches` | `fn:matches` | `evalPred` over `Regex.XPath` | `xs:string` |

### 4.8 — dates, times and durations

Before this work: `func:subtract-dateTimes` and `func:days-from-duration`
only, written against a private `dateTimeSecsOfLex` that reads a four-digit
year and treats an absent timezone as UTC. The other 70 names were absent and
`Builtins_Time` was undecided in both trees.

All 72 are cited by RIF-DTB from F&O 10.5 (accessors), 10.6 (duration
arithmetic), 10.7 (date/time arithmetic), 10.8 (date/time subtraction) and
10.4 (comparison). They compute over `XSD.DTValue` (§3.3.7's seven-property
model) and `XSD.DurValue` (§3.3.6's two-property model), and their results are
written back through `XSD.canonicalDateTime` and `XSD.canonicalDuration`.

### 4.9 / 4.10 — XMLLiteral and PlainLiteral

| DTB name | (a) F&O | (b) already in tree | (c) value space |
| --- | --- | --- | --- |
| `pred:XMLLiteral-equal` / `-not-equal` | — | absent | `rdf:XMLLiteral` |
| `func:PlainLiteral-from-string-lang` | — | `evalFunc` | `rdf:PlainLiteral` |
| `func:string-from-PlainLiteral` | — | `plainParts` | `xs:string` |
| `func:lang-from-PlainLiteral` | — | `plainParts` | `xs:string` |
| `func:PlainLiteral-compare` | `fn:compare` on the pair | `evalFunc` | codepoint order |
| `func:PlainLiteral-length` | `fn:string-length` | absent | `xs:integer` |
| `pred:matches-language-range` | — (RFC 4647 §3.3.2 extended filtering) | `matchesLanguageRange`; SPARQL `fnLangMatches` is RFC 4647 §3.3.1 BASIC filtering — **a real difference**, §4 below | — |

### 4.11 — lists

All 16 were already present (`listIndex`, `dedup` and the `evalFunc` cases).
They are RIF-specific: F&O's sequence functions are the model, but a RIF list
is a term, not a sequence, so the correspondence is by analogy only. They move
to `Fn/List.lean` as polymorphic functions over `List α` with `BEq α`, which
is what makes them reusable by a SPARQL or XPath sequence layer later.

## 4. Where the three specifications genuinely disagree

These are not defects to reconcile. Each is a stated difference between two
W3C Recommendations, and each gets a named theorem with the input that
witnesses it.

1. **`substring`, three ways.** F&O `fn:substring` is 1-based and keeps every
   position `p` with `start <= p < start + length`, with `start` and `length`
   rounded as `xs:double`. SPARQL `SUBSTR` (§17.4.3.3) cites `fn:substring`
   but takes `xs:integer` arguments. XPath 1.0 §4.2 `substring()` rounds its
   double arguments with `round()` and has the same window rule. The RIF Core
   Approved `Builtins_String` fixture additionally asserts
   `substring("foobar" 3) = "bar"`, which is 0-BASED — the 2-argument and
   3-argument forms in that fixture disagree with each other on the base, and
   the fixture is the authority for the RIF front end.
2. **Language-range matching.** `pred:matches-language-range` is RFC 4647
   §3.3.2 EXTENDED filtering (wildcards inside the range). SPARQL
   `langMatches` is §3.3.1 BASIC filtering. Witness: tag `de-Latn-DE`, range
   `de-*-DE` — extended matches, basic does not.
3. **Error versus empty.** F&O raises a dynamic error; SPARQL §17.2 makes the
   expression an error that a FILTER reads as `false`; XPath 1.0 has no error
   value at all and returns the empty string or `NaN`; RIF-DTB leaves the
   built-in with no value, which `RIF/Builtins.lean` reports as `unknown` so
   the rule does not fire. The library returns `Option`; each front end maps
   `none` to its own discipline.
4. **`concat` arity.** `fn:concat` and SPARQL `CONCAT` are variadic over the
   whole argument list; XPath 1.0 `concat()` requires at least two arguments.
5. **Timezone defaulting.** F&O 10.7 uses an implicit timezone from the
   evaluation context. RIF-DTB 4.8 has no context, so an absent timezone is
   read as UTC. The library takes the implicit offset as a parameter and the
   RIF front end passes zero.

## 5. Module layout

| module | holds |
| --- | --- |
| `L4Factoidal/Fn/Numeric.lean` | `XSD.Dec` multiplication, division, integer division, modulus, rounding; the decimal-numeral string layer the RIF front end works in |
| `L4Factoidal/Fn/String.lean` | F&O 5.2-5.4: compare, concat, string-join, substring, length, case folding, the three URI escapers, substring-before/after, contains/starts-with/ends-with, RFC 4647 matching |
| `L4Factoidal/Fn/Boolean.lean` | F&O 9.1-9.2 |
| `L4Factoidal/Fn/Duration.lean` | F&O 10.5.1-10.5.6 accessors and 10.6 arithmetic over `XSD.DurValue` |
| `L4Factoidal/Fn/DateTime.lean` | F&O 10.5.7-10.5.20 accessors, 10.4 comparison, 10.7/10.8 arithmetic over `XSD.DTValue` |
| `L4Factoidal/Fn/List.lean` | the RIF-DTB 4.11 list functions, polymorphic |
| `L4Factoidal/Fn/Casting.lean` | F&O 17: a lexical form to a value of a named datatype, over `XSD.lexicalMap` |
| `L4Factoidal/Fn/Theorems.lean` | the agreement theorems and the named difference theorems |

## 6. Status

Written before the code, per the task brief. The "after" column of the table
in §2 is the target; the record's status section is updated with the measured
result when the gates run.
