# 2026-09-07 — XML Schema datatypes across the two trees: inventory, duplicates, consolidation plan

Tracking: <https://github.com/danbri/factoidal/issues/666>
Specification: [XSD 1.1 Part 2: Datatypes](https://www.w3.org/TR/xmlschema11-2/)
Companion records:
[2026-07-05 XSD.Datatypes module (F\*)](2026-07-05-xsd-datatypes-module.md),
[2026-09-07 XML Schema datatypes (Lean)](2026-09-07-xml-schema-datatypes.md),
[2026-09-07 RDF 1.2 / SPARQL 1.2 semantics](2026-09-07-rdf12-sparql12-semantics.md).

Owner, 2026-09-07, verbatim: "XML Schema datatypes: Please investigate
carefully, we may now have duplicate implementations. I asked for this to be
implemented in F\* at least, and other RDF/SPARQL functionality references XML
schema datatypes. I didn't ask for a Part One until today. ... please see where
we are."

This record is an audit. No engine code changed. Every number below carries the
command that produced it.

## Section list

1. What was measured, and how
2. F\* tree inventory
3. Lean tree inventory
4. Duplicate registers (per tree)
5. Measured differentials inside the Lean tree
6. Measured F\*-versus-Lean agreement
7. Test suites and the missing F\* runner
8. Lean consolidation plan — the ordered commits and their gates
9. F\* gap, datatype by datatype, and the verdict on "implemented in F\* at least"
10. Part 1 Structures
11. Theorems that should exist once, and where they are today

## 1. What was measured, and how

Read-only inspection of both trees, plus four executable checks:

* `lake env lean --run` over scratch programs that import two implementations
  at once and run both over the same inputs (Lean-internal differentials).
* `bin/darwin-arm64/factoidal shacl` over generated fixtures, against the same
  inputs run through the Lean implementation (F\*-versus-Lean).

The input corpus is 4355 distinct lexical forms: the text content of every
leaf element in every W3C XSD suite instance file whose name contains
`duration`, `dateTime`, `decimal`, `double`, `float`, `integer` or `date`
(`third_party/testing/xsd`, 26364 XML files scanned), plus 60 hand-written
edge cases (`+INF`, `.5`, `1.`, `13.1513.561`, `P1.5Y`, integer-tower
boundaries, and so on). The harvest and the scratch programs are not
committed; the corpus is regenerable from the submodule and the counts below
name their inputs.

Counts are stated as "agree N, disagree M (out of T)" per anti-pattern #25.

## 2. F\* tree inventory

### The three XSD modules

| module | lines | datatypes | aspects implemented | aspects absent |
|---|---:|---|---|---|
| `formal/fstar/XSD.Datatypes.fst` | 373 | boolean, integer, decimal, long, int, short, byte, unsignedLong/Int/Short/Byte, nonNegativeInteger, positiveInteger, nonPositiveInteger, negativeInteger, dateTime, float, double (**18**) | lexical space (`is_integer_lexical` 262, `is_decimal_lexical` 265, `is_float_lexical` 294, `literal_ill_formed` 331); lexical-to-value (`literal_to_scaled` 95, `dt_parse_ms` 178); order (`scaled_cmp` 100, `dt_cmp` 197, `numeric_cmp_le/lt` 207/215); one facet family (integer range, `int_lexical_in_range` 323) | canonical mapping, arithmetic, formatting, whiteSpace processing, every other facet |
| `formal/fstar/XSD.Facets.fst` | 1291 | integer family, decimal, string, boolean, float, double, `owl:real`, `owl:rational`, dateTime (timezoned only) | facet-interval reasoning for OWL 2 DL: own lexical parsers (`parse_facet_int` 145-166, `parse_decimal_rational` 484, `dt_parse_tail` 223, `dt_parse_utc_ms` 267), interval/rational/float-ordinal algebra, `value_set` combinators | canonical mapping, arithmetic, formatting |
| `formal/fstar/XSD.IEEE754.fst` | 292 | float, double (+ `rdf:JSON` numbers) | value space and equality (`fval` 89-109, `round_rational` 117), lexical-to-value (`parse_lexical` 149-234), canonicalisation to a format (`canon_double`/`canon_float` 240-271) | canonical LEXICAL mapping (it emits a record, never a string), order, facets |

`XSD.Datatypes.fst` re-exports four parsers from `SPARQL11.Algebra.fst`
(lines 72-75) rather than owning them; `SPARQL11.Algebra.fst` is the
canonical definition site (`parse_int_string` 2134, `pow10` 2222,
`parse_to_scaled` 2252, `parse_double_to_scaled` 2271). The 2026-07-05
record planned to invert that direction in a follow-up slice. It has not
happened.

### Consumers: who calls XSD, who carries its own

| module | lines | calls `XSD.*`? | evidence | own lexical/value logic |
|---|---:|---|---|---|
| `RDF.Entailment.RDFS.DatatypeClash.fst` | 280 | yes | `open XSD.Datatypes` :64 | none |
| `RDF.Entailment.Regime.fst` | 271 | yes | `open XSD.Datatypes` :40, `open XSD.IEEE754` :41 | `rdf_json_value_eq` :68 (not an XSD datatype) |
| `SHACL.Validation.fst` | 3772 | yes | `module XSD = XSD.Datatypes` :66; re-export `let`s :2155-2159 | none |
| `ShEx.Validation.fst` | 1868 | yes | `open XSD.Datatypes` :107 | `total_digit_count`/`fraction_digit_count` :217-233 (facets XSD.Facets excludes), `is_ascii_digit_char` :168 |
| `CSVW.Conversion.fst` | 1531 | yes | qualified `XSD.Datatypes.*` :215-218, :980, :1154 | none |
| `CSVW.Validate.fst` | 634 | yes | `XSD.Datatypes.literal_ill_formed` :239, :242 | none |
| `RIF.Core.Builtins.fst` | 1089 | yes | `module XD = XSD.Datatypes` :58, used :279 :303 :307 :319 :486 :537 | ADDS datatypes F\* otherwise lacks: `date_lexical_ms` :283, `parse_dayTimeDuration_ms` :414, `literal_ill_formed_ext` :271 covering hexBinary/base64Binary/normalizedString/token/language/Name/NCName/NMTOKEN |
| `VC.Credential.fst` | 960 | yes | `module XSD = XSD.Datatypes` :163, `dt_parse_ms`/`dt_cmp` :724, :732 | none |
| `XForms.Bind.fst` | 376 | yes | `open XSD.Datatypes` :30 | none |
| `Tableau.Refute.fst` | 4682 | yes | `open XSD.Facets` :129 | none |
| `SPARQL11.Algebra.fst` | 8793 | **no** | no `open XSD.*` anywhere | the numeric-promotion machinery and every parser (see above); §17 dateTime FILTER comparison falls through the generic literal branch :2444-2456 and compares LEXICAL STRINGS, never `dt_cmp` |
| `OWL.Closure.fsti` | — | **no** | reached from `RDF.Graph.Executable.fst` by `include OWL.Closure` :42 | `normalize_integer_lexical`/`normalize_decimal_lexical`/`datatype_value_eq` :5778-5875 — a second integer/decimal value equality |
| `CSVW.Formats.fst` | 786 | **no** | — | the UAX-35 picture-string engine plus its own base lexical spaces: `is_integer_base`/`is_double_base`/`is_decimal_base`/`is_date_base` :142-157, `parse_number` :205-448, `parse_date_time` :448-594, `parse_bool` :594 |
| `XPath.Eval.fst` | 2286 | **no** | — | own number model `xpath_number` :54, `string_to_xn` :170 (XPath 1.0 grammar, deliberately not XSD's), own `fn:format-number` :350-667 |
| `Parser.XPath.fst` | 889 | **no** | — | `parse_number_lit`, `pow10_nat` :173 |
| `JSONSchema.Validate.fst` | 919 | **no** | — | `parse_num_rational` :124 (JSON grammar, not XSD's) |
| `SHACL.NodeExpr.fst` | — | **no** | — | `parse_dec_lexical` :224-231 |
| `Math.Expr.fst` | — | **no** | — | `parse_decimal` :294, `pow10` :54 (symbolic-math tokens, a different input domain) |
| `Regex.XSDPattern.fst` | 437 | no | — | the Appendix G/F pattern grammar — complementary, not a duplicate |
| `RDF.Term.fsti` | 573 | no | — | `literal_eq`/`literal_value_eq` :448-556, structural and lexical only |

## 3. Lean tree inventory

### The seven XSD modules

| module | lines | datatypes | aspects |
|---|---:|---|---|
| `L4Factoidal/XSD/Datatypes.lean` | 1261 | all **49** XSD 1.1 built-ins (`Builtin` :70-83, `allBuiltins` :114) | derivation hierarchy :142-200; whiteSpace :210-239; decimal value space and arithmetic (`Dec` :241-299); date/time and duration value spaces :306-329; `Val` and equality :331-369; lexical-to-value for every builtin (`lexicalMapFuel`/`lexicalMap` :1053-1109, `lexicalMapWs` :1114); order (`valCompare` :1003, `dtCompare` :948, `durCompare` :994, `fvalCmp` :903); canonical mapping for every builtin with one (`canonicalMap` :1239-1259) |
| `XSD/SimpleType.lean` | 286 | — | §4.1/§4.3 varieties and facets, `valueOf`, `validate` :202-286. Composition only, no lexical logic |
| `XSD/SchemaReader.lean` | 297 | — | the `<simpleType>` subset of a schema document, plus the suite classification |
| `XSD/Facets.lean` | 835 | integer family, decimal, string, boolean, float, double, `owl:real`, `owl:rational`, dateTime | facet-interval reasoning (the Lean twin of `XSD.Facets.fst`). Calls the shared `daysFromCivil` (`daysFromCivilInt` :283) but keeps its own dateTime tail parser :285-353 and its own rational decimal parser :367-522 |
| `XSD/IEEE754.lean` | 301 | float, double, `rdf:JSON` numbers | value space, rounding, lexical-to-value, canonicalisation, equality, bit encoding |
| `XSD/DatatypesTheorems.lean` | 185 | — | 15 theorems (listed in §11) |
| `XSD/DatatypesTests.lean`, `FacetsTests.lean`, `IEEE754Tests.lean` | 271 / 217 / 173 | — | `#guard` batteries |

### Consumers

| module | calls `XSD.*`? | evidence | own lexical/value logic |
|---|---|---|---|
| `RDF/Datatypes.lean` | yes | `import` :60-61; `NumVal := XSD.Dec` :96; `XSD.parseIntegerLex` :101; `XSD.parseDecimalLex` :106; `XSD.inIntBounds` :109; `XSD.lexicalMap .double` :163 | only the RDF-specific part (§7 applies no whiteSpace), plus `xmlLiteralWellFormed` and `rdfJsonLexicalOk` for the two non-XSD datatypes |
| `RDF/Entailment.lean` | yes | `import XSD.IEEE754` :88; `XSD.doubleValueEq` :527, :585; `XSD.floatValueEq` :587 | `dtValueLeq` :583 is a dispatcher, not a second mapping |
| `SHACL/Validation.lean` | partly | `import` :51; `literalIllFormed` :227-230 is one call into `builtinOfIri?` + `lexicalMap` | STILL carries `isSignedDigitsChars`/`isDecimalLexicalChars`/`isIntegerLexical`/`isDecimalLexical`/`splitAtE`/`isFloatLexical`/`stripLeadingPlus`/`intLexicalInRange` :104-158, `daysFromCivil` :159, `dtParseTail`/`dtParseMs`/`dtCmp` :173-225, `literalToScaled` :237 |
| `XSD/Facets.lean` | partly | `daysFromCivilInt` :283 | own `dtParseTail`/`dtParseUtcMs` :295-342, own `Rat`/`parseDecimalRat`/`parseRationalLex` :367-522 |
| `CSVW/Formats.lean` | **no** | — | `decimalCompare` :299, `facetCompare` :336, `facetLength` :360, `isDurationLexical` :421, `isIntegerLexical` :440, `isDecimalLexical` :444, `isDoubleLexical` :452, `integerBounds` :469, `normalizeDoubleLexical` :500, `isXsdNumericLexical` :505, `canonicalDate`/`parseCanonicalDate` :731-812 |
| `RIF/Builtins.lean` | **no** | — | `inLexicalSpace` :87, `xsdFamily` :122, `daysFromCivil` :157, `tzOffsetSecs` :170, `dateTimeSecsOfLex` :200, `dayTimeDurationSecs` :234-277, and a complete decimal arithmetic system `decParts`/`addDec`/`subDec`/`mulDec`/`divDec` :352-432 (`divDec` is functionality `XSD.Dec` does not have) |
| `SPARQL/Expr.lean` | **no** | — | `Scaled` :739, `parseIntString` :768, `parseToScaled` :787, `parseDoubleToScaled` :806, `Scaled.cmp/add/sub/mul/div?` :890-936, §17.1 casts `castInteger`…`castString` :1508-1607, a third double lexical space :1461-1463, `stripLeadingPlus` :1435, `scaledToDecimalLexical` :1490. `valueCompare` :1021 orders same-datatype literals — dateTime included — by LEXICAL string |
| `XForms/Bind.lean` | **no** | — | `isIntegerLexical` :71, `isDecimalLexical` :75, `isFloatLexical` :86, `typeWellformed` :95 |
| `ShEx/XsdLexical.lean` | no (via CSVW) | `import CSVW.Formats` :32 | `isBooleanLexical` :60, `inXsdLexicalSpace` :65-100, digit-facet helpers :116-156; delegates numerics to `CSVW.Formats` |
| `XPath/Number.lean`, `XPath/Eval.lean` | **no** | — | the XPath 1.0 number model (`ofString`, `toXString`, arithmetic) |
| `LWS/Operations.lean` | no | — | `civilFromDays` :68 — the inverse calendar function, for RFC 9110 HTTP-date; adjacent, not an XSD duplicate |
| `Math/*`, `RML/Value.lean`, `RDF/Core.lean`, `CSVW/{Validate,Metadata,Emit}.lean`, `SPARQL/{ExprRefinement,Results}.lean`, `RDF/EntailmentRdfsDatatypeClash.lean` | no XSD datatype logic | — | none |

## 4. Duplicate registers

A duplicate here means the lexical or the value logic of the same datatype
written twice in the same tree.

### F\* tree — 8 substantive duplicates

| # | duplicated mapping | locations |
|---:|---|---|
| 1 | `days_from_civil` | `XSD.Datatypes.fst:123`, `XSD.Facets.fst:209` |
| 2 | dateTime fraction/timezone tail | `XSD.Datatypes.fst:135`, `XSD.Facets.fst:223` |
| 3 | dateTime to milliseconds | `XSD.Datatypes.fst:178` (`dt_parse_ms`), `XSD.Facets.fst:267` (`dt_parse_utc_ms`, requires a timezone and rejects negative years — the two differ at the edges) |
| 4 | integer lexical parser | `SPARQL11.Algebra.fst:2134`, `XSD.Facets.fst:145-166` |
| 5 | decimal / E-notation lexical parser | `SPARQL11.Algebra.fst:2252`, `XSD.Facets.fst:484`, `XSD.IEEE754.fst:199` — three exact representations |
| 6 | integer/decimal VALUE equality | `OWL.Closure.fsti:5856` (`datatype_value_eq`, lexical-normalisation) versus `XSD.Datatypes.fst:95-109` (scaled). **Divergent**: `normalize_decimal_lexical` leaves `"1.0"` as `"1.0"` and `"1"` as `"1"`, so that copy answers `"1"^^xsd:decimal ≠ "1.0"^^xsd:decimal`, which the scaled comparison equates. `RDF.Graph.Executable.fst` reaches this copy through `include OWL.Closure` :42 |
| 7 | scaled-decimal lexical parser | `SHACL.NodeExpr.fst:224` — a fourth, in a file that already imports `SPARQL11.Algebra` |
| 8 | min/maxInclusive/Exclusive facet IRI constants | `Tableau.fst:232-254`, `XSD.Facets.fst:379-391` |

Plus two systemic trivial-helper patterns: `is_ascii_digit` in at least 12
places and `pow10` in at least 9. They are two lines each and are counted
separately from the eight.

### Lean tree — 10 substantive duplicates

| # | duplicated mapping | locations |
|---:|---|---|
| 1 | `daysFromCivil` | `XSD/Datatypes.lean:922` (reference), `SHACL/Validation.lean:159`, `RIF/Builtins.lean:157` — 2 copies |
| 2 | dateTime tail parser + UTC milliseconds | `XSD/Datatypes.lean:766`+`934` (reference), `SHACL/Validation.lean:173`+`205`, `XSD/Facets.lean:295`+`330` — 2 copies, and the two copies DIVERGE from each other on an untimezoned value (`SHACL.dtParseMs` reads it as UTC; `XSD.Facets.dtParseUtcMs` returns `none`) |
| 3 | integer/decimal/float lexical space | `XSD/Datatypes.lean:391`+`403` (reference), `SHACL/Validation.lean:111-140`, `CSVW/Formats.lean:440-452`, `XForms/Bind.lean:71-94`, `SPARQL/Expr.lean:1461` — 4 copies |
| 4 | decimal value space and arithmetic | `XSD/Datatypes.lean:241-299` (`Dec`), `SPARQL/Expr.lean:739`+`890-936` (`Scaled`), `RIF/Builtins.lean:352-432` (`decParts`…`divDec`) — 2 copies |
| 5 | integer/decimal/double lexical-to-value for SPARQL | `SPARQL/Expr.lean:787`, `:806` versus `XSD/Datatypes.lean:391`, `:403`, `:1053` |
| 6 | integer bounds table | `XSD/Datatypes.lean:427` (`intBounds`), `CSVW/Formats.lean:469` (`integerBounds`), `NatBounds.lean` constants |
| 7 | `xsd:duration` lexical space | `XSD/Datatypes.lean:631` versus `CSVW/Formats.lean:421` |
| 8 | date lexical space and canonical form | `XSD/Datatypes.lean:766`+`1167` versus `CSVW/Formats.lean:657`+`731`+`804` |
| 9 | rational decimal parser | `XSD/Facets.lean:367-522` versus `XSD/Datatypes.lean:403` — inside the same namespace |
| 10 | double canonical/normalised lexical form | `XSD/Datatypes.lean:1218` (`canonicalFval`), `XSD/IEEE754.lean:240-256`, `CSVW/Formats.lean:500` (`normalizeDoubleLexical`, a documented deviation from the XSD canonical mapping to match the CSVW corpus), `SPARQL/Expr.lean:1490` |

Dead code found by this audit: after today's switch of `literalIllFormed`,
`SHACL/Validation.lean:104-158` (`isSignedDigitsChars`, `isDecimalLexicalChars`,
`isIntegerLexical`, `isDecimalLexical`, `splitAtE`, `isFloatLexical`,
`stripLeadingPlus`, `intLexicalInRange`) has no caller anywhere in the tree —
verified by `grep -rn` for each name across `formal/lean4`; the only hits are
the definitions themselves and unrelated same-named definitions in
`SPARQL/Expr.lean` and `XForms/Bind.lean`. `isAsciiDigit` :101 IS still used,
by `dtParseTail` :178.

## 5. Measured differentials inside the Lean tree

All four ran through `lake env lean --run` against the built `.olean`s of this
worktree.

**5.1 `daysFromCivil`, three copies, over 5880 date triples** (years -4000 to
123456 in 137-year steps plus edge years, twelve months, seven days):
agree 5880, XSD-versus-RIF disagree 0, XSD-versus-SHACL disagree 0 (out of
5880). The three are behaviourally identical over that range; consolidating
them is a pure deletion.

**5.2 `CSVW/Formats.lean` lexical spaces versus `XSD.lexicalMap`, over the
4355-form corpus:**

| datatype | agree | disagree | of |
|---|---:|---:|---:|
| duration | 4353 | **2** | 4355 |
| decimal, integer, double, float, byte, int, long, unsignedLong, positiveInteger | 4355 | 0 | 4355 each |

The two duration disagreements are `"P1.5Y"` and `"P200.5Y"`: XSD §3.3.6
allows a fraction only on the seconds component, and `CSVW.isDurationLexical`
accepts it on any component. CSVW is wrong here; the numeric spaces agree
exactly, so switching them is a substitution and switching duration is a
repair.

**5.3 `SPARQL/Expr.lean` numerics versus `XSD.Datatypes`, over the same
corpus:**

* `XSD.parseDecimalLex` versus `SPARQL.parseToScaled`: agree 3126, acceptance
  disagree **720**, value disagree **0** (out of 3846). Where both accept, the
  `(mantissa, scale)` pairs are identical after normalisation — so the value
  space is the same and only the accepted lexical space differs.
  `parseToScaled` accepts forms outside `xsd:decimal` (`"13.1513.561"`,
  `"123.456E4"`) and rejects forms inside it (`"+1"`, `".5"`). Some of the
  `+` cases are compensated at the call sites by
  `SPARQL/Expr.lean:1435 stripLeadingPlus`, which is exactly the kind of
  compensation that a single implementation removes.
* `XSD.lexicalMap .double` versus `SPARQL.parseDoubleToScaled`: agree 3633,
  disagree **213** (out of 3846). `Scaled` has no representation for `INF`,
  `-INF` or `NaN` at all, which the file's own comment at :734 states.
* `XForms.isFloatLexical` versus `XSD.lexicalMap .double`: agree 3845,
  disagree **1** (out of 3846) — it rejects `"+INF"`, which XSD 1.1 accepts.

**5.4 `SHACL.dtCmp` versus `XSD.dtCompare`, over 180 dateTime pairs** drawn
from the suite's dateTime instances: agree 147, disagree **33** (out of 180).
Two classes, both real:

* `SHACL.dtCmp` answers `none` where `XSD.dtCompare` decides. It requires the
  two operands to agree on whether a timezone is PRESENT; XSD §3.2.7.4 lets an
  untimezoned value compare against a timezoned one whenever the ±14-hour
  window makes the comparison determinate. Example:
  `"1985-04-12T10:30:00"` versus `"2002-01-01T12:01:01Z"`.
* `SHACL.dtCmp` decides where `XSD.dtCompare` answers `none`, because
  `dtParseMs` is a fixed-width field reader with no field-range check and
  accepts `"1821-05-26T40:44:50"` (hour 40).

Neither shows up in `l4shacl` (98 pass, 0 fail out of 98), so the suite is not
a gate on this behaviour.

## 6. Measured F\*-versus-Lean agreement

Same inputs, same way: 2610 (datatype, lexical) pairs restricted to the 18
datatypes `literal_ill_formed` recognises, written as a Turtle graph plus a
SHACL shapes graph with one `sh:datatype` property shape per node, so a
violation means exactly "ill-formed for this datatype".

* F\*: `bin/darwin-arm64/factoidal shacl --data … --shapes …` over 27 chunks of
  100 (one 2610-shape input segfaults; chunking is a harness workaround, and
  the crash is itself worth an issue).
* Lean: `XSD.builtinOfIri?` + `XSD.lexicalMap`, the same function
  `SHACL/Validation.lean:227` calls.

**Agreement: 2600 agree, 10 disagree (out of 2610).** Every disagreement is
the F\* side being wrong against XSD 1.1 Part 2:

| class | count | example | cause |
|---|---:|---|---|
| F\* accepts an out-of-range dateTime field | 8 | `"1821-05-26T40:44:50"` | `dt_parse_ms` (`XSD.Datatypes.fst:178`) reads fixed-width fields and never checks `hour ≤ 24`, `minute ≤ 59`, month/day validity |
| F\* rejects `"+INF"` for float and double | 2 | `"+INF"^^xsd:double` | `is_float_lexical` (`XSD.Datatypes.fst:294`) tests only `NaN`, `INF`, `-INF`; XSD 1.1 §3.3.5 admits `+INF` |

The `+INF` reading is not settled inside the Lean tree either:
`ShEx/XsdLexical.lean:76-79` documents a deliberate XSD 1.0 reading that
rejects it, while `XSD/Datatypes.lean` implements the 1.1 reading. One
implementation forces that choice to be made once.

## 7. Test suites and the missing F\* runner

* Corpus: `third_party/testing/xsd`, a shallow submodule of
  `github.com/w3c/xsdtests`, present, 214 MB, 26364 `.xml`, 78 `.testSet`
  manifests under `suite.xml`. Registered in `tools/ensure-test-env.sh:77`.
* Lean runner: `formal/lean4/Harness/XsdDatatypesRun.lean`, target
  `formal/lean4/lakefile.lean:328`, command `lake -d formal/lean4 exe
  l4xsd-datatypes`. Score 18951 pass, 5 fail (out of 18956 scored instance
  tests).
* F\* runner: **none**. `ls bin/` has 33 consumer runners and no `xsd-runner`;
  `.github/test-suites/*.yaml` has 83 suites and none named `xsd`;
  `tools/dispatch_test_suites.sh` contains no `xsd` string;
  `docs/test-results/latest.json` has no XSD entry. The F\* modules are
  exercised only indirectly, through `rdf-mt`, `sparql11-entailment`,
  `owl-type-*`, `rif`, `csvw-*`, `shacl12-core`, `shex` and `jsonschema`.

What an F\* runner needs, by analogy to `bin/xml-runner/xml_runner.ml` (1099
lines), which already walks a root manifest with per-contributor
sub-manifests:

1. Manifest walk with the project's own extracted XML parser
   (`Parser.XML.fst`, as `xml_runner.ml` does) — `suite.xml` to
   `ts:testSetRef` to each `*Meta/*.testSet` to each `testGroup`.
2. A schema-document classifier equivalent to
   `L4Factoidal/XSD/SchemaReader.lean`, so structures tests are counted and
   not scored. This is the largest new piece, and it is F\* work, not glue.
3. Calls into `XSD.Datatypes.literal_ill_formed` and the `XSD.Facets`
   predicates for the answer.
4. Build wiring: both modules are already in `formal/fstar/build-ocaml.sh`
   (:520, :550), so only a `bin/xsd-runner/` stanza, `NATIVE_TARGETS` and
   `NATIVE_SOURCES` entries, and a `.github/test-suites/xsd.yaml` are new.

## 8. Lean consolidation plan

Target: `L4Factoidal.XSD` (`Datatypes.lean` + `IEEE754.lean` +
`SimpleType.lean`) is the ONLY place a lexical space, a lexical-to-value
mapping, a canonical mapping, a value order or a value equality for an XSD
datatype is written. Every other module is a call site. Format-specific
grammars that are NOT XSD's — the CSVW UAX-35 picture strings, the XPath 1.0
number grammar, the JSON number grammar, the Appendix G pattern regex — stay
where they are; they are different specifications, not duplicates.

Ordered commits, each with the gate it must hold:

| # | commit | gate |
|---:|---|---|
| 1 | Delete the dead lexical block `SHACL/Validation.lean:104-158` except `isAsciiDigit`. No behaviour change; it is unreachable (§4). | `l4shacl` 98 pass, 0 fail (out of 98); `lake build` clean |
| 2 | `SHACL/Validation.lean`: `daysFromCivil`, `dtParseTail`, `dtParseMs`, `dtCmp` become calls into `XSD.parseDateTimeLex` + `XSD.dtCompare`. This CHANGES behaviour on the 33 pairs of §5.4 — in the direction XSD specifies — so it needs new `#guard`s for the mixed-timezone and out-of-range-field cases. | `l4shacl` 98 pass, 0 fail (out of 98); new `#guard`s in `SHACL/ShaclTests.lean` |
| 3 | `RIF/Builtins.lean`: `daysFromCivil` becomes a call (§5.1 shows 0 disagreements over 5880 inputs, so this is a deletion); `dateTimeSecsOfLex` becomes `XSD.parseDateTimeLex` + `XSD.timeOnTimeline`, keeping the RIF-DTB 4.8 implicit-UTC rule at the call site, not inside the mapping. `decParts`…`divDec` STAY until `XSD.Dec` gains division. | `l4rif` 42 pass, 0 fail (out of 42 decided) |
| 4 | `XSD/Facets.lean`: `dtParseTail`/`dtParseUtcMs` become `XSD.parseDateTimeLex` + `XSD.timeOnTimeline`; `parseDecimalRat`/`parseRationalLex` keep the `Rat` representation (interval reasoning needs exact rationals) but take their digits from `XSD.parseDecimalLex`. Removes the undocumented untimezoned divergence named in §4. | `l4owl-probe`; OWL 2 RL and DL suites unchanged |
| 5 | `XForms/Bind.lean`: `typeWellformed` becomes `XSD.builtinOfIri?` + `XSD.lexicalMap`. Fixes the `"+INF"` case of §5.3. | `l4xforms` (and `l4xmlconf` 1861 pass, 0 fail out of 1861 in profile) |
| 6 | `CSVW/Formats.lean`: decompose. The picture-string engine stays; after it has produced a normalised lexical form, the base-type decision routes to `XSD.lexicalMap` and `integerBounds` to `XSD.intBounds`. Repairs the two duration cases of §5.2. `normalizeDoubleLexical` STAYS with its existing comment — it is a stated corpus-driven deviation from the XSD canonical mapping, not a duplicate of it. | `l4csvw-validate` 281 pass, 1 fail (out of 282); `l4csvw-json`; `l4csvw-rdf`; `ShEx/XsdLexical.lean`'s consumers via `l4shex` |
| 7 | `SPARQL/Expr.lean`: replace `Scaled` with `XSD.Dec` and route `parseToScaled`/`parseDoubleToScaled` through `XSD.lexicalMap`, keeping `NumKind` promotion and the §17.1 casts at this layer. §5.3 shows 0 value disagreements on the intersection and 720 acceptance disagreements, so this commit MOVES semantics and must be gated hardest. `Scaled.div?` needs a `Dec` division first. | SPARQL 1.1: 631 pass, 0 fail (out of 631); SPARQL 1.2; `l4rdf-semantics` 40 pass, 7 fail (out of 47); `l4shacl` (it consumes `literalToScaled`) |
| 8 | `SPARQL/Expr.lean:1021 valueCompare`: order same-datatype dateTime literals by `XSD.dtCompare`, not by lexical string. Separate commit from 7 — it is a §17.4 ordering repair, not a representation change. | the SPARQL suites above, plus new `#guard`s for equal-instant different-offset pairs |

Not consolidated, by decision: `XPath/Number.lean` (XPath 1.0 has its own
number grammar and its own `string()` output rules), `Regex/XSDPattern.lean`
(the pattern facet's regex flavour), `LWS/Operations.lean:68 civilFromDays`
(the inverse direction, for HTTP-date), `RIF`'s decimal division until `Dec`
has one.

## 9. F\* gap, datatype by datatype

`✅` implemented in the F\* tree, `➖` partial, `❌` absent. "elsewhere" means an
F\* module other than `XSD.Datatypes.fst` carries it.

| datatype | Lean | F\* | note |
|---|---|---|---|
| boolean | ✅ | ➖ | lexical space only; no value, no canonical |
| decimal, integer, long, int, short, byte, unsignedLong/Int/Short/Byte, nonNegativeInteger, positiveInteger, nonPositiveInteger, negativeInteger | ✅ | ➖ | lexical space + scaled value + order; no canonical mapping, no whiteSpace, no facets beyond range |
| float, double | ✅ | ➖ | `XSD.IEEE754.fst` has the value space and equality; `is_float_lexical` rejects `+INF` (§6); no order exposed, no canonical lexical form |
| dateTime | ✅ | ➖ | `dt_parse_ms` accepts out-of-range fields (§6); comparison requires equal timezone presence |
| date | ✅ | ➖ elsewhere | `RIF.Core.Builtins.fst:283 date_lexical_ms` only |
| dayTimeDuration | ✅ | ➖ elsewhere | `RIF.Core.Builtins.fst:414` only |
| hexBinary, base64Binary, normalizedString, token, language, Name, NCName, NMTOKEN | ✅ | ➖ elsewhere | `RIF.Core.Builtins.fst:271 literal_ill_formed_ext` only |
| string, anySimpleType, anyAtomicType | ✅ | ➖ | trivially admitted (`literal_ill_formed` returns "well-formed" for every unrecognised datatype — a default, not an implementation) |
| time, duration, yearMonthDuration, gYearMonth, gYear, gMonthDay, gDay, gMonth, dateTimeStamp, anyURI, QName, NOTATION, NMTOKENS, ID, IDREF, IDREFS, ENTITY, ENTITIES, precisionDecimal | ✅ | ❌ | not implemented anywhere in the F\* tree |

Aspects: the F\* tree implements NO canonical mapping for any datatype, NO
whiteSpace processing (§4.3.6), and only the integer-range facet plus the
OWL-oriented interval reasoning of `XSD.Facets.fst`. The Lean tree implements
all of them.

**Verdict on "I asked for this to be implemented in F\* at least".** Not met.
What is true: the F\* tree HAS an XSD datatypes module, it is the one every F\*
consumer except `SPARQL11.Algebra`, `CSVW.Formats`, `XPath.Eval` and
`OWL.Closure` calls, and where it and Lean overlap they agree on 2600 of 2610
inputs (§6). What is not true: it is not an implementation of XSD 1.1 Part 2.
It covers 18 of 49 built-in datatypes for lexical validity (30 with the RIF
extensions, in the wrong module), implements no canonical mapping, has never
been run against the W3C XSD test suite, and carries three defects this audit
measured (out-of-range dateTime fields, `+INF`, and the divergent
`OWL.Closure.fsti` decimal equality that makes `"1"` and `"1.0"` unequal).

Closing the gap in F\* means: (a) the runner of §7, to get a number at all;
(b) the missing 19 datatypes and the canonical mappings; (c) whiteSpace;
(d) the three repairs. That is a large piece of work, and the standing
direction since 2026-08-29 is that the Lean tree is the full-scope target. The
decision to put to the owner is which of these two the F\* line means:

* **Parity** — build the F\* runner and close the datatype gap, so both trees
  implement Part 2; or
* **A stated floor** — keep `XSD.Datatypes.fst` as the F\* engine's literal
  validity layer, fix the three measured defects, add the runner so its
  coverage is MEASURED rather than assumed, and record that full Part 2 lives
  in Lean.

This audit does not choose. 🧭

## 10. Part 1 Structures

Part 1 Structures adds schema components, the schema-document parser, PSVI,
identity constraints (`key`/`keyref`/`unique`), conditional type assignment,
assertions (§4.3.12, which needs XPath 2.0 over the value), and the §3.16
schema component constraints that decide the 15378 schema-validity tests the
Lean runner counts and does not score.

It was NOT requested before 2026-09-07. The owner's words that day were "we
should bite the bullet and do all of XML Schema, to unlock later
xslt/xpath/xquery avenues", and the same day's record scoped Part 1 out of
that run. It stays a separate decision on
<https://github.com/danbri/factoidal/issues/666> and is not part of the
consolidation plan in §8.

## 11. The theorems that should exist once

Stated once over both trees where the owner's 2026-08-26 "prove over an
abstraction" steer applies; Lean first, F\* optional.

| property | Lean today | F\* today |
|---|---|---|
| whiteSpace applies before the lexical mapping, never inside it | ✅ `lexicalMapWs_factors` | ❌ (no whiteSpace at all) |
| `xsd:string`'s lexical mapping is total | ✅ `string_lexical_total` | ❌ |
| the §3.4 derivation hierarchy is reflexive and correct on the integer/decimal chain | ✅ `derivedFrom_refl`, `byte_derived_integer`, `integer_derived_decimal`, `decimal_not_derived_integer` | ❌ (no derivation relation) |
| an integer-tower literal outside its bounds has NO value — the bound is inside the lexical mapping, not a forgettable facet | ✅ `int_lexical_in_bounds` | ❌ (the bound IS a separate check, `int_lexical_in_range`) |
| canonical mapping round-trips | ✅ for boolean (`boolean_canonical_roundTrip`, `boolean_canonical_idempotent`); `#guard` only for infinite value spaces | ❌ (no canonical mapping) |
| NaN is outside the order and fails every bound facet | ✅ `nan_incomparable`, `nan_fails_every_bound` | ❌ |
| `validate` is exactly "the literal has a value under this type" | ✅ `validate_iff_valueOf`, `atomic_valueOf_eq` | ❌ |
| facet checking is sound against the value space | ✅ `atomic_valid_has_value`, `atomic_valid_satisfies_facets`, `atomic_valid_matches_patterns` | ❌ |

`grep -rn "Lemma" formal/fstar/XSD.Datatypes.fst formal/fstar/XSD.IEEE754.fst`
returns nothing, and `XSD.Facets.fst` contains 0 occurrences of `Lemma`. The
F\* XSD modules carry no theorems at all; `docs/theorem-registry.md` mentions
XSD only as the `xsd_datatype_axioms` table for D-entailment, which is a
different obligation.

Two further properties should exist and exist in NEITHER tree:

* the lexical mapping is injective where the specification says the canonical
  mapping is its inverse (`canonicalMap (lexicalMap s) = s` for every canonical
  `s`), proved rather than `#guard`-ed, for the datatypes with infinite value
  spaces;
* the consolidation itself: after §8, a theorem per switched consumer that the
  consumer's predicate EQUALS the `XSD` one, so a future edit cannot silently
  reintroduce a second answer. §5 states the same claim as a measured score
  over a finite corpus; the theorem states it for every input.
