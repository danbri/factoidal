# XML Schema 1.1 Part 2 Datatypes in Lean 4 — corpus, runner, and scores

Tracking: <https://github.com/danbri/factoidal/issues/666>
Specification: [XML Schema Definition Language (XSD) 1.1 Part 2:
Datatypes](https://www.w3.org/TR/xmlschema11-2/)

Owner, 2026-09-07, verbatim: "we should bite the bullet and do all of
XML Schema, to unlock later xslt/xpath/xquery avenues."

Part 1 Structures is **not** in scope for this run. Schema components,
the schema-document parser, PSVI, identity constraints, conditional
type assignment and assertions stay on
<https://github.com/danbri/factoidal/issues/666>. The runner classifies
every test group and reports the structures count beside the datatype
score, so the denominator is visible and no structures test is counted
as a datatype failure.

## The corpus

`third_party/testing/xsd` is a shallow submodule of
<https://github.com/w3c/xsdtests>, the W3C XML Schema Test Suite.
Licence: the suite's `00COPYRIGHT` puts the whole tree under the
[W3C Document Notice and
Licence](http://www.w3.org/Consortium/Legal/copyright-documents-19990405.html),
Copyright (C) World Wide Web Consortium 2006, 2007. It is used
unmodified and read-only. Full record:
`third_party/testing/xsd-PROVENANCE.md`. Registered in
`tools/ensure-test-env.sh`.

Contributors named in `suite.xml`: NIST (2004), Sun (2004, 2006),
Microsoft (2006), Boeing (2007), Saxonica (2010), IBM (2011), Oracle
(2011), and the W3C XML Schema Working Group. The `precisionDecimal`
test sets are referenced from `extra-suite.xml`, not `suite.xml`, and
are outside the denominator below.

## The runner

`Harness/XsdDatatypesRun.lean`, `lake -d formal/lean4 exe
l4xsd-datatypes` (about 30 seconds over the whole suite). It reads
`suite.xml`, then each `*Meta/*.testSet` manifest, then each
`testGroup`, with the project's own XML parser — the manifests are XML,
and a second reader of the syntax under test would be a second answer
to the same question.

Each test group is classified from its schema document:

| class | meaning | scored |
|---|---|---|
| `datatype` | only simple type definitions and element declarations of simple type | yes |
| `structures` | complex types, attributes, groups, identity constraints | no |
| `mixed` | both, or `include`/`import`/`redefine`/`override` | no |

and four further buckets keep a test out of the score for a stated
reason: `schema-invalid` (the group expects the SCHEMA to be rejected,
so the instance outcome is undefined), `version-1.0` (the group applies
to XSD 1.0 only; this engine implements 1.1), `unreadable` (the
document is not UTF-8, does not parse, or the element declaration is
not found), `not-simple` (the instance's document element has element
children).

Schema-validity tests — whether the SCHEMA document is itself valid,
15378 of them — are counted and not scored. Deciding them needs the
Part 1 §3.16 schema component constraints.

## The implementation

| module | content |
|---|---|
| `L4Factoidal/XSD/Datatypes.lean` | §3: the built-ins, `Val`, the lexical mappings, the canonical mappings, the §4.2 order and identity relations |
| `L4Factoidal/XSD/SimpleType.lean` | §4.1, §4.3: the simple type varieties (atomic, list, union), the constraining facets, `validate` |
| `L4Factoidal/XSD/SchemaReader.lean` | the `<simpleType>` subset of a schema document, and the classification above |
| `L4Factoidal/XSD/DatatypesTests.lean` | the `#guard` battery, every literal quoted from the specification section named beside it |

`pattern` (§4.3.4) is decided by the XSD regular-expression engine that
already existed: `L4Factoidal/Regex/XSDPattern.lean` parses XML Schema
Appendix G syntax and `Regex/Exec.lean` runs it by Brzozowski
derivatives.

`float`/`double` (§3.3.4, §3.3.5) are decided by
`L4Factoidal/XSD/IEEE754.lean`, which already carried the exact
rational rounding to binary32 and binary64.

No `sorry`, no user `axiom`, no `native_decide`, no `unsafe`, no new
`partial def`.

## Baseline — 2026-09-07

Measured by `lake -d formal/lean4 exe l4xsd-datatypes` over the whole
suite:

**XSD datatype instance tests: 18249 pass, 905 fail (out of 19154
scored).**

Not scored: structures 7053, mixed 0, schema-invalid 1, version-1.0 8,
unreadable 133, not-simple 8. Schema tests seen and not scored: 15378.

Per datatype, failures first:

| datatype | pass | fail | of |
|---|---:|---:|---:|
| list variety | 7977 | 680 | 8657 |
| union variety | 327 | 129 | 456 |
| QName | 88 | 45 | 133 |
| anyURI | 230 | 25 | 255 |
| string | 267 | 10 | 277 |
| float | 120 | 4 | 124 |
| boolean | 61 | 3 | 64 |
| anyAtomicType | 2 | 3 | 5 |
| positiveInteger | 341 | 3 | 344 |
| decimal | 391 | 2 | 393 |
| anySimpleType | 3 | 1 | 4 |
| every other datatype | | 0 | |

The zero-failure set at baseline: `dateTime`, `date`, `time`,
`gYearMonth`, `gYear`, `gMonthDay`, `gDay`, `gMonth`, `dateTimeStamp`,
`duration`, `yearMonthDuration`, `dayTimeDuration`, `double`,
`integer`, `int`, `long`, `short`, `byte`, `nonNegativeInteger`,
`nonPositiveInteger`, `negativeInteger`, `positiveInteger` (3 fail),
`unsignedLong`, `unsignedInt`, `unsignedShort`, `unsignedByte`,
`hexBinary`, `base64Binary`, `normalizedString`, `token`, `Name`,
`NCName`, `NMTOKEN`, `NMTOKENS`, `language`.

## Status — 2026-09-07, end of the first run

**XSD datatype instance tests: 18951 pass, 5 fail (out of 18956
scored).** Baseline at the start of the run was 18249 pass, 905 fail
(out of 19154 scored); the denominator moved because 198 tests left the
score into named buckets (below), which is a change in what is
MEASURED, not a change in what passes.

Not scored, each with its reason: structures 7053, mixed 0,
schema-invalid 1, version-1.0 8, unreadable 138, not-simple 8,
assertion 32, unreadable-pattern 105, nilled 3, value-constraint 53.
Schema-validity tests seen and not scored: 15378.

Per datatype, at the end of the run:

| datatype | pass | fail | of |
|---|---:|---:|---:|
| list variety | 8593 | 0 | 8593 |
| union variety | 425 | 1 | 426 |
| integer | 343 | 0 | 343 |
| int | 342 | 0 | 342 |
| long, nonNegativeInteger, nonPositiveInteger, negativeInteger, unsignedLong, unsignedInt | 340 each | 0 | 340 each |
| positiveInteger | 340 | 1 | 341 |
| short, unsignedShort | 335 each | 0 | 335 each |
| byte, unsignedByte | 315 each | 0 | 315 each |
| decimal | 391 | 1 | 392 |
| dateTime | 309 | 0 | 309 |
| time | 290 | 0 | 290 |
| date | 289 | 0 | 289 |
| gYearMonth | 289 | 0 | 289 |
| duration | 285 | 0 | 285 |
| gMonthDay | 285 | 0 | 285 |
| gYear | 283 | 0 | 283 |
| gMonth | 275 | 0 | 275 |
| gDay | 270 | 0 | 270 |
| dateTimeStamp | 7 | 0 | 7 |
| yearMonthDuration, dayTimeDuration | 5 each | 0 | 5 each |
| anyURI | 255 | 0 | 255 |
| string | 244 | 1 | 245 |
| normalizedString | 210 | 0 | 210 |
| NMTOKENS | 207 | 0 | 207 |
| token, Name, NMTOKEN | 205 each | 0 | 205 each |
| language | 200 | 0 | 200 |
| NCName | 180 | 0 | 180 |
| hexBinary, base64Binary | 130 each | 0 | 130 each |
| double | 124 | 0 | 124 |
| float | 120 | 0 | 120 |
| QName | 108 | 0 | 108 |
| boolean | 60 | 1 | 61 |
| anySimpleType | 2 | 0 | 2 |

The five failures: namespace-qualified type-name resolution (the
`targetNS00101m1` and `ST_name00101m1` groups — the reader matches a
type QName by local name and does not check that the prefix resolves to
the schema's target namespace), one version-control-attribute group
(`vc_003_2`), one boolean group whose expected outcome turns on
something outside the datatype, and one union group.

### What the run changed

1. §4.3.5 `enumeration` was applied to atomic types only. A list
   enumeration member is itself a list literal (§3.1.2) and a union
   enumeration member is a literal of the union, so each is mapped
   through the item type or the member types before the identity
   comparison. list 7977 -> 8593 pass, union 327 -> 425 pass.
2. §4.3.1: `length`, `minLength` and `maxLength` are not applicable to
   `QName` and `NOTATION`. QName 88 -> 108 pass with no failures.
3. `Regex/XSDPattern.lean` did not read the Appendix G class escapes
   `\i`, `\I`, `\c` and `\C` (the XML `NameStartChar` and `NameChar`
   classes). An unreadable pattern makes its group vacuous, so every
   `anyURI` pattern group answered valid. anyURI 230 -> 255 pass.

## Theorems

`L4Factoidal/XSD/DatatypesTheorems.lean`, each closed by
`#print axioms` with only `propext`, `Classical.choice` and
`Quot.sound`:

| theorem | statement |
|---|---|
| `lexicalMapWs_factors` | whiteSpace (§4.3.6) is applied BEFORE the lexical mapping and never inside it — the factorisation RDF 1.1 Semantics §7 depends on, since it needs the version without whiteSpace |
| `string_lexical_total` | §3.3.1: `string` fixes whiteSpace to `preserve`, so its lexical mapping is the identity and its lexical space is every string |
| `derivedFrom_refl`, `byte_derived_integer`, `integer_derived_decimal`, `decimal_not_derived_integer` | the §3.4 derivation hierarchy |
| `int_lexical_in_bounds` | for every integer-tower type, a literal outside the type's bounds has NO value: the bound check is inside the lexical mapping, not a facet a caller can forget |
| `boolean_canonical_roundTrip` | §3.3.2: the canonical mapping produces a lexical representation that maps back to the same value |
| `boolean_canonical_idempotent` | canonicalising the value of a canonical representation returns that representation |
| `nan_incomparable` | §3.3.4: NaN is outside the order relation, so `valCompare` answers `none` for every partner |
| `nan_fails_every_bound` | consequently NaN fails every §4.3.7-§4.3.10 bound facet whose bound is in the lexical space |
| `validate_iff_valueOf` | `validate` is exactly "the literal has a value under this type" |
| `atomic_valueOf_eq` | the atomic case of `valueOf`, unfolded once — the equation the three soundness statements below are corollaries of |
| `atomic_valid_has_value` | a validated literal IS in the base type's lexical space after whiteSpace processing |
| `atomic_valid_satisfies_facets` | facet checking is SOUND against the value space: the value of a validated literal satisfies every value-space facet the type declares |
| `atomic_valid_matches_patterns` | §4.3.4: it also matches every pattern group, on the whiteSpace-normalized literal |

The canonical-mapping round trip is stated and proved for `boolean`,
whose value space is finite. For the datatypes with infinite value
spaces it is exercised by the `#guard` battery, not proved.

### Consumer gates after the switch

| gate | score | before |
|---|---|---|
| `l4rdf-semantics` | 40 pass, 7 fail, 0 unsupported (out of 47) | 40 pass — unchanged |
| `l4shacl` | 98 pass, 0 fail, 0 skip, 0 unsupported (out of 98) | 98 — unchanged |
| `l4csvw-validate` | 281 pass, 1 fail, 0 skip (out of 282) | 281 — unchanged |
| `l4xmlconf` | 1861 pass, 0 fail (out of 1861 in profile) | 1861 — unchanged |
| `l4rif` | 42 pass, 0 fail (out of 42 decided) | unchanged |
| `tools/lean-hygiene-audit.py` | clean; `partial def` 172, the committed baseline | unchanged |

## Consumers

The point of one implementation is that every consumer reads the same
lexical-to-value mappings. Switched in this run:

| consumer | what changed | gate |
|---|---|---|
| `RDF/Datatypes.lean` | `NumVal` IS `XSD.Dec`; `parseIntegerLexical`, `parseDecimalLexical`, `intInRange` and the float/double lexical space are the §3 mappings. The RDF-specific part stays: §7 does NOT apply whiteSpace, so `lexicalMap` is called and never `lexicalMapWs` | `l4rdf-semantics` |
| `SHACL/Validation.lean` | `literalIllFormed` is one call into `XSD.builtinOfIri?` + `XSD.lexicalMap`, replacing 18 hand-written datatype arms | `l4shacl` 98 pass, 0 fail (out of 98) |
| `XSD/Facets.lean` | its private `daysFromCivil` is one call into the shared one | `l4owl-probe` (its catalog fixtures were not present in this worktree; the module builds and the OWL probe was not re-measured) |

Not yet switched, named so the next session does not have to rediscover
them:

* `CSVW/Formats.lean` carries its own `xsd:duration` lexical space, its
  own numeric-base lexical spaces and its own `integerBounds`. They
  coexist with format-string handling (grouping and decimal separators,
  percent scaling), so the switch is a decomposition and not a
  substitution.
* `RIF/Builtins.lean` and `SHACL/Validation.lean` each carry a second
  `daysFromCivil` in their own namespace.

## Open

* The `float`/`double` canonical mapping (§3.3.4.2) emits the EXACT
  decimal expansion of the binary value rather than the shortest
  numeral that round-trips. Both round-trip; only the digit count
  differs.
* `precisionDecimal` (§3.2.5) carries the decimal lexical space plus
  the three specials, with no separate precision-carrying value space.
  Its test sets are commented out of `suite.xml`.
* `QName` and `NOTATION` values are the (prefix, local) pair. Comparing
  EXPANDED names needs the in-scope namespace bindings, which a
  datatype-only validator does not have.
* `assertion` (§4.3.12) is recorded on the facet record and not
  decided; it needs XPath 2.0 over the value.
* Schema-validity tests are counted, not scored — 15378 of them.
  Deciding them needs the Part 1 §3.16 schema component constraints.
* 105 scored-in-principle tests sit in the `unreadable-pattern` bucket:
  the largest construct the XSD regular-expression parser does not read
  is character-class SUBTRACTION (`[a-z-[m-n]]`, §G.1).
* The reader matches a type QName by local name. Two groups turn on the
  prefix resolving to the schema's target namespace.
* Part 1 Structures — schema components, PSVI, identity constraints,
  conditional type assignment, assertions — is the next slice, on
  <https://github.com/danbri/factoidal/issues/666>.
