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
* Schema-validity tests are counted, not scored.
