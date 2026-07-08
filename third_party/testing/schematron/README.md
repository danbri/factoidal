# Schematron validation corpus (spec-cited)

Test corpus for the F* Schematron validator
(`formal/fstar/Schematron.Validate.fst`, ISO/IEC 19757-3 XSLT-1 /
XPath-1 query binding), exercised by `bin/schematron-runner`.

## Provenance — spec-cited (FALLBACK path), stated loudly

These cases are **authored from the specification and the classic
Schematron literature**, not extracted from a repository of
(schema, instance, expected-report) triples. That fallback was taken
deliberately, and here is why:

The reference implementation repository `Schematron/schematron`
(GitHub, cloned at commit
`77dcd36c53d12ed786c144ece3b2af7694abdc56`) was inspected in full. It
does **not** contain direct-validation triples with machine-checkable
expected reports:

- `trunk/xsd2sch/test/**` — 345 `*.xsd.sch` schemas mechanically
  generated from XSD, with no paired instance documents and no
  expected SVRL/report output.
- `trunk/ant-schematron/test/**` — a handful of real `.sch` schemas
  plus instance `.xml` files, but they are Ant-pipeline fixtures with
  **no expected-report files**, and the schemas use the `xslt2` query
  binding and heavy OOXML namespaces (out of this slice's XPath-1
  scope).

There is therefore no upstream corpus of (schema, instance,
expected) triples to vendor. Per Iron Rule #6 ("run the real test
files; no synthetic queries passed off as conformance"), synthetic
cases must not masquerade as a conformance suite — so every case here
**cites its source in the schema file** and the expected outcome is
derived directly from the ISO firing semantics. This is a
spec-cited-and-labelled corpus, not a W3C/ISO conformance run.

### Cited sources

- **ISO/IEC 19757-3** — Information technology — Document Schema
  Definition Languages (DSDL) — Part 3: Rule-based validation —
  Schematron. Sections 5.4.3 (`assert`), 5.4.4 (`report`), 6.5
  (rule firing / first-matching-rule).
- **Rick Jelliffe, "The Schematron Assertion Language"** and the
  schematron.com tutorial — the canonical "a car has four wheels"
  co-occurrence example and the `not(condition) or requirement`
  conditional-co-occurrence idiom.
- **Schematron/schematron @ 77dcd36c53d12ed786c144ece3b2af7694abdc56**
  — confirms the namespace URI `http://purl.oclc.org/dsdl/schematron`
  and the element vocabulary (`schema`, `pattern`, `rule`, `assert`,
  `report`, `ns`, `let`).

## What each case covers

| name | category | what it checks |
|------|----------|----------------|
| library-cardinality-valid | cardinality-assert | `assert count(book) >= 1` holds — valid document, no findings |
| library-cardinality-invalid | cardinality-assert | same assert fails on an empty `<library>` |
| car-four-wheels | cooccurrence-assert | `assert count(wheel) = 4`; the 3-wheeled car fails |
| book-flags-violation | forbidden-combination-report | `report @discount and @clearance` fires on the book with both flags |
| book-flags-clean | forbidden-combination-report | same report does not fire — valid document |
| first-matching-rule | firing-semantics | a `<item>` matches the `item` rule only, NOT the later `*` rule in the same pattern (ISO 6.5) |
| payment-conditional-cooccurrence | cooccurrence-assert | `assert not(@type='card') or card-number`; the card payment without a card-number fails |
| unsupported-axis-indeterminate | soundness-indeterminate | `preceding-sibling::` cannot be parsed by the engine → recorded INDETERMINATE, not silently passed |

## Manifest format

`manifest.json` is a JSON array (parsed by the F*-extracted
`Parser_JSON`); each entry:

```
{ "name": ..., "category": ..., "schema": <path>, "instance": <path>,
  "expect": [ { "type": "assert-fail" | "report-hit" | "indeterminate",
                "context": <rule @context>, "test": <@test string> }, ... ] }
```

`expect` is compared as a multiset of `type|context|test` keys (one
entry per firing node). An empty `expect` means the instance is valid
(no assert failed and no report fired). Firing-node paths and message
text are produced by the validator but not compared (paths are
position-derived and not load-bearing for conformance).
