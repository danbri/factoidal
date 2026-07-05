# W3C XML Conformance Test Suite (vendored)

Vendored 2026-07-05 for the `xml-runner` assessment harness
(`bin/xml-runner/`), per owner directive to check
`formal/fstar/Parser.XML.fst` (generic XML → AST parser) and
`formal/fstar/XML.Wellformedness.fst` against the real W3C corpus
(iron rule #6 — no synthetic "inspired by" test files).

## Source

- **Canonical page**: <https://www.w3.org/XML/Test/>
- **Release fetched**: `XML W3C Conformance Test Suite 20130923`
  (2013-09-23), the latest release listed on the page as of
  2026-07-05. Earlier releases (20031210, 20080205, 20080827) are
  listed on the same page but were not fetched — 20130923 is a
  superset ("a minor release, including a small number of small
  corrections and additions" per the page's release notes).
- **Fetched from**: `https://www.w3.org/XML/Test/xmlts20130923.tar.gz`
  — reachable directly through this environment's outbound-HTTPS
  proxy (`HTTP 200`, `641522` bytes downloaded, gzip data with an
  embedded mtime of 2013-09-23). No mirror fallback was needed.
- **Archive contents**: a single top-level `xmlconf/` directory,
  copied here as-is (`third_party/testing/xml/xmlconf/`).

## What's in it

3386 files, 17 MB. Breakdown by collection directory (each is one of
the historical contributing organizations):

| Directory | Files | Contributor |
|---|---|---|
| `xmlconf/xmltest/` | 606 | James Clark's original "XMLTEST" suite |
| `xmlconf/sun/` | 203 | Sun Microsystems |
| `xmlconf/ibm/` | 1526 | IBM Java Technology Center (incl. `ibm/xml-1.1/` for XML 1.1-specific cases) |
| `xmlconf/oasis/` | 372 | OASIS/NIST |
| `xmlconf/eduni/` | 655 | University of Edinburgh (errata suites, XML 1.1, Namespaces 1.0/1.1) |
| `xmlconf/japanese/` | 19 | Fuji Xerox (Japanese-encoding documents) |
| `xmlconf/files/`, `testcases.dtd`, `xmlconf.xml` | 3 + 2 | shared manifest infrastructure |

Every `TEST` entry across every collection totals roughly 2748
individual test cases (`not-wf` 1071, `valid` 701, `invalid` 169,
`error` 29, per the manifest's own `TYPE` attribute distribution —
exact totals are printed by the runner, not hand-counted here per
anti-pattern #25).

## License / terms

The suite ships no single top-level `LICENSE` file; provenance and
usage terms are recorded per-collection, inline in the files
themselves and in two contributor readmes vendored unmodified:

- `xmlconf/sun/cxml.html` — Sun Microsystems' canonical-forms
  writeup; `xmlconf/xmlconf.xml`'s own header states "Original
  version copyright 1998 by Sun Microsystems, Inc. All Rights
  Reserved. Modifications copyright 1999 by OASIS. Modifications
  copyright 2001 by OASIS."
- `xmlconf/ibm/ibm_oasis_readme.txt` — IBM's contribution readme
  ("This test suite is contributed by the testing team in the IBM
  Java Technology Center and used for the conformance test on the
  XML parsers based on XML 1.0 Specification").

The W3C page (<https://www.w3.org/XML/Test/>) that distributes the
combined release states: "The XML 1.0 (Second Edition) Conformance
Test Suite was transferred from OASIS to W3C forming the basis for
the XML W3C Conformance Test Suite... Contributions have come from
the W3C XML Core Working Group and The OASIS XML Conformance
Technical Committee," and invites reuse: "Implementors are encouraged
to write a harness around these tests to test their implementation
for XML conformance." No page-level restrictive copyright/license
banner was found on the index page itself (checked programmatically,
2026-07-05); this vendoring follows the same "licence-clean, publicly
distributed W3C test corpus" posture already applied to the other
`third_party/testing/w3c*` / `owl` / `rdf-canon` suites in this repo
per `docs/designissues/2026-04-23-external-sparql-test-suites.md`.
If a stricter notice surfaces later, replace this vendored copy with
the corrected terms in the same commit that discovers it.

## Manifest structure

`xmlconf/xmlconf.xml` is the master manifest: an XML document whose
`<!DOCTYPE TESTSUITE SYSTEM "testcases.dtd" [ <!ENTITY ...> ]>`
internal subset declares one general entity per sub-manifest file
(e.g. `<!ENTITY jclark-xmltest SYSTEM "xmltest/xmltest.xml">`), and
whose body is a sequence of `<TESTCASES PROFILE="...">` elements that
reference those entities (`&jclark-xmltest;`) to pull in each
collection's own test list. `testcases.dtd` (vendored alongside)
documents the full grammar; the load-bearing attributes on every
`<TEST>` element are:

- `TYPE` — one of `valid` / `invalid` / `not-wf` / `error`. Per the
  DTD's own comment: "All parsers must accept 'valid' testcases.
  Nonvalidating parsers must also accept 'invalid' testcases, but
  validating ones must reject them. No parser should accept a
  'not-wf' testcase unless it's a nonvalidating parser and the test
  contains external entities that the parser doesn't read. Parsers
  are not required to report 'errors'."
- `ENTITIES` — `none` / `general` / `parameter` / `both`: whether the
  test's outcome depends on reading external general and/or parameter
  entities. This is the suite's own, sanctioned escape hatch for
  non-validating parsers that don't resolve external entities — see
  `bin/xml-runner/xml_runner.ml`'s SKIP-bucket logic, which uses this
  attribute directly rather than reinventing the exemption.
- `URI`, `ID`, `SECTIONS` (spec section citation), `NAMESPACE`
  (`yes`/`no`), `VERSION`/`EDITION` (XML 1.0 vs 1.1), `RECOMMENDATION`.
- The element's `#PCDATA` body is a one-line human description of
  what the test exercises (used by the runner's fail-cluster report
  instead of re-deriving a construct name from scratch).

**Important structural fact discovered while building the runner**:
`Parser.XML.fst` has no `<!DOCTYPE ...>` production at all (confirmed
by reading `parse_xml_document` — `skip_misc` only skips whitespace
and comments, never a DOCTYPE). So `xmlconf.xml` itself — which opens
with a DOCTYPE internal subset — cannot be parsed by our own engine;
`xml_runner` dogfoods `Parser_XML.parse_xml_document` on it first,
observes the `None` result, and falls back to a targeted textual scan
for the `<!ENTITY name SYSTEM "path">` declarations to discover the
~19 leaf manifest files. Each **leaf** manifest file (`xmltest.xml`,
`sun-valid.xml`, `ibm_oasis_valid.xml`, `oasis.xml`, the `eduni/*`
files, `japanese.xml`, …) has no DOCTYPE of its own and parses cleanly
via the real extracted parser — so the actual `<TEST>` entry
enumeration is genuinely dogfooded, only the master manifest's
entity-inclusion layer is not.
