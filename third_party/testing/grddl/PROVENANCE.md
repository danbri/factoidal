# Vendored W3C GRDDL test suite — provenance

Offline copy of the W3C GRDDL ("Gleaning Resource Descriptions from
Dialects of Languages") test cases, so Factoidal's GRDDL Stage 1 runner
(`bin/grddl-runner/grddl_runner.ml`) can discover transformations,
apply them, and compare result graphs **without any network access**.

There is no upstream git repository for this suite (unlike the other
suites under `third_party/testing/`, which are git submodules). The
files are served as plain documents under
`https://www.w3.org/2001/sw/grddl-wg/td/`, so they are vendored here as
a plain directory tree mirroring the source URL paths.

## What was retrieved

- **Retrieved:** 2026-07-09, via `curl -sS -L` through the session's
  configured HTTPS proxy.
- **Spec:** GRDDL, W3C Recommendation 11 September 2007
  (<https://www.w3.org/TR/grddl/>).
- **Test-cases document:** <https://www.w3.org/TR/grddl-tests/>;
  manifest data root <https://www.w3.org/2001/sw/grddl-wg/td/>.

### Manifest

- `grddl-tests-normative.rdf` — the normative test manifest (RDF/XML).
  - Source: `https://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.rdf`
  - SHA-256: `bb7ddcd379fce93d4128e95f2e97bf065a55f45da3cfc1dd91222ef245e524a4`
- `grddl-tests-normative.n3` — the same manifest in Turtle/N3 (kept for
  human reference; the runner parses the RDF/XML copy).
  - Source: `https://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.n3`
  - SHA-256: `70dba2618dbb5c7eff8e46ae687ad50c585261496e2b6a3838e1dfe69cefdcd6`

The manifest uses the rdfcore test-schema vocabulary
(`http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#`) plus the
GRDDL-specific extension vocabulary
(`http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#`), which
adds `exercisesRule`, `alternative`, and the `NetworkedTest` class that
flags tests requiring live HTTP.

### Document tree — `docroot/`

`docroot/` is a URL mirror the runner maps absolute test-suite IRIs
into (`iri_to_local`):

- `docroot/td/`  ← `http://www.w3.org/2001/sw/grddl-wg/td/`
  (input documents, transformation stylesheets, expected-output RDF/XML,
  and the `base/` subdirectory for the xml:base tests).
- `docroot/g/`  ← `http(s)://www.w3.org/2003/g/`
  (the shared GRDDL transformation stylesheets `embeddedRDF.xsl`,
  `inline-rdf.xsl`, and the `glean-profile` profile document).

Every input document, transformation stylesheet, and expected-output
file referenced by the normative manifest was fetched (all HTTP 200).
Extension-less content-negotiated URLs (e.g. `td/hcard`,
`td/four-transforms`) were saved under their basename; these belong to
the networked namespace/profile-document tests (Stage 2, skipped by the
Stage 1 runner) and are vendored for completeness.

## Licence

The W3C GRDDL specification, its test cases, and the served test
documents are published by the W3C and made available under the **W3C
Document Licence** and the **W3C Software and Document Notice and
Licence**
(<https://www.w3.org/copyright/software-license-2023/> and
<https://www.w3.org/copyright/document-license-2023/>). These vendored
copies are byte-identical to the upstream documents; they are
reproduced here unmodified solely to let the offline GRDDL Stage 1
runner exercise the suite without a network fetch. No warranty; see the
W3C licences for terms.
