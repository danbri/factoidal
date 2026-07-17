# Provenance — Apache Xalan XSLT 1.0 conformance test suite

This corpus is the **OASIS/W3C XSLT 1.0 conformance test suite** as
mirrored, cleaned, and redistributed by the **Apache Xalan** project.
It is vendored as a pinned git submodule; this directory adds only a
generated `manifest.json` (the schema the `xslt_runner` consumes, which
the upstream repo does not ship) plus this provenance record. The
vendored files are never edited (third-party vendoring policy,
`docs/designissues/2026-05-07-io-verification-and-third-party.md`).

## Owner directive (verbatim, 2026-07-17)

> "Xslt1 find the best apache/mit/w3c-licensed opensource
> implementations and vendor in their unit tests to third_party/,
> copies or submodule but wired in to CLAUDE.md or our skills so we
> restore access fully in fresh envs or after Container resets. Agreed
> no xslt2."

Context: `docs/designissues/2026-07-17-xpath-xslt-coverage-matrix.md`
established that our existing 88-test XSLT corpus is a slice-1-filtered
regression pin (a vendored subset of `w3c/xslt30-test` whose selection
criteria structurally exclude every unimplemented feature), and
recommended the Apache-2.0 Xalan XSLT-1.0 conformance mirror as the
hole-targeted corpus. This is that corpus.

## Upstream

- Repository: `https://github.com/apache/xalan-test`
- Submodule path: `third_party/testing/xslt1-xalan/xalan-test-src`
- Pinned commit: `5120be9b3704a724ff0205b750d3cb409b62869b`
  ("Xalanj 2821 (#12)", `master`)
- Cloned / recorded: 2026-07-17
- Subtree used: `tests/conf/` (stylesheets + source XML) and
  `tests/conf-gold/` (expected serialized output). These are the
  historical OASIS XSLT/XPath conformance cases (contributed by
  Lotus/IBM, Sun/Oracle, Microsoft and others), re-hosted by Apache
  under the Apache License; see the upstream `NOTICE` file.

## License verdict

- **License: Apache License 2.0** — OK against the owner's
  apache/mit/w3c constraint. `xalan-test-src/LICENSE` (Apache-2.0) and
  `xalan-test-src/NOTICE` are included with the submodule; every
  vendored `*.xsl` carries the ASF licence header inline.
- No copyleft, no field-of-use restriction. Redistribution as vendored
  test data is permitted with the retained LICENSE + NOTICE.

## Candidate corpora considered (research, 2026-07-17)

| Corpus | License | Verdict | Notes |
|---|---|---|---|
| **Apache Xalan `xalan-test` `tests/conf`** | Apache-2.0 | ✅ vendored | 1690 test triples (xsl+xml+gold), 35 categories mapping directly onto the coverage-matrix holes (namespace, string/translate, boolean/lang, numbering, numberformat, idkey, impincl, attribset, output, message, processorinfo). `version="1.0"` stylesheets; genuine W3C/OASIS-derived cases (iron rule #6). Clean to pin as a submodule. |
| Apache Xalan-J `xalan-java` | Apache-2.0 | not needed | The processor, not a separable conformance corpus — its tests point back at `xalan-test`. |
| libxslt `tests/` | MIT | ✅ eligible, deferred | GNOME libxslt (`gitlab.gnome.org/GNOME/libxslt`), MIT. Real `.xsl`/`.xml`/`.out` triples incl. the XSLT REC examples. A viable MIT second corpus; the Xalan conf suite already covers every matrix hole at higher density, so a second corpus was deferred rather than vendored this pass (add under `third_party/testing/xslt1-libxslt/` with the same manifest+runner wiring if broader coverage is wanted). |
| lxml XSLT tests | BSD (lxml) + libxslt | eligible | Thin wrapper over libxslt's engine/tests; subsumed by vendoring libxslt directly. |
| Mozilla TransforMiiX tests | MPL-2.0 | ⚠️ skipped | MPL-2.0 is outside the owner's stated apache/mit/w3c constraint. Not vendored; flagged here rather than assumed acceptable. |
| OASIS XSLT/XPath conformance ZIP (direct) | OASIS IPR / per-contributor | ⚠️ avoided | The historical source set, but the canonical OASIS endpoint serves HTML (not directly fetchable) and carries the OASIS IPR question. The Apache-hosted `xalan-test` copy is the same cases under a clean Apache-2.0 grant, so we take that instead. |

## Not edited

Per the vendoring policy, no file under `xalan-test-src/` is modified.
The runner performs XML-line-ending normalization and an
XML-declaration strip on **both** sides at comparison time (see
`bin/xslt-runner/xslt_runner.ml`), never by rewriting the vendored
gold files.
