# third_party/

Vendored or git-submodule'd external dependencies, grouped by origin.

The goal is that every non-first-party artifact (test suites, reference
corpora, upstream libraries we re-pack, etc.) lives under a predictable
path rooted here, so licence compliance, attribution, and updates are
easy to review in one place.

## Layout

```
third_party/
├── testing/        external test corpora
│   ├── w3c/        submodule: https://github.com/w3c/rdf-tests
│   │               (RDF 1.1 + SPARQL 1.1 + RDF 1.2 conformance tests;
│   │               the 1.2 "sparql-mixed-rdf-version-tests" branch is
│   │               part of this repo — no separate submodule needed)
│   ├── owl/        vendored from https://www.w3.org/2009/11/owl-test/
│   │               (OWL 2 Test Cases — static drop, not a git repo
│   │               upstream; see owl/README.md for refresh instructions)
│   ├── shex/       submodule: https://github.com/shexSpec/shexTest
│   │               (ShEx schema-validation test suite — active upstream)
│   ├── csvw/       submodule: https://github.com/w3c/csvw (gh-pages branch;
│   │               CSV on the Web tests live under tests/)
│   ├── rdf-canon/  submodule: https://github.com/w3c/rdf-canon
│   │               (RDF Dataset Canonicalization — RDFC-1.0 tests;
│   │               first suite we intend to wire up, per existing
│   │               scoping in docs/designissues/attestation-model.md
│   │               and kgx-pipeline.md)
│   ├── vc/         submodule: https://github.com/w3c/vc-data-model-2.0-test-suite
│   │               (Verifiable Credentials 2.0 test suite)
│   ├── did/        submodule: https://github.com/w3c/did-test-suite
│   │               (Decentralized Identifiers test suite)
│   └── rml/        submodule: https://github.com/kg-construct/rml-test-cases
│                   (RML mapping tests; upstream repo archived but the
│                   test corpus is stable)
├── apache/         reserved for Apache-family test assets
│                   (e.g. Jena ARQ test corpus, when vendored)
├── eleventy/       vendored npm cache: @11ty/eleventy + full dep tree
│                   (134 packages), so the docs/ Pages build runs
│                   offline via `npm ci --offline`. See its README.md.
└── observable/     vendored ESM bundles for the documentation hub:
                    @observablehq/{runtime,inspector,stdlib,plot} + d3,
                    esbuild-bundled into self-contained modules (no
                    CDN, no bare-specifier imports). See its README.md.
```

## Status: vendored vs wired up

As of 2026-04-24, **only `w3c/` is currently driven by our test harness**
(`w3c_runner`). The others are vendored for offline availability and so
that we can scope each subsequent wiring task with real test data in
hand. Scoping for `rdf-canon` already exists in
`docs/designissues/attestation-model.md` + `kgx-pipeline.md` and is the
next intended consumer.

## Why this lives here, not under `tests/`

1. It's *external* code/data under its own licence, not authored in-
   house. Grouping by provenance (third_party/ vs tests/) makes
   licence review at the repo root straightforward.
2. Our own tests under `tests/` stay small and focused on Factoidal-
   specific harnesses.
3. Adding a new upstream suite (Jena test corpus, OWL 2 Test Cases,
   SHACL, etc.) is a one-line submodule add here — no tree
   restructuring each time.

## Adding a new third-party dependency

```
git submodule add <url> third_party/<category>/<name>
```

Current categories: `testing/` (corpora and harnesses), `eleventy/`
and `observable/` (vendored npm libraries backing the site build and
the documentation hub — each vendored via an install/build script
rather than a submodule, since npm packages don't need the full git
history a submodule would carry). Add a new category folder when
vendoring a different kind of asset (e.g. `third_party/libraries/`
for a vendored C library).

Update this README when you add a category or a submodule.

## Migration note (2026-04-24)

Factoidal's W3C test fixtures used to live at `tests/w3c/`. They
moved here so vendored-upstream and first-party test code stop
sharing a directory. The `w3c_runner` keeps the old
`../../tests/w3c/...` paths as candidate fallbacks so stale checkouts
or external tooling don't break.
