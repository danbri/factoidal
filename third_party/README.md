# third_party/

Vendored or git-submodule'd external dependencies, grouped by origin.

The goal is that every non-first-party artifact (test suites, reference
corpora, upstream libraries we re-pack, etc.) lives under a predictable
path rooted here, so licence compliance, attribution, and updates are
easy to review in one place.

## Layout

```
third_party/
├── testing/        external test corpora (W3C, etc.)
│   └── w3c/        submodule: https://github.com/w3c/rdf-tests
│                   (RDF 1.1 + SPARQL 1.1 conformance tests)
└── apache/         reserved for Apache-family test assets
                    (e.g. Jena ARQ test corpus, when vendored)
```

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

Current categories: `testing/` (corpora and harnesses). Add a new
category folder when vendoring a different kind of asset (e.g.
`third_party/libraries/` for a vendored C library).

Update this README when you add a category or a submodule.

## Migration note (2026-04-24)

Factoidal's W3C test fixtures used to live at `tests/w3c/`. They
moved here so vendored-upstream and first-party test code stop
sharing a directory. The `w3c_runner` keeps the old
`../../tests/w3c/...` paths as candidate fallbacks so stale checkouts
or external tooling don't break.
