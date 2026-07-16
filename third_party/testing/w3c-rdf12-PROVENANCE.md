# Provenance — W3C RDF 1.2 / SPARQL 1.2 test suites

These suites are **already vendored** as part of the `w3c` git submodule
(`third_party/testing/w3c`, the `w3c/rdf-tests` upstream) — the same
mechanism by which the RDF 1.1 and SPARQL 1.1 suites are vendored. This
file records provenance for the RDF 1.2 / SPARQL 1.2 subtrees so the
2026-07-16 impact investigation has a citable pin; it does **not**
duplicate or edit the submodule content (per the third-party vendoring
policy, `docs/designissues/2026-05-07-io-verification-and-third-party.md`
— never edit vendored files).

## Upstream

- Repository: `https://github.com/w3c/rdf-tests` (mirrors
  `https://w3c.github.io/rdf-tests/`)
- Submodule path: `third_party/testing/w3c`
- Pinned commit: `35c503a6323db83c2e54ff404387210c20d57c18`
  ("Automated manifest generation", 2026-02-26)
- Recorded: 2026-07-16

## License

Per every manifest header in these trees:

> Distributed under both the "W3C Test Suite License"
> (https://www.w3.org/Consortium/Legal/2008/04-testsuite-license) and
> the "W3C 3-clause BSD License"
> (https://www.w3.org/Consortium/Legal/2008/03-bsd-license).

See also `third_party/testing/w3c/LICENSE.md`.

## Subtrees covered

RDF 1.2 syntax + eval + canonicalization + semantics:

- `third_party/testing/w3c/rdf/rdf12/rdf-n-triples/` (syntax, c14n)
- `third_party/testing/w3c/rdf/rdf12/rdf-n-quads/` (syntax, c14n)
- `third_party/testing/w3c/rdf/rdf12/rdf-turtle/` (syntax, eval)
- `third_party/testing/w3c/rdf/rdf12/rdf-trig/` (syntax, eval)
- `third_party/testing/w3c/rdf/rdf12/rdf-xml/` (eval)
- `third_party/testing/w3c/rdf/rdf12/rdf-semantics/`

SPARQL 1.2:

- `third_party/testing/w3c/sparql/sparql12/` (syntax,
  syntax-triple-terms-positive, syntax-triple-terms-negative,
  eval-triple-terms, expression, lang-basedir, version, grouping,
  codepoint-escapes, rdf11)

## Measured baseline against these suites

See `docs/designissues/2026-07-16-rdf12-sparql12-impact-strategy.md`
for the full census of the current (RDF/SPARQL 1.1) engine run against
these 1.2 suites.
