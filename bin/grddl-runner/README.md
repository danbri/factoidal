# bin/grddl-runner — W3C GRDDL Stage 1 test runner (local subset)

Stand-alone CLI that drives the local, non-networked subset of the W3C
GRDDL ("Gleaning Resource Descriptions from Dialects of Languages")
test suite against the F\*-extracted `GRDDL.Discovery` module and the
engines it composes.

```
grddl_runner [manifest.rdf]
```

Reads `third_party/testing/grddl/grddl-tests-normative.rdf` (RDF/XML)
via the F\*-extracted `Parser_RDFXML`, walks the parsed triples to
build a per-test index (rdfcore test-schema: `t:Test`,
`t:inputDocument`, `t:outputDocument`, `g:exercisesRule`), and for each
Stage-1 test:

1. reads the source document from
   `third_party/testing/grddl/docroot/` (allowlisted local files — **no
   network fetch**),
2. discovers same-document transformation references with
   `GRDDL_Discovery.discover_transformations` (path (a) the
   `grddl:transformation` root attribute; path (b) the XHTML
   `head/@profile` gate + `link`/`a` `rel="transformation"` links),
3. applies each discovered stylesheet via `XSLT_Transform.transform`
   and re-parses the RDF/XML output with `Parser_RDFXML`, unioned with
   the RDF/XML-base contribution for RDF/XML sources
   (`GRDDL_Discovery.grddl_result`), and
4. compares the result graph against the expected-output graph with
   `GRDDL_Discovery.graphs_isomorphic` (RDFC-1.0 canonicalization — not
   a string diff).

**I/O glue only** (CLAUDE.md iron rule #11 / anti-pattern #15): all
discovery, transformation, parsing, canonicalization, and graph
comparison live in `formal/fstar/GRDDL.Discovery.fst` and the modules
it composes. The runner does file I/O, the manifest triple-walk (data
extraction), and result bucketing.

## Scope (Stage 1)

Per `docs/designissues/2026-07-08-grddl-scoping.md`: same-document
discovery over well-formed XML/XHTML, no network, RDF/XML
transformation output only.

Three-bucket reporting (rule #25), final line
`grddl: X pass, Y fail, Z skip (out of N)`:

- **pass** — result graph isomorphic to the expected graph.
- **fail** — with reason sub-buckets:
  - `fail-known-gap-xslt-nametest` — the transform relies on
    namespace-prefix-aware XPath name tests against a default-namespace
    source; the XSLT engine's name tests are prefix-string based
    (`XSLT.Transform.fst` lists "prefix-aware match patterns" as
    deliberately out of scope). This is the dominant Stage-1 blocker
    for XHTML/XML sources.
  - `fail-known-gap-xslt-feature` — the transform uses an out-of-scope
    XSLT 1.0 feature (`document()`, `xsl:key`, `xsl:import`, …).
  - `fail-graph-mismatch` — the transform ran but produced a
    non-isomorphic graph for another reason.
  - `fail-known-gap-xml-parse` / `fail-discovery` / `fail-*` — see the
    runner source.
- **skip** — `skip-network` (`NetworkedTest`-flagged) and
  `skip-stage2-ns-or-profile-document` (tests exercising the
  namespace-document / profile-document transformation paths, which
  require a second-resource fetch — Stage 2).

A `GRDDL_DEBUG=<test-id>` environment variable dumps the discovered
transforms and the result-vs-expected canonical N-Quads for one test.
