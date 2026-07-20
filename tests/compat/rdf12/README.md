# RDF 1.2 Compatibility Bucket

> **Note (2026-07-16 un-park):** the "before Factoidal has a settled RDF
> 1.2 support story" framing below is out of date. RDF 1.2 / SPARQL 1.2
> IS now an implemented target — term model + N-Triples/N-Quads/Turtle/
> TriG syntaxes verified (RDF 1.2 212/0, SPARQL 1.2 248/6); see
> [`../../../docs/claude-rules/w3c-completeness-ledger.md`](../../../docs/claude-rules/w3c-completeness-ledger.md).
> This bucket is now for ad-hoc probes/reduced cases, not a
> holding-pen for an unsupported feature. Conformance lives in the
> vendored W3C rdf12/sparql12 suites run via `w3c_runner --rdf12` /
> `--sparql12`.

This directory is for RDF 1.2 and adjacent examples, kept as small reduced
cases alongside the vendored W3C conformance suites.

Purpose:

- collect real examples and small reduced cases
- distinguish parser compatibility from semantic support

Current policy:

- 1.2 is a supported target; 1.1 remains the default parse mode (Mode_11)
  so 1.1 output stays byte-identical
- examples placed here are compatibility probes, not normative conformance
- each example should say whether it is:
  - `1.1-compatible`
  - `recognized-not-supported`
  - `intentionally-rejected-in-1.1-mode`

Suggested file layout:

- `*.ttl`, `*.trig`, `*.nq`, `*.rq`: input examples
- `*.md`: short note for why the example matters

When adding a case, prefer the smallest reduced example that still demonstrates
the issue.
