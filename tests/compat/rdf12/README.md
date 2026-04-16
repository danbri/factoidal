# RDF 1.2 Compatibility Bucket

This directory is for RDF 1.2 and adjacent examples that we expect to encounter
in the wild before Factoidal has a settled RDF 1.2 support story.

Purpose:

- collect real examples and small reduced cases
- distinguish parser compatibility from semantic support
- avoid silently drifting the 1.1 implementation target

Current policy:

- RDF/SPARQL 1.1 remains the main normative target
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
