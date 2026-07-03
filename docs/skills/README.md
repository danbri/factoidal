# Retired: pre-pivot narrative skill docs

The seven narrative how-to files that lived here (`testing.md`,
`measuring.md`, `optimising.md`, `improving-sparql.md`,
`validating.md`, `rdf-format-conversion.md`, `periodic-review.md`)
described the **pre-pivot Rust implementation** (`rdf-wasm/`,
`cargo test`, hand-written parsers). That architecture was retired
when the project committed to F\*-as-the-product (Iron Rules #1–#2),
and the files' commands and checklists had become actively
misleading.

They were removed on 2026-07-03. Their durable disciplines —
regression checklists, scorecard tracking, periodic review hooks —
were carried forward, rewritten for the F\*/OCaml pipeline, into the
agentskills.io skill files at the repo root:

- [`skills/test-suites/SKILL.md`](../../skills/test-suites/SKILL.md)
- [`skills/perf-benchmarking/SKILL.md`](../../skills/perf-benchmarking/SKILL.md)
- [`skills/site-and-dashboard/SKILL.md`](../../skills/site-and-dashboard/SKILL.md)
- [`skills/build-and-test/SKILL.md`](../../skills/build-and-test/SKILL.md)

The old files remain available in git history
(`git log --diff-filter=D -- docs/skills/`).
