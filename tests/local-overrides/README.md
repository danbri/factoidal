# Local overrides for carefully-disputed upstream fixtures

This directory is the project's **local-override layer**: a place to
record, per test, where we have *carefully disagreed* with a vendored
upstream conformance fixture and score against our own expectation
instead — without ever editing the vendored fixture itself (third-party
policy) and without silently inflating a pass count.

## Owner directive

> "if we carefully disagree with test make our own local override of
> it. Shex Also."
> — owner, 2026-07-17

This directory is the mechanism that directive asks for.

## The honesty invariant

An override is **never** folded into a plain pass. A runner that
consumes this layer reports an overridden test on its own per-test line:

```
PASS (local-override): <test name>
```

and carries a **separate labelled count** in its suite summary:

```
N pass, M fail, K local-overrides (out of T)
```

`K` is always shown distinctly from `N`. This is the same
no-misleading-scores discipline as CLAUDE.md anti-pattern #25: an
override is a *documented local disagreement*, not a clean upstream
pass, and the numbers must say so.

## The bar for adding an override ("carefully disagree")

Two things are required before a fixture may be overridden here — neither
is optional:

1. **A written analysis.** A prose explanation, checked into the repo
   (a runner comment, an `.fst` header comment, a `README.md`, or a
   ledger entry), that shows *why* the vendored fixture's expectation is
   wrong, contested, or internally inconsistent — not merely
   inconvenient to pass. "Our engine gives a different answer" is not a
   reason; "the fixture set contradicts itself and the spec authors
   never reconciled it" is.
2. **Upstream provenance.** A link to the upstream issue / commit /
   manifest that documents the defect or the version mismatch, so a
   later reader can re-check whether upstream has since fixed it. If
   upstream fixed it, the override must be removed and the fixture
   re-scored normally.

An override is a standing claim that *we are right and the vendored
fixture is wrong*. That claim must be auditable from the files in this
directory plus the analyses they cite. When in doubt, carry the failure
honestly instead of overriding it.

## File format

One JSON file per overridden test. Filename convention:
`<suite>__<test-id>.json` (the runner does not depend on the filename —
it reads every `*.json` here and filters by the `suite` field — so the
name is purely for humans).

| Field | Type | Consumed by runner? | Meaning |
|---|---|---|---|
| `test_id` | string | **yes** | The exact id/name the runner keys each test on (ShEx: `mf:name`; JSON-LD: the manifest `@id`, e.g. `#t0038`). |
| `suite` | string | **yes** | Suite key: `shex-validation`, `jsonld-compact`, `jsonld-fromrdf`, … The runner only applies overrides whose `suite` matches its own. |
| `dispute_kind` | string | partly | `verdict` (the disagreement is over a boolean pass/fail verdict — the runner also reads `our_expectation` and only overrides when the engine's actual verdict equals it) or `output` (the disagreement is over serialized output — the runner reclassifies the output-mismatch failure). |
| `our_expectation` | bool | **yes** (verdict kind) | The verdict our engine produces and that we assert is correct. For `verdict` overrides the runner requires the engine to actually produce this value before it will honor the override — a *different* wrong answer still fails. |
| `upstream_expectation` | bool/string | no (human) | What the vendored fixture expects. |
| `rationale` | string | no (human) | The disagreement, in prose. Should cite the written analysis. |
| `analysis_refs` | string[] | no (human) | Repo paths (with anchors) to the full written analysis. |
| `upstream_provenance` | string[] | no (human) | Upstream issue / commit / manifest links documenting the defect. |
| `date` | string | no (human) | When the override was added. |
| `owner_directive` | string | no (human) | The owner directive authorizing local overrides (quote above). |

Unrecognized fields are inert — the runners read named fields via the
F\*-extracted `Parser_JSON` and ignore the rest — so the human-facing
fields never affect scoring.

## How a runner consumes this layer

Each runner that participates reads every `*.json` here at startup,
keeps the entries whose `suite` matches its own, and:

- **ShEx validation** (`bin/shex-runner/shex_runner.ml`): when the
  engine's boolean verdict disagrees with the manifest's expected
  verdict, it checks for an override on that `test_id`. If one exists
  **and** the engine's actual verdict equals `our_expectation`, the
  outcome is reclassified `Override` (reported `PASS (local-override)`);
  otherwise it stays a real `MISMATCH`.
- **JSON-LD compact / fromRdf**
  (`bin/jsonld-compact-runner/`, `bin/jsonld-fromrdf-runner/`): the
  former skip entries are removed, so the disputed test now runs and
  produces an output-mismatch failure; if the failing `test_id` has an
  `output`-kind override, the outcome is reclassified `Override`.

## Current overrides

| File | Suite | Test | Why |
|---|---|---|---|
| `shex-validation__start2RefS1-IstartS2.json` | shex-validation | `start2RefS1-IstartS2` | Three-way vendored-fixture disagreement: `start2RefS2.json`/`.ttl` say predicate `p1`, `start2RefS2.shex` says `p2`; upstream shexSpec/shexTest#43 closed unreconciled. Our ShExJ-first policy scores against the JSON (`p1`), yielding `false`; the manifest's `true` depends on the `.shex` reading. |
| `jsonld-compact__t0038.json` | jsonld-compact | `#t0038` | The fixture's `option.specVersion=json-ld-1.0` expected output directly contradicts the *same suite's* 1.1 pin `#tp001`; one processing-mode-driven engine state cannot satisfy both, and this engine implements the 1.1 API. |
| `jsonld-fromrdf__t0008.json` | jsonld-fromrdf | `#t0008` | The fixture pins JSON-LD 1.0's partially-ordered RDF-collection-to-`@list` conversion; this engine implements the 1.1 fully-collapsing algorithm, which does not reproduce the 1.0-only partial shape. |
