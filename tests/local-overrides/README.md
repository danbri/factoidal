# Local test overrides

A **local override** records a deliberate, documented disagreement
between this project and a specific upstream conformance fixture — a
case where the fixture's stated expectation cannot be met without
being *wrong*, because the fixture data itself is defective.

An override is a **disposition, not a semantic change**. The engine
pipeline still runs unchanged and still reports its real answer; the
override only reclassifies one named, justified divergence out of the
`FAIL` bucket into a distinctly-counted `local-override` bucket, so a
suite can reach exit 0 without hiding the divergence. Nothing here
alters RDF / SPARQL / RIF reasoning — this is test-harness
bookkeeping consumed by the per-suite runner (a rule #11 consumer),
which is why override loading lives in `bin/<suite>-runner/` and not
in any `.fst` module.

## Convention

```
tests/local-overrides/<suite>/<TestName>.override
```

- One file per overridden test. The **file count per suite is the
  suite's "local-override" count** — a runner reports overrides
  separately from plain passes and from fails.
- Each `.override` is a small header block of `key: value` lines,
  then a `---` line, then free-text rationale. Runners parse only the
  header keys they key on (`test`, `disposition`); the rationale body
  is for humans.

### Header keys

| key             | meaning                                                        |
|-----------------|----------------------------------------------------------------|
| `suite`         | which suite this override belongs to (e.g. `rif`)              |
| `test`          | the exact test name the runner emits (the match key)          |
| `category`      | the upstream test category (e.g. `PositiveEntailmentTest`)    |
| `upstream-result` | what the fixture manifest expects                            |
| `our-result`    | what our pipeline actually computes                            |
| `kind`          | why they differ (e.g. `corpus-data-defect`)                    |
| `disposition`   | must be `local-override` for a runner to honour the file       |
| `date`          | when the override was authored                                 |
| `provenance`    | where the defect was confirmed upstream                        |

## Runner contract

A runner that honours overrides MUST:

1. Only apply an override when the test's observed outcome is the
   expected divergence (a real `FAIL`). An override never masks a
   `PASS` — if an overridden test starts passing on its own, the
   runner flags the override as **stale** (removable) and counts a
   plain pass, never a silent success.
2. Count honoured overrides in a distinct bucket, printed on its own
   line, excluded from the fail count (so a suite whose only reds are
   dispositioned overrides can exit 0).
3. Never let an override change any computed result — the pipeline
   output that the override reclassifies must be the same output the
   runner would print without the override file present.

Because an override is a standing disagreement with a published test,
each file must carry enough provenance for a reviewer to confirm the
defect independently.
