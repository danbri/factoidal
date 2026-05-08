# Per-suite manifest dispatch (#235 Step 3 onward)

Each `<name>.yaml` file in this directory describes ONE test suite that the
W3C-tests workflow can run independently. The dispatch script (TODO: lands
alongside this README in the next commit) reads the manifest set, computes
the diff between the PR base and head, and emits a list of suites that need
to run for the current change.

## Manifest schema

```yaml
name: <Human-readable name>
spec: <URL to the canonical W3C/OGC/IETF spec, or "internal">
runner: <repo-relative path to the runner binary>
runner_args: [<list of CLI args>]
manifest: <repo-relative path to the test-corpus manifest, if any>
log_path: <repo-relative output path the runner writes>
result_path: <repo-relative path under docs/test-results/by-suite/>
triggers:
  paths:
    - <glob>
    - <glob>
  excludes:
    - <glob>           # paths under triggers.paths that should NOT trigger
foundational: false    # if true, ANY change in the foundational set fires
                       # this suite regardless of triggers.paths
domain: <track-id>     # one of RDF, RDFC, OWL, RIF, SHACL,
                       # SPARQL.QUERY, SPARQL.UPDATE, SPARQL.PROTOCOL,
                       # COTTAS, PERF
```

## Foundational set

Lives in [`_foundational.yaml`](./_foundational.yaml). Per
[`docs/designissues/2026-05-08-foundational-fstar-tier.md`](../../docs/designissues/2026-05-08-foundational-fstar-tier.md),
the budget is ≤ 10 paths.

## Adding a new suite

1. Create `<name>.yaml` here with the schema above.
2. Add the suite-specific runner if it's not one of the existing
   `bin/<consumer>/` runners.
3. Verify locally: run `tools/dispatch_test_suites.sh --diff <base> <head>`
   and confirm the manifest-driven dispatch picks up your suite for the
   right path changes.

## Why per-suite manifests

See [#235](https://github.com/danbri/factoidal/issues/235). One sentence:
re-running every suite on every push doesn't scale to the test catalogues we
need (OWL DL ~3000, JSON-LD ~800, SHACL ~400, GeoSPARQL ~150, ...) at full
fidelity, and the current ~50-minute monolithic pipeline is already
unreliable enough that public-dashboard staleness is a recurring complaint.
