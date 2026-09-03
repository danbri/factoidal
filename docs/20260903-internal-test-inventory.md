# Internal test inventory and the `internal-tests.sh` runner

Scope: every project-internal test asset — the ones that check this
repository's own code against its own expectations, not against a W3C
test manifest. The W3C conformance suites (RDF, SPARQL, OWL, SHACL,
CSVW, JSON-LD, XSLT, ...) already have a runner (`w3c-tests.sh` /
`formal/fstar/generate-report.sh` for the F* tree; per-suite dispatch
via `tools/dispatch_test_suites.sh` for suites whose manifest `spec:`
field is a real W3C/OGC/IETF URL) and a score. This document and
`tools/internal-tests.sh` cover what did not have either: internal
regression scripts, Lean corpus probes, and the Node test suites.

Method: read the tree at the date of this note (2026-09-03,
`claude/main`, darwin-arm64), plus one real run of every suite found.
Where a suite could not run in this environment, the reason is stated;
where it ran and failed, the cause is stated to the depth the task
allowed (root-caused where cheap, named as an open question otherwise).

Reproduce with `tools/internal-tests.sh --list` (derives the same list
from the tree) and `tools/internal-tests.sh` (runs it).

## Result, this run

```
internal-tests TOTAL: 70 pass, 40 fail, 16 skip (out of 126)
```

`--quick` (60s per-suite budget): 68 pass, 40 fail, 18 skip (out of
126) — the two extra skips are `lean-probe-l4rdfs-semi` (92s) and
`w3c-persisted-census` (54s), both of which pass when given the full
budget.

`shellcheck` is not installed in this environment; the `shellcheck
tools/internal-tests.sh` gate could not be run.

## Categories

| Category | What it is | How invoked | Typical time | This run | In `.github/workflows/`? |
| --- | --- | --- | --- | --- | --- |
| `lean-guard-build` | Every `#guard` in `formal/lean4` (build-time check) | `lake build` in `formal/lean4/` | a few seconds, warm cache | PASS — 7,026 `#guard` declarations across 281 modules | yes, `verify-lean4.yml` (`lake build L4Factoidal`) |
| `lean-wasm-native-smoke` | 63 checks of every Wasm dispatch ABI op | `formal/lean4/Wasm/native-smoke.sh` | ~5s | PASS | no |
| `lean-wasm-cli-smoke` | Every verb of the `l4factoidal` CLI | `formal/lean4/Wasm/cli-smoke.sh` | ~1s | PASS | no |
| `lean-probe-*` (30 zero-arg probes) | Corpus census/conformance probes declared `lean_exe` in `formal/lean4/lakefile.lean` (OWL, Turtle, RDFC-1.0, JSON-LD ×3, CSVW ×3, SPARQL syntax, VC, SHACL ×3, XML conf, XSLT, GRDDL, ShEx ×2, RIF, RML, Schematron, MathML, JSON Schema, property-based, HDT, RDFS semi-naive) | `lake exe <name>`, no arguments | most <5s; `l4owl-probe` ~30s, `l4rdfs-semi` ~90-115s | 27 PASS, 3 FAIL (`l4owl-probe`, `l4xslt`, `l4grddl` — see Findings), 2 SKIP (`l4w3c`, `l4diff` — these take required arguments, see below) | no |
| `node-hub-tests` | `tests/hub/*_test.mjs`, one per docs-hub post, against the JS/wasm bundle | `node --test tests/hub/*.mjs` | ~25-40s | PASS — 415 pass, 0 fail, 1 skip (out of 416) | no |
| `node-npm-tests` | `npm/factoidal/test/*.test.js` | `node --test npm/factoidal/test/*.test.js` | ~5-10s | PASS — 252 pass, 0 fail, 2 skip (out of 254) | no (a subset, `test/l4-core.test.js`, runs in `npm-publish-lean.yml`) |
| `blockengine-*-smoke` (16 non-Postgres) | Shardborough pack/activate/query/compact/delta regressions | `bash tools/blockengine-*-smoke.sh` | <15s each | 12 PASS, 4 FAIL (see Findings) | no |
| `blockengine-postgres-*-smoke` (2) | PostgreSQL bytea host-boundary smoke | `bash tools/blockengine-postgres*-smoke.sh` | needs a live `psql` server | SKIP — no PostgreSQL server reachable on 127.0.0.1 in this environment | no |
| `w3c-persisted-census` | Executability + row-agreement census of W3C SPARQL QueryEvaluationTests through the persisted (pack→activate→query) path — NOT a conformance score | `bash tools/w3c-persisted-census.sh` | ~55-80s | PASS — 564 of 570 eligible entries executed, 564/564 matched the reference engine, 6 refused at query (named-graph subset) | no |
| `podman-fly-smoke` | UK Parliament dataset bundle smoke via Podman | `sh tools/podman-fly-smoke.sh` | needs a running podman machine | SKIP — podman machine not started in this environment | no |
| F* internal suite registry (20 manifests) | Every `.github/test-suites/*.yaml` whose `spec:` field is `internal` (as opposed to a W3C/OGC spec URL) — `tests/unit`, the `tests/local/*_regressions.sh` COTTAS/parser/serializer/graph suites, `toan-matrix`, `check-pages-links`, `negative-test-vacuity` | `tools/dispatch_test_suites.sh --list` + `--field <suite> spec/runner/runner_args`, then run the named runner | most <5s | 6 PASS, 13 FAIL, 1 SKIP (see Findings) | not directly; this is the registry the W3C-tests workflow dispatches from, per suite, on path triggers |
| Orphaned `tests/*/run.sh` (4: `known-defects`, `vc-api-shim`, `rdf-mt-generated`, `shexc-treesitter`) | Standalone regression harnesses that are not the `runner:` of any `.github/test-suites/*.yaml` manifest | `bash tests/<name>/run.sh` | <10s | 3 PASS, 1 FAIL (`known-defects` — by design when a tracked defect stops reproducing; see Findings) | no |
| Orphaned `tests/local/*.sh` (35 of 52; the other 17 are registered runners in the F* internal suite registry above) | Ad hoc regression scripts covering CLI parity, CoTTAS storage stages, durable-update crash/compaction, RDFS entailment regimes, Turtle/TriG undeclared-prefix handling, full-text, geo, RML pushdown, SPARQL client protocol | `bash tests/local/<name>.sh` | <2s each | 16 PASS, 19 FAIL (see Findings — dominated by two environment gaps, not per-test logic bugs) | no |
| `tests/web-demos/*.sh` (10) | Headless-Chromium (Playwright) smokes of the docs-hub pages | `bash tests/web-demos/<name>.sh` | needs Playwright + a built site | SKIP — no `node_modules/` (Playwright) installed at the repository root in this environment | no |
| `tests/beyond-w3c` parity | Demo-query row-set parity across runtimes (native/JS/wasm) for the public site's live query cells | `python3 tests/beyond-w3c/bin/run-parity.py --manifest tests/beyond-w3c/fixtures/index.json --runners native` | ~1-3s (native only; JS/wasm runners exist but were not exercised here) | PASS — 2 of 2 fixed queries | no |
| `tests/did`, `tests/did-local`, `tests/local-overrides`, `tests/qudt`, `tests/compat/rdf12` | Fixture directories | consumed by `bin/did-runner`, `bin/qudt-runner`, and the F* `w3c_runner`'s local-override mechanism | n/a | out of scope here — already run by `w3c-tests.sh` | yes, via `w3c-tests.yml` |
| `tests/parity/run_backend_parity.py` | Full corpus-driven in-memory-vs-COTTAS parity | invoked WITH the required `--manifest`/`--bin`/`--pycottas-python` args by `tests/local/backend_parity_regressions.sh` and `tests/local/backend_parity_full.sh` (both already counted above) | n/a standalone | not run directly — it is a library the two registered wrapper scripts call | no |
| `tests/perf/l4_vs_fstar_wasm_bench.mjs` | Lean-wasm vs F*-wasm/js query-time benchmark | `node tests/perf/l4_vs_fstar_wasm_bench.mjs` | a benchmark, not a pass/fail test | out of scope here — see `skills/perf-benchmarking` | no |

Total suite count this run: 126 (from `tools/internal-tests.sh --list`,
2026-09-03). This number moves as scripts are added or removed; treat
the count in this document as a snapshot, and `--list` as the source
of truth.

## Findings

Ordered by how many suites they explain, most first. None of these
were fixed in this landing; each is either a filed defect (VC. GitHub
issue numbers are named where one already exists) or a plain
environment gap.

1. **Wrong-platform binary at `formal/fstar/ocaml-output/<tool>`
   (17 of 52 `tests/local/*.sh`, plus `local-graphs-api`,
   `local-jsonld-regressions`, `local-parquet-footer-version-gate`,
   `local-parser-unicode`, `local-sparql-parser`, `local-turtle-pretty`,
   `local-serializer-unicode`, `rdf-mt-generated`).** CLAUDE.md iron
   rule #9 states these symlinks "point at the current platform's
   `bin/` dir". In this darwin-arm64 checkout they were committed
   pointing at `bin/linux-x86_64/*` (`git show HEAD:formal/fstar/
   ocaml-output/factoidal` → `../../../bin/linux-x86_64/factoidal`, an
   ELF binary; running it gives `Exec format error`).
   `tools/sandbox-bootstrap.sh` has the correct repair logic (lines
   ~73-79) but only acts `if [[ ! -e ... ]]` — it will not repoint a
   symlink that already exists and is simply wrong for this platform.
   Repointing the 11 of 12 affected symlinks that have a
   `bin/darwin-arm64/` counterpart (working-tree only, not committed —
   see below) turned six previously-failing suites to PASS in this
   run. `bin/darwin-arm64/factoidal-dump-nq` is missing outright (no
   darwin-arm64 build of that consumer tool is committed), so
   `local-serializer-unicode` still fails for that reason alone.
   Separately, `tools/negative-test-vacuity.py` and
   `tests/local/rdfs_schema_split_regressions.sh` /
   `turtle_undeclared_prefix_regression.sh` hardcode
   `bin/linux-x86_64/factoidal` directly rather than going through the
   symlink, so repointing the symlink does not fix them — 17 of the 52
   `tests/local/*.sh` scripts hardcode a `linux-x86_64` path this way.
   Not fixed here: the committed symlink target is a CI-vs-local
   trade-off (CI runs `ubuntu-latest`), not a one-line "correct" value,
   and the hardcoded paths are a separate, larger cleanup.
2. **`_tmp.junk/pycottas-venv/bin/python` not provisioned (16 of 52
   `tests/local/*.sh`, plus `local-backend-parity`,
   `local-backend-parity-full`, `local-cottas-ask-decode-failure`,
   `local-cottas-corpus`, `local-cottas-groupby-counts`,
   `local-cottas-row-order`, `local-graph-default-semantics`,
   `local-parquet-footer`, `dict_global_cache_parity`,
   `durable_update_stage3`, and others).** The session bootstrap hook
   provisions this venv; a worktree built only from
   `tools/ensure-test-env.sh` (this task's instructed setup) does not
   get it. Environment gap, not a defect — same root cause across all
   of these.
3. **Query-plan `open-mode` descriptor strings have drifted from three
   `blockengine-*-smoke.sh` assertions.**
   `blockengine-ibk3-w3c-disk-query-smoke.sh` expects
   `open-mode=ibk3-paged-merkle-full-manifest(3)` and gets
   `open-mode=ibk3-sri2-tli1-subject-point(3)`;
   `blockengine-sbm6-synthetic-smoke.sh` expects
   `open-mode=ibk3-sri2-tli1-oli2-object-subject-join(2) delta=base`
   and does not find it in the actual output;
   `blockengine-shard-merkle-scan-smoke.sh`'s final `grep -q
   'open-mode=predicate-selective-merkle-limit-prefix(1)'` does not
   match either. Rows returned are correct in all three; the query
   planner now names its access path differently (a new
   subject-point/join index mode superseding what these scripts still
   name). Test staleness against a planner improvement, not a
   correctness regression — needs a decision on whether to update the
   three scripts' expected strings.
4. **`blockengine-shard-session-smoke.sh` checks for
   `store/manifest.sbm1`; `l4block-shard-pack` now writes
   `manifest.sbm2`.** Confirmed by running `l4block-shard-pack`
   directly: it reports `format=predicate-ibk2-merkle-v2-streaming
   ... manifest=manifest.sbm2 wire-version=2`. The script's `test -s
   .../manifest.sbm1` assertion is checking a filename the packer
   stopped writing; per `shardborough-storage`, a wire-format version
   bump should update every consumer, and this script was missed.
5. **`tests/unit/run-all.sh` fails at the `ocamlfind ocamlopt` build
   step for all 50 files with `line 262: TEST_CMX[@]: unbound
   variable`**, even though `TEST_CMX=()` is set immediately before the
   loop that populates it (line 242) and bash 5.3 (confirmed on this
   host) does not reproduce the empty-array-under-`set -u` bug that
   affected older bash. Root cause not found within this task's time
   box — it is a harness bug (every file fails identically at the
   build step, before any file-specific compilation is attempted), not
   50 independent regressions. Needs its own investigation.
6. **`tests/known-defects/run.sh`: 3 of 5 tracked defects no longer
   reproduce (XPASS), 2 probes errored.** XPASS on
   [#324](https://github.com/danbri/factoidal/issues/324) (`sameTerm`
   case-folding), [#334](https://github.com/danbri/factoidal/issues/334)
   (Turtle silently drops undeclared-prefix statements — now exits
   126), and [#275](https://github.com/danbri/factoidal/issues/275)
   (syntax-error message). ERROR on
   [#336](https://github.com/danbri/factoidal/issues/336) (probe
   produced no rows — query or binary changed) and
   [#337](https://github.com/danbri/factoidal/issues/337) (BGP itself
   did not match; probe invalid). The suite is designed to fail loudly
   on exactly this signal (its own header: "not automatically good
   news ... either somebody fixed it ... or the probe has drifted").
   This needs an owner decision per issue, not a fix inside this task.
7. **`tests/local/cottas_corpus_regressions.sh` is missing the
   executable bit** (`-rw-r--r--`, siblings are `-rwxr-xr-x`). A direct
   exec (`"$runner" args`, the pattern `tools/dispatch_test_suites.sh`-
   style dispatch would use) fails with `Permission denied`;
   `internal-tests.sh` invokes every runner via `bash "$runner"` for
   this reason, which works. Not fixed in the tree (a one-line `chmod
   +x`, left for a dedicated hygiene commit).
8. **`local-check-pages-links` needs `docs/_site` built**
   (`cd docs && npx @11ty/eleventy --output=_site`) and
   **`local-sparql-negative` needs a Jena ARQ checkout at
   `/tmp/jena/jena-arq/testing/DAWG-Final`** — both external build/
   fixture prerequisites, not provisioned by
   `tools/ensure-test-env.sh`. Environment gaps.
9. **`l4owl-probe`, `l4xslt`, `l4grddl` fail with known, already-scored
   gaps**, not new regressions: `l4owl-probe` reports `TOTAL: 1131
   pass, 316 fail, 2 skip, 8 unsupported (out of 1457)` — closure gaps
   already tracked in the probe's own per-catalog breakdown against
   `docs/test-results/latest.json`; `l4xslt` reports `84 pass, 3 fail
   (out of 87 decided)`; `l4grddl` reports `19 pass, 22 fail (out of 41
   decided)`, of which 7 failures are stated upstream http/https
   vendoring drift and 17 cases are unavailable (documents not
   fetched, by design — the runner makes no network request).

## What the runner does NOT cover

- The W3C conformance manifests (`w3c-tests.sh`,
  `formal/fstar/generate-report.sh`, and every `.github/test-suites/
  *.yaml` whose `spec:` is a real spec URL) — those have their own
  runner and score already.
- `tests/perf/*` — a benchmark, not a pass/fail gate
  (`skills/perf-benchmarking`).
- `tests/vc-di-eddsa/run.sh` and `tests/vc20-api/run.sh` — registered
  in the W3C-suite dispatch registry (`spec:` is a real
  `w3c.github.io` test-suite URL), already excluded for the same
  reason as the conformance manifests. Both also need `npm install` in
  their vendored submodule directories, not run in this environment.

## CI proposal (not wired in this commit)

Add a `internal-tests-quick` job to a new or existing workflow, gated
the same way `verify-lean4.yml` is (push to `claude/main`, PR,
`workflow_dispatch`):

```yaml
  internal-tests-quick:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with: { submodules: recursive }
      - run: bash tools/ensure-test-env.sh
      - run: bash tools/internal-tests.sh --quick
```

On `ubuntu-latest` the `bin/linux-x86_64/*` symlinks are already
correct, so Findings 1 and most of Finding 2's provisioning gap would
not appear there — CI would measure closer to the suites' real
pass/fail than this darwin-arm64 run did. Left as a proposal, not
landed, per this task's scope.
