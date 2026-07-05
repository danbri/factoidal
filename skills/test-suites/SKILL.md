---
name: test-suites
description: Run and interpret every test suite in the Factoidal project — W3C conformance (SPARQL 1.1, RDF 1.1/1.2 syntax, rdf-mt, RDF canonicalization, OWL 2), local regression scripts, cross-runtime parity (native/JS/wasm), Apache Jena ARQ comparison probes, running only the suites a diff touches (`tools/affected-tests.sh`), regression-pinning discipline (write the failing test before the fix, confirm it fails for the right reason), and the policy for importing external suites. Use when the user asks to "run the tests", "check conformance", "compare against Jena", to investigate a score change, when landing a bug fix and deciding which regression to write, or before claiming any change is done. Testing (with perf measured separately — see perf-benchmarking) drives everything in this project.
---

# Test suites: what exists, how to run them, what the numbers mean

**Backend rule (owner directive, 2026-07-04): semantic compliance is
claimed PER BACKEND, and every semantic regression test runs on all
backends.** The W3C scores exercise the in-memory evaluation path
only; the on-disk COTTAS path has its own search/scope code, and
every soundness bug found in 2026-07 (#261, the GROUP BY estimate
leak, #267 dataset semantics) lived exactly in that gap. Until #118
makes the F\* spec the single runtime for all storage layers (the
architectural fix — one verified semantics, storage as a data source
with equivalence lemmas), the cross-backend parity harness is the
detector: new semantic tests follow the
`graph_default_semantics_regressions.sh` pattern — same fixtures,
same queries, every backend, results diffed.

Every change in this repo is judged by test counts. Conformance and
performance are measured on **separate, repeatable harnesses and never
conflated**: this skill covers correctness; timing lives in the
`perf-benchmarking` skill. A change is not done until the suites that
cover it have been run and the numbers reported in full-sentence form
(anti-pattern #25: "631 pass, 0 fail (out of 631)", never "631/631"
without labels).

## Run only affected suites

For local iteration, don't run the full ~25-minute W3C battery on
every landing — `tools/affected-tests.sh` maps your diff to the
suites it actually touches (via the `.github/test-suites/*.yaml`
manifests + `tools/dispatch_test_suites.sh --diff`) and runs just
those, with a labelled pass/fail line per suite:

```bash
tools/affected-tests.sh                 # base=merge-base(origin/claude/main, HEAD)
                                         # head=working tree (incl. uncommitted changes)
tools/affected-tests.sh <base>          # explicit base, head=working tree
tools/affected-tests.sh <base> <head>   # explicit base and head (committed refs only)
tools/affected-tests.sh --only <suite>  # force-run one named suite, bypassing diff detection
```

It prints the plan (which changed paths fired which suites), runs
each affected suite's runner with its manifest's `runner_args`, and
SKIPs loudly (not silently) any suite whose runner binary isn't built
in this checkout. Touching a **foundational** path
(`.github/test-suites/_foundational.yaml`) fires every suite — that's
by design, not a bug in the tool.

**The full battery still gates release-grade landings** — nightly CI
(`.github/workflows/w3c-tests.yml`) and any multi-package landing
must still run the complete suite (`./w3c-tests.sh`) before those.
`affected-tests.sh` is a fast local signal, not a substitute.

## The one command

```bash
./w3c-tests.sh            # run the W3C suites, regenerate the dashboard
./w3c-tests.sh --cached   # regenerate dashboard from the last logs, no re-run
```

Run it **from the repo root** — the runner resolves fixture base URIs
via `Sys.getcwd()`; rdf-xml tests silently diverge (same triple counts,
different IRI strings) if CWD changes. The wrapper enforces this by
`cd`-ing to the repo root itself, so prefer it over calling the inner
script directly.

It wraps `formal/fstar/generate-report.sh`, which picks the platform
binaries from `bin/darwin-arm64/` or `bin/linux-x86_64/` (committed per
Iron Rule #9 — a fresh clone runs tests with **no F\*/opam toolchain**)
and drives three runners:

| Runner | Suites | Raw log |
|---|---|---|
| `w3c_runner` | SPARQL 1.1 query/update/protocol/service-description | `formal/fstar/ocaml-output/sparql_results.log` |
| `w3c_runner --rdf` | N-Triples, Turtle, N-Quads, TriG, RDF/XML, rdf-mt | `formal/fstar/ocaml-output/rdf_results.log` |
| `owl_runner` | OWL 2 RL PositiveEntailmentTests + 7 DL catalogs, each with its own timeout budget (60s–900s) | `owl_profile_rl_results.log` |
| `rdfc10_runner` | RDF Dataset Canonicalization (RDFC-1.0; SHA-256 + SHA-384 per-test via rdfc:hashAlgorithm; Map tests compared structurally per the suite README; NegEval via HNDQ work budget). Baseline 2026-07-05 (wave 8): **86 pass, 0 fail (of 86) — suite complete** | `rdfc10_results.log` |
| `shacl_runner` | W3C SHACL core suite (98 tests; full report-isomorphism compare by default, `--conforms-only` for the slice-1 floor). Baseline 2026-07-05 (wave 6): core 98 pass, 0 fail; sparql section (pass manifest path) 22 pass, 0 fail (of 22) — suite complete incl. custom constraint components | stdout |
| `jsonld_runner` | W3C JSON-LD 1.1 toRdf manifest (467 tests; not yet folded into generate-report — run directly). Score 2026-07-05 (wave 9): 399 pass, 57 fail, 11 skip; remaining clusters: @graph containers (needs the graph-name-vs-reference-identity rule — a naive fix regresses 22 tests, see wave-9 agent diagnosis), @import-sourced protected terms, nested lists in @list, IRI-resolve edge cases, JCS float formatting | stdout |
| `shex_runner` | ShEx validation suite (shexSpec/shexTest, 1182 entries; ShExJ-first, DEFERRED = construct beyond current stage, never guessed). Baseline 2026-07-05 (wave 8): 1022 pass, 11 mismatch, 123 deferred, 26 skipped. Mismatch remainder: 4 SemanticAction (out of scope), 3 non-normative extends edges, 1 recursive-schema stage-5 edge, 3 misc | stdout |
| `rif_runner` | W3C RIF Core: 4 vendored SPARQL-manifest cases (third_party/testing/rif/tc/) + the official Core_v1.22 corpus (46 tests, third_party/testing/rif-core-suite/). Baseline 2026-07-05 (wave 9): 11 pass, 3 fail, 36 skip (of 50) — skip buckets + fail diagnoses in bin/rif-runner/README.md (one fail is a 2010-era defect in the official W3C zip) | stdout |

Outputs: `docs/test-results/index.html` (dashboard),
`latest.csv` / `latest.json` (machine-readable),
`history/<iso-timestamp>.{csv,json}` (archive). These are
**CI-maintained on the main lines** — do not commit local
regenerations from feature branches; CI will overwrite them.

Known reporting gap: rdf-canon scores appear in `latest.csv` but are
not folded into `latest.json`'s RDF totals. Treat the CSV as the
complete record until that is fixed.

## Direct runner invocation

```bash
cd formal/fstar/ocaml-output   # or repo root — see CWD note above
./w3c_runner                   # all SPARQL suites
./w3c_runner --rdf             # all RDF suites
./w3c_runner --all             # both
./w3c_runner --list            # list suite names
./w3c_runner bind functions    # just the named suites
./w3c_runner -v aggregates     # verbose: full expected/actual rows on stderr
```

Scores as of 2026-07-03 (verify against
`docs/test-results/latest.json` rather than trusting this file):
SPARQL 631 pass, 0 fail; RDF 1031 pass, 0 fail — 1662/1662 runnable.
OWL 2 RL profile positive-entailment: 20 pass, 10 fail (out of 30).

## Where the test data lives

`third_party/testing/` (moved from `tests/w3c/` in 2026-04; the runner
keeps the old path as a fallback):

- `w3c/` — git **submodule** of `w3c/rdf-tests` (RDF 1.1 + SPARQL 1.1,
  plus RDF 1.2 via the `sparql-mixed-rdf-version-tests` branch).
  Without it the runner reports zero tests — and
  `generate-report.sh --run` will then happily **overwrite the
  committed logs and dashboard with a 0/0 result**. If a run reports
  "0 pass, 0 fail", the suite didn't run: init the submodules,
  `git checkout` the clobbered logs, and rerun. The two suites need:
  `git submodule update --init third_party/testing/w3c
  third_party/testing/rdf-canon` (full setup detail in the
  `fstar-env` skill, §6).
- `owl/` — vendored static drop of the W3C OWL 2 Test Cases.
- `rdf-canon/` — submodule, RDFC-1.0 canonicalization tests.
- `rif/tc/` — RIF test cases. The four RIF Core entailment tests run
  via `bin/rif-runner` (4 pass, 0 fail since 2026-07-05; supported
  subset documented in `docs/claude-rules/scope.md`). `w3c_runner`
  still reports its own RIF entries as skips — the runner of record
  is `rif_runner`.
- `json-ld/` — submodule of w3c/json-ld-api (vendored 2026-07-04; 837
  toRdf test files + manifests). Not yet wired; the conformance
  target is the **toRdf manifest only** (compact/flatten/frame are
  JSON-to-JSON, out of scope for an RDF engine), and the suite's
  "remote" context documents ship as local fixture files — see
  `docs/designissues/2026-07-04-jsonld-program-lessons.md` before
  touching this program.
- `shex/`, `csvw/`, `vc/`, `did/`, `rml/` — vendored for offline use,
  **not yet wired** to any runner.
- `third_party/data/ukparliament/` — perf-bench corpus (see
  `perf-benchmarking`).

Iron Rule #6 applies: run the real W3C files from disk. No synthetic
queries "inspired by" W3C tests. Never default to SPARQL 1.0 manifests
when 1.1 exists (Iron Rule #5).

## First-party harnesses under `tests/`

- `tests/unit/` — OCaml unit tests + `run-all.sh` (includes
  companion-file writer round-trips, UTF-8/codepoint semantics,
  RDF/XML perf repros).
- `tests/local/` — regression shell scripts:
  `sparql_parser_regressions.sh`, `sparql_negative_regressions.sh`,
  `backend_parity_regressions.sh`, `backend_parity_full.sh`,
  `cottas_corpus_regressions.sh`, `cottas_groupby_counts_regressions.sh`,
  `cottas_ask_decode_failure_regressions.sh`,
  `graph_default_semantics_regressions.sh`, `graphs_api_regressions.sh`,
  `jsonld_regressions.sh`, `parquet_footer_regressions.sh`,
  `serializer_unicode_regressions.sh`, `turtle_pretty_regressions.sh`,
  `check_pages_links.sh`. Each has a `local-*` manifest in
  `.github/test-suites/`, so `tools/affected-tests.sh --only
  local-<name>` runs any one of them directly. Run the ones touching
  your area before pushing. Environment notes: the COTTAS/parity/footer
  scripts need the pycottas venv at `_tmp.junk/pycottas-venv` (the
  session bootstrap hook provisions it); `sparql_parser_regressions.sh`
  additionally expects an external HDT corpus at `/tmp/Corpus3` —
  without it, 6 of its 7 checks fail on environment, not on code;
  `check_pages_links.sh` needs a fresh Eleventy build at `docs/_site`
  first.
- `tests/beyond-w3c/` — cross-runtime parity: every demo-page query in
  `tests/beyond-w3c/fixtures/index.json` runs on native and
  js-of-ocaml-under-Node via `tests/beyond-w3c/bin/run-parity.py`. Any non-zero exit is an engine crash unless the
  manifest declares a `known_failures` entry **pointing at an open
  GitHub issue**. CI: `.github/workflows/beyond-w3c.yml` (per-PR).
- `tests/web-demos/` — demo-specific checks (`lifesci_parity.sh`).

## Comparison probes against other engines

Jena ARQ probes (scripts in `tools/`, expect a Jena checkout at
`/tmp/jena` with `jena-arq/testing/DAWG-Final`):

```bash
tools/jena_arq_syntax_probe.sh   # syntax accept/reject parity
tools/jena_arq_basic_probe.sh    # SELECT execution, row-count compare
tools/jena_arq_graph_probe.sh    # named-graph semantics
tools/jena_arq_ask_probe.sh      # ASK
```

These deliberately compare **row counts**, not full result-set
isomorphism — fast signal, narrower claim. Findings and current scores
are logged in `docs/designissues/jena-arq-probe.md`,
`jena-arq-basic-probe.md`, `jena-arq-graph-probe.md`. Interesting Jena
disagreements get distilled into `tests/local/` regressions so the
probe environment isn't needed to keep the lesson.

Parser-count comparison against pyoxigraph:
`tools/compare_rdf_parser_counts.py` (see
`docs/designissues/2026-04-25-fstar-parser-vs-pyoxigraph-and-parquet-cli.md`).

## Importing external test suites

Policy from
`docs/designissues/2026-04-23-external-sparql-test-suites.md`:
licence-clean only (no GPL/AGPL anywhere in the chain); land as
`tests/external/<project>/` with provenance recorded in a
`THIRD_PARTY_NOTICES.md`. Ranked candidates: Oxigraph (planner
regressions, parser error-recovery), Eclipse RDF4J (SPARQL 1.2 draft
fixtures, SERVICE federation), Apache Jena (RDFS rule tests, pre-baked
BSBM). The single best idea found there: Jena's shaded-old-build
pattern — benchmark the current build against a **frozen older binary
of itself** (we already commit binaries, so a
`bin/<platform>/factoidal.v<N>` + diff script is cheap to add).

## CI: what runs when

| Workflow | Role |
|---|---|
| `w3c-tests.yml` | Heavy pipeline on main lines + nightly cron: debounced, dual-platform shadow builds to `bin/ci-<platform>/`, full suites, commits dashboard artifacts |
| `beyond-w3c.yml` | Per-PR native/JS parity over demo queries |
| `ukparliament-bench.yml` | Perf-regression gate (see `perf-benchmarking`) |
| `check-derived-files.yml`, `check-fstar-purity.yml`, `check-ocaml-output-cleanliness.yml`, `check-extraction.yml` | Boundary/extraction discipline gates (see `ocaml-boundary`) |
| `dashboard-refresh.yml`, `deploy-pages.yml` | Publishing (see `site-and-dashboard`) |

`.github/test-suites/*.yaml` holds one manifest per suite (runner,
args, log path, `domain`, `foundational`, trigger paths) — this
covers both the W3C corpora (`rdf-*`, `sparql11-*`, `owl-profile-rl`,
`rdfc10`, `jsonld-tordf`) and the `tests/local/*.sh` regression
scripts (`local-*` manifests). `tools/dispatch_test_suites.sh --diff
<base> [<head>]` computes which suites a change touches — the
scaling plan for when OWL DL (~3000), JSON-LD (~800), SHACL (~400)
tests are wired in — and `tools/affected-tests.sh` (see "Run only
affected suites" above) wraps it with actual execution. When you add
a suite (W3C or local script), add its manifest.

## Regression-pinning discipline

When fixing a bug, write the regression BEFORE rebuilding, assert the
FIXED behavior, and run it against the current (broken) binary to
confirm it FAILS for the expected reason. That pre-fix failing run is
the proof the test bites; paste it in the report/commit. Two
refinements from 2026-07-04:

- If a future improvement could make the fixture stop reproducing the
  setup condition (e.g. a decoder gets smarter and the "undecodable
  column" fixture decodes), have the script self-check the condition
  and SKIP loudly instead of passing vacuously
  (`cottas_ask_decode_failure_regressions.sh` pattern).
- A strict external consumer is a regression test you didn't have to
  write: the npm entry's JSON.parse caught a weeks-old escaper bug
  the suites never fed. When adding a serializer/writer, give its
  output to the strictest available parser somewhere in the battery.

## Reporting discipline

- Full-sentence scores, labelled numerators and denominators, always
  (anti-pattern #25). Distinguish pass-vs-fail from pass-vs-total when
  skips exist.
- Regressions block: if a previously passing test fails, diagnose
  before committing. Run the affected suites before AND after.
- Disclose the standing caveats whenever claiming "verified" or
  quoting scores in public prose (from
  `docs/claude-rules/current-state.md`): ASK comparison does not check
  the expected boolean; blank-node comparison is
  any-bnode-matches-any, not graph isomorphism;
  `SPARQL11.Parser.fst` is ~65% under `--admit_smt_queries true`.
- Scope changes (a test becoming a permanent SKIP, or un-skipped) must
  update `docs/claude-rules/scope.md` **in the same commit**.
- Cap ad-hoc runs at 10 minutes (`timeout 600`, anti-pattern #17); log
  long runs under `.claude-runs/` (#19).

## What this skill does NOT cover

- Building the runners — `build-and-test` skill.
- Making the verify/extract/compile loop itself fast — this skill's
  `affected-tests.sh` cuts down which suites you run once you have a
  binary; cutting down the build that produces the binary is
  `fast-verify-extract`.
- Timing/perf measurement — `perf-benchmarking` skill.
- Publishing scores to the site/dashboard — `site-and-dashboard` skill.
- Toolchain setup — `fstar-env` skill.
