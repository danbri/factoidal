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

## Step 0: verify fixtures exist (or every score below lies)

```bash
tools/ensure-test-env.sh          # init all 14 testing submodules + verify (idempotent)
tools/ensure-test-env.sh --check  # verify only, no network
```

Fixtures live in git submodules that fresh containers, git worktrees,
and CI runners do NOT populate automatically. A missing suite does not
error loudly — it shows up as a 0/0 dashboard row, a "0 tests" run, or
fixture-ENOENT test failures that look like engine regressions. Exit 1
from the script means: fix the environment before trusting any number.

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
| `jsonld_runner` | W3C JSON-LD 1.1 **toRdf** manifest (467 tests; not yet folded into generate-report — run directly). Score 2026-08-22 (re-measured, darwin-arm64): 467 pass, 0 fail, 0 skip (out of 467). The Lean 4 port's `lake exe l4jsonld-probe` (run from the repo root) scores the same 467 pass, 0 fail, 0 skip (out of 467) and additionally checks negative tests' error codes (103 of 106 match `expectErrorCode`). History: 2026-07-05 wave 9 was 399 pass, 57 fail, 11 skip | stdout |
| `jsonld_expand_runner` | W3C JSON-LD 1.1 **expand** manifest (§5.1 Expansion). F\* 2026-08-22: 385 pass, 0 fail, 0 skip (out of 385). Lean 4 (`lake exe l4jsonld-api`, run from the repo root) 2026-08-22: 385 pass, 0 fail, 0 local-override (out of 385) | stdout |
| `jsonld_compact_runner` | W3C JSON-LD 1.1 **compact** manifest (§6 Compaction: inverse context, IRI compaction, term selection, value compaction). F\* 2026-08-22: 245 pass, 0 fail, 1 local-override, 0 skip (out of 246). Lean 4 2026-08-22: 245 pass, 0 fail, 1 local-override (out of 246). The local-override is `#t0038` (a JSON-LD 1.0-only expectation that contradicts the suite's own 1.1 pin `#tp001`), argued in `tests/local-overrides/` | stdout |
| `jsonld_flatten_runner` | W3C JSON-LD 1.1 **flatten** manifest (§7 Flattening + node map generation). F\* 2026-08-22: 58 pass, 0 fail, 0 skip (out of 58). Lean 4 2026-08-22: 58 pass, 0 fail, 0 local-override (out of 58) | stdout |
| `jsonld_fromrdf_runner` | W3C JSON-LD 1.1 **fromRdf** manifest (§8.5 Serialize RDF as JSON-LD; `useNativeTypes`, `useRdfType`, both `rdfDirection` modes, RDF-collection-to-`@list`). F\* 2026-08-22: 53 pass, 0 fail, 1 local-override (out of 54). Lean 4 2026-08-22: 53 pass, 0 fail, 1 local-override (out of 54). The local-override is `#t0008` (the JSON-LD 1.0 partially-ordered list conversion) | stdout |
| `jsonld_html_runner` | W3C JSON-LD 1.1 **html** manifest (HTML Content Algorithms: `<script type="application/ld+json">` extraction, `<base href>`, fragment targeting, `extractAllScripts`; entries then run expand / compact / flatten / toRdf). F\* 2026-08-22: 50 pass, 0 fail, 0 skip (out of 50). Lean 4 2026-08-22: 50 pass, 0 fail, 0 local-override (out of 50) | stdout |
| — (Lean 4 aggregate) | `lake exe l4jsonld-api` covers expand + compact + flatten + fromRdf + html in one run: **791 pass, 0 fail, 2 local-override, 0 unsupported (out of 793)**, matching the F\* runners manifest for manifest, plus 140 of 144 negative tests producing the exact `expectErrorCode` the manifest names | stdout |
| `shex_runner` | ShEx validation suite (shexSpec/shexTest, 1182 entries; ShExJ-first with hand-translated twins in tests/shex-shexj-twins/ for ShExC-only fixtures; DEFERRED = construct beyond current stage, never guessed). Baseline 2026-07-29: 1182 pass, 0 mismatch, 0 local-override, 0 deferred, 0 skipped. (Until 2026-07-29 this read 1181 pass, 1 mismatch — the upstream start2RefS2.json p1-vs-p2 fixture defect, carried as a local override. Upstream commit 0f45c51 reconciled all three formats to p2 and added synchronization actions; the submodule was updated, the test now passes on its own merits, and the override file was deleted.) Validation uses descendant-witness semantics (arXiv 2503.24299), differentially confirmed against @shexjs/validator. Two more modes: `--differential` (ShExC-vs-ShExJ parse oracle over schemas/, 433 of 433 structurally equal — the Parser.ShExC positive floor) and `--negative-syntax` (the 100-fixture ShExC grammar-reject suite; 2026-07-10 baseline 100 pass, 0 fail, log `shex_negative_syntax_results.log`). The vendored tree-sitter-shexc comparison probe (advisory, three-way vs expected verdicts) is `tests/shexc-treesitter/run.sh` — see §comparison probes | stdout |
| `rml_runner` | RML (kg-construct suites, third_party/testing/rml-modules/). Baseline 2026-07-05: rml-core 76 pass, 0 fail (of 76); rml-io 17 pass, 15 fail (documented stage-4+ gaps), 41 logical-target skips (of 73) | stdout |
| `rif_runner` | W3C RIF Core: 4 vendored SPARQL-manifest cases (third_party/testing/rif/tc/) + the official Core_v1.22 corpus (46 tests, third_party/testing/rif-core-suite/). Baseline 2026-07-05 (goal wave): 34 pass, 4 labelled fails (1 KNOWN-DEFECT W3C-zip, 3 KNOWN-GAP), 12 precise skips naming the exact builtin/feature (of 50). DTB builtins in RIF.Core.Builtins.fst; safeness + import-rejection in RIF.Core.Conformance.fst; details in bin/rif-runner/README.md. NOTE: new extracted modules must be registered in THREE places — build-ocaml.sh's three lists. tests/unit/run-all.sh used to be a fourth (a frozen copy of COMMON_MODULES); by 2026-08-22 that copy had drifted 22 modules behind and every unit-test link died with 'No implementations provided: RDFS_Closure_SemiNaive', so run-all.sh now extracts the list from build-ocaml.sh at runtime and the fourth place no longer exists | stdout |
| `xml_runner` (`bin/linux-x86_64/xml_runner`, no `build-ocaml.sh` args — standalone `mktemp`-scratch compile, see `bin/xml-runner/README.md`) | W3C XML Conformance Test Suite (`xmlconf`, third_party/testing/xml/xmlconf/, jclark/sun/ibm/oasis/eduni/japanese collections). Assesses `Parser.XML.fst` + `XML.Wellformedness.fst` (informational NCName check only — its NCName production excludes `:`, so it's RDF/XML-domain, not generic XML) + `XML.Namespaces.fst` (new 2026-07-05 wave 2 — Namespaces-in-XML layer, gated to the `eduni/namespaces/{1.0,1.1}` collections only). 2026-07-08 integrity accounting (vacuous DOCTYPE-forced rejections no longer counted as passes): **244 real pass, 0 fail, 2341 skip (of 2585)**. A `not-wf` test counts as a pass only when the parser rejects it for the tested construct. The earlier **1442** was inflated: 1166 of those "passes" were vacuous (rejected only because `Parser.XML.fst` has no DOCTYPE/DTD production, so the reject is forced by that gap, not the documented construct) — now counted as SKIP, not pass (anti-patterns #3 / #25). `valid` bucket (labelled "wf-accept" — no DTD validation implemented) is 0/0/812: every `valid` test carries a DOCTYPE, so it's 100% `Skip "DOCTYPE/DTD not parsed"` (DTD slice plan: `docs/designissues/2026-07-08-xml-dtd-support.md`). `invalid`/`error` (275 tests) are always skip by design. `not-wf` is 244 real pass/0 fail/skip-balance (of 1498); of the skips, 1166 are vacuous DOCTYPE-forced and 32 are out-of-profile (not-wf only under XML 1.1 / Namespaces — the ibm xml-1.1 restricted-C1 and eduni rmt-ns10-042 colon-in-PITarget clusters; the parser accepts them since they are well-formed under its XML 1.0 non-namespace profile). Prolog PIs are now consumed per XML 1.0 §2.8 (un-skips 8 XSLT stylesheets: `xslt_runner` 22→25 pass). The wave-1 84 fails (non-character codepoints, XML declaration grammar, namespace-spec violations, epilog/trailing-content, comment `--`, `]]>`-in-text, attribute value/uniqueness, PI/decl target-name casing, 3 singletons) are now all fixed — per-cluster fix summary in `bin/xml-runner/README.md`'s "Wave 1 → wave 2" section; downstream SPARQL (631 pass, 0 fail) and RIF (30 pass, 8 fail, 12 skip — identical to the pre-change committed binary, so unchanged by this work) floors reverified after the `Parser.XML.fst` prolog-PI change, since it's also consumed by `Parser.RDFXML`/`Parser.RIFXML`/`Parser.SRX`; raw logs `.claude-runs/xml-runner-2026-07-05.log` (wave 1) and `.claude-runs/xml-runner-2026-07-05-fixed.log` (wave 2) | stdout |
| `xslt_runner` (`bin/linux-x86_64/xslt_runner`) | XSLT 1.0 transform conformance against `XSLT.Transform.fst` (slice 1). Default corpus = the slice-1-scoped subset of `w3c/xslt30-test` vendored at `third_party/testing/xslt/` (88 tests). Baseline 2026-07-17: **87 pass, 1 fail (of 88)** — the 1 fail is `node-1601` (`namespace::` axis, unmodeled). ⚠️ This corpus is a **regression pin**, not a conformance measurement: its selection criteria blocklist every unimplemented feature (see `docs/designissues/2026-07-17-xpath-xslt-coverage-matrix.md`) | stdout |
| `xslt_runner --base third_party/testing/xslt1-xalan` | **XSLT 1.0 conformance mirror** (Apache Xalan `xalan-test` `tests/conf`, Apache-2.0; submodule at `third_party/testing/xslt1-xalan/xalan-test-src` + generated `manifest.json`). 1690 test triples across 35 categories; same committed `xslt_runner` + F\*-extracted `XSLT.Transform` oracle, `--base` selects the corpus. Built to **surface** the coverage-matrix holes (namespace axis, translate/lang, xsl:number, key/generate-id, import/include, format-number/decimal-format, attribute-set, output attrs, …), so a large red count is expected and is the deliverable — the measured burndown target for the matrix. Baseline 2026-07-17 (no engine changes): **970 pass, 712 fail, 8 skip (of 1690)**; per-feature fail clustering in `third_party/testing/xslt1-xalan/INFO.txt`. Fresh-env restore + regen: `tools/ensure-test-env.sh`; `tools/gen-xslt1-xalan-manifest.py` | stdout |

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
- `json-ld/` — submodule of w3c/json-ld-api (vendored 2026-07-04).
  WIRED, and to more than toRdf: the toRdf, expand, compact, flatten,
  fromRdf and html manifests all have runners (table above), in both
  the F\* and Lean 4 trees. (Until 2026-08-22 this bullet read "Not yet wired"
  and "compact/flatten/frame are JSON-to-JSON, out of scope for an RDF
  engine" — both false by then: the F\* runners had been green for
  weeks and the Lean port matched them on all five manifests that day.
  A stale negative claim, exactly the kind the `obsolescence-sweep`
  skill exists to catch.) Framing IS still out of scope in both trees —
  a separate specification with a separate suite. The suite's "remote"
  context documents ship as local fixture files; read
  `docs/designissues/2026-07-04-jsonld-program-lessons.md` before
  touching this program.
- `shex/`, `csvw/`, `vc/`, `did/`, `rml/` — vendored for offline use.
  `csvw/`, `vc/` and `did/` have runners in both trees (F\* `csvw_runner`
  / `vc_runner`; Lean `Harness/CsvwJsonRun`, `CsvwRdfRun`, `l4vc-probe`);
  `shex/` has a Lean module and its runner status is in the
  `using-factoidal` capability matrix; `rml/` has no runner. (The earlier
  "not yet wired to any runner" line was stale by 2026-09-02.)
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
- `tests/web-demos/` — demo-specific checks (`lifesci_parity.sh`);
  `hub_browser_all.sh` drives headless Chromium over every docs-hub
  post (`docs/web/hub/NN-*.md`) to catch browser-only `observable-js`
  cell regressions node-side tests can't see — see
  `tests/web-demos/README.md`.

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

ShExC three-way grammar probe against tree-sitter-shexc (vendored at
`third_party/tree-sitter-shexc/`, MIT — provenance in its
PROVENANCE.md; never product code, never in the verified boundary or
shipped bundles): `tests/shexc-treesitter/run.sh` compiles the vendored
grammar with node-gyp and emits an expected × Parser.ShExC ×
tree-sitter agreement table over the shexTest positive schemas and
negativeSyntax fixtures. Advisory only — disagreements are triaged
(our bug / tree-sitter grammar bug / corpus defect), not scored;
dispositions live in
`docs/designissues/2026-07-10-shexc-treesitter-grammar-audit.md`.

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
| `verify-lean4.yml` | Lean 4 full-corpus gate: `lake build` of the whole tree (every `#guard`, every theorem) on each push to the main line; see `docs/20260831-lean-ci-gate.md` |
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

## Drift signal: a suite that runs but is never RE-run is a silent gap

The manifest system triggers a suite on a PR that touches ITS trigger
paths. That leaves two silent gaps, both surfaced by the 2026-07-19 audit:

1. A change that affects a suite TRANSITIVELY (not via its trigger paths)
   never re-runs it — its committed score drifts with no signal.
2. A suite with no manifest at all (the OWL 2 DL semantics catalogs had
   none) is never triggered even by relevant changes.

Proof it's real, not theoretical: committed `owl_type_inconsistency` +
`csvw` result logs predated their own source files by a day. The green
number on the dashboard was stale, not wrong-then — but nothing would have
caught a *real* regression either.

The durable fix (landed as `.github/workflows/conformance-rerun.yml`,
epic #235): a **scheduled** (daily cron + `workflow_dispatch`) job that
re-runs EVERY suite off the committed `bin/linux-x86_64` binaries via
`generate-report.sh --run` and commits refreshed logs back — so drift
becomes a visible scheduled-commit diff. Rules that follow:

- Every new suite gets a manifest AND is covered by the scheduled re-run
  (it is, automatically, if `generate-report.sh --run` invokes its runner —
  check that it does).
- Before quoting a suite's score as *current*, remember the committed log
  may be stale. If it matters, re-run the suite and read the LIVE number
  (committed binaries, no toolchain). Cross-ref `obsolescence-sweep`
  § "score-staleness trap."
- Auditing "what's silently untested": the dangerous pattern is a clean
  fully-dispositioned score nobody re-verifies — NOT a big labeled skip
  pool (those are honest). Labeled skips = good discipline; un-re-run
  scores = the hole.

## Reporting a correct-but-net-zero change honestly

Sometimes a spec-correct, F\*-verified fix flips ZERO tests because the
target cases have a SEPARATE blocker (e.g. the XML UTF-8-BOM skip was
correct per XML 1.0 §4.3.3, but its two BOM tests were also blocked by an
internal-DTD subset and an undecoded encoding; the SPARQL 1.2 UPDATE
VarOrIri-graph parser fix was necessary but the tests also needed the
runner-side `.trig` dataset load). Land these — correct behaviour and a
prerequisite are worth having — but label the commit and the report
**"net-zero conformance"** with the reason, NEVER as the "+N" you
predicted. Predicting +N and reporting +N when it was +0 is exactly the
misleading-score anti-pattern (#3/#25), just in a subtler form. Measure
before you claim the delta; re-baseline against the LAST landing's
numbers, not an older snapshot.

## Proving zero live callers before deleting verified code

Retiring dead F\* (or its shadow OCaml glue) is high-value cleanup, but
"dead" must be PROVEN, not assumed — and the audit doc that says something
is dead can itself be stale (2026-07-19: the boundary audit claimed Bet7
was "blocked on a Tot→ML cascade through `cottas_ondisk_row_to_quad`"; the
whole chain already had zero callers — the code had moved past the doc).
Before deleting a definition:

- grep for callers across ALL of `*.fst`, `formal/fstar/ocaml-output/*.ml`,
  `bin/*/*.ml`, `tests/unit/*.ml`, AND `experimental_ocaml_glue/*.sh`.
- **Distinguish real call sites from comment/prose references** — most
  hits on a retired name are historical `//` / `(* *)` / markdown
  mentions. A name in `cottas_memory_buffer_unit.ml` was pure comment;
  the live calls had migrated to the `_tok` variant.
- Watch for cross-module callers the local grep misses (a
  `Parser.Ballyhoo*` backend calling into the module you're pruning).
- Gate the deletion on the real suites (unit 47/47, the relevant
  conformance floors), not just "it still compiles" — a dead-code delete
  that changes a live number means it wasn't dead.

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
  `docs/claude-rules/current-state.md`). (Two former caveats are gone:
  since 2026-07-09 graph/result comparison is strict — RDFC-1.0
  canonicalization + byte-compare, ASK booleans evaluated, SELECT
  bnodes via canonicalized row reification; and since 2026-07-10
  `SPARQL11.Parser.fst` verifies with zero admits.)
- **Disposition taxonomy (owner directive 2026-07-10): a SKIP is
  actionable debt — something we intend to run one day.** Tests the
  upstream suite has WITHDRAWN (removed/deprecated as unsound) are a
  separate disposition, "withdrawn-upstream": excluded from the
  scorable denominator, never counted as skips, each carrying the
  upstream commit/date that removed it. Calling them skips pollutes
  the gap lists that direct work. Similarly keep "upstream fixture
  defect" fails annotated as such (e.g. the ShEx start2RefS2 twin
  mismatch) rather than silently patching around them. Precedent:
  vc_runner's `Withdrawn` outcome (3 fixtures, 117-scorable
  denominator, 2026-07-10).
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

## ⚠️ A green suite can measure nothing

A negative test ("X must NOT be entailed") is passed for free by an
engine that derives nothing. Measured 2026-07-31: **19 of 42** negative
tests across rdf-mt, rdf12-semantics and sparql11-entailment were
vacuous, while every W3C score stayed green. Run
`python3 tools/negative-test-vacuity.py` after any change to a rule set
or entailment regime, and read
[`skills/measuring-inference/SKILL.md`](../measuring-inference/SKILL.md)
for why a score alone cannot tell you whether the rules fired.

## ⚠️ A suite score certifies only the evaluated path

Learned 2026-08-02, the hard way. The engine has more than one
evaluation path for the same query: the W3C runner calls
`eval_select_query` (the pure algebra path), while `factoidal query`,
the npm bundle, and the HTTP server all route through
`SPARQL11.Store.eval_pattern_backend`. `FILTER EXISTS` was completely
broken on the backend path — every row dropped, both EXISTS and NOT
EXISTS empty at once — while the suite read **631 of 631**, because the
suite only ever exercises the runner's path. The score was true and
certified nothing about what users run. An external reviewer found it
in minutes of ordinary use.

Consequences for practice:

1. **When quoting a score, know which code path it certifies.** A
   public claim shaped "631 of 631 W3C SPARQL" implicitly claims the
   *product* conforms; if the runner path and the product path diverge,
   the claim is false in effect even though the number is exact.
2. **Every user-facing entry point carries its own pins** —
   `tests/local/cli_*.sh` run the actual CLI binary on actual W3C
   fixtures plus the reported repro shapes. The npm surface pins live
   in `npm/factoidal/test/`. A fix for any runner/user divergence adds
   its regression THROUGH THE USER PATH, so the next path split fails a
   test instead of a user.
3. **Path splits are load-bearing architecture, not plumbing detail.**
   `eval_pattern_backend` vs `eval_pattern` vs streaming fast-paths:
   when adding an arm to one, ask what the corresponding arm in the
   others does, and which suite would notice if they disagreed. Usually
   the answer is "none" — that is what the pins are for.

War story in full: issue #343; hazard #20 in
`skills/workflow-gotchas-debugging/SKILL.md`.
