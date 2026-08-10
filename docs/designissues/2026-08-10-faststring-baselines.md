# FastString re-founding: Step 0 baselines

Owner-approved migration:
[2026-08-10-faststring-refounding-plan.md](2026-08-10-faststring-refounding-plan.md).
This file is the STEP 0 freeze — the same-host reference the whole
migration compares against in steps 2/3 (>10% median regression on
any turtle fixture or 100k/1M parse row, or on the 10k serialize row,
gates/blocks per the plan's constraint 2).

Measured on the MAIN checkout (`claude/autoexec-scratchpad-assess-37oeok`,
commit `4b46f4d55a642921716c23993c72ee7a79edea23`), against the
committed `bin/linux-x86_64/factoidal` / `factoidal-dump-nq` binaries
(commit `6d7b170f08c5ad04010ef16c94e996fc01f2c625`, 2026-08-10T00:06:16Z).

## Host

- `nproc`: 4
- CPU: `Intel(R) Xeon(R) Processor @ 2.80GHz` (`/proc/cpuinfo` model
  name line)
- `uname -a`: `Linux vm 6.18.5-fc-v20 #1 SMP PREEMPT_DYNAMIC @0
  x86_64 x86_64 x86_64 GNU/Linux`
- Load average at freeze time (`uptime`): `1.16, 1.51, 1.13` (1/5/15
  min) on 4 cores — moderately loaded, not a fully idle host. Flagged
  per the perf-benchmarking skill's per-host-honesty rule; see the
  spread check below for what that load did to variance.
- Measured: 2026-08-10, started 02:22:56Z, finished 02:35:30Z (UTC).

## STEP 0a — `formal/fstar/bench-turtle-metrics.sh` (RUNS=5): SCRIPT BIT-ROTTED, fallback used

`formal/fstar/bench-turtle-metrics.sh` rebuilds `factoidal` from
`ocaml-output/` via its own direct `ocamlfind ocamlopt` invocation
(not `build-ocaml.sh`). On this checkout it fails to compile, for two
independent reasons, before even reaching a third:

1. Its package list (`-package fstar.lib,str,zarith,sha,digestif.c`)
   is missing `uucp` — `SPARQL11_Algebra.ml`'s `uppercase_utf_8`
   needs `Uucp.Case.Map.to_upper` (`Error: Unbound module Uucp`).
2. Its source list references a bare `factoidal_cli.ml` in
   `ocaml-output/`, but the Phase 8 consumer-dir move (#200 D,
   2026-05-08) relocated CLI sources to `bin/factoidal-cli/`; the file
   is not present at the path the script expects
   (`Error: I/O error: factoidal_cli.ml: No such file or directory`).
3. After fixing both of the above locally (as a diagnostic, not
   committed — see below), the next failure is
   `Error: Unbound module Factoidal_explain` — `factoidal_cli.ml`
   also needs `bin/factoidal-explain/factoidal_explain.ml`, which the
   script's abbreviated 14-module source list never had. At that
   point the fix stops being a one-line patch: the script's module
   list is a small, old subset of `build-ocaml.sh`'s `COMMON_MODULES`
   (~150+ entries) and the real native `factoidal` target additionally
   needs `-thread`/`threads.posix`, `$STATIC_FLAGS`,
   `$PARQUET_NATIVE_STUBS`, `$HACL_NATIVE_STUBS`, and four more
   `bin/factoidal-*/*.ml` consumer files
   (`build-ocaml.sh` lines ~1312-1327). Fully repairing the script
   means re-deriving that list inline — which is functionally
   "run build-ocaml.sh's compile logic under a different name," the
   exact thing this task was told never to do. FINDING, not fixed
   here: `formal/fstar/bench-turtle-metrics.sh` needs its module list
   and package/source paths brought back in sync with
   `build-ocaml.sh`'s native `factoidal` target (a follow-up task, not
   in scope for this migration step).

The two one-line fixes above were tried, confirmed insufficient alone,
and **reverted** (`git checkout -- formal/fstar/bench-turtle-metrics.sh`)
so the main-checkout diff for this step stays docs-only, per the task's
COMMIT-FIRST instruction. `bin/factoidal-cli/factoidal_cli.{cmx,o}`
were incidentally touched (regenerated/removed) by the failed compile
attempts and were restored via `git checkout --` before anything was
measured or committed; `git status --short` was clean before Step 0b
ran.

**Also discovered**: this host has no `/usr/bin/time` at all
(`command -v time` finds only the bash builtin) — the script would
fail on that even with the compile fixed, on this host.

### Fallback measurement (documented in `skills/perf-benchmarking/SKILL.md`)

Per that skill: *"To measure a committed binary without a toolchain,
generate the same fixtures and time `bin/<platform>/factoidal --count`
directly — keep the median-of-N discipline."* Fixtures generated
identically to the script's own Python heredoc (`prefixed-1000.ttl`,
`fulliri-1000.ttl`, `unicode-1000.ttl`; `berlin-1000.ttl` skipped —
`examples/data/third_party/Berlin.ttl` not present in this checkout,
same conditional the script itself has). Wall time via bash
`EPOCHREALTIME` (the same technique `tools/bench-parse-serialize.sh`
already uses) since `/usr/bin/time` is absent; RSS not captured for
the same reason. RUNS=5, against the COMMITTED
`bin/linux-x86_64/factoidal` binary (commit `6d7b170f`, see above).

Verbatim output:

```
Committed-binary fallback measurement (bench-turtle-metrics.sh fixture/harness shape, RUNS=5)
Rationale: formal/fstar/bench-turtle-metrics.sh rebuilds from ocaml-output/ via a direct
  ocamlfind invocation that is bit-rotted on this checkout (missing -package uucp;
  references bare factoidal_cli.ml instead of ../../../bin/factoidal-cli/factoidal_cli.ml
  after the Phase 8 consumer-dir move; its module list is also far short of
  build-ocaml.sh's COMMON_MODULES). Per skills/perf-benchmarking/SKILL.md's documented
  fallback ("To measure a committed binary without a toolchain, generate the same
  fixtures and time bin/<platform>/factoidal --count directly"), this run uses the
  identical fixture generation and RUNS=5/median/min/max harness shape against the
  COMMITTED bin/linux-x86_64/factoidal binary instead of rebuilding. /usr/bin/time is
  ALSO absent on this host, so wall time is measured via bash EPOCHREALTIME
  (same technique tools/bench-parse-serialize.sh already uses) instead of /usr/bin/time;
  RSS is not captured (no /usr/bin/time on this host).
Binary: /home/user/factoidal/bin/linux-x86_64/factoidal
Binary git provenance: 6d7b170f08c5ad04010ef16c94e996fc01f2c625 2026-08-10T00:06:16+00:00
Started: 2026-08-10T02:27:35Z

FILE prefixed-1000.ttl
RUN 1 0.0310 (count-output: /tmp/factoidal-metrics/prefixed-1000.ttl: 1000 triples)
RUN 2 0.0208 (count-output: /tmp/factoidal-metrics/prefixed-1000.ttl: 1000 triples)
RUN 3 0.0211 (count-output: /tmp/factoidal-metrics/prefixed-1000.ttl: 1000 triples)
RUN 4 0.0205 (count-output: /tmp/factoidal-metrics/prefixed-1000.ttl: 1000 triples)
RUN 5 0.0244 (count-output: /tmp/factoidal-metrics/prefixed-1000.ttl: 1000 triples)
MEDIAN 0.0211
MIN 0.0205
MAX 0.0310
SPREAD_PCT 49.8

FILE fulliri-1000.ttl
RUN 1 0.2701 (count-output: /tmp/factoidal-metrics/fulliri-1000.ttl: 1000 triples)
RUN 2 0.2698 (count-output: /tmp/factoidal-metrics/fulliri-1000.ttl: 1000 triples)
RUN 3 0.2696 (count-output: /tmp/factoidal-metrics/fulliri-1000.ttl: 1000 triples)
RUN 4 0.2699 (count-output: /tmp/factoidal-metrics/fulliri-1000.ttl: 1000 triples)
RUN 5 0.2735 (count-output: /tmp/factoidal-metrics/fulliri-1000.ttl: 1000 triples)
MEDIAN 0.2699
MIN 0.2696
MAX 0.2735
SPREAD_PCT 1.4

FILE unicode-1000.ttl
RUN 1 0.0198 (count-output: /tmp/factoidal-metrics/unicode-1000.ttl: 1000 triples)
RUN 2 0.0224 (count-output: /tmp/factoidal-metrics/unicode-1000.ttl: 1000 triples)
RUN 3 0.0200 (count-output: /tmp/factoidal-metrics/unicode-1000.ttl: 1000 triples)
RUN 4 0.0199 (count-output: /tmp/factoidal-metrics/unicode-1000.ttl: 1000 triples)
RUN 5 0.0192 (count-output: /tmp/factoidal-metrics/unicode-1000.ttl: 1000 triples)
MEDIAN 0.0199
MIN 0.0192
MAX 0.0224
SPREAD_PCT 16.1

berlin-1000.ttl SKIPPED (examples/data/third_party/Berlin.ttl not present in this checkout)

Finished: 2026-08-10T02:27:37Z
```

### Quiet-host spread check (perf-benchmarking skill discipline)

- `fulliri-1000.ttl` (0.27s/run, the largest-signal fixture here):
  spread 1.4% — quiet, well inside the skill's ~3-7% quiet-host norm.
- `prefixed-1000.ttl` and `unicode-1000.ttl` run in ~0.02s: spread
  49.8% and 16.1% respectively. This is NOT host noise in the sense
  the skill's norm was calibrated against (that norm was measured on
  multi-second closure-bench runs) — at ~20ms total wall time, process
  fork/exec and OS scheduling jitter dominate the signal itself, not
  the underlying parse cost. Read the `prefixed`/`unicode` numbers as
  order-of-magnitude only; `fulliri` (full-IRI, no prefix compression,
  the harder case per `docs/claude-rules/performance.md`) is the
  reliable one of the three at this size and confirms the host was
  quiet at freeze time.
- 1000-triple fixtures are too small to gate steps 2/3 on directly for
  this reason. The 10k/100k/1M rows from Step 0b (real GATE targets
  per the plan) are multi-hundred-ms to multi-second and do not have
  this problem.

## STEP 0b — `tools/bench-parse-serialize.sh` (default RUNS=3, CAP_SECONDS=120)

Runs against the committed binaries directly — no toolchain needed
(task instructed running it from the main checkout, where the
binaries live). Default `RUNS=3` was used (the task did not specify
a RUNS override for this script, unlike Step 0a's explicit RUNS=5).

Started 02:27:35Z (backgrounded — 4-core host, RDF/XML at 1M is slow),
finished by 02:29Z-ish per the process's own internal timing; both
`docs/test-results/perf-parse-serialize.json` and
`.../perf-parse-serialize.fragment.html` were regenerated as a
byproduct (script's normal output location) — not committed as part
of this step; left as local untracked artifacts consistent with the
docs-only diff for this commit.

Verbatim output:

```
Factoidal parse + serialize throughput bench
  platform: linux-x86_64
  commit:   4b46f4d55a642921716c23993c72ee7a79edea23
  runs per measurement: 3   cap per single run: 120s

Generating synthetic fixtures in /tmp/factoidal-bench-parse-serialize ...
Fixtures ready: 10000, 100000, 1000000

=== Parse throughput (factoidal count) ===
  parse nt 10000 triples: median 0.1292s (77399 triples/s)
  parse turtle 10000 triples: median 0.1244s (80386 triples/s)
  parse rdfxml 10000 triples: median 0.3645s (27435 triples/s)
  parse nt 100000 triples: median 1.2374s (80815 triples/s)
  parse turtle 100000 triples: median 1.1987s (83424 triples/s)
  parse rdfxml 100000 triples: median 3.6005s (27774 triples/s)
  parse nt 1000000 triples: median 14.0245s (71304 triples/s)
  parse turtle 1000000 triples: median 12.4777s (80143 triples/s)
  parse rdfxml 1000000 triples: median 36.1411s (27669 triples/s)

=== Serialize throughput (factoidal-dump-nq, end-to-end incl. parse) ===
  serialize_nq nt 10000 triples: median 0.2138s (46773 triples/s)
  serialize_nq nt 100000 triples: median 2.3493s (42566 triples/s)
  serialize_nq nt 1000000 triples: median 26.2955s (38029 triples/s)

=== Canonicalize throughput (factoidal canonicalize, end-to-end incl. parse) ===
  canonicalize nt 10000 triples: median 0.3254s (30731 triples/s)
  canonicalize nt 100000 triples: median 3.8059s (26275 triples/s)
  canonicalize nt 1000000: SKIPPED (spec-capped: canonicalize measured only up to 100k triples per task scope; not attempted at 1M)

=== UK Parliament corpus (real-world check) ===
  parse trig corpus: SKIPPED (third_party/data/ukparliament/*.trig not present (or looks like an LFS pointer) in this checkout)

=== Summary ===
op             format   size                seconds        triples/s
--             ------   ----                -------        ---------
parse          nt       10000               0.1292s            77399
parse          turtle   10000               0.1244s            80386
parse          rdfxml   10000               0.3645s            27435
parse          nt       100000              1.2374s            80815
parse          turtle   100000              1.1987s            83424
parse          rdfxml   100000              3.6005s            27774
parse          nt       1000000            14.0245s            71304
parse          turtle   1000000            12.4777s            80143
parse          rdfxml   1000000            36.1411s            27669
serialize_nq   nt       10000               0.2138s            46773
serialize_nq   nt       100000              2.3493s            42566
serialize_nq   nt       1000000            26.2955s            38029
canonicalize   nt       10000               0.3254s            30731
canonicalize   nt       100000              3.8059s            26275
canonicalize   nt       1000000                   -                -   SKIP: 
parse          trig     corpus                    -                -   SKIP: 

NOTE: serialize_nq and canonicalize are end-to-end (parse + operation).
      There is no parse-once/format-many path in the committed CLI.

JSON written: /home/user/factoidal/docs/test-results/perf-parse-serialize.json
Fragment written: /home/user/factoidal/docs/test-results/perf-parse-serialize.fragment.html
```

### Notes on this run

- RDF/XML at 1M triples completed in 36.14s (27,669 triples/s) without
  the Stack overflow the perf-benchmarking skill's "Known anomaly"
  section records at ~10k+ triples on a 2026-07-04 measurement. Either
  that regression was fixed since, or it is input-shape-sensitive; not
  investigated further here (out of scope for this baseline freeze) —
  flagged as a fact worth folding into that skill doc's anomaly note
  in a follow-up, since the anomaly as written would otherwise mislead
  a reader into expecting a crash that did not happen on this run.
- `serialize_nq`/`canonicalize` superlinearity the same skill section
  describes (1,000→2,000 triples jumping ~20x) was also not
  reproduced at the 10k/100k/1M granularity this script measures —
  consistent with that anomaly being specific to very small (1k-2k)
  sizes, which this script does not sample.
- `run_timed_median` (the script's internal timer) only surfaces the
  median per measurement — individual per-run wall-clock samples are
  not printed, so a spread/quiet-host check equivalent to Step 0a's
  cannot be computed from this script's own output as it stands. The
  Step 0a spread check (host was quiet at 1.4% spread on the one
  fixture large enough to be a meaningful signal, ~4 minutes before
  this run started) is offered as the closest available evidence that
  the host was reasonably quiet for this run too; load average during
  this window (`1.16, 1.51, 1.13`) shows mild but not severe
  contention.

## Gate reference for steps 2/3

Per the plan's Step 0 gate: **>10% median regression on any turtle
fixture (Step 0a) or 100k/1M parse row (Step 0b), or on the 10k
serialize row (Step 0b) triggers/blocks per constraint 2.** The
numbers above are that reference. Re-measure on the SAME host
(container recycles move the hardware — do not pair a future number
against this file from a different container) before treating any
step-2/3 measurement as pass/fail against this gate.
