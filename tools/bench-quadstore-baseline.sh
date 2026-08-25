#!/bin/bash
# tools/bench-quadstore-baseline.sh
#
# Quad-store performance BASELINE, run against the COMMITTED platform
# binaries (bin/<platform>/factoidal) only -- no F* toolchain, no
# rebuild. Companion to tools/bench-parse-serialize.sh (parse/serialize
# throughput); this one measures the COTTAS store path: cold import
# time, on-disk size, and query latency, against the SAME queries
# through the in-memory parse path -- so the report shows the
# store-vs-memory gap. Workstream A of the persistence program,
# https://github.com/danbri/factoidal/issues/595.
#
# Conventions followed from tools/bench-parse-serialize.sh: committed
# binaries only; deterministic synthetic fixtures; median of RUNS (3);
# per-run `timeout` (CAP_SECONDS, 120) with a cap trip recorded as a
# documented skip, never a silent omission (anti-pattern #17); every
# exit code captured explicitly, never `|| true` (anti-pattern #14).
#
# --- Two writers, and why both appear here -----------------------------
# `factoidal cottas-import` is the documented import verb (a thin exec
# wrapper around tools/corpus_pipeline.py -> pycottas/DuckDB). This
# script measures its cold wall time and on-disk size, as asked.
# BUT: as of issue #445 (2026-08-15, landed 10 days before this
# baseline), the committed reader's format-compatibility gate
# (`RDF.CottasStore.cottas_ondisk_version_ok`, checked in
# `cottas_ondisk_open`) accepts ONLY files stamped with
# `Parquet.Footer.cottas_format_version` (445) in the Parquet
# FileMetaData.version field -- a value only `RDF.CottasStore.
# BaseWriter.fst`'s native writer stamps. DuckDB/pycottas writes the
# Parquet-conventional version field, so a `cottas-import`-produced
# store is REJECTED on open by this binary ("was not written by this
# store's current writer (FileMetaData version mismatch)"). This
# script verifies that rejection ONCE (fast) and records it as a
# top-level, documented finding rather than retrying a doomed query at
# every size. The only writer whose OUTPUT the committed reader
# currently opens is the native `factoidal import --nq FILE --out DIR`
# path, so query-latency measurements (store path) use THAT writer's
# stores; `cottas-import`'s own numbers stay to cold-time + size only.
# This is a measurement finding, not a fix -- report only.
#
# --- Fixture format: N-Quads for both paths, not N-Triples/Turtle -----
# The task brief asks for "the SAME three queries through the in-memory
# Turtle parse path". This script uses N-Quads (.nq) for BOTH the
# store-import source and the in-memory `--data` query path instead of
# a separate Turtle fixture: N-Quads is a syntactic superset of the
# Turtle triple form used elsewhere in this repo's benches, and reusing
# one fixture file isolates the store-vs-memory variable from a
# parser-format variable that this bench is not trying to measure
# (tools/bench-parse-serialize.sh already covers format-vs-format
# parse cost). Documented deviation, not a silent one.
#
# --- Disk: fixtures/stores land on tmpfs, not the repo's disk ---------
# The container's root filesystem (which /tmp and the repo checkout
# share) was measured near-full at harness-authoring time (`df -h /`:
# well under 1 MiB free). Fixture and store generation targets
# /dev/shm (tmpfs, ~16G, measured empty) instead of ${TMPDIR:-/tmp} to
# avoid ENOSPC; override with QUADSTORE_BENCH_FIXTURE_DIR if needed.
# Only the final JSON + HTML fragment (this script's real deliverable)
# land in the repo tree.
#
# --- RSS: no /usr/bin/time -v in this container ------------------------
# `/usr/bin/time` is not installed here. Peak RSS is measured via a
# short Python wrapper around `resource.getrusage(RUSAGE_CHILDREN)`
# after each single subprocess run (`ru_maxrss`, kB on Linux) -- the
# same rusage field GNU time -v itself reports as "Maximum resident
# set size". Reported peak_rss_kb is the MAX observed across the
# RUNS repetitions of a measurement (a peak of peaks), not a median.
#
# Measures at 10k / 100k / 1,000,000 triples (default graph) plus a
# quads variant (4 named graphs) at 100k:
#   - cottas-import (pycottas/DuckDB writer): cold wall time + on-disk
#     size, with and without --build-sidecars
#   - factoidal import (native F* writer): cold wall time + on-disk
#     size, with and without --build-sidecars -- and, because this is
#     the only writer whose output opens (see above), THIS writer's
#     stores are what "query latency through the store path" measures
#   - three fixed queries (q1 point lookup, q2 star join, q3
#     path-shaped two-hop join), through the store path
#     (`factoidal query --data-cottas`) and the in-memory path
#     (`factoidal query --data`), each with peak RSS
#
# Outputs:
#   stdout                                                human-readable table
#   docs/test-results/perf-quadstore-baseline.json        machine-readable
#   docs/test-results/perf-quadstore-baseline.fragment.html
#                                                          dashboard HTML fragment,
#                                                          included fail-soft by
#                                                          generate-report.sh
#
# Usage: tools/bench-quadstore-baseline.sh [--runs N] [--cap-seconds N]

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

RUNS="${RUNS:-3}"
CAP_SECONDS="${CAP_SECONDS:-120}"

# --- args ----------------------------------------------------------------
while [ $# -gt 0 ]; do
  case "$1" in
    --runs) RUNS="$2"; shift 2 ;;
    --cap-seconds) CAP_SECONDS="$2"; shift 2 ;;
    *) echo "Unknown argument: $1" >&2; exit 2 ;;
  esac
done

# --- platform + binaries ---------------------------------------------------
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) PLATFORM="linux-x86_64" ;;
  Darwin-arm64) PLATFORM="darwin-arm64" ;;
  *)
    echo "Unsupported platform $(uname -s)-$(uname -m); this bench targets" \
         "committed bin/linux-x86_64 (or darwin-arm64) binaries only." >&2
    exit 2
    ;;
esac

BIN_DIR="$REPO_ROOT/bin/$PLATFORM"
FACTOIDAL="$BIN_DIR/factoidal"
DUMP_NQ="$BIN_DIR/factoidal-dump-nq"

for bin in "$FACTOIDAL"; do
  if [ ! -x "$bin" ]; then
    echo "::error::Required committed binary missing or not executable: $bin" >&2
    echo "This bench runs against committed binaries only -- no toolchain build." >&2
    exit 2
  fi
done

# tools/corpus_pipeline.py's exec_corpus_pipeline (bin/factoidal-cli/
# factoidal_cli.ml) picks a converter binary by literal name search
# order ("factoidal-dump-nq.byte" first) -- the committed .byte build
# aborts in this container (`dllnums.so: cannot open shared object
# file`, a pre-existing bytecode-linking gap, not something this bench
# fixes). FACTOIDAL_BIN pins it to the working native binary.
export FACTOIDAL_BIN="$DUMP_NQ"

OUTPUT_DIR="$REPO_ROOT/docs/test-results"
JSON_OUT="$OUTPUT_DIR/perf-quadstore-baseline.json"
FRAGMENT_OUT="$OUTPUT_DIR/perf-quadstore-baseline.fragment.html"
mkdir -p "$OUTPUT_DIR"

FIXTURE_DIR="${QUADSTORE_BENCH_FIXTURE_DIR:-/dev/shm/factoidal-bench-quadstore}"
mkdir -p "$FIXTURE_DIR/fixtures" "$FIXTURE_DIR/stores"
FIXTURE_SUBDIR="$FIXTURE_DIR/fixtures"
STORE_DIR="$FIXTURE_DIR/stores"

TIMESTAMP_UTC="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
COMMIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"

echo "Factoidal quad-store performance baseline"
echo "  platform:   $PLATFORM"
echo "  commit:     $COMMIT_SHA"
echo "  fixtures:   $FIXTURE_DIR (tmpfs -- repo disk was near-full)"
echo "  runs per measurement: $RUNS   cap per single run: ${CAP_SECONDS}s"
echo ""

# --- pycottas availability (needed only for `factoidal cottas-import`) ---
PYCOTTAS_PATH_PREFIX=""
if ! python3 -c "import pycottas" >/dev/null 2>&1; then
  CACHED_VENV="$REPO_ROOT/_tmp.junk/pycottas-venv/bin"
  if [ -x "$CACHED_VENV/python3" ] && "$CACHED_VENV/python3" -c "import pycottas" >/dev/null 2>&1; then
    PYCOTTAS_PATH_PREFIX="$CACHED_VENV"
  fi
fi
if [ -n "$PYCOTTAS_PATH_PREFIX" ]; then
  export PATH="$PYCOTTAS_PATH_PREFIX:$PATH"
  PYCOTTAS_AVAILABLE=1
  echo "pycottas: available (cached venv $PYCOTTAS_PATH_PREFIX)"
elif python3 -c "import pycottas" >/dev/null 2>&1; then
  PYCOTTAS_AVAILABLE=1
  echo "pycottas: available (system python3)"
else
  PYCOTTAS_AVAILABLE=0
  echo "pycottas: NOT available -- 'factoidal cottas-import' rows will be documented skips"
fi
echo ""

# --- fixture generation (deterministic; regenerated only if missing) -----
echo "Generating synthetic fixtures in $FIXTURE_SUBDIR ..."
python3 - "$FIXTURE_SUBDIR" <<'PY'
import sys
from pathlib import Path

fixture_dir = Path(sys.argv[1])
fixture_dir.mkdir(parents=True, exist_ok=True)

# label, subject_count, n_graphs (None = default graph only)
# Each subject gets 4 quads (p1, p2, p3, next) so total quads =
# 4 * subject_count exactly -- no rounding.
datasets = [
    ("10k", 2500, None),
    ("100k", 25000, None),
    ("1m", 250000, None),
    ("quads100k", 25000, 4),
]

for label, subjects, n_graphs in datasets:
    path = fixture_dir / f"bench-{label}.nq"
    if path.exists():
        continue
    with path.open("w", encoding="utf-8") as f:
        for i in range(subjects):
            s = f"<http://example.org/s{i}>"
            o1 = f"<http://example.org/o1-{i}>"
            o2 = f"<http://example.org/o2-{i}>"
            o3 = f"<http://example.org/o3-{i}>"
            nxt = f"<http://example.org/s{(i + 1) % subjects}>"
            gpart = ""
            if n_graphs:
                gpart = f" <http://example.org/g{i % n_graphs}>"
            f.write(f"{s} <http://example.org/p1> {o1}{gpart} .\n")
            f.write(f"{s} <http://example.org/p2> {o2}{gpart} .\n")
            f.write(f"{s} <http://example.org/p3> {o3}{gpart} .\n")
            f.write(f"{s} <http://example.org/next> {nxt}{gpart} .\n")
    print(f"  {label}: {4 * subjects} quads ({subjects} subjects)"
          + (f", {n_graphs} named graphs" if n_graphs else ", default graph"))
PY
echo ""

# --- extra corpora (real-world check; skip gracefully if absent) ---------
UKPAR_CORPUS=""
for candidate in "$REPO_ROOT"/third_party/data/ukparliament/*.trig; do
  [ -f "$candidate" ] && UKPAR_CORPUS="$candidate"
  break
done
BERLIN_TTL="$REPO_ROOT/examples/data/third_party/Berlin.ttl"
[ -f "$BERLIN_TTL" ] || BERLIN_TTL=""

# --- measurement plumbing -------------------------------------------------
# Record files: tab-separated, one line per measured (or skipped) entry.
IMPORT_RECORDS="$(mktemp)"
QUERY_RECORDS="$(mktemp)"
RUN_STDERR_FILE="$(mktemp)"
trap 'rm -f "$IMPORT_RECORDS" "$QUERY_RECORDS" "$RUN_STDERR_FILE"' EXIT

# run_timed_rss CMD... -- runs CMD once under `timeout $CAP_SECONDS`,
# wrapped in a Python subprocess.call so wall time (Python's own clock,
# equivalent to bash's $EPOCHREALTIME) and peak child RSS
# (resource.getrusage(RUSAGE_CHILDREN).ru_maxrss, kB) come back
# together. Discards the command's stdout; stderr is captured to
# $RUN_STDERR_FILE (overwritten each call) so a caller-side failure can
# report WHY, not just that it failed. Prints "seconds<TAB>rss_kb" on
# success. Return codes:
#   0   success
#   124 the run hit the CAP_SECONDS timeout
#   1   the run failed for a non-timeout reason
run_timed_rss_once () {
  local out rc
  out="$(timeout "$CAP_SECONDS" python3 -c '
import resource, subprocess, sys, time
errfile = sys.argv[1]
cmd = sys.argv[2:]
t0 = time.time()
with open(errfile, "wb") as ef:
    rc = subprocess.call(cmd, stdout=subprocess.DEVNULL, stderr=ef)
t1 = time.time()
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"{rc} {t1 - t0:.4f} {ru.ru_maxrss}")
' "$RUN_STDERR_FILE" "$@")"
  rc=$?
  if [ "$rc" -eq 124 ]; then
    return 124
  fi
  if [ "$rc" -ne 0 ]; then
    return 1
  fi
  local child_rc
  child_rc="$(awk '{print $1}' <<<"$out")"
  if [ "$child_rc" != "0" ]; then
    echo "::warning:: command '$*' exited rc=$child_rc" >&2
    return 1
  fi
  awk '{printf "%s\t%s", $2, $3}' <<<"$out"
}

# failure_reason -- one compact line explaining the last run_timed_rss_once
# failure, read from $RUN_STDERR_FILE. Prefers a Python traceback's final
# "Error:"/"RuntimeError:" line (corpus_pipeline.py's own failure mode);
# falls back to the last non-empty stderr line; falls back to a generic
# label if stderr was empty (e.g. a plain nonzero exit with no message).
failure_reason () {
  local line
  line="$(grep -E 'Error[: ]|error:' "$RUN_STDERR_FILE" 2>/dev/null | tail -1)"
  [ -z "$line" ] && line="$(grep -v '^\s*$' "$RUN_STDERR_FILE" 2>/dev/null | tail -1)"
  [ -z "$line" ] && line="command failed, no stderr captured"
  printf '%s' "$line" | cut -c1-300
}

# run_timed_median_rss CMD... -- runs run_timed_rss_once $RUNS times,
# prints "median_seconds<TAB>max_rss_kb" on success. Same 0/124/1
# return-code contract as run_timed_rss_once.
run_timed_median_rss () {
  local durations=() rsses=() i rc pair sec rss
  for i in $(seq 1 "$RUNS"); do
    pair="$(run_timed_rss_once "$@")"
    rc=$?
    if [ "$rc" -eq 124 ]; then
      echo "::warning:: run $i of '$*' exceeded ${CAP_SECONDS}s cap" >&2
      return 124
    fi
    if [ "$rc" -ne 0 ]; then
      echo "::warning:: run $i of '$*' failed" >&2
      return 1
    fi
    sec="$(cut -f1 <<<"$pair")"
    rss="$(cut -f2 <<<"$pair")"
    durations+=("$sec")
    rsses+=("$rss")
  done
  python3 -c "
import statistics
secs = [float(x) for x in '''${durations[*]}'''.split()]
rsses = [int(x) for x in '''${rsses[*]}'''.split()]
print(f'{statistics.median(secs):.4f}\t{max(rsses)}')
"
}

# record_import -- runs the median-of-N timing, then (success OR
# failure -- a failed run can still have written a partial data.cottas,
# as pycottas's eager-sidecar path does, see header comment) sizes
# $6=data.cottas path and its data.cottas.* sidecar files. Every field
# lands in IMPORT_RECORDS -- including size on a SKIP row -- so the
# JSON never has to guess why a number is missing.
record_import () {
  # $1=writer $2=sidecars(true/false) $3=dataset $4=quad_count
  # $5=data.cottas path (for sizing, may not exist yet) ; remaining = command
  local writer="$1" sidecars="$2" dataset="$3" quads="$4" cottas_path="$5"
  shift 5
  local out rc median rss cbytes scbytes reason
  out="$(run_timed_median_rss "$@")"
  rc=$?
  cbytes="$(du_bytes "$cottas_path")"
  scbytes="$(du -sb "$cottas_path".* 2>/dev/null | awk '{s+=$1} END{print s+0}')"
  scbytes="${scbytes:-0}"
  # NOTE ON FIELD PLACEHOLDERS: `read -r ... <<<line` with IFS=$'\t'
  # still collapses CONSECUTIVE tabs and strips leading/trailing ones --
  # tab is an "IFS whitespace" character per POSIX word-splitting rules
  # regardless of what else IFS contains, so two adjacent tabs (meant to
  # mark an empty field) merge into one delimiter and every field after
  # them shifts left by one. Every "no value here" cell below is
  # therefore an explicit "-", never a bare empty string between tabs.
  if [ "$rc" -eq 124 ]; then
    printf 'SKIP\t%s\t%s\t%s\t%s\t-\t-\t%s\t%s\ttimeout: exceeded %ss cap\n' \
      "$writer" "$sidecars" "$dataset" "$quads" "$cbytes" "$scbytes" "$CAP_SECONDS" >> "$IMPORT_RECORDS"
    echo "  import $writer sidecars=$sidecars $dataset: SKIPPED (timeout)"
    return
  fi
  if [ "$rc" -ne 0 ]; then
    reason="$(failure_reason)"
    printf 'SKIP\t%s\t%s\t%s\t%s\t-\t-\t%s\t%s\t%s\n' \
      "$writer" "$sidecars" "$dataset" "$quads" "$cbytes" "$scbytes" "$reason" >> "$IMPORT_RECORDS"
    echo "  import $writer sidecars=$sidecars $dataset: SKIPPED ($reason)"
    return
  fi
  median="$(cut -f1 <<<"$out")"
  rss="$(cut -f2 <<<"$out")"
  printf 'OK\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t-\n' \
    "$writer" "$sidecars" "$dataset" "$quads" "$median" "$rss" "$cbytes" "$scbytes" >> "$IMPORT_RECORDS"
  echo "  import $writer sidecars=$sidecars $dataset ($quads quads): median ${median}s, peak ${rss}kB, data.cottas ${cbytes}B, sidecars ${scbytes}B"
}

record_import_skip () {
  # $1=writer $2=sidecars $3=dataset $4=quads $5=reason
  printf 'SKIP\t%s\t%s\t%s\t%s\t-\t-\t0\t0\t%s\n' "$1" "$2" "$3" "$4" "$5" >> "$IMPORT_RECORDS"
  echo "  import $1 sidecars=$2 $3: SKIPPED ($5)"
}

record_query () {
  # $1=path(cottas/memory) $2=writer $3=sidecars $4=dataset $5=query_id ; remaining = command
  local path="$1" writer="$2" sidecars="$3" dataset="$4" qid="$5"
  shift 5
  local out rc median rss
  out="$(run_timed_median_rss "$@")"
  rc=$?
  if [ "$rc" -eq 124 ]; then
    printf 'SKIP\t%s\t%s\t%s\t%s\t%s\t-\t-\ttimeout: exceeded %ss cap\n' \
      "$path" "$writer" "$sidecars" "$dataset" "$qid" "$CAP_SECONDS" >> "$QUERY_RECORDS"
    echo "  query $path $writer $dataset $qid: SKIPPED (timeout)"
    return
  fi
  if [ "$rc" -ne 0 ]; then
    printf 'SKIP\t%s\t%s\t%s\t%s\t%s\t-\t-\tcommand failed\n' \
      "$path" "$writer" "$sidecars" "$dataset" "$qid" >> "$QUERY_RECORDS"
    echo "  query $path $writer $dataset $qid: SKIPPED (command failed)"
    return
  fi
  median="$(cut -f1 <<<"$out")"
  rss="$(cut -f2 <<<"$out")"
  printf 'OK\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t-\n' \
    "$path" "$writer" "$sidecars" "$dataset" "$qid" "$median" "$rss" >> "$QUERY_RECORDS"
  echo "  query $path $writer $dataset $qid: median ${median}s, peak ${rss}kB"
}

record_query_skip () {
  # $1=path $2=writer $3=sidecars $4=dataset $5=qid $6=reason
  printf 'SKIP\t%s\t%s\t%s\t%s\t%s\t-\t-\t%s\n' "$1" "$2" "$3" "$4" "$5" "$6" >> "$QUERY_RECORDS"
  echo "  query $1 $2 $4 $5: SKIPPED ($6)"
}

du_bytes () {
  # $1=path; 0 if missing
  if [ -e "$1" ]; then
    du -sb "$1" 2>/dev/null | awk '{print $1}'
  else
    echo 0
  fi
}

# --- fixed queries per dataset ---------------------------------------------
# q1: point lookup ?o for one known (s,p).
# q2: star join -- two patterns sharing subject s0 (all properties of
#     one subject joined with a second pattern).
# q3: path-shaped two-hop join via the `next` chain predicate.
build_queries () {
  # $1=dataset ; sets Q1 Q2 Q3 (globals)
  local ds="$1" gopen="" gclose=""
  case "$ds" in
    quads100k)
      gopen="GRAPH <http://example.org/g0> { "
      gclose=" }"
      ;;
  esac
  Q1="SELECT ?o WHERE { ${gopen}<http://example.org/s0> <http://example.org/p1> ?o${gclose} }"
  Q2="SELECT * WHERE { ${gopen}<http://example.org/s0> <http://example.org/p1> ?o1 . <http://example.org/s0> <http://example.org/p2> ?o2${gclose} }"
  Q3="SELECT ?o WHERE { ${gopen}<http://example.org/s0> <http://example.org/next> ?mid . ?mid <http://example.org/p1> ?o${gclose} }"
}

# =========================================================================
# QLever probe (recorded here so it lands in the same JSON; the actual
# attempt was run interactively before this script existed -- see
# docs/claude-rules/performance.md's baseline subsection for the full
# transcript). Fixed outcome, not re-attempted every run (network +
# pip install cost, and the outcome is a container-capability fact, not
# a number that changes run to run).
# =========================================================================
QLEVER_OUTCOME="unavailable: pip install qlever succeeds (installs the Python control script only); qlever index --system native fails ('qlever-index: command not found' -- the QLever C++ binaries are not shipped by the pip package and are not present in this container); the container-native alternative, --system docker (the package's default), cannot be reached either (docker ps: 'dial unix /var/run/docker.sock: connect: no such file or directory' -- no daemon running). No native or containerized QLever run was possible in this container."

# =========================================================================
# Import measurements: dataset x writer x sidecars
# =========================================================================
DATASETS=(10k 100k 1m quads100k)
declare -A DATASET_QUADS=( [10k]=10000 [100k]=100000 [1m]=1000000 [quads100k]=100000 )

echo "=== Import: factoidal cottas-import (pycottas/DuckDB writer) ==="
for ds in "${DATASETS[@]}"; do
  fixture="$FIXTURE_SUBDIR/bench-$ds.nq"
  quads="${DATASET_QUADS[$ds]}"
  if [ "$PYCOTTAS_AVAILABLE" -ne 1 ]; then
    record_import_skip pycottas false "$ds" "$quads" "pycottas not available in this container"
    record_import_skip pycottas true "$ds" "$quads" "pycottas not available in this container"
    continue
  fi
  for sidecars in false true; do
    corpus_root="$STORE_DIR/pycottas-$ds-sc$sidecars"
    rm -rf "$corpus_root"
    extra_flag=()
    [ "$sidecars" = "true" ] && extra_flag=(--build-sidecars)
    record_import pycottas "$sidecars" "$ds" "$quads" "$corpus_root/bench-$ds/v1/data.cottas" \
      "$FACTOIDAL" cottas-import --input "$fixture" --input-format nq \
      --corpus-root "$corpus_root" --dataset-name bench --chunk-name "bench-$ds" \
      "${extra_flag[@]}"
  done
done
echo ""

echo "=== Import: factoidal import (native F* writer) ==="
for ds in "${DATASETS[@]}"; do
  fixture="$FIXTURE_SUBDIR/bench-$ds.nq"
  quads="${DATASET_QUADS[$ds]}"
  for sidecars in false true; do
    out_dir="$STORE_DIR/native-$ds-sc$sidecars"
    rm -rf "$out_dir"
    extra_flag=()
    [ "$sidecars" = "false" ] && extra_flag=(--no-sidecars)
    record_import native "$sidecars" "$ds" "$quads" "$out_dir/data.cottas" \
      "$FACTOIDAL" import --nq "$fixture" --out "$out_dir" "${extra_flag[@]}"
  done
done
echo ""

# --- verify the pycottas-store version-gate rejection, once ---------------
PYCOTTAS_QUERYABLE=0
PYCOTTAS_GATE_DETAIL=""
if [ "$PYCOTTAS_AVAILABLE" -eq 1 ]; then
  probe_store="$STORE_DIR/pycottas-10k-scfalse/bench-10k/v1/data.cottas"
  if [ -f "$probe_store" ]; then
    probe_err="$(mktemp)"
    timeout 30 "$FACTOIDAL" query --data-cottas "$probe_store" \
      -e 'SELECT ?o WHERE { <http://example.org/s0> <http://example.org/p1> ?o }' \
      >/dev/null 2>"$probe_err"
    probe_rc=$?
    if [ "$probe_rc" -eq 0 ]; then
      PYCOTTAS_QUERYABLE=1
    else
      PYCOTTAS_GATE_DETAIL="$(grep -m1 'FileMetaData version mismatch' "$probe_err" || tail -1 "$probe_err")"
    fi
    rm -f "$probe_err"
  fi
fi
echo "pycottas-produced store queryable by this binary: $([ "$PYCOTTAS_QUERYABLE" -eq 1 ] && echo yes || echo NO)"
[ -n "$PYCOTTAS_GATE_DETAIL" ] && echo "  detail: $PYCOTTAS_GATE_DETAIL"
echo ""

# =========================================================================
# Query measurements: dataset x {cottas store (native writer), memory} x
# {q1,q2,q3}, and, only if the probe above found it queryable, the
# pycottas-written store too.
# =========================================================================
echo "=== Query latency: store path (factoidal query --data-cottas, native writer) ==="
for ds in "${DATASETS[@]}"; do
  build_queries "$ds"
  for sidecars in false true; do
    out_dir="$STORE_DIR/native-$ds-sc$sidecars"
    store="$out_dir/data.cottas"
    if [ ! -f "$store" ]; then
      record_query_skip cottas native "$sidecars" "$ds" q1 "no store (import skipped/failed)"
      record_query_skip cottas native "$sidecars" "$ds" q2 "no store (import skipped/failed)"
      record_query_skip cottas native "$sidecars" "$ds" q3 "no store (import skipped/failed)"
      continue
    fi
    record_query cottas native "$sidecars" "$ds" q1 \
      "$FACTOIDAL" query --data-cottas "$store" -e "$Q1"
    record_query cottas native "$sidecars" "$ds" q2 \
      "$FACTOIDAL" query --data-cottas "$store" -e "$Q2"
    record_query cottas native "$sidecars" "$ds" q3 \
      "$FACTOIDAL" query --data-cottas "$store" -e "$Q3"
  done
done
echo ""

if [ "$PYCOTTAS_QUERYABLE" -eq 1 ]; then
  echo "=== Query latency: store path (factoidal query --data-cottas, pycottas writer) ==="
  for ds in "${DATASETS[@]}"; do
    build_queries "$ds"
    for sidecars in false true; do
      corpus_root="$STORE_DIR/pycottas-$ds-sc$sidecars"
      store="$corpus_root/bench-$ds/v1/data.cottas"
      if [ ! -f "$store" ]; then
        record_query_skip cottas pycottas "$sidecars" "$ds" q1 "no store (import skipped/failed)"
        continue
      fi
      record_query cottas pycottas "$sidecars" "$ds" q1 \
        "$FACTOIDAL" query --data-cottas "$store" -e "$Q1"
      record_query cottas pycottas "$sidecars" "$ds" q2 \
        "$FACTOIDAL" query --data-cottas "$store" -e "$Q2"
      record_query cottas pycottas "$sidecars" "$ds" q3 \
        "$FACTOIDAL" query --data-cottas "$store" -e "$Q3"
    done
  done
  echo ""
else
  record_query_skip cottas pycottas n/a all q1 \
    "issue #445 format-compatibility gate rejects pycottas/DuckDB-written stores on this binary (see header comment); not retried per-size"
fi

echo "=== Query latency: in-memory path (factoidal query --data, same .nq fixture) ==="
for ds in "${DATASETS[@]}"; do
  build_queries "$ds"
  fixture="$FIXTURE_SUBDIR/bench-$ds.nq"
  record_query memory n/a n/a "$ds" q1 \
    "$FACTOIDAL" query --data "$fixture" -e "$Q1"
  record_query memory n/a n/a "$ds" q2 \
    "$FACTOIDAL" query --data "$fixture" -e "$Q2"
  record_query memory n/a n/a "$ds" q3 \
    "$FACTOIDAL" query --data "$fixture" -e "$Q3"
done
echo ""

# --- extra corpora: import + q1-shaped smoke query, skip gracefully ------
echo "=== Extra corpora (real-world check) ==="
if [ -n "$UKPAR_CORPUS" ]; then
  echo "  UK Parliament corpus present: $UKPAR_CORPUS (not sized into the main table -- see JSON 'extra_corpora')"
else
  record_import_skip extra false ukparliament 0 \
    "third_party/data/ukparliament/*.trig not present in this checkout"
fi
if [ -n "$BERLIN_TTL" ]; then
  echo "  Berlin.ttl present: $BERLIN_TTL (not sized into the main table -- see JSON 'extra_corpora')"
else
  record_import_skip extra false berlin 0 \
    "examples/data/third_party/Berlin.ttl not present in this checkout"
fi
echo ""

# --- render: human-readable table ----------------------------------------
echo "=== Summary: import ==="
printf '%-10s %-9s %-10s %10s %12s %10s %14s %12s\n' "writer" "sidecars" "dataset" "quads" "seconds" "peak-kB" "cottas-bytes" "sc-bytes"
while IFS=$'\t' read -r status writer sidecars dataset quads median rss cbytes scbytes note; do
  if [ "$status" = "OK" ]; then
    printf '%-10s %-9s %-10s %10s %12s %10s %14s %12s\n' "$writer" "$sidecars" "$dataset" "$quads" "${median}s" "$rss" "$cbytes" "$scbytes"
  else
    printf '%-10s %-9s %-10s %10s %12s %10s %14s %12s   SKIP: %s\n' "$writer" "$sidecars" "$dataset" "$quads" "-" "-" "$cbytes" "$scbytes" "$note"
  fi
done < "$IMPORT_RECORDS"
echo ""
echo "=== Summary: query ==="
printf '%-7s %-9s %-9s %-10s %-4s %10s %10s\n' "path" "writer" "sidecars" "dataset" "q" "seconds" "peak-kB"
while IFS=$'\t' read -r status path writer sidecars dataset qid median rss note; do
  if [ "$status" = "OK" ]; then
    printf '%-7s %-9s %-9s %-10s %-4s %10s %10s\n' "$path" "$writer" "$sidecars" "$dataset" "$qid" "${median}s" "$rss"
  else
    printf '%-7s %-9s %-9s %-10s %-4s %10s %10s   SKIP: %s\n' "$path" "$writer" "$sidecars" "$dataset" "$qid" "-" "-" "$note"
  fi
done < "$QUERY_RECORDS"
echo ""
echo "QLever probe: $QLEVER_OUTCOME"

# --- render: JSON ----------------------------------------------------------
esc_json () { printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'; }

{
  printf '{\n'
  printf '  "timestamp": "%s",\n' "$TIMESTAMP_UTC"
  printf '  "commit": "%s",\n' "$COMMIT_SHA"
  printf '  "platform": "%s",\n' "$PLATFORM"
  printf '  "runs_per_measurement": %s,\n' "$RUNS"
  printf '  "cap_seconds_per_run": %s,\n' "$CAP_SECONDS"
  printf '  "fixture_dir": "%s",\n' "$(esc_json "$FIXTURE_DIR")"
  printf '  "note": "seconds_median is a median of %s runs; peak_rss_kb is the MAX ru_maxrss (RUSAGE_CHILDREN) observed across those %s runs, i.e. a peak of peaks, not a median. Fixtures are N-Quads for both the store-import and in-memory --data query paths (documented deviation from a separate Turtle fixture -- see script header). data.cottas.* sidecar files, where present, are summed separately from the base data.cottas file.",\n' "$RUNS" "$RUNS"
  printf '  "qlever_probe": {\n'
  printf '    "attempted": true,\n'
  printf '    "outcome": "unavailable",\n'
  printf '    "detail": "%s"\n' "$(esc_json "$QLEVER_OUTCOME")"
  printf '  },\n'
  printf '  "pycottas_store_queryable_by_this_binary": %s,\n' "$([ "$PYCOTTAS_QUERYABLE" -eq 1 ] && echo true || echo false)"
  printf '  "pycottas_gate_detail": "%s",\n' "$(esc_json "$PYCOTTAS_GATE_DETAIL")"
  printf '  "import_results": [\n'
  first=1
  while IFS=$'\t' read -r status writer sidecars dataset quads median rss cbytes scbytes note; do
    [ "$status" = "OK" ] || continue
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    printf '    {"writer":"%s","sidecars":%s,"dataset":"%s","quads":%s,"seconds_median":%s,"peak_rss_kb":%s,"cottas_bytes":%s,"sidecars_bytes":%s}' \
      "$writer" "$sidecars" "$dataset" "$quads" "$median" "$rss" "$cbytes" "$scbytes"
  done < "$IMPORT_RECORDS"
  printf '\n  ],\n'
  printf '  "import_skipped": [\n'
  first=1
  while IFS=$'\t' read -r status writer sidecars dataset quads median rss cbytes scbytes note; do
    [ "$status" = "SKIP" ] || continue
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    printf '    {"writer":"%s","sidecars":%s,"dataset":"%s","quads":%s,"cottas_bytes":%s,"sidecars_bytes":%s,"reason":"%s"}' \
      "$writer" "$sidecars" "$dataset" "$quads" "$cbytes" "$scbytes" "$(esc_json "$note")"
  done < "$IMPORT_RECORDS"
  printf '\n  ],\n'
  printf '  "query_results": [\n'
  first=1
  while IFS=$'\t' read -r status path writer sidecars dataset qid median rss note; do
    [ "$status" = "OK" ] || continue
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    printf '    {"path":"%s","writer":"%s","sidecars":"%s","dataset":"%s","query":"%s","seconds_median":%s,"peak_rss_kb":%s}' \
      "$path" "$writer" "$sidecars" "$dataset" "$qid" "$median" "$rss"
  done < "$QUERY_RECORDS"
  printf '\n  ],\n'
  printf '  "query_skipped": [\n'
  first=1
  while IFS=$'\t' read -r status path writer sidecars dataset qid median rss note; do
    [ "$status" = "SKIP" ] || continue
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    printf '    {"path":"%s","writer":"%s","sidecars":"%s","dataset":"%s","query":"%s","reason":"%s"}' \
      "$path" "$writer" "$sidecars" "$dataset" "$qid" "$(esc_json "$note")"
  done < "$QUERY_RECORDS"
  printf '\n  ],\n'
  printf '  "extra_corpora": {\n'
  printf '    "ukparliament_trig_present": %s,\n' "$([ -n "$UKPAR_CORPUS" ] && echo true || echo false)"
  printf '    "berlin_ttl_present": %s\n' "$([ -n "$BERLIN_TTL" ] && echo true || echo false)"
  printf '  }\n'
  printf '}\n'
} > "$JSON_OUT"
echo ""
echo "JSON written: $JSON_OUT"

# --- render: dashboard HTML fragment (included fail-soft by generate-report.sh) -
esc_html () { printf '%s' "$1" | sed 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g'; }

{
  printf '<h2>Quad-store baseline <span class="inline-numbers">measured %s &middot; commit <a href="https://github.com/danbri/factoidal/commit/%s">%s</a></span></h2>\n' \
    "$TIMESTAMP_UTC" "$COMMIT_SHA" "${COMMIT_SHA:0:7}"
  printf '<p style="margin: 0.3em 0 0.8em; color: var(--muted); font-size: 0.85em;">\n'
  printf '  Measured against the committed <code>bin/%s/factoidal</code> binary (median of %s runs, no toolchain build). ' \
    "$PLATFORM" "$RUNS"
  printf '  Store-path queries use the native <code>factoidal import</code> writer -- the pycottas/DuckDB <code>cottas-import</code> writer'
  printf ' is measured for cold import time and size only; its stores are rejected on open by this binary%s (issue <a href="https://github.com/danbri/factoidal/issues/445">#445</a> format-compatibility gate).\n' \
    "$([ "$PYCOTTAS_QUERYABLE" -eq 1 ] && echo " -- NOT reproduced this run" || echo ", reproduced this run")"
  printf '  QLever comparison: %s\n' "$(esc_html "$QLEVER_OUTCOME")"
  printf '  Source: <a href="https://github.com/danbri/factoidal/blob/main/tools/bench-quadstore-baseline.sh">tools/bench-quadstore-baseline.sh</a>, '
  printf '  raw data <a href="perf-quadstore-baseline.json">perf-quadstore-baseline.json</a>.\n'
  printf '</p>\n'

  printf '<h3 style="font-size:0.95em; margin:0.8em 0 0.3em;">Import (cold wall time, on-disk size)</h3>\n'
  printf '<div style="overflow-x:auto;">\n<table style="border-collapse:collapse; width:100%%; font-size:0.88em;">\n<thead><tr>'
  for h in Writer Sidecars Dataset Quads "Median seconds" "Peak kB" "data.cottas bytes" "Sidecars bytes"; do
    printf '<th style="text-align:left; border-bottom:1px solid var(--border); padding:0.3em 0.6em;">%s</th>' "$h"
  done
  printf '</tr></thead>\n<tbody>\n'
  while IFS=$'\t' read -r status writer sidecars dataset quads median rss cbytes scbytes note; do
    if [ "$status" = "OK" ]; then
      printf '<tr><td style="padding:0.25em 0.6em; font-family:ui-monospace,monospace;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%ss</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td></tr>\n' \
        "$writer" "$sidecars" "$dataset" "$quads" "$median" "$rss" "$cbytes" "$scbytes"
    else
      printf '<tr style="color:var(--muted);"><td style="padding:0.25em 0.6em; font-family:ui-monospace,monospace;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td><td colspan="4" style="padding:0.25em 0.6em;"><em>skipped: %s</em></td></tr>\n' \
        "$writer" "$sidecars" "$dataset" "$quads" "$(esc_html "$note")"
    fi
  done < "$IMPORT_RECORDS"
  printf '</tbody></table>\n</div>\n'

  printf '<h3 style="font-size:0.95em; margin:0.8em 0 0.3em;">Query latency (store vs. in-memory)</h3>\n'
  printf '<div style="overflow-x:auto;">\n<table style="border-collapse:collapse; width:100%%; font-size:0.88em;">\n<thead><tr>'
  for h in Path Writer Sidecars Dataset Query "Median seconds" "Peak kB"; do
    printf '<th style="text-align:left; border-bottom:1px solid var(--border); padding:0.3em 0.6em;">%s</th>' "$h"
  done
  printf '</tr></thead>\n<tbody>\n'
  while IFS=$'\t' read -r status path writer sidecars dataset qid median rss note; do
    if [ "$status" = "OK" ]; then
      printf '<tr><td style="padding:0.25em 0.6em; font-family:ui-monospace,monospace;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%ss</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td></tr>\n' \
        "$path" "$writer" "$sidecars" "$dataset" "$qid" "$median" "$rss"
    else
      printf '<tr style="color:var(--muted);"><td style="padding:0.25em 0.6em; font-family:ui-monospace,monospace;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td colspan="3" style="padding:0.25em 0.6em;"><em>skipped: %s</em></td></tr>\n' \
        "$path" "$writer" "$sidecars" "$dataset" "$(esc_html "$note")"
    fi
  done < "$QUERY_RECORDS"
  printf '</tbody></table>\n</div>\n'
} > "$FRAGMENT_OUT"
echo "Fragment written: $FRAGMENT_OUT"
