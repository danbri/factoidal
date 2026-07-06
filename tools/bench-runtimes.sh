#!/bin/bash
# tools/bench-runtimes.sh
#
# Runtime-vs-runtime performance bench: how does the SAME engine
# behave across its four extraction targets (native OCaml,
# js_of_ocaml, wasm_of_ocaml, KaRaMeL C)? Different axis from
# tools/bench-competitive.py (engine-vs-engine, e.g. factoidal vs
# pyoxigraph) and from formal/fstar/bench-turtle-metrics.sh /
# tools/bench-parse-serialize.sh (native-only throughput). See
# skills/perf-benchmarking/SKILL.md for the measurement discipline
# this follows (median-of-N, dated + commit-linked, no unlabelled
# ratios) and docs/web/perf/index.md for the write-up this feeds.
#
# Sections:
#   1. Full-engine three-runtime bench (native / node-js / node-wasm):
#      Turtle parse + 4 SPARQL query shapes over a synthetic
#      multi-predicate fixture at 100k triples (+ a reduced set at 1M).
#   2. Delta-log micro-bench, "pure" mode (hand-built delta_batch,
#      no SPARQL): OCaml-native vs C-native vs C-wasm(wasi), the
#      apples-to-apples comparison for the owner's "would KaRaMeL->
#      wasm beat js_of_ocaml" question -- except the shipped JS/wasm
#      bundles don't expose the raw serialize/parse functions, only
#      the SPARQL-driven wrapper below, so this leg is OCaml/C/C-wasm
#      only.
#   3. Delta-log micro-bench, "sparql" mode (INSERT DATA -> the
#      shipped `deltaBatchToHex` export): OCaml-native vs
#      js_of_ocaml vs wasm_of_ocaml, the three-runtime comparison for
#      the SAME wrapper function. Small N only -- see the quadratic-
#      looking SPARQL-Update-parsing wall documented below and in the
#      perf hub doc.
#
# Requires: eval $(opam env --switch=fstar) already run (builds an
# OCaml native bench binary from formal/fstar/ocaml-output/ + links
# the committed docs/fstar-extracted/*.js bundles; does NOT re-run F*
# extraction). krml + KRML_HOME (default /root/karamel) for the C
# legs; if krml isn't on PATH, section 2's C rows are skipped with a
# note, not fabricated.
#
# Usage: tools/bench-runtimes.sh [--runs N] [--cap-seconds N] [--skip-1m]
#
# Outputs:
#   stdout                                    human-readable log
#   docs/test-results/runtime-bench.json      machine-readable results
#
# Anti-pattern #14: every exit code captured explicitly, no `|| true`.
# Anti-pattern #17: every single run capped by `timeout`; a cap trip
# is a recorded, documented skip.
# Anti-pattern #20: this script can run long (the 1M section especially)
# -- run it with run_in_background and poll, don't foreground-block.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

RUNS=3
CAP_SECONDS=600
SKIP_1M=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --runs) RUNS="$2"; shift 2 ;;
    --cap-seconds) CAP_SECONDS="$2"; shift 2 ;;
    --skip-1m) SKIP_1M=1; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

RUN_LOG_DIR="$REPO_ROOT/.claude-runs"
mkdir -p "$RUN_LOG_DIR"
MAIN_LOG="$RUN_LOG_DIR/bench-runtimes-$(date -u +%Y%m%dT%H%M%SZ).log"
exec > >(tee -a "$MAIN_LOG") 2>&1

FIXTURE_DIR="${TMPDIR:-/tmp}/factoidal-runtime-bench"
mkdir -p "$FIXTURE_DIR/queries"
OUTPUT_JSON="$REPO_ROOT/docs/test-results/runtime-bench.json"
RECORDS_FILE="$(mktemp)"
trap 'rm -f "$RECORDS_FILE"' EXIT

COMMIT_SHA="$(git rev-parse HEAD)"
TIMESTAMP_UTC="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"

echo "Factoidal runtime-vs-runtime bench"
echo "  commit:   $COMMIT_SHA"
echo "  date:     $TIMESTAMP_UTC"
echo "  runs per measurement: $RUNS   cap per single run: ${CAP_SECONDS}s"
echo ""

# --- machine facts -----------------------------------------------------
CPU_MODEL="$(grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2 | sed 's/^ //')"
NPROC="$(nproc 2>/dev/null || echo unknown)"
NODE_VERSION="$(node --version 2>/dev/null || echo missing)"
OCAML_VERSION="$(ocaml -version 2>/dev/null || echo missing)"
GCC_VERSION="$(gcc --version 2>/dev/null | head -1 || echo missing)"
CLANG_VERSION="$(clang --version 2>/dev/null | head -1 || echo missing)"
KRML_HOME="${KRML_HOME:-/root/karamel}"
HAVE_KRML=0
command -v krml >/dev/null 2>&1 && [[ -d "$KRML_HOME/include/krml" ]] && HAVE_KRML=1

echo "Machine facts:"
echo "  CPU:    $CPU_MODEL ($NPROC logical cores)"
echo "  node:   $NODE_VERSION"
echo "  ocaml:  $OCAML_VERSION"
echo "  gcc:    $GCC_VERSION"
echo "  clang:  $CLANG_VERSION"
echo "  krml available for C legs: $HAVE_KRML"
echo ""

record() {
  # section  engine  op  size  status  median_s  extra_json
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$7" >> "$RECORDS_FILE"
}

# run_timed_median CMD... -- median of $RUNS wall-clock seconds via
# bash EPOCHREALTIME (no /usr/bin/time dependency -- see
# tools/bench_rusage_run.py's header for why). Returns 124 on a
# cap trip, 1 on any other failure, prints median on success.
run_timed_median () {
  local durations=() i rc t0 t1
  for i in $(seq 1 "$RUNS"); do
    t0="$EPOCHREALTIME"
    timeout "$CAP_SECONDS" "$@" >/tmp/bench-runtimes.out 2>/tmp/bench-runtimes.err
    rc=$?
    t1="$EPOCHREALTIME"
    if [[ "$rc" -eq 124 ]]; then
      echo "::warning:: run $i of '$*' exceeded ${CAP_SECONDS}s cap" >&2
      return 124
    fi
    if [[ "$rc" -ne 0 ]]; then
      echo "::warning:: run $i of '$*' failed rc=$rc" >&2
      cat /tmp/bench-runtimes.err >&2
      return 1
    fi
    durations+=("$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.4f", b-a}')")
  done
  python3 -c "
import statistics
vals = [float(x) for x in '''${durations[*]}'''.split()]
print(f'{statistics.median(vals):.4f}')
"
}

# =========================================================================
# Section 1: full-engine three-runtime bench (native / node-js / node-wasm)
# =========================================================================
echo "=== Section 1: full-engine parse + SPARQL, three runtimes ==="

NATIVE_BIN="bin/linux-x86_64/factoidal"
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) NATIVE_BIN="bin/darwin-arm64/factoidal" ;;
  Linux-x86_64) NATIVE_BIN="bin/linux-x86_64/factoidal" ;;
esac
JS_BUNDLE="docs/fstar-extracted/factoidal.js"
WASM_BUNDLE="docs/fstar-extracted/factoidal.wasm.js"

[[ -x "$NATIVE_BIN" ]] || { echo "FATAL: missing $NATIVE_BIN" >&2; exit 2; }
[[ -f "$JS_BUNDLE" ]] || { echo "FATAL: missing $JS_BUNDLE" >&2; exit 2; }
[[ -f "$WASM_BUNDLE" ]] || { echo "FATAL: missing $WASM_BUNDLE" >&2; exit 2; }

# --- fixture generation (deterministic; regenerated only if absent) ------
# Synthetic multi-predicate dataset (no suitably large real corpus is
# checked into this worktree -- third_party/data/ukparliament/ ships
# only the SPARQL query text + a readme, not the 3.1M-quad corpus
# itself; docs/fstar-extracted/samples/*.ttl are <50-line demo
# fixtures). Same precedent as tools/bench-parse-serialize.sh's own
# synthetic fixtures. Each entity gets 4 triples (rdf:type, foaf:name,
# ex:dept cycling through 20 buckets, foaf:knows a ring neighbour) so
# COUNT/JOIN/GROUP BY/regex all have real structure to work over.
echo "Generating multi-predicate fixtures in $FIXTURE_DIR ..."
python3 - "$FIXTURE_DIR" 100000 1000000 <<'PY'
import sys
from pathlib import Path

fixture_dir = Path(sys.argv[1])
sizes = [int(s) for s in sys.argv[2:]]
NDEPTS = 20

for total_triples in sizes:
    n_entities = max(1, total_triples // 4)
    path = fixture_dir / f"multi-{total_triples}.ttl"
    if path.exists():
        continue
    with path.open("w", encoding="utf-8") as f:
        f.write("@prefix ex: <http://example.org/> .\n")
        f.write("@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n")
        for i in range(n_entities):
            dept = i % NDEPTS
            friend = (i + 1) % n_entities
            f.write(f"ex:p{i} a ex:Person ;\n")
            f.write(f"  foaf:name \"Person{i}\" ;\n")
            f.write(f"  ex:dept ex:dept{dept} ;\n")
            f.write(f"  foaf:knows ex:p{friend} .\n")
    print(f"  {path}: {n_entities} entities, {n_entities*4} triples")
PY

cat > "$FIXTURE_DIR/queries/count.rq" <<'EOF'
SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }
EOF
cat > "$FIXTURE_DIR/queries/join-filter.rq" <<'EOF'
PREFIX ex: <http://example.org/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
SELECT ?s ?friend WHERE {
  ?s foaf:knows ?friend .
  ?friend ex:dept ?d .
  FILTER(?d = ex:dept3)
}
EOF
cat > "$FIXTURE_DIR/queries/group-by.rq" <<'EOF'
PREFIX ex: <http://example.org/>
SELECT ?dept (COUNT(?s) AS ?c) WHERE {
  ?s ex:dept ?dept
} GROUP BY ?dept
EOF
cat > "$FIXTURE_DIR/queries/regex-filter.rq" <<'EOF'
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
SELECT ?s WHERE {
  ?s foaf:name ?n .
  FILTER regex(?n, "^Person1[0-9]$")
}
EOF
echo ""

run_engine_parse () {
  # $1=engine(native|js|wasm) $2=size -- Turtle parse only, via the
  # CLI's `count` subcommand (same proxy every other repo bench uses:
  # parse + triple count, no index build, no query eval).
  local engine="$1" size="$2" median rc
  local data="$FIXTURE_DIR/multi-$size.ttl"
  case "$engine" in
    native) median="$(run_timed_median "$NATIVE_BIN" count "$data")" ;;
    js)     median="$(run_timed_median node "$JS_BUNDLE" count "$data")" ;;
    wasm)   median="$(run_timed_median node "$WASM_BUNDLE" count "$data")" ;;
  esac
  rc=$?
  if [[ "$rc" -eq 124 ]]; then
    record fullengine "$engine" parse "$size" SKIP "" "timeout ${CAP_SECONDS}s"
    echo "  $engine parse @${size}: SKIP (timeout)"
    return
  fi
  if [[ "$rc" -ne 0 ]]; then
    record fullengine "$engine" parse "$size" SKIP "" "command failed"
    echo "  $engine parse @${size}: SKIP (command failed)"
    return
  fi
  record fullengine "$engine" parse "$size" OK "$median" ""
  echo "  $engine parse @${size}: median ${median}s"
}

run_engine_query () {
  # $1=engine(native|js|wasm) $2=size $3=op
  local engine="$1" size="$2" op="$3" median rc
  local data="$FIXTURE_DIR/multi-$size.ttl"
  local query="$FIXTURE_DIR/queries/$op.rq"
  case "$engine" in
    native) median="$(run_timed_median "$NATIVE_BIN" query --data "$data" --query "$query" -o json)" ;;
    js)     median="$(run_timed_median node "$JS_BUNDLE" query --data "$data" --query "$query" -o json)" ;;
    wasm)   median="$(run_timed_median node "$WASM_BUNDLE" query --data "$data" --query "$query" -o json)" ;;
  esac
  rc=$?
  if [[ "$rc" -eq 124 ]]; then
    record fullengine "$engine" "$op" "$size" SKIP "" "timeout ${CAP_SECONDS}s"
    echo "  $engine $op @${size}: SKIP (timeout)"
    return
  fi
  if [[ "$rc" -ne 0 ]]; then
    record fullengine "$engine" "$op" "$size" SKIP "" "command failed"
    echo "  $engine $op @${size}: SKIP (command failed)"
    return
  fi
  record fullengine "$engine" "$op" "$size" OK "$median" ""
  echo "  $engine $op @${size}: median ${median}s"
}

echo "--- 100,000 triples: parse (count subcommand) ---"
for engine in native js wasm; do
  run_engine_parse "$engine" 100000
done
echo ""

echo "--- 100,000 triples: count + join-filter + group-by + regex-filter ---"
for engine in native js wasm; do
  for op in count join-filter group-by regex-filter; do
    run_engine_query "$engine" 100000 "$op"
  done
done
echo ""

if [[ "$SKIP_1M" -eq 1 ]]; then
  echo "--- 1,000,000 triples: skipped (--skip-1m) ---"
  record fullengine all all 1000000 SKIP "" "--skip-1m passed"
else
  echo "--- 1,000,000 triples: parse (count subcommand) ---"
  for engine in native js wasm; do
    run_engine_parse "$engine" 1000000
  done
  echo ""
  echo "--- 1,000,000 triples: count + join-filter + group-by (regex-filter skipped, time budget) ---"
  for engine in native js wasm; do
    for op in count join-filter group-by; do
      run_engine_query "$engine" 1000000 "$op"
    done
  done
  record fullengine all regex-filter 1000000 SKIP "" "time-budget capped in this bench run; not attempted at 1M"
  echo "  (regex-filter @1000000: SKIPPED, time-budget capped, not attempted)"
fi
echo ""

# =========================================================================
# Section 2 + 3: delta-log micro-bench
# =========================================================================
echo "=== Section 2/3: delta-log micro-bench (RDF.Store.Columnar.DeltaLog) ==="

DL_WORK="${TMPDIR:-/tmp}/factoidal-deltalog-bench"
mkdir -p "$DL_WORK"
DL_DIR="formal/fstar/c-output/deltalog"
DL_OV="$DL_DIR/compat-override"

# --- 2a. OCaml native bench binary (built once, from committed
#     ocaml-output/ -- no F* re-extraction; uses the same COMMON_MODULES
#     module list formal/fstar/build-ocaml.sh uses for the `factoidal`
#     target, since deltalog_bench.ml's `sparql` mode needs
#     SPARQL11_Parser + RDF_Store_Columnar_DeltaMerge alongside
#     RDF_Store_Columnar_DeltaLog). ---
OCAML_BENCH_BIN="$DL_WORK/deltalog_bench_ocaml"
HAVE_OCAML_BENCH=0
if command -v ocamlfind >/dev/null 2>&1; then
  echo "Building OCaml-native delta-log bench binary ..."
  (
    cd formal/fstar/ocaml-output
    # Reuse build-ocaml.sh's own COMMON_MODULES assignment verbatim
    # (same anchors as tests/local/delta_log_crash_harness.sh's accepted
    # duplication risk, but eval'd from the source instead of copied):
    eval "$(sed -n '/COMMON_MODULES="Util_Log/,/SPARQL_GraphStore.ml"/p' ../build-ocaml.sh)"
    ZSTD_INC=""
    for dir in /usr/include /opt/homebrew/include /opt/homebrew/opt/zstd/include; do
      [[ -f "$dir/zstd.h" ]] && { ZSTD_INC="-I $dir"; break; }
    done
    ZSTD_LIB=""
    for dir in /usr/lib/x86_64-linux-gnu /usr/lib /opt/homebrew/lib /opt/homebrew/opt/zstd/lib; do
      [[ -f "$dir/libzstd.a" || -f "$dir/libzstd.so" ]] && { ZSTD_LIB="-L$dir"; break; }
    done
    ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,uucp -linkpkg -w -8-14-26 \
      $COMMON_MODULES \
      $ZSTD_INC ../experimental_ocaml_glue/parquet_zstd_stubs.c \
      -cclib "$ZSTD_LIB" -cclib -lzstd \
      ../../../tools/deltalog-bench/deltalog_bench.ml \
      -o "$OCAML_BENCH_BIN" > "$DL_WORK/_ocaml_bench_build.log" 2>&1
  )
  if [[ -x "$OCAML_BENCH_BIN" ]]; then
    HAVE_OCAML_BENCH=1
    echo "  built: $OCAML_BENCH_BIN"
  else
    echo "  WARNING: OCaml bench build failed -- see $DL_WORK/_ocaml_bench_build.log"
  fi
else
  echo "  SKIP: ocamlfind not on PATH (run: eval \$(opam env --switch=fstar))"
fi
echo ""

# --- 2b. C native + C-wasm(wasi) bench binaries ---
HAVE_C_NATIVE=0
HAVE_C_WASM=0
C_BENCH_NATIVE="$DL_WORK/deltalog_bench_c_native"
C_BENCH_WASM="$DL_WORK/deltalog_bench_c_wasm.wasm"
WASI_RUNNER="tools/deltalog-bench/run-wasi.mjs"

if [[ -f "$DL_DIR/Factoidal_DeltaLog.c" ]]; then
  echo "Building C-native delta-log bench binary ..."
  NCFLAGS=(-O2 -I "$DL_OV" -I "$KRML_HOME/include" -I "$KRML_HOME/krmllib/dist/minimal" -I "$DL_DIR")
  NOBJ="$DL_WORK/native-obj"
  mkdir -p "$NOBJ"
  NCC_RC=0
  {
    gcc -c "${NCFLAGS[@]}" "$DL_DIR/Factoidal_DeltaLog.c" -o "$NOBJ/Factoidal_DeltaLog.o" &&
    gcc -c "${NCFLAGS[@]}" "$DL_DIR/krmlinit.c" -o "$NOBJ/krmlinit.o" &&
    gcc -c "${NCFLAGS[@]}" "$DL_OV/prims64.c" -o "$NOBJ/prims64.o" &&
    for f in fstar_char fstar_string fstar_uint32; do
      gcc -c "${NCFLAGS[@]}" -I "$KRML_HOME/krmllib/dist/generic" "$KRML_HOME/krmllib/dist/generic/$f.c" -o "$NOBJ/$f.o" || exit 1
    done &&
    gcc -c "${NCFLAGS[@]}" "$DL_DIR/demo/deltalog_stubs.c" -o "$NOBJ/deltalog_stubs.o" &&
    gcc -c "${NCFLAGS[@]}" tools/deltalog-bench/deltalog_bench.c -o "$NOBJ/deltalog_bench.o" &&
    gcc "$NOBJ/deltalog_bench.o" "$NOBJ/Factoidal_DeltaLog.o" "$NOBJ/krmlinit.o" "$NOBJ/prims64.o" \
        "$NOBJ/fstar_char.o" "$NOBJ/fstar_string.o" "$NOBJ/fstar_uint32.o" "$NOBJ/deltalog_stubs.o" \
        -o "$C_BENCH_NATIVE"
  } > "$DL_WORK/_c_native_build.log" 2>&1 || NCC_RC=$?
  if [[ "$NCC_RC" -eq 0 && -x "$C_BENCH_NATIVE" ]]; then
    HAVE_C_NATIVE=1
    echo "  built: $C_BENCH_NATIVE"
  else
    echo "  WARNING: C-native bench build failed (rc=$NCC_RC) -- see $DL_WORK/_c_native_build.log"
  fi

  if command -v clang >/dev/null 2>&1 && [[ -d /usr/include/wasm32-wasi ]]; then
    echo "Building C-wasm(wasi) delta-log bench binary (clang --target=wasm32-wasi, apt wasi-libc) ..."
    WCFLAGS=(--target=wasm32-wasi --sysroot=/usr -O2 -I "$DL_OV" -I "$KRML_HOME/include" -I "$KRML_HOME/krmllib/dist/minimal" -I "$DL_DIR")
    WOBJ="$DL_WORK/wasm-obj"
    mkdir -p "$WOBJ"
    WCC_RC=0
    {
      clang -c "${WCFLAGS[@]}" "$DL_DIR/Factoidal_DeltaLog.c" -o "$WOBJ/Factoidal_DeltaLog.o" &&
      clang -c "${WCFLAGS[@]}" "$DL_DIR/krmlinit.c" -o "$WOBJ/krmlinit.o" &&
      clang -c "${WCFLAGS[@]}" "$DL_OV/prims64.c" -o "$WOBJ/prims64.o" &&
      for f in fstar_char fstar_string fstar_uint32; do
        clang -c "${WCFLAGS[@]}" -I "$KRML_HOME/krmllib/dist/generic" "$KRML_HOME/krmllib/dist/generic/$f.c" -o "$WOBJ/$f.o" || exit 1
      done &&
      clang -c "${WCFLAGS[@]}" "$DL_DIR/demo/deltalog_stubs.c" -o "$WOBJ/deltalog_stubs.o" &&
      clang -c "${WCFLAGS[@]}" tools/deltalog-bench/deltalog_bench.c -o "$WOBJ/deltalog_bench.o" &&
      clang --target=wasm32-wasi --sysroot=/usr -O2 \
        -Wl,-z,stack-size=1073741824 -Wl,--max-memory=4294901760 -Wl,--initial-memory=1179648000 \
        "$WOBJ/deltalog_bench.o" "$WOBJ/Factoidal_DeltaLog.o" "$WOBJ/krmlinit.o" "$WOBJ/prims64.o" \
        "$WOBJ/fstar_char.o" "$WOBJ/fstar_string.o" "$WOBJ/fstar_uint32.o" "$WOBJ/deltalog_stubs.o" \
        -o "$C_BENCH_WASM"
    } > "$DL_WORK/_c_wasm_build.log" 2>&1 || WCC_RC=$?
    if [[ "$WCC_RC" -eq 0 && -f "$C_BENCH_WASM" ]]; then
      HAVE_C_WASM=1
      echo "  built: $C_BENCH_WASM"
    else
      echo "  WARNING: C-wasm bench build failed (rc=$WCC_RC) -- see $DL_WORK/_c_wasm_build.log"
    fi
  else
    echo "  SKIP C-wasm: clang or /usr/include/wasm32-wasi (apt: wasi-libc, libclang-rt-18-dev-wasm32) not present"
  fi
else
  echo "  SKIP: $DL_DIR/Factoidal_DeltaLog.c not present (run tools/karamel-c-build.sh first)"
fi
echo ""

# Both native C and native OCaml need a large stack for the
# non-tail-recursive serialize_ops/parse_n_delta_entries the F* spec
# extracts (see docs/web/perf/index.md "what this reveals" --
# ~40KB of C stack per recursion frame observed; default 8MB ulimit
# overflows above ~1000-3000 entries). wasm needs BOTH V8's own
# --stack-size raised (its interpreter frame per wasm call, not the
# wasm linear-memory stack the linker flags above already grew) AND
# ulimit -s unlimited for the surrounding node process.
run_median_stack () {
  # Wraps run_timed_median in a subshell with ulimit -s unlimited.
  ( ulimit -s unlimited 2>/dev/null; run_timed_median "$@" )
}

last_run_json () {
  # The bench binaries print one JSON line per run; run_timed_median
  # redirects each run's stdout to /tmp/bench-runtimes.out, so after a
  # successful median this holds the LAST run's per-phase timings
  # (serialize_s / parse_s / total_s) -- more informative than the
  # process wall clock alone, so it rides along in the record note.
  tr -d '\t\n' < /tmp/bench-runtimes.out 2>/dev/null || echo ""
}

record_dl () {
  # $1=mode $2=engine $3=n $4=status $5=median $6=note
  record "deltalog" "$2" "$1" "$3" "$4" "$5" "$6"
  if [[ "$4" == OK ]]; then
    echo "  [$1] $2 N=$3: median ${5}s ($6)"
  else
    echo "  [$1] $2 N=$3: SKIP ($6)"
  fi
}

echo "--- 'pure' mode (hand-built batch, no SPARQL): OCaml-native / C-native / C-wasm ---"
for n in 1000 5000 10000; do
  if [[ "$HAVE_OCAML_BENCH" -eq 1 ]]; then
    median="$(run_median_stack "$OCAML_BENCH_BIN" pure "$n")"; rc=$?
    [[ $rc -eq 0 ]] && record_dl pure ocaml-native "$n" OK "$median" "$(last_run_json)" || record_dl pure ocaml-native "$n" SKIP "" "rc=$rc"
  else
    record_dl pure ocaml-native "$n" SKIP "" "bench binary not built"
  fi
  if [[ "$HAVE_C_NATIVE" -eq 1 ]]; then
    median="$(run_median_stack "$C_BENCH_NATIVE" "$n")"; rc=$?
    [[ $rc -eq 0 ]] && record_dl pure c-native "$n" OK "$median" "$(last_run_json)" || record_dl pure c-native "$n" SKIP "" "rc=$rc"
  else
    record_dl pure c-native "$n" SKIP "" "bench binary not built"
  fi
  if [[ "$HAVE_C_WASM" -eq 1 ]]; then
    median="$(run_median_stack node --stack-size=200000 "$WASI_RUNNER" "$C_BENCH_WASM" "$n")"; rc=$?
    [[ $rc -eq 0 ]] && record_dl pure c-wasm "$n" OK "$median" "$(last_run_json)" || record_dl pure c-wasm "$n" SKIP "" "rc=$rc"
  else
    record_dl pure c-wasm "$n" SKIP "" "bench binary not built"
  fi
done
echo ""

echo "--- 'pure' mode, C-native scaling beyond 10k (peak RSS via bench_rusage_run.py) ---"
for n in 100000 300000; do
  if [[ "$HAVE_C_NATIVE" -eq 1 ]]; then
    RUSAGE_JSON="$(bash -c 'ulimit -s unlimited; exec python3 "$1" /tmp/dl_rss.out /tmp/dl_rss.err "$2" "$3"' \
      _ "$REPO_ROOT/tools/bench_rusage_run.py" "$C_BENCH_NATIVE" "$n")"
    echo "  c-native pure N=$n rusage: $RUSAGE_JSON"
    record "deltalog_rss" c-native pure "$n" INFO "$RUSAGE_JSON" ""
  fi
done
if [[ "$HAVE_C_NATIVE" -eq 1 ]]; then
  echo "  (N=1,000,000 attempted separately during development of this script:"
  echo "   OOM-killed at ~15GB peak RSS after ~15s wall on this box's 15GB RAM --"
  echo "   see docs/web/perf/index.md; not re-run here to avoid destabilizing the sandbox.)"
  record "deltalog_rss" c-native pure 1000000 SKIP "" "OOM-killed at ~15GB RSS in prior manual run; not re-attempted automatically"
fi
echo ""

echo "--- 'sparql' mode (INSERT DATA -> deltaBatchToHex): OCaml-native / js / wasm ---"
echo "    (quadratic-looking SPARQL-Update-parsing wall observed -- see perf hub; capped at N<=300)"
for n in 100 300; do
  if [[ "$HAVE_OCAML_BENCH" -eq 1 ]]; then
    median="$(run_median_stack "$OCAML_BENCH_BIN" sparql "$n")"; rc=$?
    [[ $rc -eq 0 ]] && record_dl sparql ocaml-native "$n" OK "$median" "$(last_run_json)" || record_dl sparql ocaml-native "$n" SKIP "" "rc=$rc"
  fi
  median="$(run_timed_median node tools/deltalog-bench/bench-js-wasm.mjs js "$n")"; rc=$?
  [[ $rc -eq 0 ]] && record_dl sparql js-of-ocaml "$n" OK "$median" "$(last_run_json)" || record_dl sparql js-of-ocaml "$n" SKIP "" "rc=$rc"
  median="$(run_timed_median node tools/deltalog-bench/bench-js-wasm.mjs wasm "$n")"; rc=$?
  [[ $rc -eq 0 ]] && record_dl sparql wasm-of-ocaml "$n" OK "$median" "$(last_run_json)" || record_dl sparql wasm-of-ocaml "$n" SKIP "" "rc=$rc"
done
record "deltalog" all sparql 1000 SKIP "" "quadratic-looking SPARQL-Update-parsing wall: N=1000 took ~39s native vs ~0.4s at N=100 (~100x for 10x input); not attempted at larger N in this bench run"
echo ""

# =========================================================================
# Emit JSON
# =========================================================================
echo "=== Writing $OUTPUT_JSON ==="
python3 - "$OUTPUT_JSON" "$COMMIT_SHA" "$TIMESTAMP_UTC" "$RUNS" "$CAP_SECONDS" \
  "$CPU_MODEL" "$NPROC" "$NODE_VERSION" "$OCAML_VERSION" "$GCC_VERSION" "$CLANG_VERSION" "$HAVE_KRML" \
  "$RECORDS_FILE" <<'PY'
import json
import sys

(out_path, commit, ts, runs, cap, cpu, nproc, node_v, ocaml_v, gcc_v,
 clang_v, have_krml, records_path) = sys.argv[1:14]

records = []
for line in open(records_path):
    line = line.rstrip("\n")
    if not line:
        continue
    parts = line.split("\t")
    while len(parts) < 7:
        parts.append("")
    section, engine, op, size, status, median, note = parts[:7]
    rec = {
        "section": section, "engine": engine, "op": op,
        "size": size, "status": status, "note": note,
    }
    if status == "OK":
        try:
            rec["median_s"] = float(median)
        except ValueError:
            rec["raw"] = median
    elif status == "INFO":
        rec["raw"] = median
    records.append(rec)

result = {
    "commit": commit,
    "measured_at_utc": ts,
    "runs_per_measurement": int(runs),
    "cap_seconds": int(cap),
    "machine": {
        "cpu_model": cpu,
        "logical_cores": nproc,
        "node_version": node_v,
        "ocaml_version": ocaml_v,
        "gcc_version": gcc_v,
        "clang_version": clang_v,
        "krml_available": have_krml == "1",
    },
    "records": records,
}
with open(out_path, "w") as f:
    json.dump(result, f, indent=2)
    f.write("\n")
print(f"  wrote {len(records)} records to {out_path}")
PY

echo ""
echo "Done. Full log: $MAIN_LOG"
