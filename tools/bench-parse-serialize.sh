#!/bin/bash
# tools/bench-parse-serialize.sh
#
# Parse + serialize throughput benchmark, run against the COMMITTED
# platform binaries (bin/<platform>/factoidal, factoidal-dump-nq) --
# no F* toolchain required. See skills/perf-benchmarking/SKILL.md for
# the measurement discipline this follows (median-of-N, never
# conflate with correctness) and formal/fstar/bench-turtle-metrics.sh
# for the sibling harness this complements (that one rebuilds from
# ocaml-output/ and only covers Turtle; this one runs the shipped
# binary across N-Triples / Turtle / RDF/XML plus serialize ops).
#
# Measures, at 10k / 100k / 1,000,000 triples (deterministic synthetic
# fixtures, generated once per run):
#   - Parse:        factoidal count FILE          (nt, turtle, rdfxml)
#   - Serialize:    factoidal-dump-nq FILE        (-> sorted N-Quads)
#   - Canonicalize: factoidal canonicalize FILE   (RDFC-1.0 canonical N-Quads;
#                                                   10k/100k only -- 1M is a
#                                                   documented skip, not a
#                                                   silent omission)
# Also measures the UK Parliament TriG corpus at
# third_party/data/ukparliament/*.trig if it is present in the
# checkout; skipped gracefully (documented, not silent) if absent.
#
# IMPORTANT -- "serialize" and "canonicalize" here are END-TO-END
# (parse included). The committed CLI has no parse-once/format-many
# entry point, so there is no way to isolate pure serialization cost.
# Read these numbers as "on-disk RDF text -> on-disk N-Quads /
# canonical N-Quads", not as a serializer-only microbenchmark. This
# caveat is repeated in the JSON output and the dashboard fragment so
# it can't be misread later (CLAUDE.md anti-pattern #25: no
# unlabelled/misleading numbers).
#
# Anti-pattern #14: no `|| true` swallowing -- every exit code is
# captured explicitly and inspected.
# Anti-pattern #17: every single run is capped at CAP_SECONDS via
# `timeout`; a trip is recorded as a documented skip, never a silent
# omission or an indefinite hang.
#
# Outputs:
#   stdout                                             human-readable table
#   docs/test-results/perf-parse-serialize.json        machine-readable
#   docs/test-results/perf-parse-serialize.fragment.html
#                                                       dashboard HTML fragment,
#                                                       included fail-soft by
#                                                       generate-report.sh
#
# Usage: tools/bench-parse-serialize.sh [--runs N] [--cap-seconds N]
#
# Portability: Linux only (relies on bash 5 $EPOCHREALTIME and the
# committed bin/linux-x86_64 binaries). Mirrors the platform scope of
# ukparliament-bench.yml.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

RUNS="${RUNS:-3}"
CAP_SECONDS="${CAP_SECONDS:-120}"
SIZES=(10000 100000 1000000)
CANONICALIZE_SIZES=(10000 100000)

# --- args --------------------------------------------------------------
while [ $# -gt 0 ]; do
  case "$1" in
    --runs) RUNS="$2"; shift 2 ;;
    --cap-seconds) CAP_SECONDS="$2"; shift 2 ;;
    *) echo "Unknown argument: $1" >&2; exit 2 ;;
  esac
done

# --- platform + binaries -------------------------------------------------
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

for bin in "$FACTOIDAL" "$DUMP_NQ"; do
  if [ ! -x "$bin" ]; then
    echo "::error::Required committed binary missing or not executable: $bin" >&2
    echo "This bench runs against committed binaries only -- no toolchain build." >&2
    exit 2
  fi
done

OUTPUT_DIR="$REPO_ROOT/docs/test-results"
JSON_OUT="$OUTPUT_DIR/perf-parse-serialize.json"
FRAGMENT_OUT="$OUTPUT_DIR/perf-parse-serialize.fragment.html"
mkdir -p "$OUTPUT_DIR"

FIXTURE_DIR="${TMPDIR:-/tmp}/factoidal-bench-parse-serialize"
mkdir -p "$FIXTURE_DIR"

TIMESTAMP_UTC="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
COMMIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"

echo "Factoidal parse + serialize throughput bench"
echo "  platform: $PLATFORM"
echo "  commit:   $COMMIT_SHA"
echo "  runs per measurement: $RUNS   cap per single run: ${CAP_SECONDS}s"
echo ""

# --- fixture generation (deterministic; regenerated each invocation) ----
echo "Generating synthetic fixtures in $FIXTURE_DIR ..."
python3 - "$FIXTURE_DIR" "${SIZES[@]}" <<'PY'
import sys
from pathlib import Path

fixture_dir = Path(sys.argv[1])
sizes = [int(s) for s in sys.argv[2:]]

for n in sizes:
    # N-Triples: full IRIs, no prefixes -- the harder case per
    # docs/claude-rules/performance.md ("full-IRI" rows).
    nt_path = fixture_dir / f"bench-{n}.nt"
    if not nt_path.exists():
        with nt_path.open("w", encoding="utf-8") as f:
            for i in range(n):
                f.write(
                    f"<http://example.org/s{i}> <http://example.org/p> "
                    f"<http://example.org/o{i}> .\n"
                )

    # Turtle: prefixed -- the common case.
    ttl_path = fixture_dir / f"bench-{n}.ttl"
    if not ttl_path.exists():
        with ttl_path.open("w", encoding="utf-8") as f:
            f.write("@prefix ex: <http://example.org/> .\n")
            for i in range(n):
                f.write(f"ex:s{i} ex:p ex:o{i} .\n")

    # RDF/XML: one rdf:Description per triple.
    rdf_path = fixture_dir / f"bench-{n}.rdf"
    if not rdf_path.exists():
        with rdf_path.open("w", encoding="utf-8") as f:
            f.write('<?xml version="1.0"?>\n')
            f.write(
                '<rdf:RDF xmlns:rdf='
                '"http://www.w3.org/1999/02/22-rdf-syntax-ns#" '
                'xmlns:ex="http://example.org/">\n'
            )
            for i in range(n):
                f.write(f'  <rdf:Description rdf:about="http://example.org/s{i}">\n')
                f.write(f'    <ex:p rdf:resource="http://example.org/o{i}"/>\n')
                f.write('  </rdf:Description>\n')
            f.write('</rdf:RDF>\n')

print("Fixtures ready:", ", ".join(f"{n}" for n in sizes))
PY
echo ""

# --- UK Parliament corpus (real-world check; skip gracefully if absent) --
UKPAR_CORPUS=""
for candidate in "$REPO_ROOT"/third_party/data/ukparliament/*.trig; do
  if [ -f "$candidate" ]; then
    SIZE_BYTES=$(wc -c < "$candidate" | tr -d ' ')
    if [ "$SIZE_BYTES" -ge 1048576 ]; then
      UKPAR_CORPUS="$candidate"
    fi
    break
  fi
done

# --- measurement plumbing -------------------------------------------------
# Accumulators: newline-separated records, one per measured (or skipped)
# entry, built up as we go and rendered into JSON/table/fragment at the end.
# Record shape (tab-separated): STATUS<TAB>op<TAB>format<TAB>size<TAB>seconds_median<TAB>triples_per_sec<TAB>note
RECORDS_FILE="$(mktemp)"
trap 'rm -f "$RECORDS_FILE"' EXIT

# run_timed_median CMD... -- runs CMD $RUNS times (each capped at
# CAP_SECONDS), discards stdout, captures wall time via bash's
# $EPOCHREALTIME (no external `time` binary dependency -- CI images and
# this sandbox don't reliably ship GNU `time`). Prints the median
# duration (seconds, 4dp) on success. Return codes:
#   0   success; median printed on stdout
#   124 a run hit the CAP_SECONDS timeout (caller should record a skip)
#   1   a run failed for a non-timeout reason (caller should record a skip)
run_timed_median () {
  local durations=()
  local i rc t0 t1
  for i in $(seq 1 "$RUNS"); do
    t0="$EPOCHREALTIME"
    timeout "$CAP_SECONDS" "$@" >/dev/null 2>/tmp/bench-parse-serialize.err
    rc=$?
    t1="$EPOCHREALTIME"
    if [ "$rc" -eq 124 ]; then
      echo "::warning:: run $i of '$*' exceeded ${CAP_SECONDS}s cap" >&2
      rm -f /tmp/bench-parse-serialize.err
      return 124
    fi
    if [ "$rc" -ne 0 ]; then
      echo "::warning:: run $i of '$*' failed rc=$rc" >&2
      cat /tmp/bench-parse-serialize.err >&2
      rm -f /tmp/bench-parse-serialize.err
      return 1
    fi
    rm -f /tmp/bench-parse-serialize.err
    durations+=("$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.4f", b-a}')")
  done
  python3 -c "
import statistics
vals = [float(x) for x in '''${durations[*]}'''.split()]
print(f'{statistics.median(vals):.4f}')
"
}

record_measurement () {
  # $1=op $2=format $3=size ; remaining args = command to time
  local op="$1" fmt="$2" size="$3"
  shift 3
  local median rc
  median="$(run_timed_median "$@")"
  rc=$?
  if [ "$rc" -eq 124 ]; then
    printf 'SKIP\t%s\t%s\t%s\t\t\ttimeout: exceeded %ss cap\n' \
      "$op" "$fmt" "$size" "$CAP_SECONDS" >> "$RECORDS_FILE"
    return
  fi
  if [ "$rc" -ne 0 ]; then
    printf 'SKIP\t%s\t%s\t%s\t\t\tcommand failed (see stderr above)\n' \
      "$op" "$fmt" "$size" >> "$RECORDS_FILE"
    return
  fi
  local rate
  rate=$(awk -v s="$size" -v m="$median" 'BEGIN{ if (m > 0) printf "%.0f", s/m; else print 0 }')
  printf 'OK\t%s\t%s\t%s\t%s\t%s\t\n' "$op" "$fmt" "$size" "$median" "$rate" >> "$RECORDS_FILE"
  echo "  $op $fmt $size triples: median ${median}s (${rate} triples/s)"
}

record_skip () {
  # $1=op $2=format $3=size $4=reason
  printf 'SKIP\t%s\t%s\t%s\t\t\t%s\n' "$1" "$2" "$3" "$4" >> "$RECORDS_FILE"
  echo "  $1 $2 $3: SKIPPED ($4)"
}

# --- parse throughput: nt / turtle / rdfxml at each size ------------------
echo "=== Parse throughput (factoidal count) ==="
for n in "${SIZES[@]}"; do
  record_measurement parse nt      "$n" "$FACTOIDAL" count "$FIXTURE_DIR/bench-$n.nt"
  record_measurement parse turtle  "$n" "$FACTOIDAL" count "$FIXTURE_DIR/bench-$n.ttl"
  record_measurement parse rdfxml  "$n" "$FACTOIDAL" count "$FIXTURE_DIR/bench-$n.rdf"
done
echo ""

# --- serialize throughput: dump-nq (parse + sorted N-Quads dump) ---------
# Source format fixed to N-Triples so the number isolates the
# dump-nq path from cross-format parse-cost differences already
# captured above.
echo "=== Serialize throughput (factoidal-dump-nq, end-to-end incl. parse) ==="
for n in "${SIZES[@]}"; do
  record_measurement serialize_nq nt "$n" "$DUMP_NQ" "$FIXTURE_DIR/bench-$n.nt"
done
echo ""

# --- canonicalize throughput: RDFC-1.0 (10k/100k only; 1M documented skip) -
echo "=== Canonicalize throughput (factoidal canonicalize, end-to-end incl. parse) ==="
for n in "${CANONICALIZE_SIZES[@]}"; do
  record_measurement canonicalize nt "$n" "$FACTOIDAL" canonicalize "$FIXTURE_DIR/bench-$n.nt"
done
record_skip canonicalize nt 1000000 \
  "spec-capped: canonicalize measured only up to 100k triples per task scope; not attempted at 1M"
echo ""

# --- UK Parliament corpus (real-world parse check) ------------------------
echo "=== UK Parliament corpus (real-world check) ==="
if [ -n "$UKPAR_CORPUS" ]; then
  record_measurement parse trig "corpus:$(basename "$UKPAR_CORPUS")" "$FACTOIDAL" count "$UKPAR_CORPUS"
else
  record_skip parse trig corpus \
    "third_party/data/ukparliament/*.trig not present (or looks like an LFS pointer) in this checkout"
fi
echo ""

# --- render: human-readable table ----------------------------------------
echo "=== Summary ==="
printf '%-14s %-8s %-16s %10s %16s\n' "op" "format" "size" "seconds" "triples/s"
printf '%-14s %-8s %-16s %10s %16s\n' "--" "------" "----" "-------" "---------"
while IFS=$'\t' read -r status op fmt size median rate note; do
  if [ "$status" = "OK" ]; then
    printf '%-14s %-8s %-16s %10s %16s\n' "$op" "$fmt" "$size" "${median}s" "$rate"
  else
    printf '%-14s %-8s %-16s %10s %16s   SKIP: %s\n' "$op" "$fmt" "$size" "-" "-" "$note"
  fi
done < "$RECORDS_FILE"
echo ""
echo "NOTE: serialize_nq and canonicalize are end-to-end (parse + operation)."
echo "      There is no parse-once/format-many path in the committed CLI."

# --- render: JSON ----------------------------------------------------------
{
  printf '{\n'
  printf '  "timestamp": "%s",\n' "$TIMESTAMP_UTC"
  printf '  "commit": "%s",\n' "$COMMIT_SHA"
  printf '  "platform": "%s",\n' "$PLATFORM"
  printf '  "runs_per_measurement": %s,\n' "$RUNS"
  printf '  "cap_seconds_per_run": %s,\n' "$CAP_SECONDS"
  printf '  "note": "serialize_nq and canonicalize ops are end-to-end (parse included); there is no parse-once/format-many path in the committed CLI.",\n'
  printf '  "results": [\n'
  first=1
  while IFS=$'\t' read -r status op fmt size median rate note; do
    [ "$status" = "OK" ] || continue
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    printf '    {"op":"%s","format":"%s","size":"%s","seconds_median":%s,"triples_per_sec":%s}' \
      "$op" "$fmt" "$size" "$median" "$rate"
  done < "$RECORDS_FILE"
  printf '\n  ],\n'
  printf '  "skipped": [\n'
  first=1
  while IFS=$'\t' read -r status op fmt size median rate note; do
    [ "$status" = "SKIP" ] || continue
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    esc_note=$(printf '%s' "$note" | sed 's/\\/\\\\/g; s/"/\\"/g')
    printf '    {"op":"%s","format":"%s","size":"%s","reason":"%s"}' \
      "$op" "$fmt" "$size" "$esc_note"
  done < "$RECORDS_FILE"
  printf '\n  ]\n'
  printf '}\n'
} > "$JSON_OUT"
echo ""
echo "JSON written: $JSON_OUT"

# --- render: dashboard HTML fragment (included fail-soft by generate-report.sh) -
{
  printf '<h2>Parse + serialize throughput <span class="inline-numbers">measured %s &middot; commit <a href="https://github.com/danbri/factoidal/commit/%s">%s</a></span></h2>\n' \
    "$TIMESTAMP_UTC" "$COMMIT_SHA" "${COMMIT_SHA:0:7}"
  printf '<p style="margin: 0.3em 0 0.8em; color: var(--muted); font-size: 0.85em;">\n'
  printf '  Measured against the committed <code>bin/%s/factoidal</code> binary (median of %s runs, no toolchain build). ' \
    "$PLATFORM" "$RUNS"
  printf '  <strong>serialize_nq</strong> and <strong>canonicalize</strong> are end-to-end (parse included) -- the CLI has no parse-once/format-many entry point.\n'
  printf '  Source: <a href="https://github.com/danbri/factoidal/blob/main/tools/bench-parse-serialize.sh">tools/bench-parse-serialize.sh</a>, '
  printf '  raw data <a href="perf-parse-serialize.json">perf-parse-serialize.json</a>.\n'
  printf '</p>\n'
  printf '<div style="overflow-x:auto;">\n'
  printf '<table style="border-collapse:collapse; width:100%%; font-size:0.88em;">\n'
  printf '<thead><tr>'
  for h in Operation Format Size "Median seconds" "Triples/sec"; do
    printf '<th style="text-align:left; border-bottom:1px solid var(--border); padding:0.3em 0.6em;">%s</th>' "$h"
  done
  printf '</tr></thead>\n<tbody>\n'
  while IFS=$'\t' read -r status op fmt size median rate note; do
    if [ "$status" = "OK" ]; then
      printf '<tr><td style="padding:0.25em 0.6em; font-family:ui-monospace,monospace;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%ss</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td></tr>\n' \
        "$op" "$fmt" "$size" "$median" "$rate"
    else
      esc_note=$(printf '%s' "$note" | sed 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g')
      printf '<tr style="color:var(--muted);"><td style="padding:0.25em 0.6em; font-family:ui-monospace,monospace;">%s</td><td style="padding:0.25em 0.6em;">%s</td><td style="padding:0.25em 0.6em; text-align:right;">%s</td><td colspan="2" style="padding:0.25em 0.6em;"><em>skipped: %s</em></td></tr>\n' \
        "$op" "$fmt" "$size" "$esc_note"
    fi
  done < "$RECORDS_FILE"
  printf '</tbody></table>\n'
  printf '</div>\n'
} > "$FRAGMENT_OUT"
echo "Fragment written: $FRAGMENT_OUT"
