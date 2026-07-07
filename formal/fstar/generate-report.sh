#!/bin/bash
# Generate a W3C conformance report for docs/test-results/.
#
# Inputs  (cached from the w3c_runner invocation):
#   ocaml-output/sparql_results.log
#   ocaml-output/rdf_results.log
#
# Outputs:
#   docs/test-results/index.html            (human-readable)
#   docs/test-results/latest.csv            (one row per suite)
#   docs/test-results/latest.json           (totals + suites)
#   docs/test-results/history/<ts>.csv      (timestamped copy)
#   docs/test-results/history/<ts>.json     (timestamped copy)
#
# Usage:
#   ./generate-report.sh                    # re-generate from cached logs
#   ./generate-report.sh --run              # re-run the W3C tests first
#
# Portability: BSD/macOS + GNU/Linux. No grep -P.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
OCAML_DIR="$SCRIPT_DIR/ocaml-output"
OUTPUT_DIR="$SCRIPT_DIR/../../docs/test-results"
HISTORY_DIR="$OUTPUT_DIR/history"
SPARQL_LOG="$OCAML_DIR/sparql_results.log"
RDF_LOG="$OCAML_DIR/rdf_results.log"
OWL_LOG="$OCAML_DIR/owl_profile_rl_results.log"
# Phase 2.3 DL catalog logs (added 2026-05-08). Per-catalog log
# path so we can score independently and surface separate dashboard
# rows. Loop-driven below.
OWL_TPE_LOG="$OCAML_DIR/owl_type_positive_entailment_results.log"
OWL_TNE_LOG="$OCAML_DIR/owl_type_negative_entailment_results.log"
OWL_TCON_LOG="$OCAML_DIR/owl_type_consistency_results.log"
OWL_TINC_LOG="$OCAML_DIR/owl_type_inconsistency_results.log"
OWL_EL_LOG="$OCAML_DIR/owl_profile_el_results.log"
OWL_QL_LOG="$OCAML_DIR/owl_profile_ql_results.log"
OWL_SEMDL_LOG="$OCAML_DIR/owl_semantics_direct_results.log"
RDFC10_LOG="$OCAML_DIR/rdfc10_results.log"
# Wave (2026-07-05): SHACL / ShEx / JSON-LD / RML / RIF Core / VC —
# same "committed binary, no toolchain needed" pattern as owl_runner /
# rdfc10_runner above. Log paths match each suite's
# .github/test-suites/<suite>.yaml `log_path` field so the dashboard,
# tools/dispatch_test_suites.sh, and a human reading the manifest all
# agree on where the data lives.
SHACL_CORE_LOG="$OCAML_DIR/shacl_results.log"
SHACL_SPARQL_LOG="$OCAML_DIR/shacl_sparql_results.log"
SHEX_LOG="$OCAML_DIR/shex_results.log"
JSONLD_LOG="$OCAML_DIR/jsonld_results.log"
RML_LOG="$OCAML_DIR/rml_results.log"
RIFCORE_LOG="$OCAML_DIR/rif_results.log"
VC_LOG="$OCAML_DIR/vc_results.log"

mkdir -p "$OUTPUT_DIR" "$HISTORY_DIR"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/w3c_runner"
    OWL_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/owl_runner"
    RDFC10_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/rdfc10_runner"
    SHACL_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/shacl_runner"
    SHEX_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/shex_runner"
    JSONLD_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/jsonld_runner"
    RML_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/rml_runner"
    RIF_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/rif_runner"
    VC_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/vc_runner"
    ;;
  Linux-x86_64)
    RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/w3c_runner"
    OWL_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/owl_runner"
    RDFC10_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/rdfc10_runner"
    SHACL_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/shacl_runner"
    SHEX_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/shex_runner"
    JSONLD_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/jsonld_runner"
    RML_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/rml_runner"
    RIF_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/rif_runner"
    VC_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/vc_runner"
    ;;
  *)
    RUNNER="$OCAML_DIR/w3c_runner"
    OWL_RUNNER="$OCAML_DIR/owl_runner"
    RDFC10_RUNNER="$OCAML_DIR/rdfc10_runner"
    SHACL_RUNNER="$OCAML_DIR/shacl_runner"
    SHEX_RUNNER="$OCAML_DIR/shex_runner"
    JSONLD_RUNNER="$OCAML_DIR/jsonld_runner"
    RML_RUNNER="$OCAML_DIR/rml_runner"
    RIF_RUNNER="$OCAML_DIR/rif_runner"
    VC_RUNNER="$OCAML_DIR/vc_runner"
    ;;
esac

if [ "$1" = "--run" ]; then
  [ -x "$RUNNER" ] || { echo "Runner not found or not executable: $RUNNER" >&2; exit 2; }
  # Runner exits nonzero when any test fails (by design). `|| true` keeps
  # the log either way — the per-suite numbers are what we need.
  # Always run from repo root so the runner's relative third_party/ paths
  # resolve correctly regardless of caller CWD. Without this, rdf-xml
  # base-URI tests false-fail with "expected X, got X" mismatches.
  REPO_ROOT="$SCRIPT_DIR/../.."
  echo "Running SPARQL 1.1 suite…"
  ( cd "$REPO_ROOT" && "$RUNNER"       > "$SPARQL_LOG" 2>&1 ) || true
  echo "  done."
  echo "Running RDF 1.1 suite…"
  ( cd "$REPO_ROOT" && "$RUNNER" --rdf > "$RDF_LOG" 2>&1 ) || true
  echo "  done."
  if [ -x "$OWL_RUNNER" ]; then
    echo "Running OWL 2 RL profile suite (PositiveEntailmentTests)…"
    ( cd "$REPO_ROOT" && "$OWL_RUNNER" > "$OWL_LOG" 2>&1 ) || true
    echo "  done."
    # Phase 2.3 — OWL DL catalogs. Runs each catalog in turn under
    # RL semantics (DL via Tableau is a follow-up; see #238 about
    # Tableau perf). RL is sound but incomplete for DL — false-
    # negative scores on DL-only entailments are expected; baseline
    # gives a "what RL can certify" floor that DL strictly improves.
    for entry in \
        "type-positive-entailment.rdf $OWL_TPE_LOG    240" \
        "type-negative-entailment.rdf $OWL_TNE_LOG     60" \
        "type-consistency.rdf         $OWL_TCON_LOG   600" \
        "type-inconsistency.rdf       $OWL_TINC_LOG   240" \
        "profile-EL.rdf               $OWL_EL_LOG     120" \
        "profile-QL.rdf               $OWL_QL_LOG     120" \
        "semantics-direct.rdf         $OWL_SEMDL_LOG  900"; do
      IFS=' ' read -r catalog log_path budget <<< "$entry"
      echo "Running OWL 2 catalog $catalog (RL, ${budget}s budget)…"
      ( cd "$REPO_ROOT" && timeout "$budget" "$OWL_RUNNER" \
          "third_party/testing/owl/$catalog" \
          > "$log_path" 2>&1 ) || true
      echo "  done."
    done
  else
    echo "  owl_runner not found at $OWL_RUNNER — skipping OWL 2 RL suite." >&2
  fi
  if [ -x "$RDFC10_RUNNER" ]; then
    echo "Running RDFC-1.0 (RDF Dataset Canonicalization) suite…"
    ( cd "$REPO_ROOT" && "$RDFC10_RUNNER" > "$RDFC10_LOG" 2>&1 ) || true
    echo "  done."
  else
    echo "  rdfc10_runner not found at $RDFC10_RUNNER — skipping RDFC-1.0 suite." >&2
  fi

  # Wave (2026-07-05) — SHACL / ShEx / JSON-LD / RML / RIF Core / VC.
  # Same committed-binary pattern as owl_runner/rdfc10_runner above: each
  # runner is optional (guarded by -x), capped with `timeout` so a stuck
  # runner can't hang the dashboard refresh, and failure never aborts the
  # script (`|| true`) — the log is the source of truth either way, and a
  # missing/empty log means the scrape step below reports "not measured
  # this run" rather than fabricating a score.
  run_optional_suite () {
    local label="$1" runner="$2" log="$3" budget="$4"; shift 4
    if [ -x "$runner" ]; then
      echo "Running $label…"
      ( cd "$REPO_ROOT" && timeout "$budget" "$runner" "$@" > "$log" 2>&1 ) || true
      echo "  done."
    else
      echo "  $(basename "$runner") not found at $runner — skipping $label." >&2
    fi
  }
  run_optional_suite "SHACL Core suite"               "$SHACL_RUNNER"  "$SHACL_CORE_LOG"   60
  run_optional_suite "SHACL SPARQL-constraints suite" "$SHACL_RUNNER"  "$SHACL_SPARQL_LOG" 60 \
    "third_party/testing/shacl/data-shapes-test-suite/tests/sparql/manifest.ttl"
  run_optional_suite "ShEx validation suite"          "$SHEX_RUNNER"   "$SHEX_LOG"    180
  run_optional_suite "JSON-LD 1.1 toRdf suite"        "$JSONLD_RUNNER" "$JSONLD_LOG"   90
  run_optional_suite "RML rml-core suite"             "$RML_RUNNER"    "$RML_LOG"      90
  run_optional_suite "RIF Core suite"                 "$RIF_RUNNER"    "$RIFCORE_LOG"  90
  run_optional_suite "VC Data Model 2.0 stage-1 suite" "$VC_RUNNER"    "$VC_LOG"       60
fi

if [ ! -f "$SPARQL_LOG" ] || [ ! -f "$RDF_LOG" ]; then
  echo "No cached test logs. Run with --run first." >&2
  exit 1
fi

# --- Scrape per-suite lines --------------------------------------------------
# Suite lines look like:   add  pass:8 fail:0 skip:0 unsupported:0
SPARQL_SUITES=$(grep '^  [a-z]' "$SPARQL_LOG" | grep 'pass:' || true)
RDF_SUITES=$(grep    '^  [a-z]' "$RDF_LOG"    | grep 'pass:' || true)

extract_field () {
  # $1 = field name, $2 = multi-line blob
  echo "$2" | sed -nE "s/.*${1}:([0-9]+).*/\\1/p" | awk '{s+=$1}END{print s+0}'
}

SPARQL_PASS=$(extract_field  pass        "$SPARQL_SUITES")
SPARQL_FAIL=$(extract_field  fail        "$SPARQL_SUITES")
SPARQL_SKIP=$(extract_field  skip        "$SPARQL_SUITES")
SPARQL_UNSUP=$(extract_field unsupported "$SPARQL_SUITES")
RDF_PASS=$(extract_field     pass        "$RDF_SUITES")
RDF_FAIL=$(extract_field     fail        "$RDF_SUITES")
RDF_SKIP=$(extract_field     skip        "$RDF_SUITES")
RDF_UNSUP=$(extract_field    unsupported "$RDF_SUITES")

# --- OWL 2 RL scoreboard (orthogonal to the SPARQL/RDF tables) --------------
# Score line in owl_runner stdout:
#   Profile-RL PositiveEntailmentTests: 3 pass, 27 fail (out of 30) in 0.39s
OWL_PASS=0; OWL_FAIL=0; OWL_TOTAL=0; OWL_PRESENT=0
OWL_NEG_PASS=0; OWL_NEG_FAIL=0; OWL_NEG_TOTAL=0; OWL_NEG_PRESENT=0
if [ -f "$OWL_LOG" ]; then
  OWL_LINE=$(grep -E '^Profile-RL PositiveEntailmentTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_LINE" ]; then
    OWL_PRESENT=1
    OWL_PASS=$(echo "$OWL_LINE"  | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_FAIL=$(echo "$OWL_LINE"  | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_TOTAL=$(echo "$OWL_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    OWL_PASS=${OWL_PASS:-0}
    OWL_FAIL=${OWL_FAIL:-0}
    OWL_TOTAL=${OWL_TOTAL:-0}
  fi
  # Phase 2.1 — NegativeEntailmentTest (added 2026-05-08).
  OWL_NEG_LINE=$(grep -E '^Profile-RL NegativeEntailmentTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_NEG_LINE" ]; then
    OWL_NEG_PRESENT=1
    OWL_NEG_PASS=$(echo  "$OWL_NEG_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_NEG_FAIL=$(echo  "$OWL_NEG_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_NEG_TOTAL=$(echo "$OWL_NEG_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    OWL_NEG_PASS=${OWL_NEG_PASS:-0}
    OWL_NEG_FAIL=${OWL_NEG_FAIL:-0}
    OWL_NEG_TOTAL=${OWL_NEG_TOTAL:-0}
  fi
  # Phase 2.2 — ConsistencyTest + InconsistencyTest (added 2026-05-08).
  OWL_CONS_LINE=$(grep -E '^Profile-RL ConsistencyTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_CONS_LINE" ]; then
    OWL_CONS_PRESENT=1
    OWL_CONS_PASS=$(echo  "$OWL_CONS_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_CONS_FAIL=$(echo  "$OWL_CONS_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_CONS_TOTAL=$(echo "$OWL_CONS_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
  fi
  OWL_INC_LINE=$(grep -E '^Profile-RL InconsistencyTests:' "$OWL_LOG" | tail -1 || true)
  if [ -n "$OWL_INC_LINE" ]; then
    OWL_INC_PRESENT=1
    OWL_INC_PASS=$(echo  "$OWL_INC_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    OWL_INC_FAIL=$(echo  "$OWL_INC_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    OWL_INC_TOTAL=$(echo "$OWL_INC_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
  fi
fi
OWL_CONS_PRESENT=${OWL_CONS_PRESENT:-0}
OWL_CONS_PASS=${OWL_CONS_PASS:-0}; OWL_CONS_FAIL=${OWL_CONS_FAIL:-0}; OWL_CONS_TOTAL=${OWL_CONS_TOTAL:-0}
OWL_INC_PRESENT=${OWL_INC_PRESENT:-0}
OWL_INC_PASS=${OWL_INC_PASS:-0};   OWL_INC_FAIL=${OWL_INC_FAIL:-0};   OWL_INC_TOTAL=${OWL_INC_TOTAL:-0}

# Phase 2.3 — generic per-catalog parser. Reads one log file and
# extracts up to 4 score lines (Positive/NegativeEntailmentTests,
# Consistency/InconsistencyTests). Returns nothing; sets four
# 4-tuple variables prefixed by the caller-supplied prefix.
#
# Score-line shape (printed by owl_runner regardless of catalog):
#   Profile-RL <Type>Tests: N pass, M fail (out of K) in <s>s
extract_owl_scores () {
  local prefix="$1" log="$2"
  local t L p f tt
  for t in PositiveEntailmentTests NegativeEntailmentTests ConsistencyTests InconsistencyTests; do
    declare -g "${prefix}_${t}_PRESENT=0"
    declare -g "${prefix}_${t}_PASS=0"
    declare -g "${prefix}_${t}_FAIL=0"
    declare -g "${prefix}_${t}_TOTAL=0"
    [ -f "$log" ] || continue
    L=$(grep -E "^Profile-RL ${t}:" "$log" | tail -1 || true)
    [ -z "$L" ] && continue
    p=$(echo  "$L" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    f=$(echo  "$L" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    tt=$(echo "$L" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    declare -g "${prefix}_${t}_PRESENT=1"
    declare -g "${prefix}_${t}_PASS=${p:-0}"
    declare -g "${prefix}_${t}_FAIL=${f:-0}"
    declare -g "${prefix}_${t}_TOTAL=${tt:-0}"
  done
}

extract_owl_scores OWL_TPE   "$OWL_TPE_LOG"
extract_owl_scores OWL_TNE   "$OWL_TNE_LOG"
extract_owl_scores OWL_TCON  "$OWL_TCON_LOG"
extract_owl_scores OWL_TINC  "$OWL_TINC_LOG"
extract_owl_scores OWL_EL    "$OWL_EL_LOG"
extract_owl_scores OWL_QL    "$OWL_QL_LOG"
# semantics-direct.rdf — heaviest catalog (1127 tests). Runs in a
# separate scheduled workflow, not in the dashboard-refresh hot path.
extract_owl_scores OWL_SEMDL "$OWL_SEMDL_LOG"

# RIF Core scoring derived from sparql_results.log (the SPARQL
# entailment runner already executes RIF tests as part of the
# entailment regime sub-suite). We surface them on the dashboard
# as a dedicated row so RIF Core conformance is visible at a
# glance, not buried under a SPARQL row.
RIF_PRESENT=0; RIF_PASS=0; RIF_FAIL=0; RIF_TOTAL=0
if [ -f "$SPARQL_LOG" ]; then
  # `grep -c` always emits the count; exits non-zero on 0 matches.
  # Use `|| true` (NOT `|| echo 0`) so we don't double-echo the
  # zero count and end up with a multi-line value.
  RIF_PASS=$(grep -cE "^[[:space:]]+PASS: RIF " "$SPARQL_LOG" || true)
  RIF_FAIL=$(grep -cE "^[[:space:]]+FAIL: RIF " "$SPARQL_LOG" || true)
  RIF_PASS=${RIF_PASS:-0}
  RIF_FAIL=${RIF_FAIL:-0}
  RIF_TOTAL=$((RIF_PASS + RIF_FAIL))
  if [ "$RIF_TOTAL" -gt 0 ]; then
    RIF_PRESENT=1
  fi
fi

# --- RDFC-1.0 scoreboard (folded into the RDF table as suite "rdf-canon") ---
# Score line in rdfc10_runner stdout:
#   RDFC-1.0 tests: 0 pass, 67 fail, 22 stub (out of 89)
# STUB = Map / Negative entries that aren't wired in Phase 0; we report them
# in the `skip` column so they don't inflate the failure count, parallel to
# how the SPARQL runner uses skip for unsupported test types.
RDFC10_PASS=0; RDFC10_FAIL=0; RDFC10_SKIP=0; RDFC10_TOTAL=0; RDFC10_PRESENT=0
if [ -f "$RDFC10_LOG" ]; then
  RDFC10_LINE=$(grep -E '^RDFC-1\.0 tests:' "$RDFC10_LOG" | tail -1 || true)
  if [ -n "$RDFC10_LINE" ]; then
    RDFC10_PRESENT=1
    RDFC10_PASS=$(echo  "$RDFC10_LINE" | sed -nE 's/.* ([0-9]+) pass.*/\1/p')
    RDFC10_FAIL=$(echo  "$RDFC10_LINE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')
    RDFC10_SKIP=$(echo  "$RDFC10_LINE" | sed -nE 's/.* ([0-9]+) stub.*/\1/p')
    RDFC10_TOTAL=$(echo "$RDFC10_LINE" | sed -nE 's/.*out of ([0-9]+).*/\1/p')
    RDFC10_PASS=${RDFC10_PASS:-0}
    RDFC10_FAIL=${RDFC10_FAIL:-0}
    RDFC10_SKIP=${RDFC10_SKIP:-0}
    RDFC10_TOTAL=${RDFC10_TOTAL:-0}
  fi
fi

# --- Generic "last summary line" scraper -----------------------------------
# Shared by the SHACL / ShEx / JSON-LD / RML / RIF Core / VC suites added
# 2026-07-05. Each runner prints its own final tally line ending
# "(out of N)"; the label vocabulary differs per runner (pass/fail/
# mismatch/skip/skipped/deferred/stub) so we SUM matching tokens rather
# than hard-coding one shape — e.g. shex_runner's "N pass, N mismatch,
# N deferred, N skipped (out of N)" folds mismatch into the fail bucket
# and deferred+skipped into the skip bucket. Missing log or no matching
# line => PRESENT stays 0 and every count stays 0, which the HTML/CSV/
# JSON emitters below render as "not measured this run" — never a
# fabricated number (CLAUDE.md anti-pattern #3/#25).
scrape_last_summary () {
  local prefix="$1" log="$2" anchor="${3:-}"
  declare -g "${prefix}_PRESENT=0"
  declare -g "${prefix}_PASS=0"
  declare -g "${prefix}_FAIL=0"
  declare -g "${prefix}_SKIP=0"
  declare -g "${prefix}_TOTAL=0"
  [ -f "$log" ] || return 0
  local line
  if [ -n "$anchor" ]; then
    line=$(grep -E "$anchor" "$log" 2>/dev/null | tail -1 || true)
  else
    line=$(grep -E '\(out of [0-9]+\)[[:space:]]*$' "$log" 2>/dev/null | tail -1 || true)
  fi
  [ -z "$line" ] && return 0
  local p f s t
  p=$(echo "$line" | grep -oE '[0-9]+ pass'                         | awk '{s+=$1} END{print s+0}')
  f=$(echo "$line" | grep -oE '[0-9]+ (fail|mismatch)'              | awk '{s+=$1} END{print s+0}')
  s=$(echo "$line" | grep -oE '[0-9]+ (skip|skipped|deferred|stub)' | awk '{s+=$1} END{print s+0}')
  t=$(echo "$line" | sed -nE 's/.*\(out of ([0-9]+)\).*/\1/p')
  declare -g "${prefix}_PRESENT=1"
  declare -g "${prefix}_PASS=${p:-0}"
  declare -g "${prefix}_FAIL=${f:-0}"
  declare -g "${prefix}_SKIP=${s:-0}"
  declare -g "${prefix}_TOTAL=${t:-0}"
}

# SHACL / ShEx / JSON-LD / RML: one final summary line each, no ambiguity.
scrape_last_summary SHACL_CORE   "$SHACL_CORE_LOG"
scrape_last_summary SHACL_SPARQL "$SHACL_SPARQL_LOG"
scrape_last_summary SHEX         "$SHEX_LOG"
scrape_last_summary JSONLD       "$JSONLD_LOG"
scrape_last_summary RML          "$RML_LOG"
scrape_last_summary VC           "$VC_LOG"
# RIF Core: rif_runner prints THREE summary lines in one log (Part 1 —
# the 4 vendored SPARQL-manifest cases; Part 2 — the 46-test W3C
# Core_v1.22 corpus walk; and a combined total) — anchor each explicitly
# rather than taking "the last line", since all three coexist.
scrape_last_summary RIFCORE_PART1    "$RIFCORE_LOG" '^rif \(original'
scrape_last_summary RIFCORE_PART2    "$RIFCORE_LOG" '^rif-core-suite'
scrape_last_summary RIFCORE_COMBINED "$RIFCORE_LOG" '^rif TOTAL:'

# --- Cross-suite family roll-ups --------------------------------------------
# Sums PASS/FAIL/SKIP/TOTAL across a list of "<PREFIX>" scrape results
# (only counting prefixes that are PRESENT), plus an ANY flag so a family
# with zero measured suites renders as "not measured this run" instead of
# a fabricated all-zero row.
sum_family () {
  local pfx tp=0 tf=0 ts=0 tt=0 any=0
  local pv fv sv tv prv
  for pfx in $1; do
    pv="${pfx}_PASS";  fv="${pfx}_FAIL"; sv="${pfx}_SKIP"
    tv="${pfx}_TOTAL"; prv="${pfx}_PRESENT"
    if [ "${!prv:-0}" -eq 1 ]; then
      any=1
      tp=$((tp + ${!pv:-0})); tf=$((tf + ${!fv:-0}))
      ts=$((ts + ${!sv:-0})); tt=$((tt + ${!tv:-0}))
    fi
  done
  echo "$tp $tf $ts $tt $any"
}
read -r SHAPES_PASS SHAPES_FAIL SHAPES_SKIP SHAPES_TOTAL SHAPES_ANY <<< "$(sum_family "SHACL_CORE SHACL_SPARQL SHEX")"

SPARQL_TOTAL=$((SPARQL_PASS + SPARQL_FAIL + SPARQL_SKIP + SPARQL_UNSUP))
RDF_TOTAL=$((RDF_PASS + RDF_FAIL + RDF_SKIP + RDF_UNSUP))
COMBINED_PASS=$((SPARQL_PASS + RDF_PASS))
COMBINED_FAIL=$((SPARQL_FAIL + RDF_FAIL))
COMBINED_SKIP=$((SPARQL_SKIP + RDF_SKIP))
COMBINED_UNSUP=$((SPARQL_UNSUP + RDF_UNSUP))
COMBINED_TOTAL=$((SPARQL_TOTAL + RDF_TOTAL))

run_total=$((COMBINED_PASS + COMBINED_FAIL))
if [ "$run_total" -gt 0 ]; then
  COMBINED_PCT=$(awk -v p="$COMBINED_PASS" -v t="$run_total" 'BEGIN{printf "%.1f", 100*p/t}')
else
  COMBINED_PCT="0.0"
fi

TIMESTAMP_HUMAN=$(date -u +"%Y-%m-%d %H:%M UTC")
TIMESTAMP_ISO=$(date -u +"%Y-%m-%dT%H-%M-%SZ")
GIT_SHA=$(git -C "$SCRIPT_DIR" rev-parse --short HEAD 2>/dev/null || echo "unknown")
GIT_SHA_FULL=$(git -C "$SCRIPT_DIR" rev-parse HEAD 2>/dev/null || echo "unknown")
GIT_BRANCH=$(git -C "$SCRIPT_DIR" branch --show-current 2>/dev/null || echo "unknown")
GIT_SUBJECT=$(git -C "$SCRIPT_DIR" log -1 --pretty=%s 2>/dev/null || echo "")

# Tests-data timestamp: the most-recent commit that touched any of the
# *_results.log inputs. Distinguishes "page rendered now" from "test
# data is from N hours ago". Falls back to the page-render timestamp
# if no log files are tracked or git is unavailable.
TESTS_TIMESTAMP_RAW=$(git -C "$SCRIPT_DIR" log -1 --format='%ai' -- \
  "$SPARQL_LOG" "$RDF_LOG" "$RDFC10_LOG" "$OWL_LOG" 2>/dev/null | head -1)
if [ -n "$TESTS_TIMESTAMP_RAW" ]; then
  # macOS BSD `date` rejects the GNU -d flag; fall back through both.
  TESTS_TIMESTAMP_HUMAN=$(date -u -d "$TESTS_TIMESTAMP_RAW" +"%Y-%m-%d %H:%M UTC" 2>/dev/null || \
    date -u -j -f "%Y-%m-%d %H:%M:%S %z" "$TESTS_TIMESTAMP_RAW" +"%Y-%m-%d %H:%M UTC" 2>/dev/null || \
    echo "$TESTS_TIMESTAMP_RAW")
else
  TESTS_TIMESTAMP_HUMAN="$TIMESTAMP_HUMAN"
fi
TESTS_GIT_SHA=$(git -C "$SCRIPT_DIR" log -1 --format='%h' -- \
  "$SPARQL_LOG" "$RDF_LOG" "$RDFC10_LOG" "$OWL_LOG" 2>/dev/null || echo "unknown")

# --- CSV artifact ------------------------------------------------------------
CSV="$OUTPUT_DIR/latest.csv"
{
  echo "timestamp,commit,branch,category,suite,pass,fail,skip,unsupported"
  emit_csv_rows () {
    local blob="$1" category="$2"
    while IFS= read -r line; do
      [ -z "$line" ] && continue
      local name pass fail skip unsup
      name=$(echo  "$line" | awk '{print $1}')
      pass=$(echo  "$line" | sed -nE 's/.*pass:([0-9]+).*/\1/p')
      fail=$(echo  "$line" | sed -nE 's/.*fail:([0-9]+).*/\1/p')
      skip=$(echo  "$line" | sed -nE 's/.*skip:([0-9]+).*/\1/p')
      unsup=$(echo "$line" | sed -nE 's/.*unsupported:([0-9]+).*/\1/p')
      pass=${pass:-0}; fail=${fail:-0}; skip=${skip:-0}; unsup=${unsup:-0}
      echo "${TIMESTAMP_HUMAN},${GIT_SHA_FULL},${GIT_BRANCH},${category},${name},${pass},${fail},${skip},${unsup}"
    done <<<"$blob"
  }
  emit_csv_rows "$SPARQL_SUITES" sparql
  emit_csv_rows "$RDF_SUITES"    rdf
  if [ "$RDFC10_PRESENT" -eq 1 ]; then
    echo "${TIMESTAMP_HUMAN},${GIT_SHA_FULL},${GIT_BRANCH},rdf,rdf-canon,${RDFC10_PASS},${RDFC10_FAIL},${RDFC10_SKIP},0"
  fi
  # Wave (2026-07-05): SHACL / ShEx / JSON-LD / RML / RIF Core / VC. Only
  # emitted when PRESENT — a suite this checkout never measured gets no
  # CSV row, same convention emit_csv_rows already uses for suites absent
  # from a log (never a fabricated 0-pass row).
  emit_csv_row_if_present () {
    local prefix="$1" category="$2" name="$3"
    local prv="${prefix}_PRESENT"
    [ "${!prv:-0}" -eq 1 ] || return 0
    local pv="${prefix}_PASS" fv="${prefix}_FAIL" sv="${prefix}_SKIP"
    echo "${TIMESTAMP_HUMAN},${GIT_SHA_FULL},${GIT_BRANCH},${category},${name},${!pv},${!fv},${!sv},0"
  }
  emit_csv_row_if_present SHACL_CORE        shacl shacl-core
  emit_csv_row_if_present SHACL_SPARQL      shacl shacl-sparql
  emit_csv_row_if_present SHEX              shex  shex-validation
  emit_csv_row_if_present JSONLD            jsonld jsonld-tordf
  emit_csv_row_if_present RML               rml   rml-core
  emit_csv_row_if_present RIFCORE_PART1     rif   rif-sparql-manifest
  emit_csv_row_if_present RIFCORE_PART2     rif   rif-core-corpus
  emit_csv_row_if_present VC                vc    vc-credential-structural
} > "$CSV"
cp "$CSV" "$HISTORY_DIR/${TIMESTAMP_ISO}.csv"

# --- JSON artifact -----------------------------------------------------------
JSON="$OUTPUT_DIR/latest.json"
emit_json_suites () {
  local blob="$1" first=1
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local name pass fail skip unsup
    name=$(echo  "$line" | awk '{print $1}')
    pass=$(echo  "$line" | sed -nE 's/.*pass:([0-9]+).*/\1/p')
    fail=$(echo  "$line" | sed -nE 's/.*fail:([0-9]+).*/\1/p')
    skip=$(echo  "$line" | sed -nE 's/.*skip:([0-9]+).*/\1/p')
    unsup=$(echo "$line" | sed -nE 's/.*unsupported:([0-9]+).*/\1/p')
    pass=${pass:-0}; fail=${fail:-0}; skip=${skip:-0}; unsup=${unsup:-0}
    [ "$first" -eq 0 ] && printf ',\n'
    first=0
    printf '      {"name":"%s","pass":%s,"fail":%s,"skip":%s,"unsupported":%s}' \
      "$name" "$pass" "$fail" "$skip" "$unsup"
  done <<<"$blob"
}

{
  printf '{\n'
  printf '  "timestamp": "%s",\n' "$TIMESTAMP_HUMAN"
  printf '  "commit": "%s",\n'    "$GIT_SHA_FULL"
  printf '  "branch": "%s",\n'    "$GIT_BRANCH"
  printf '  "totals": {\n'
  printf '    "sparql":   {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s},\n' \
    "$SPARQL_PASS" "$SPARQL_FAIL" "$SPARQL_SKIP" "$SPARQL_UNSUP" "$SPARQL_TOTAL"
  printf '    "rdf":      {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s},\n' \
    "$RDF_PASS" "$RDF_FAIL" "$RDF_SKIP" "$RDF_UNSUP" "$RDF_TOTAL"
  printf '    "combined": {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s,"pass_pct_of_runnable":%s},\n' \
    "$COMBINED_PASS" "$COMBINED_FAIL" "$COMBINED_SKIP" "$COMBINED_UNSUP" "$COMBINED_TOTAL" "$COMBINED_PCT"
  printf '    "owl_rl_positive_entailment": {"pass":%s,"fail":%s,"total":%s,"catalog":"third_party/testing/owl/profile-RL.rdf"},\n' \
    "$OWL_PASS" "$OWL_FAIL" "$OWL_TOTAL"
  printf '    "rdfc10": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"spec":"https://www.w3.org/TR/rdf-canon/"},\n' \
    "$RDFC10_PASS" "$RDFC10_FAIL" "$RDFC10_SKIP" "$RDFC10_TOTAL"
  printf '    "shacl_core":   {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/shacl/"},\n' \
    "$SHACL_CORE_PASS" "$SHACL_CORE_FAIL" "$SHACL_CORE_SKIP" "$SHACL_CORE_TOTAL" "$([ "$SHACL_CORE_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "shacl_sparql": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/shacl/#sparql-constraints"},\n' \
    "$SHACL_SPARQL_PASS" "$SHACL_SPARQL_FAIL" "$SHACL_SPARQL_SKIP" "$SHACL_SPARQL_TOTAL" "$([ "$SHACL_SPARQL_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "shex":         {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://shex.io/shex-semantics/"},\n' \
    "$SHEX_PASS" "$SHEX_FAIL" "$SHEX_SKIP" "$SHEX_TOTAL" "$([ "$SHEX_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "jsonld_tordf": {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/json-ld11-api/#deserialize-json-ld-to-rdf-algorithm"},\n' \
    "$JSONLD_PASS" "$JSONLD_FAIL" "$JSONLD_SKIP" "$JSONLD_TOTAL" "$([ "$JSONLD_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "rml_core":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://kg-construct.github.io/rml-core/spec/"},\n' \
    "$RML_PASS" "$RML_FAIL" "$RML_SKIP" "$RML_TOTAL" "$([ "$RML_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "rif_core":     {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/rif-core/"},\n' \
    "$RIFCORE_COMBINED_PASS" "$RIFCORE_COMBINED_FAIL" "$RIFCORE_COMBINED_SKIP" "$RIFCORE_COMBINED_TOTAL" "$([ "$RIFCORE_COMBINED_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '    "vc_stage1":    {"pass":%s,"fail":%s,"skip":%s,"total":%s,"present":%s,"spec":"https://www.w3.org/TR/vc-data-model-2.0/"}\n' \
    "$VC_PASS" "$VC_FAIL" "$VC_SKIP" "$VC_TOTAL" "$([ "$VC_PRESENT" -eq 1 ] && echo true || echo false)"
  printf '  },\n'
  printf '  "suites": {\n'
  printf '    "sparql": [\n'
  emit_json_suites "$SPARQL_SUITES"
  printf '\n    ],\n'
  printf '    "rdf": [\n'
  emit_json_suites "$RDF_SUITES"
  printf '\n    ]\n'
  printf '  }\n'
  printf '}\n'
} > "$JSON"
cp "$JSON" "$HISTORY_DIR/${TIMESTAMP_ISO}.json"

# --- HTML suite rows ---------------------------------------------------------
# meter_segments — the shared 3-segment pass/fail/skip stacked-bar
# markup. One definition, reused by every row emitter on the page (this
# function, emit_owl_bar_row, emit_owl_skip_row, and the new
# family_suite_row) so a suite's proportions always render the same way
# regardless of which corpus it came from.
meter_segments () {
  local pass="$1" fail="$2" skip="$3" total="$4"
  local pp fp sp
  if [ "$total" -gt 0 ]; then
    pp=$(awk -v p="$pass" -v t="$total" 'BEGIN{printf "%.2f", 100*p/t}')
    fp=$(awk -v p="$fail" -v t="$total" 'BEGIN{printf "%.2f", 100*p/t}')
    sp=$(awk -v p="$skip" -v t="$total" 'BEGIN{printf "%.2f", 100*p/t}')
  else
    pp=0; fp=0; sp=0
  fi
  printf '<div class="meter"><div class="seg seg-pass" style="width:%s%%"></div><div class="seg seg-fail" style="width:%s%%"></div><div class="seg seg-skip" style="width:%s%%"></div></div>' \
    "$pp" "$fp" "$sp"
}

emit_suite_rows () {
  local blob="$1"
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local name pass fail skip unsup total row_class extra meter
    name=$(echo  "$line" | awk '{print $1}')
    pass=$(echo  "$line" | sed -nE 's/.*pass:([0-9]+).*/\1/p')
    fail=$(echo  "$line" | sed -nE 's/.*fail:([0-9]+).*/\1/p')
    skip=$(echo  "$line" | sed -nE 's/.*skip:([0-9]+).*/\1/p')
    unsup=$(echo "$line" | sed -nE 's/.*unsupported:([0-9]+).*/\1/p')
    pass=${pass:-0}; fail=${fail:-0}; skip=${skip:-0}; unsup=${unsup:-0}
    total=$((pass + fail + skip + unsup))
    if [ "$total" -eq 0 ]; then continue; fi
    if [ "$fail" -eq 0 ] && [ "$pass" -gt 0 ]; then      row_class="green"
    elif [ "$pass" -eq 0 ] && [ "$fail" -eq 0 ]; then    row_class="grey"
    else                                                  row_class="amber"
    fi
    extra=""
    [ "$skip" -gt 0 ]  && extra="skip ${skip}"
    [ "$unsup" -gt 0 ] && extra="${extra} unsup ${unsup}"
    # Inline scope hint for the SPARQL "entailment" suite — it's a
    # narrow regime suite, NOT OWL conformance, and the name alone
    # invites confusion. The OWL panel below is the larger, separate
    # universe of entailment tests.
    name_html="${name}"
    if [ "$name" = "entailment" ]; then
      name_html='entailment <small style="font-weight:normal;color:var(--muted)">(SPARQL 1.1 regime — RDFS / D-entailment, 70 tests)</small>'
    fi
    meter=$(meter_segments "$pass" "$fail" "$skip" "$total")
    # Labelled numbers, never a bare ratio (CLAUDE.md anti-pattern #25):
    # "N pass, N fail" plus an extra clause for skip/unsupported counts
    # when present.
    cat <<ROW
      <div class="suite-row ${row_class}">
        <div class="suite-name">${name_html}</div>
        ${meter}
        <div class="suite-numbers">
          <span class="p">${pass} pass</span>, <span class="f">${fail} fail</span>
          <small>${extra}</small>
        </div>
      </div>
ROW
  done <<<"$blob"
}

# Per-REC bucket → list of W3C suite names.
# Each bucket gets its own <h3> subsection inside the SPARQL 1.1 / RDF 1.1
# parents. Unmatched suites fall through to the "Other" bucket so they
# stay visible on the dashboard.
sparql_rec_for_suite () {
  case "$1" in
    aggregates|bind|bindings|cast|construct|csv-tsv-res|exists|functions|grouping|json-res|negation|project-expression|property-path|subquery|syntax-query)
      echo "query" ;;
    add|basic-update|clear|copy|delete|delete-data|delete-insert|delete-where|drop|move|syntax-update-1|syntax-update-2|update-silent)
      echo "update" ;;
    protocol|http-rdf-update)
      echo "protocol" ;;
    service|syntax-fed)
      echo "federated" ;;
    service-description)
      echo "service-description" ;;
    entailment)
      echo "entailment" ;;
    *)
      echo "other" ;;
  esac
}

rdf_rec_for_suite () {
  case "$1" in
    rdf-n-triples) echo "n-triples" ;;
    rdf-turtle)    echo "turtle" ;;
    rdf-n-quads)   echo "n-quads" ;;
    rdf-trig)      echo "trig" ;;
    rdf-xml)       echo "rdf-xml" ;;
    rdf-mt)        echo "semantics" ;;
    *)             echo "other" ;;
  esac
}

# Filter $1 (raw suite log lines) to only those whose suite name maps
# to bucket $2, using the bucket-fn $3.
filter_suites_by_bucket () {
  local blob="$1"; local target_bucket="$2"; local bucket_fn="$3"
  local out=""
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local name; name=$(echo "$line" | awk '{print $1}')
    local bucket; bucket=$("$bucket_fn" "$name")
    if [ "$bucket" = "$target_bucket" ]; then
      out+="$line"$'\n'
    fi
  done <<<"$blob"
  printf '%s' "$out"
}

# emit_rec_subsection — h3 + suite rows inside a per-REC bucket, but
# only if the bucket has at least one suite. Layout: pure markup; the
# h3 sits inside the parent .suites container in the existing CSS, so
# subsection headings stay aligned with the surrounding bars.
emit_rec_subsection () {
  local title="$1"; local href="$2"; local lines="$3"
  if [ -z "$(echo "$lines" | tr -d '[:space:]')" ]; then
    return
  fi
  local rows; rows=$(emit_suite_rows "$lines")
  cat <<HTML
  <h3 class="rec-subhead"><a href="${href}" target="_blank" rel="noopener">${title}</a></h3>
${rows}
HTML
}

SPARQL_ROWS_HTML=$(
  emit_rec_subsection "SPARQL 1.1 Query Language"      "https://www.w3.org/TR/sparql11-query/"               "$(filter_suites_by_bucket "$SPARQL_SUITES" query              sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Update"              "https://www.w3.org/TR/sparql11-update/"              "$(filter_suites_by_bucket "$SPARQL_SUITES" update             sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Protocol"            "https://www.w3.org/TR/sparql11-protocol/"            "$(filter_suites_by_bucket "$SPARQL_SUITES" protocol           sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Federated Query"     "https://www.w3.org/TR/sparql11-federated-query/"     "$(filter_suites_by_bucket "$SPARQL_SUITES" federated          sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Service Description" "https://www.w3.org/TR/sparql11-service-description/" "$(filter_suites_by_bucket "$SPARQL_SUITES" service-description sparql_rec_for_suite)"
  emit_rec_subsection "SPARQL 1.1 Entailment Regimes"  "https://www.w3.org/TR/sparql11-entailment/"          "$(filter_suites_by_bucket "$SPARQL_SUITES" entailment         sparql_rec_for_suite)"
  emit_rec_subsection "Other (uncategorised)"          ""                                                    "$(filter_suites_by_bucket "$SPARQL_SUITES" other              sparql_rec_for_suite)"
)

RDF_ROWS_HTML=$(
  emit_rec_subsection "RDF 1.1 N-Triples"  "https://www.w3.org/TR/n-triples/"           "$(filter_suites_by_bucket "$RDF_SUITES" n-triples rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 Turtle"     "https://www.w3.org/TR/turtle/"              "$(filter_suites_by_bucket "$RDF_SUITES" turtle    rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 N-Quads"    "https://www.w3.org/TR/n-quads/"             "$(filter_suites_by_bucket "$RDF_SUITES" n-quads   rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 TriG"       "https://www.w3.org/TR/trig/"                "$(filter_suites_by_bucket "$RDF_SUITES" trig      rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 RDF/XML"    "https://www.w3.org/TR/rdf-syntax-grammar/"  "$(filter_suites_by_bucket "$RDF_SUITES" rdf-xml   rdf_rec_for_suite)"
  emit_rec_subsection "RDF 1.1 Semantics"  "https://www.w3.org/TR/rdf11-mt/"            "$(filter_suites_by_bucket "$RDF_SUITES" semantics rdf_rec_for_suite)"
  emit_rec_subsection "Other (uncategorised)" ""                                        "$(filter_suites_by_bucket "$RDF_SUITES" other     rdf_rec_for_suite)"
)

# ---------------------------------------------------------------------
# emit_failure_detail — given a per-category log file and a section id,
# extract every "FAIL: …" / "skip: …" / "SKIP: …" line and render an
# inline <details> block. The h2 totals link to the section ids
# (#sparql-failures, #sparql-skips, #rdf-failures) so a reader who
# clicks "1 fail" lands on the actual failure description, not a
# dead-end count.
# ---------------------------------------------------------------------
emit_failure_detail () {
  local log="$1"
  local id_prefix="$2"
  local label="$3"

  # Bail with empty output if the log doesn't exist (e.g. RDF-only run).
  if [ ! -f "$log" ]; then
    echo ""
    return
  fi

  # FAIL lines.
  local fail_block=""
  fail_block=$(grep -E '^[[:space:]]*FAIL:' "$log" 2>/dev/null \
               | sed -E 's/^[[:space:]]+//' \
               | sed -E 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g' \
               | awk '{ printf "<li>%s</li>\n", $0 }' || true)

  # skip lines (lower- and upper-case).
  local skip_block=""
  skip_block=$(grep -E '^[[:space:]]*([sS][kK][iI][pP]):' "$log" 2>/dev/null \
               | sed -E 's/^[[:space:]]+//' \
               | sed -E 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g' \
               | awk '{ printf "<li>%s</li>\n", $0 }' || true)

  cat <<HTML
<details id="${id_prefix}-failures" class="failure-detail">
  <summary>${label} failures (click to expand)</summary>
  <ul>
${fail_block:-<li>(none)</li>}
  </ul>
</details>

<details id="${id_prefix}-skips" class="failure-detail">
  <summary>${label} skips (click to expand)</summary>
  <ul>
${skip_block:-<li>(none)</li>}
  </ul>
</details>
HTML
}

SPARQL_FAILURE_DETAIL_HTML=$(emit_failure_detail "$SPARQL_LOG" "sparql" "SPARQL 1.1")
RDF_FAILURE_DETAIL_HTML=$(emit_failure_detail "$RDF_LOG" "rdf" "RDF 1.1")

# Note: RDFC-1.0 (RDF Dataset Canonicalization) is a SEPARATE W3C
# corpus (vendored at third_party/testing/rdf-canon/). Earlier
# versions of this report stitched a synthetic "rdf-canon" row into
# the RDF 1.1 panel above, which made readers think the 26 RDFC-1.0
# fails were RDF 1.1 core fails. They are not — the RDF 1.1 totals
# (~1031 tests) come exclusively from third_party/testing/w3c/rdf/
# rdf11/{rdf-mt, rdf-n-quads, rdf-n-triples, rdf-trig, rdf-turtle,
# rdf-xml}. RDFC-1.0 has its own dedicated panel below.

# --- OWL 2 panel ---------------------------------------------------------
# Distinct corpus, distinct denominator; deliberately NOT folded into the
# SPARQL/RDF totals tiles. profile-RL gets actual pass/fail from
# owl_runner; other OWL 2 catalogs are listed as "skipped for now" with
# rationale, so the user can see the full W3C OWL 2 Test Cases footprint
# we've vendored and what we're NOT yet exercising.
if [ "$OWL_PRESENT" -ne 1 ]; then
  OWL_PASS=0; OWL_FAIL=0; OWL_TOTAL=0
fi

# ConsistencyTest + InconsistencyTest bars (Phase 2.2, 2026-05-08).
emit_owl_bar_row () {
  local label="$1" pass="$2" fail="$3" total="$4"
  local skip=$((total - pass - fail))
  [ "$skip" -lt 0 ] && skip=0
  local cls meter
  if [ "$fail" -eq 0 ] && [ "$pass" -gt 0 ]; then     cls="green"
  elif [ "$pass" -eq 0 ] && [ "$fail" -eq 0 ]; then    cls="grey"
  else                                                  cls="amber"
  fi
  meter=$(meter_segments "$pass" "$fail" "$skip" "$total")
  printf '<div class="suite-row %s">
    <div class="suite-name">%s</div>
    %s
    <div class="suite-numbers">
      <span class="p">%s pass</span>, <span class="f">%s fail</span>
      <small>(of %s)</small>
    </div>
  </div>' "$cls" "$label" "$meter" "$pass" "$fail" "$total"
}
OWL_NEG_ROW=""
if [ "$OWL_NEG_PRESENT" -eq 1 ]; then
  OWL_NEG_ROW=$(emit_owl_bar_row "profile-RL NegEnt" "$OWL_NEG_PASS" "$OWL_NEG_FAIL" "$OWL_NEG_TOTAL")
fi
OWL_CONS_ROW=""
if [ "$OWL_CONS_PRESENT" -eq 1 ]; then
  OWL_CONS_ROW=$(emit_owl_bar_row "profile-RL Consistency"   "$OWL_CONS_PASS" "$OWL_CONS_FAIL" "$OWL_CONS_TOTAL")
fi
OWL_INC_ROW=""
if [ "$OWL_INC_PRESENT" -eq 1 ]; then
  OWL_INC_ROW=$(emit_owl_bar_row  "profile-RL Inconsistency" "$OWL_INC_PASS"  "$OWL_INC_FAIL"  "$OWL_INC_TOTAL")
fi
# Phase 2.3 — DL catalog rows (generic, loop-driven).
emit_catalog_rows () {
  # $1 = prefix (e.g. OWL_TPE), $2 = catalog short label (e.g. type-PosEnt)
  local prefix="$1" label="$2"
  local types_with_short="PositiveEntailmentTests:PE NegativeEntailmentTests:NE ConsistencyTests:Cons InconsistencyTests:Inc"
  for entry in $types_with_short; do
    local t="${entry%%:*}" short="${entry##*:}"
    local p_var="${prefix}_${t}_PRESENT"
    local present="${!p_var}"
    [ "${present:-0}" -eq 1 ] || continue
    local pass_var="${prefix}_${t}_PASS"
    local fail_var="${prefix}_${t}_FAIL"
    local total_var="${prefix}_${t}_TOTAL"
    emit_owl_bar_row "$label $short" "${!pass_var}" "${!fail_var}" "${!total_var}"
  done
}
OWL_DL_ROWS=$( {
  emit_catalog_rows OWL_TPE   "type-PosEnt"
  emit_catalog_rows OWL_TNE   "type-NegEnt"
  emit_catalog_rows OWL_TCON  "type-Cons"
  emit_catalog_rows OWL_TINC  "type-Inc"
  emit_catalog_rows OWL_EL    "profile-EL"
  emit_catalog_rows OWL_QL    "profile-QL"
  emit_catalog_rows OWL_SEMDL "sem-Direct"
} )

# RIF Core dedicated row (Phase 2.3c).
RIF_ROW=""
if [ "$RIF_PRESENT" -eq 1 ]; then
  RIF_ROW=$(emit_owl_bar_row "RIF Core" "$RIF_PASS" "$RIF_FAIL" "$RIF_TOTAL")
fi

# Deferred-category counts are the `<test:TestCase>` occurrences in each
# vendored OWL 2 Test Cases catalog file (Agent D scoping on 2026-04-24).
# Compute fresh so the numbers never go stale.
OWL_DIR="$SCRIPT_DIR/../../third_party/testing/owl"
count_testcases () {
  local f="$1"
  if [ -f "$f" ]; then
    grep -c "test:TestCase" "$f" 2>/dev/null || echo 0
  else
    echo 0
  fi
}
OWL_EL_N=$(count_testcases "$OWL_DIR/profile-EL.rdf")
OWL_QL_N=$(count_testcases "$OWL_DIR/profile-QL.rdf")
OWL_RL_CATALOG_N=$(count_testcases "$OWL_DIR/profile-RL.rdf")
OWL_SEMDL_N=$(count_testcases "$OWL_DIR/semantics-direct.rdf")
OWL_SYNDL_N=$(count_testcases "$OWL_DIR/syntax-dl.rdf")
OWL_TPE_N=$(count_testcases "$OWL_DIR/type-positive-entailment.rdf")
OWL_TNE_N=$(count_testcases "$OWL_DIR/type-negative-entailment.rdf")
OWL_TCON_N=$(count_testcases "$OWL_DIR/type-consistency.rdf")
OWL_TINC_N=$(count_testcases "$OWL_DIR/type-inconsistency.rdf")

emit_owl_skip_row () {
  local name="$1" count="$2" reason="$3"
  local css_class="${4:-grey}"
  cat <<ROW
  <div class="suite-row ${css_class}">
    <div class="suite-name">${name}</div>
    <div class="meter"><div class="seg seg-skip" style="width:100%"></div></div>
    <div class="suite-numbers">
      <span style="color:var(--muted)">&mdash;</span>
      <small>${count} tests &middot; ${reason}</small>
    </div>
  </div>
ROW
}

# Note (2026-05-08): the W3C SPARQL 1.1 entailment-regime suite (70/70
# pass, see SPARQL section above) is the **live testbed for Tableau
# materialisation**. parent4/5/6/7 + simple7/8 + sparqldl-01..12 +
# many-others are OWL-DL queries; they pass because Tableau is on
# the codepath. The "semantics-direct" row below points at the
# vendored W3C OWL-DL conformance test catalog (separate, larger);
# it isn't wired through owl_runner yet, but the underlying engine
# (Tableau.tableau_materialise + has_disjoint_witness +
# materialise_for_ce + tableau_introduce_witnesses) is sound, on the
# codepath, and contributing to the wins above. The "blocked" labels
# below are about *runner wiring*, not engine readiness.
OWL_SKIP_ROWS=""
# Most catalog skip-rows above (profile-EL, profile-QL,
# semantics-direct, type-*) were retired 2026-05-08 when their
# runner wiring landed (Phase 2.1-2.3). The catalogs now have live
# scored bars in the OWL panel.
#
# Remaining catalog still needing wiring:
OWL_SKIP_ROWS+="$(emit_owl_skip_row "syntax-dl" "$OWL_SYNDL_N" "runner not wired (engine: DL syntactic-profile checker pending)")"$'\n'
# RL-RDF-rules-tests.rdf (the per-rule attribution catalog) and
# all.rdf (an aggregator) are intentionally skipped — they're not
# independent test sets.
#
# OGC GeoSPARQL — Tier C, separate spec stack. Roadmap in #239.
OWL_SKIP_ROWS+="$(emit_owl_skip_row "GeoSPARQL"  "v0"           "v0 implemented (RDF.Geo.* — exact-rational WKT geometry + Simple-Features topology + geof: functions, 11 local tests); OGC W3C-suite runner pending (see <a href='https://github.com/danbri/factoidal/issues/239'>#239</a>)")"$'\n'
# 2026-07-05 wave: ShEx, JSON-LD 1.1, VC 2.0, and RML now have their own
# runners and live dashboard families below (Shapes, JSON-LD 1.1, VC,
# Mapping) — retired from this roadmap list so the same suite doesn't
# appear both as "runner pending" here AND scored elsewhere.
#
# CSVW, DID — still vendored at third_party/testing/ with no runner.
OWL_SKIP_ROWS+="$(emit_owl_skip_row "DID"        "?"            "vendored at third_party/testing/did; runner pending")"$'\n'

# --- RDFC-1.0 subsection (folded into the RDF 1.1 core family) ----------
# RDFC-1.0 (W3C RDF Dataset Canonicalization 1.0) is a separate W3C
# suite with its own denominator, surfaced as a subsection inside the
# "RDF 1.1 core" family rather than its own top-level section — same
# spec family (RDF graph-level semantics), just a different corpus.
# Baseline 2026-07-05 (wave 8): HFDQ + full HNDQ permutation
# enumeration lands, Map tests compared structurally, NegEval checked
# against an HNDQ work budget — the suite reads 86 pass, 0 fail (of
# 86), not the earlier "Map is STUB" state this prose used to say.
if [ "$RDFC10_PRESENT" -ne 1 ]; then
  RDFC10_PASS=0; RDFC10_FAIL=0; RDFC10_SKIP=0; RDFC10_TOTAL=0
fi
RDFC10_ROW=$(emit_owl_bar_row "RDFC-1.0 (eval + Map + NegEval)" "$RDFC10_PASS" "$RDFC10_FAIL" "$RDFC10_TOTAL")
RDFC10_HTML=$(cat <<RDFCEOF
  <h3 class="rec-subhead"><a href="https://www.w3.org/TR/rdf-canon/" target="_blank" rel="noopener">RDF Dataset Canonicalization (RDFC-1.0)</a></h3>
${RDFC10_ROW}
  <p class="suite-prov">
    Runner: <code>bin/rdfc10-runner</code> (<code>bin/linux-x86_64/rdfc10_runner</code>) &middot;
    Suite: <code>third_party/testing/rdf-canon/</code> &middot;
    Algorithm: F&#42; <code>formal/fstar/RDF.Canonical.fst</code> (Hash First Degree Quads +
    full Hash N-Degree Quads permutation enumeration), verified with no
    <code>--lax</code> and no <code>--admit_smt_queries</code>. Eval tests compare the
    canonical N-Quads form bytewise; Map tests compare the bnode&rarr;canonical-id
    mapping structurally; NegEval tests are bounded by an HNDQ work budget.
  </p>
RDFCEOF
)

OWL_TOTAL_UNIVERSE=$(( OWL_TOTAL + ${OWL_EL_N:-174} + ${OWL_QL_N:-130} + ${OWL_SEMDL_N:-976} + ${OWL_SYNDL_N:-646} + ${OWL_TPE_N:-412} + ${OWL_TNE_N:-46} + ${OWL_TCON_N:-708} + ${OWL_TINC_N:-256} ))
if [ "$OWL_TOTAL_UNIVERSE" -gt 0 ]; then
  OWL_UNIVERSE_PCT=$(awk -v p="$OWL_PASS" -v t="$OWL_TOTAL_UNIVERSE" 'BEGIN{printf "%.1f", (p/t)*100}')
else
  OWL_UNIVERSE_PCT="0"
fi

OWL_HTML=$(cat <<OWLEOF
<h2>OWL 2 <span class="inline-numbers">${OWL_PASS}+ pass via owl_runner across 7 catalogs (profile-RL/EL/QL + 4 DL) &middot; live scoring</span></h2>
<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">
  <strong>Scope.</strong> The OWL 2 W3C Test Cases catalog (~${OWL_TOTAL_UNIVERSE}
  <code>test:TestCase</code> entries across 9 categories) is vendored
  under <code>third_party/testing/owl/</code>. As of Phase 2.3
  (2026-05-08), <strong>seven catalogs</strong> run live through
  <code>owl_runner</code> with PositiveEntailment / NegativeEntailment /
  Consistency / Inconsistency scoring: <code>profile-RL.rdf</code>,
  <code>profile-EL.rdf</code>, <code>profile-QL.rdf</code>,
  <code>type-positive-entailment.rdf</code>,
  <code>type-negative-entailment.rdf</code>,
  <code>type-consistency.rdf</code>, <code>type-inconsistency.rdf</code>,
  and <code>semantics-direct.rdf</code>. The remaining catalog
  (<code>syntax-dl.rdf</code>) needs a DL syntactic-profile checker
  before it can score.
</p>
<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">
  <strong>Tableau on the live codepath.</strong> The F\*
  <code>Tableau.tableau_materialise</code> module (1167 LoC, 0
  <code>assume val</code>, 0 <code>--lax</code>) is also on the
  SPARQL entailment regime codepath via <code>w3c_runner.ml</code>:
  parent4/5/6/7, simple7/8, sparqldl-01…12, etc. — the
  <strong>SPARQL 1.1 Entailment Regimes row above (70/70)</strong>
  passes because Tableau drives the membership check. The owl_runner
  catalogs below currently score under the RL closure path; wiring
  Tableau into owl_runner via <code>--regime dl</code> is Phase 2.3d.
</p>
<p style="margin: 0.3em 0 0.6em; color: var(--muted); font-size: 0.85em;">
  <strong>Pass-rate context.</strong> Across the seven scored
  catalogs, the bulk of failures fall into two known categories:
  (1) tests that use OWL Functional-Style Syntax (not RDF/XML)
  trigger <code>FAIL/no-premise</code> — these need an FSS parser
  before scoring is meaningful; (2) Inconsistency-Test failures
  (notably the type-Inc 8% rate) are RL-closure incompleteness —
  RL doesn't derive every DL contradiction. Lifting requires
  either extending <code>is_inconsistent</code> or running
  Tableau (Phase 2.3d).
</p>
<div class="suites">
  $(emit_owl_bar_row "profile-RL PosEnt" "$OWL_PASS" "$OWL_FAIL" "$OWL_TOTAL")
  ${OWL_NEG_ROW}
  ${OWL_CONS_ROW}
  ${OWL_INC_ROW}
  ${OWL_DL_ROWS}
${OWL_SKIP_ROWS}</div>
<p style="margin: 0.3em 0 1em; color: var(--muted); font-size: 0.85em;">
  <strong>OWL 2 (W3C conformance):</strong>
  We vendor the full W3C OWL 2 Test Cases at
  <code>third_party/testing/owl/</code> (10 catalog files, ~2500
  <code>test:TestCase</code> entries after overlap). After Phase 2.3
  (2026-05-08), 7 of 8 main catalogs run live through
  <code>owl_runner</code> with PE/NE/Cons/Inc scoring. The runner
  applies <code>owl_rl_closure_with_reflexivity</code> (fuel 100) and
  for entailment tests checks the conclusion&rsquo;s triples against
  the closure (relaxed bnode match); for consistency tests it consults
  <code>RDF_Graph_Executable.is_inconsistent</code> against the same
  closure. <code>syntax-dl.rdf</code> is the remaining unwired catalog
  (DL syntactic-profile checker pending). The roadmap rows below
  point at adjacent W3C/OGC suites we want to add: GeoSPARQL (#239),
  JSON-LD 1.1, CSVW, ShEx, DID, VC, RML.
</p>
OWLEOF
)

# --- Parse + serialize throughput (optional; fail-soft) ---------------------
# Produced by tools/bench-parse-serialize.sh, which runs against the
# committed binary and has no toolchain dependency. This script only
# *includes* the fragment verbatim if present -- it does no JSON
# parsing of its own, so a missing or stale file degrades to simply
# omitting the section rather than breaking report generation.
PERF_FRAGMENT="$OUTPUT_DIR/perf-parse-serialize.fragment.html"
if [ -f "$PERF_FRAGMENT" ]; then
  PERF_SECTION_HTML=$(cat "$PERF_FRAGMENT")
else
  PERF_SECTION_HTML=""
fi

[ -n "$GIT_SUBJECT" ] && GIT_SUBJECT_LINE=" — &ldquo;${GIT_SUBJECT}&rdquo;" || GIT_SUBJECT_LINE=""

# =============================================================================
# Family sections (2026-07-05 dashboard redesign) ----------------------------
# Every standards suite this project measures is grouped into one of eight
# families (RDF 1.1 core, SPARQL 1.1, Reasoning: RDFS/OWL 2, Shapes, Rules,
# Mapping, JSON-LD 1.1, Verifiable Credentials 2.0), each rendered as a
# <section class="family <status>"> card with a headline roll-up, a
# collapsible (native <details>, no JS required) list of per-suite rows, and
# a one-line provenance (runner binary + vendored suite dir) under each row.
# Status colour is consistent everywhere: green = full pass; amber = partial
# with every residual fail diagnosed in writing (a link is attached to the
# row); grey = not measured this run, or genuinely out of scope. See the
# legend rendered directly above the first family section.
# =============================================================================
GITHUB_BLOB_BASE="https://github.com/danbri/factoidal/blob/${GIT_BRANCH}"

status_for () {
  # $1 = fail count, $2 = "any measured?" flag (0/1)
  local fail="$1" any="$2"
  if [ "${any:-0}" -ne 1 ]; then echo grey
  elif [ "$fail" -eq 0 ]; then echo green
  else echo amber
  fi
}

# family_suite_row — shared row renderer for the newer suites (SHACL, ShEx,
# JSON-LD, RML, RIF Core, VC). Mirrors emit_owl_bar_row's green/amber/grey
# convention, additionally handling present=0 as an explicit "not measured
# this run" grey row (never a fabricated 0-pass number), and carries a
# one-line <p class="suite-prov"> underneath with the runner + vendored
# suite dir, plus an optional diagnosis link shown only on amber rows.
family_suite_row () {
  local name="$1" pass="$2" fail="$3" skip="$4" total="$5" present="$6" prov="$7" diag="${8:-}"
  local cls numbers meter diag_html=""
  if [ "$present" -ne 1 ] || [ "$total" -eq 0 ]; then
    cls="grey"
    numbers="not measured this run"
    meter='<div class="meter"><div class="seg seg-skip" style="width:100%"></div></div>'
  else
    numbers="${pass} pass, ${fail} fail, ${skip} skip (of ${total})"
    meter=$(meter_segments "$pass" "$fail" "$skip" "$total")
    cls=$(status_for "$fail" 1)
    if [ "$fail" -gt 0 ] && [ -n "$diag" ]; then diag_html=" &middot; ${diag}"; fi
  fi
  cat <<ROW
      <div class="suite-row ${cls}">
        <div class="suite-name">${name}</div>
        ${meter}
        <div class="suite-numbers"><small>${numbers}</small></div>
      </div>
      <p class="suite-prov">${prov}${diag_html}</p>
ROW
}

# family_section — the outer card. $6 (footnote) is optional extra prose
# rendered below the collapsible suite list (used by the OWL family, which
# already carries rich inline scope prose worth preserving).
family_section () {
  local id="$1" title="$2" fstatus="$3" headline="$4" body="$5" footnote="${6:-}"
  cat <<SEC
<section class="family ${fstatus}" id="${id}">
  <h2>${title}</h2>
  <p class="fam-headline ${fstatus}">${headline}</p>
  <details open>
    <summary>Suites in this family (tap to collapse)</summary>
    <div class="suites">
${body}
    </div>
  </details>
  ${footnote}
</section>
SEC
}

# --- RDF 1.1 core: syntaxes + semantics + canonicalization -------------------
RDFCORE_PASS=$((RDF_PASS + RDFC10_PASS))
RDFCORE_FAIL=$((RDF_FAIL + RDFC10_FAIL))
RDFCORE_SKIP=$((RDF_SKIP + RDFC10_SKIP))
RDFCORE_TOTAL=$((RDF_TOTAL + RDFC10_TOTAL))
RDFCORE_STATUS=$(status_for "$RDFCORE_FAIL" 1)
RDFCORE_HEADLINE="${RDFCORE_PASS} pass, ${RDFCORE_FAIL} fail, ${RDFCORE_SKIP} skip (of ${RDFCORE_TOTAL}) across N-Triples, Turtle, N-Quads, TriG, RDF/XML, RDF 1.1 Semantics (rdf-mt), and RDFC-1.0 canonicalization."
RDFCORE_BODY=$(printf '%s\n%s\n' "$RDF_ROWS_HTML" "$RDFC10_HTML")
RDFCORE_HTML=$(family_section "rdf-core" "RDF 1.1 core" "$RDFCORE_STATUS" "$RDFCORE_HEADLINE" "$RDFCORE_BODY" "$RDF_FAILURE_DETAIL_HTML")

# --- SPARQL 1.1 ---------------------------------------------------------
SPARQL_STATUS=$(status_for "$SPARQL_FAIL" 1)
SPARQL_HEADLINE="${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip (of ${SPARQL_TOTAL}) across Query, Update, Protocol, Federated Query, Service Description, and Entailment Regimes."
SPARQL_FAMILY_HTML=$(family_section "sparql11" "SPARQL 1.1" "$SPARQL_STATUS" "$SPARQL_HEADLINE" "$SPARQL_ROWS_HTML" "$SPARQL_FAILURE_DETAIL_HTML")

# --- Reasoning: RDFS / OWL 2 ---------------------------------------------
# OWL_HTML already carries its own rich prose (scope + pass-rate context)
# from the earlier catalog-by-catalog wiring; wrap it as this family's
# footnote rather than re-deriving a numeric aggregate across catalogs
# whose test-type buckets (Positive/Negative/Consistency/Inconsistency)
# aren't directly summable into one pass/fail/skip/total the way the
# newer suites are.
OWL_FAMILY_STATUS=$(status_for "$OWL_FAIL" "$OWL_PRESENT")
OWL_FAMILY_HEADLINE="profile-RL PositiveEntailmentTests: ${OWL_PASS} pass, ${OWL_FAIL} fail (of ${OWL_TOTAL}); six further OWL 2 catalogs (NegEnt/Cons/Inc + 4 DL catalogs) scored below, RIF Core scored in its own family."
OWL_FAMILY_HTML=$(family_section "owl2" "Reasoning: RDFS / OWL 2" "$OWL_FAMILY_STATUS" "$OWL_FAMILY_HEADLINE" "$OWL_HTML" "")

# --- Shapes: SHACL / ShEx -------------------------------------------------
read -r SHAPES_PASS SHAPES_FAIL SHAPES_SKIP SHAPES_TOTAL SHAPES_ANY <<< "$(sum_family "SHACL_CORE SHACL_SPARQL SHEX")"
SHAPES_STATUS=$(status_for "$SHAPES_FAIL" "$SHAPES_ANY")
if [ "$SHAPES_ANY" -eq 1 ]; then
  SHAPES_HEADLINE="${SHAPES_PASS} pass, ${SHAPES_FAIL} fail, ${SHAPES_SKIP} skip (of ${SHAPES_TOTAL}) across SHACL Core, SHACL SPARQL-based Constraints, and ShEx validation."
else
  SHAPES_HEADLINE="Not measured this run."
fi
SHAPES_BODY=$(
  family_suite_row "SHACL Core" "$SHACL_CORE_PASS" "$SHACL_CORE_FAIL" "$SHACL_CORE_SKIP" "$SHACL_CORE_TOTAL" "$SHACL_CORE_PRESENT" \
    "Runner: <code>bin/shacl-runner</code> (<code>bin/linux-x86_64/shacl_runner</code>) &middot; Suite: <code>third_party/testing/shacl/data-shapes-test-suite/tests/core/</code>"
  family_suite_row "SHACL SPARQL-based Constraints" "$SHACL_SPARQL_PASS" "$SHACL_SPARQL_FAIL" "$SHACL_SPARQL_SKIP" "$SHACL_SPARQL_TOTAL" "$SHACL_SPARQL_PRESENT" \
    "Runner: <code>bin/shacl-runner</code> (<code>bin/linux-x86_64/shacl_runner tests/sparql/manifest.ttl</code>) &middot; Suite: <code>third_party/testing/shacl/data-shapes-test-suite/tests/sparql/</code>"
  family_suite_row "ShEx Validation" "$SHEX_PASS" "$SHEX_FAIL" "$SHEX_SKIP" "$SHEX_TOTAL" "$SHEX_PRESENT" \
    "Runner: <code>bin/shex-runner</code> (<code>bin/linux-x86_64/shex_runner</code>) &middot; Suite: <code>third_party/testing/shex/</code> (shexSpec/shexTest, ShExJ-first)" \
    "<a href=\"${GITHUB_BLOB_BASE}/.github/test-suites/shex.yaml\" target=\"_blank\" rel=\"noopener\">diagnosis: the 1 mismatch is an upstream fixture defect (start2RefS2.json p1/p2), not an engine bug</a>"
)
SHAPES_HTML=$(family_section "shapes" "Shapes: SHACL / ShEx" "$SHAPES_STATUS" "$SHAPES_HEADLINE" "$SHAPES_BODY" "")

# --- Rules: RIF Core -------------------------------------------------------
RULES_STATUS=$(status_for "$RIFCORE_COMBINED_FAIL" "$RIFCORE_COMBINED_PRESENT")
if [ "$RIFCORE_COMBINED_PRESENT" -eq 1 ]; then
  RULES_HEADLINE="${RIFCORE_COMBINED_PASS} pass, ${RIFCORE_COMBINED_FAIL} fail, ${RIFCORE_COMBINED_SKIP} skip (of ${RIFCORE_COMBINED_TOTAL}) — Part 1 (4 vendored SPARQL-manifest cases) + Part 2 (46-test W3C RIF Core dialect corpus)."
else
  RULES_HEADLINE="Not measured this run."
fi
RULES_BODY=$(
  family_suite_row "RIF Core — combined (Part 1 + Part 2)" "$RIFCORE_COMBINED_PASS" "$RIFCORE_COMBINED_FAIL" "$RIFCORE_COMBINED_SKIP" "$RIFCORE_COMBINED_TOTAL" "$RIFCORE_COMBINED_PRESENT" \
    "Runner: <code>bin/rif-runner</code> (<code>bin/linux-x86_64/rif_runner</code>) &middot; Suites: <code>third_party/testing/rif/tc/</code> + <code>third_party/testing/rif-core-suite/</code>" \
    "<a href=\"${GITHUB_BLOB_BASE}/bin/rif-runner/README.md\" target=\"_blank\" rel=\"noopener\">diagnosis: 1 corpus data defect (malformed xsd:string IRI in the official W3C zip) + 3 labelled engine KNOWN-GAPs, see bin/rif-runner/README.md</a>"
  family_suite_row "RIF Core — Part 1 (4 vendored SPARQL-manifest cases)" "$RIFCORE_PART1_PASS" "$RIFCORE_PART1_FAIL" "$RIFCORE_PART1_SKIP" "$RIFCORE_PART1_TOTAL" "$RIFCORE_PART1_PRESENT" \
    "Runner: <code>bin/rif-runner</code> &middot; Suite: <code>third_party/testing/rif/tc/</code> (the same 4 cases are also scored independently as the &ldquo;RIF Core&rdquo; row under SPARQL 1.1 Entailment Regimes above, via <code>w3c_runner</code>'s entailment dispatch — both pipelines agree)"
  family_suite_row "RIF Core — Part 2 (W3C Core_v1.22 corpus)" "$RIFCORE_PART2_PASS" "$RIFCORE_PART2_FAIL" "$RIFCORE_PART2_SKIP" "$RIFCORE_PART2_TOTAL" "$RIFCORE_PART2_PRESENT" \
    "Runner: <code>bin/rif-runner</code> &middot; Suite: <code>third_party/testing/rif-core-suite/Core_v1.22/Approved/</code>" \
    "<a href=\"${GITHUB_BLOB_BASE}/docs/claude-rules/scope.md\" target=\"_blank\" rel=\"noopener\">diagnosis: docs/claude-rules/scope.md RIF section — every skip names the exact missing builtin/feature</a>"
)
RULES_HTML=$(family_section "rules" "Rules: RIF Core" "$RULES_STATUS" "$RULES_HEADLINE" "$RULES_BODY" "")

# --- Mapping: RML / CSVW ---------------------------------------------------
MAPPING_STATUS=$(status_for "$RML_FAIL" "$RML_PRESENT")
if [ "$RML_PRESENT" -eq 1 ]; then
  MAPPING_HEADLINE="${RML_PASS} pass, ${RML_FAIL} fail, ${RML_SKIP} skip (of ${RML_TOTAL}) on RML rml-core; CSVW has an early csv2rdf runner (csvw_runner, ~19/270 on the W3C csv2rdf corpus) not yet wired into this dashboard."
else
  MAPPING_HEADLINE="Not measured this run."
fi
MAPPING_BODY=$(
  family_suite_row "RML rml-core" "$RML_PASS" "$RML_FAIL" "$RML_SKIP" "$RML_TOTAL" "$RML_PRESENT" \
    "Runner: <code>bin/rml-runner</code> (<code>bin/linux-x86_64/rml_runner</code>) &middot; Suite: <code>third_party/testing/rml-modules/rml-core/</code>"
  cat <<CSVWROW
      <div class="suite-row grey">
        <div class="suite-name">CSVW (Stage 1 metadata decode)</div>
        <div class="meter"><div class="seg seg-skip" style="width:100%"></div></div>
        <div class="suite-numbers"><small>in progress &mdash; not wired into this dashboard</small></div>
      </div>
      <p class="suite-prov">
        No committed runner or <code>*_results.log</code> yet, so this row is not
        scored. A scratch driver over <code>third_party/testing/csvw/tests</code>
        decodes 286 of 293 metadata documents to structured metadata (the other 7
        are 3 correctly-rejected malformed fixtures, 1 out-of-scope empty-table-group
        edge case, 2 out-of-scope schema-by-reference fixtures needing HTTP fetch,
        and 1 genuine decoder gap) — see
        <a href="${GITHUB_BLOB_BASE}/docs/designissues/2026-07-05-csvw-program-plan.md" target="_blank" rel="noopener">the CSVW program plan</a>
        for the staged roadmap.
      </p>
CSVWROW
)
MAPPING_HTML=$(family_section "mapping" "Mapping: RML / CSVW" "$MAPPING_STATUS" "$MAPPING_HEADLINE" "$MAPPING_BODY" "")

# --- JSON-LD 1.1 ------------------------------------------------------------
JSONLD_STATUS=$(status_for "$JSONLD_FAIL" "$JSONLD_PRESENT")
if [ "$JSONLD_PRESENT" -eq 1 ]; then
  JSONLD_FAMILY_HEADLINE="${JSONLD_PASS} pass, ${JSONLD_FAIL} fail, ${JSONLD_SKIP} skip (of ${JSONLD_TOTAL}) against the W3C JSON-LD 1.1 toRdf manifest."
else
  JSONLD_FAMILY_HEADLINE="Not measured this run."
fi
JSONLD_BODY=$(
  family_suite_row "JSON-LD 1.1 toRdf" "$JSONLD_PASS" "$JSONLD_FAIL" "$JSONLD_SKIP" "$JSONLD_TOTAL" "$JSONLD_PRESENT" \
    "Runner: <code>bin/jsonld-runner</code> (<code>bin/linux-x86_64/jsonld_runner</code>) &middot; Suite: <code>third_party/testing/json-ld/</code> (toRdf manifest)" \
    "<a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-05-docs-hub-plan.md\" target=\"_blank\" rel=\"noopener\">diagnosis: the 1 fail is the documented Ryu-class float-formatting case; the 6 skips are JSON-LD 1.0-only fixtures, out of scope for this 1.1 program</a>"
)
JSONLD_FAMILY_HTML=$(family_section "jsonld11" "JSON-LD 1.1" "$JSONLD_STATUS" "$JSONLD_FAMILY_HEADLINE" "$JSONLD_BODY" "")

# --- Verifiable Credentials 2.0 --------------------------------------------
VC_STATUS=$(status_for "$VC_FAIL" "$VC_PRESENT")
if [ "$VC_PRESENT" -eq 1 ]; then
  VC_FAMILY_HEADLINE="${VC_PASS} pass, ${VC_FAIL} fail, ${VC_SKIP} skip (of ${VC_TOTAL}) on the structural Stage 1 suite; the Data Integrity eddsa-rdfc-2022 sign/verify layer (RDFC-1.0 + SHA-256 + Ed25519 via vendored HACL* C) is implemented separately (vc_runner --crypto roundtrip, native-only, wasm tracked in #286); full W3C VC-DI conformance (JSON-LD proof-options expansion) is still pending."
else
  VC_FAMILY_HEADLINE="Not measured this run."
fi
VC_BODY=$(
  family_suite_row "VC Data Model 2.0 — structural (Stage 1)" "$VC_PASS" "$VC_FAIL" "$VC_SKIP" "$VC_TOTAL" "$VC_PRESENT" \
    "Runner: <code>bin/vc-runner</code> (<code>bin/linux-x86_64/vc_runner</code>) &middot; Suite: <code>third_party/testing/vc/tests/input/</code> (structural fixtures, filename-encoded verdicts)" \
    "<a href=\"${GITHUB_BLOB_BASE}/docs/designissues/2026-07-05-vc-program-plan.md\" target=\"_blank\" rel=\"noopener\">diagnosis: all 34 fails are documented Stage 2 deferrals (issuer shape, validFrom/validUntil ordering, credentialStatus/credentialSchema/etc. inner shapes) — see the VC program plan</a>"
)
VC_FAMILY_HTML=$(family_section "vc2" "Verifiable Credentials 2.0" "$VC_STATUS" "$VC_FAMILY_HEADLINE" "$VC_BODY" "")

# --- Legend -----------------------------------------------------------------
LEGEND_HTML=$(cat <<'LEGENDEOF'
<div class="legend">
  <p class="legend-title">How to read this page</p>
  <ul class="legend-list">
    <li><span class="dot green"></span><strong>Green</strong> — full pass: every runnable test in the suite passes.</li>
    <li><span class="dot amber"></span><strong>Amber</strong> — partial: at least one fail, but every residual fail is diagnosed in writing (a link sits next to the row).</li>
    <li><span class="dot grey"></span><strong>Grey</strong> — not measured this run, or out of scope for this suite (e.g. skipped fixtures, a roadmap item with no runner yet).</li>
  </ul>
  <p class="legend-note">Each suite row shows a stacked meter: the green segment is the pass proportion, red is fail, grey is skip — all measured against that suite's own total, so proportions are comparable across suites of very different sizes.</p>
</div>
LEGENDEOF
)

cat > "$OUTPUT_DIR/index.html" <<HTMLEOF
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Factoidal — W3C test results</title>
<style>
  /*
   * Mobile-first (owner directive 2026-07-05): base rules below target a
   * ~390px phone viewport and widen via min-width media queries. Nothing
   * in this file should require horizontal scrolling of the page itself —
   * wide content (raw logs, long paths) lives inside its own
   * overflow-x:auto container (see the "pre" rule below).
   */
  :root {
    --fg: #1a1a1a; --muted: #666; --bg: #fff; --surface: #f7f7f7;
    --border: #e0e0e0; --brand: #2d6a4f; --brand-dark: #1b4332;
    --ok: #2d6a4f; --ok-tint: #e8f3ee;
    --warn: #b45309; --warn-tint: #fdf1e2;
    --err: #c0392b; --err-tint: #fbe9e7;
    --skip: #6b7280; --skip-tint: #eef0f2;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --fg: #e8e8e8; --muted: #a3a3a3; --bg: #14181a; --surface: #1d2224;
      --border: #333c3f; --brand: #7fc9a3; --brand-dark: #9fd9bd;
      --ok: #6fbf8f; --ok-tint: #16261e;
      --warn: #e8a13d; --warn-tint: #2b2113;
      --err: #e2685c; --err-tint: #2c1917;
      --skip: #9aa4ab; --skip-tint: #22282b;
    }
  }
  * { box-sizing: border-box; }
  html, body { margin: 0; padding: 0; }
  html { font-size: 100%; } /* 1rem/1em = 16px equivalent, never shrunk below this in body copy */
  body {
    font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
    color: var(--fg); background: var(--bg); line-height: 1.55;
    overflow-x: hidden; /* belt-and-braces: no component should ever push the page wider than the viewport */
  }
  a { color: var(--brand-dark); }

  header {
    background: var(--surface);
    border-bottom: 1px solid var(--border); padding: 1em 1em;
  }
  header .inner { max-width: 900px; margin: 0 auto; }
  header h1 { margin: 0 0 0.3em; font-size: 1.3rem; color: var(--brand-dark); }
  header p  { margin: 0; color: var(--muted); font-size: 0.95rem; }
  header nav { margin-top: 0.8em; font-size: 0.95rem; }
  header nav a { margin-right: 1.1em; display: inline-block; padding: 0.3em 0; }

  /* Freshness panel — both timestamps in one place. "Rendered" = when
     this HTML was last regenerated. "Tests" = when the underlying
     *_results.log last changed. Mobile-first: a plain block under the
     title. Widens to an absolutely-positioned top-right pill once
     there's room (min-width breakpoint below). */
  .rendered-pill {
    background: var(--bg); border: 1px solid var(--border);
    border-radius: 6px;
    padding: 0.5em 0.7em;
    margin: 0.8em 0 0;
    font-size: 0.82rem; color: var(--muted);
    line-height: 1.4;
  }
  .rendered-pill .row { display: block; }
  .rendered-pill strong { color: var(--brand-dark); font-weight: 600; }
  .rendered-pill .label {
    display: inline-block; min-width: 4.4em;
    color: var(--muted); font-weight: 400;
  }
  .rendered-pill.stale strong.tests { color: var(--warn); }

  main { max-width: 900px; margin: 0 auto; padding: 1em 0.8em; }

  .summary {
    display: grid; grid-template-columns: repeat(auto-fit, minmax(130px, 1fr));
    gap: 0.6em; margin: 0 0 1.2em;
  }
  .tile {
    background: var(--surface); border: 1px solid var(--border);
    border-radius: 6px; padding: 0.7em 0.8em;
  }
  .tile .label { color: var(--muted); font-size: 0.82rem; margin-bottom: 0.15em; }
  .tile .value { font-size: 1.3rem; font-weight: 600; line-height: 1.2; }
  .tile .value small { font-size: 0.62em; font-weight: 400; color: var(--muted); }
  .tile.ok   .value { color: var(--ok); }
  .tile.err  .value { color: var(--err); }
  .tile.warn .value { color: var(--warn); }

  .caveat {
    border-left: 4px solid var(--skip);
    background: var(--surface);
    padding: 0.8em 1em; margin: 0 0 1.2em; border-radius: 0 6px 6px 0;
    font-size: 0.92rem;
  }
  .caveat strong { color: var(--brand-dark); }

  /* Colour legend — explains green/amber/grey once, up top, referenced
     by every family section below. Wraps naturally on narrow screens. */
  .legend {
    background: var(--surface); border: 1px solid var(--border);
    border-radius: 8px; padding: 0.9em 1em; margin: 0 0 1.4em;
  }
  .legend-title { margin: 0 0 0.5em; font-weight: 600; color: var(--brand-dark); }
  .legend-list { list-style: none; margin: 0 0 0.6em; padding: 0; }
  .legend-list li {
    display: flex; align-items: flex-start; gap: 0.5em;
    margin: 0.35em 0; font-size: 0.92rem;
  }
  .legend-note { margin: 0; font-size: 0.85rem; color: var(--muted); }
  .dot {
    flex: none; width: 0.85em; height: 0.85em; border-radius: 50%;
    margin-top: 0.25em;
  }
  .dot.green { background: var(--ok); }
  .dot.amber { background: var(--warn); }
  .dot.grey  { background: var(--skip); }

  /* --- Family section cards ------------------------------------------- */
  .family {
    border: 1px solid var(--border); border-left-width: 5px;
    border-radius: 8px; padding: 0.9em 1em; margin: 0 0 1.2em;
    background: var(--bg);
  }
  .family.green { border-left-color: var(--ok); }
  .family.amber { border-left-color: var(--warn); }
  .family.grey  { border-left-color: var(--skip); }
  .family h2 { margin: 0 0 0.35em; font-size: 1.08rem; color: var(--brand-dark); }
  .fam-headline {
    margin: 0 0 0.7em; font-size: 0.92rem; color: var(--muted);
    padding-left: 0.9em; border-left: 3px solid var(--border);
  }
  .fam-headline.green { border-left-color: var(--ok); }
  .fam-headline.amber { border-left-color: var(--warn); }
  .fam-headline.grey  { border-left-color: var(--skip); }

  h2 .inline-numbers {
    display: block; font-weight: 400; color: var(--muted); font-size: 0.85rem;
    margin: 0.2em 0 0;
  }
  h2 .inline-numbers a {
    color: inherit; text-decoration: underline; text-decoration-style: dotted;
  }
  h2 .inline-numbers a:hover { color: var(--brand-dark); }

  /* Per-REC subsection headings inside SPARQL 1.1 / RDF 1.1 families */
  h3.rec-subhead {
    margin: 1.0em 0 0.35em; font-size: 0.95rem; font-weight: 600;
    color: var(--brand-dark); border-bottom: 1px solid var(--border);
    padding-bottom: 0.2em;
  }
  h3.rec-subhead a {
    color: inherit; text-decoration: none; border-bottom: 1px dotted var(--muted);
  }
  h3.rec-subhead a:hover { color: var(--brand); border-bottom-color: var(--brand); }

  .failure-detail {
    margin: 0.5em 0 1em;
    padding: 0.6em 0.8em;
    border-left: 4px solid var(--muted);
    background: var(--surface);
    border-radius: 3px;
    font-size: 0.88rem;
  }
  .failure-detail summary {
    cursor: pointer; color: var(--muted); padding: 0.4em 0;
    min-height: 44px; display: flex; align-items: center;
  }
  .failure-detail summary:hover { color: var(--brand-dark); }
  .failure-detail ul {
    margin: 0.5em 0 0; padding-left: 1.3em;
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.85rem;
  }
  .failure-detail li { margin: 0.3em 0; line-height: 1.4; overflow-wrap: anywhere; }

  /* --- Suite rows: mobile-first single column, meter always full-width - */
  .suites { display: flex; flex-direction: column; gap: 0.5em; margin: 0 0 0.6em; }
  .suite-row {
    display: flex; flex-direction: column; gap: 0.35em;
    padding: 0.55em 0.7em;
    border-radius: 6px;
    background: var(--surface);
    font-size: 0.95rem;
  }
  .suite-row .suite-name {
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.92rem; font-weight: 600; overflow-wrap: anywhere;
  }
  .suite-row .suite-numbers {
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.85rem; color: var(--muted);
  }
  .suite-row .suite-numbers .p { color: var(--ok); font-weight: 600; }
  .suite-row .suite-numbers .f { color: var(--err); font-weight: 600; }
  .suite-row .suite-numbers small { color: var(--muted); font-weight: 400; }
  .suite-row.green { background: var(--ok-tint); }
  .suite-row.amber { background: var(--warn-tint); }
  .suite-row.grey  { background: var(--skip-tint); }

  /* Stacked pass/fail/skip meter — one definition, used by every suite
     row on the page. Always full-width of its row. */
  .meter {
    display: flex; width: 100%; height: 0.85em;
    background: var(--border); border-radius: 3px; overflow: hidden;
  }
  .meter .seg { height: 100%; }
  .meter .seg-pass { background: var(--ok); }
  .meter .seg-fail { background: var(--err); }
  .meter .seg-skip { background: var(--skip); }

  .suite-prov {
    margin: -0.25em 0 0.15em; font-size: 0.78rem; color: var(--muted);
    overflow-wrap: anywhere;
  }
  .suite-prov a { color: var(--brand-dark); }
  .suite-prov code {
    background: var(--surface); padding: 0.05em 0.3em; border-radius: 3px;
    font-size: 0.95em;
  }

  details {
    margin: 1em 0; background: var(--surface); border-radius: 6px;
    padding: 0.4em 0.8em; border: 1px solid var(--border);
  }
  details summary {
    cursor: pointer; font-weight: 500; color: var(--muted);
    font-size: 0.95rem; padding: 0.7em 0.2em;
    min-height: 44px; display: flex; align-items: center;
  }
  details pre {
    background: var(--bg); padding: 0.6em 0.7em;
    border: 1px solid var(--border); border-radius: 4px;
    font-size: 0.8rem; overflow-x: auto; margin: 0.4em 0 0.6em;
    white-space: pre;
  }
  details ul { margin: 0.4em 0 0.6em; padding-left: 1.2em; font-size: 0.92rem; }
  details li { overflow-wrap: anywhere; }
  details code {
    background: var(--bg); padding: 0.1em 0.3em;
    border: 1px solid var(--border); border-radius: 2px;
    font-size: 0.88em; overflow-wrap: anywhere;
  }

  footer {
    max-width: 900px; margin: 2em auto 3em; padding: 1em 0.8em;
    color: var(--muted); font-size: 0.85rem; border-top: 1px solid var(--border);
  }
  footer code { background: var(--surface); padding: 0.1em 0.4em; border-radius: 3px; }

  /* --- Widen past phone width ------------------------------------------ */
  @media (min-width: 640px) {
    main { padding: 1.5em 1em; }
    header { padding: 1.2em 1em; }
    .family { padding: 1em 1.2em; }
    .suite-row {
      display: grid;
      grid-template-columns: 15em 1fr 9em;
      align-items: center; gap: 0.8em;
    }
    .suite-row .suite-numbers { text-align: right; }
    .suite-prov { margin: -0.3em 0 0.3em 0.2em; }
  }
  @media (min-width: 760px) {
    header { position: relative; }
    header .inner { position: relative; padding-right: 13em; }
    .rendered-pill {
      position: absolute; top: 0; right: 0; margin: 0;
      white-space: nowrap;
      box-shadow: 0 1px 2px rgba(0,0,0,0.08);
    }
    h2 .inline-numbers { display: inline; margin-left: 0.5em; }
  }
</style>
</head>
<body>

<header>
  <div class="inner">
    <div class="rendered-pill" title="Rendered = when this page was last regenerated. Tests = when the *_results.log files inside the repository were last updated. Both UTC.">
      <span class="row"><span class="label">Rendered</span><strong>${TIMESTAMP_HUMAN}</strong></span>
      <span class="row"><span class="label">Tests</span><strong class="tests">${TESTS_TIMESTAMP_HUMAN}</strong></span>
    </div>
    <h1>W3C test results</h1>
    <p>Pass/fail/skip counts against every standards suite this project measures: RDF 1.1, SPARQL 1.1, RDFS/OWL 2, SHACL, ShEx, RIF Core, RML, JSON-LD 1.1, and Verifiable Credentials 2.0.</p>
    <nav>
      <a href="/factoidal/">Home</a>
      <a href="/factoidal/fstar-extracted/">Demos</a>
      <a href="https://github.com/danbri/factoidal">GitHub</a>
    </nav>
  </div>
</header>

<main>

<div class="summary">
  <div class="tile ok">
    <div class="label">Pass</div>
    <div class="value">${COMBINED_PASS}</div>
  </div>
  <div class="tile err">
    <div class="label">Fail</div>
    <div class="value">${COMBINED_FAIL}</div>
  </div>
  <div class="tile warn">
    <div class="label">Skipped</div>
    <div class="value">${COMBINED_SKIP}</div>
  </div>
  <div class="tile">
    <div class="label">Pass / runnable</div>
    <div class="value">${COMBINED_PCT}%<small> of ${run_total}</small></div>
  </div>
  <div class="tile">
    <div class="label">Total in suites</div>
    <div class="value">${COMBINED_TOTAL}</div>
  </div>
</div>

<div class="caveat">
  <strong>Scope.</strong> These counts measure conformance only — whether the
  engine produces the expected result on each vendored fixture. They say
  nothing about performance, memory use, scale, or real-world query shape
  (see the parse/serialize throughput section below for that, measured
  separately). Skipped tests are features not yet implemented or explicitly
  out of scope for the current stage. Raw per-suite logs and machine-readable
  artifacts are linked at the bottom of the page.
</div>

${LEGEND_HTML}

${SPARQL_FAMILY_HTML}

${RDFCORE_HTML}

${OWL_FAMILY_HTML}

${SHAPES_HTML}

${RULES_HTML}

${MAPPING_HTML}

${JSONLD_FAMILY_HTML}

${VC_FAMILY_HTML}

${PERF_SECTION_HTML}

<details>
  <summary>Machine-readable artifacts</summary>
  <ul>
    <li><a href="latest.csv"><code>latest.csv</code></a> — one row per suite (timestamp, commit, branch, category, suite, pass/fail/skip/unsupported)</li>
    <li><a href="latest.json"><code>latest.json</code></a> — same data plus totals, structured</li>
    <li><code>history/&lt;timestamp&gt;.csv</code> / <code>.json</code> — timestamped copies, one pair per runner invocation</li>
    <li><a href="perf-parse-serialize.json"><code>perf-parse-serialize.json</code></a> — parse/serialize/canonicalize throughput (if present; produced by <code>tools/bench-parse-serialize.sh</code>, not this script)</li>
  </ul>
  <p style="margin: 0.6em 0 0; color: var(--muted); font-size: 0.9em;">
    The raw runner logs (including per-test FAIL lines with diffs) are committed under
    <code>formal/fstar/ocaml-output/*_results.log</code> — one file per suite, named to
    match each suite's <code>.github/test-suites/&lt;suite&gt;.yaml</code> manifest.
  </p>
</details>

<details>
  <summary>Raw per-suite numbers</summary>
  <h3 style="font-size: 0.95em; margin: 0.8em 0 0.3em;">SPARQL 1.1</h3>
  <pre>${SPARQL_TOTAL} total: ${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip, ${SPARQL_UNSUP} unsupported
${SPARQL_SUITES}</pre>
  <h3 style="font-size: 0.95em; margin: 0.8em 0 0.3em;">RDF 1.1</h3>
  <pre>${RDF_TOTAL} total: ${RDF_PASS} pass, ${RDF_FAIL} fail, ${RDF_SKIP} skip, ${RDF_UNSUP} unsupported
${RDF_SUITES}</pre>
  <h3 style="font-size: 0.95em; margin: 0.8em 0 0.3em;">Shapes / Rules / Mapping / JSON-LD / VC</h3>
  <pre>shacl-core:   ${SHACL_CORE_PASS} pass, ${SHACL_CORE_FAIL} fail, ${SHACL_CORE_SKIP} skip (of ${SHACL_CORE_TOTAL}) — present=${SHACL_CORE_PRESENT}
shacl-sparql: ${SHACL_SPARQL_PASS} pass, ${SHACL_SPARQL_FAIL} fail, ${SHACL_SPARQL_SKIP} skip (of ${SHACL_SPARQL_TOTAL}) — present=${SHACL_SPARQL_PRESENT}
shex:         ${SHEX_PASS} pass, ${SHEX_FAIL} fail, ${SHEX_SKIP} skip (of ${SHEX_TOTAL}) — present=${SHEX_PRESENT}
jsonld-tordf: ${JSONLD_PASS} pass, ${JSONLD_FAIL} fail, ${JSONLD_SKIP} skip (of ${JSONLD_TOTAL}) — present=${JSONLD_PRESENT}
rml-core:     ${RML_PASS} pass, ${RML_FAIL} fail, ${RML_SKIP} skip (of ${RML_TOTAL}) — present=${RML_PRESENT}
rif-core:     ${RIFCORE_COMBINED_PASS} pass, ${RIFCORE_COMBINED_FAIL} fail, ${RIFCORE_COMBINED_SKIP} skip (of ${RIFCORE_COMBINED_TOTAL}) — present=${RIFCORE_COMBINED_PRESENT}
vc-stage1:    ${VC_PASS} pass, ${VC_FAIL} fail, ${VC_SKIP} skip (of ${VC_TOTAL}) — present=${VC_PRESENT}</pre>
</details>

<details>
  <summary>How this page is generated</summary>
  <p style="margin: 0.5em 0; color: var(--muted); font-size: 0.9em;">
    Source: <code>formal/fstar/generate-report.sh</code>. It shells out to the
    <code>w3c_runner</code> binary (extracted from F* specs, compiled via OCaml),
    scrapes per-suite counts, and writes <code>index.html</code>, <code>latest.csv</code>,
    and <code>latest.json</code>. Run <code>./generate-report.sh --run</code> in
    <code>formal/fstar/</code> to regenerate. CI re-runs on every push and nightly
    at 06:00 UTC.
  </p>
</details>

</main>

<footer>
  Generated <strong>${TIMESTAMP_HUMAN}</strong> from commit
  <code><a href="https://github.com/danbri/factoidal/commit/${GIT_SHA_FULL}">${GIT_SHA}</a></code>
  on branch <code>${GIT_BRANCH}</code>${GIT_SUBJECT_LINE}.
  Re-run locally: <code>cd formal/fstar &amp;&amp; ./generate-report.sh --run</code>.
</footer>

</body>
</html>
HTMLEOF

echo ""
echo "Report generated: $OUTPUT_DIR/index.html"
echo "  CSV:  $CSV  (+ history/${TIMESTAMP_ISO}.csv)"
echo "  JSON: $JSON (+ history/${TIMESTAMP_ISO}.json)"
echo "  SPARQL: ${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip, ${SPARQL_UNSUP} unsupported"
echo "  RDF:    ${RDF_PASS} pass, ${RDF_FAIL} fail, ${RDF_SKIP} skip, ${RDF_UNSUP} unsupported"
echo "  Overall: ${COMBINED_PASS}/${run_total} runnable = ${COMBINED_PCT}%"
if [ "$OWL_PRESENT" -eq 1 ]; then
  echo "  OWL 2 RL (profile-RL PositiveEntailmentTests): ${OWL_PASS} pass, ${OWL_FAIL} fail (out of ${OWL_TOTAL})"
else
  echo "  OWL 2 RL: no cached log ($OWL_LOG); re-run with --run to populate"
fi
report_suite_line () {
  local label="$1" prefix="$2"
  local prv="${prefix}_PRESENT" pv="${prefix}_PASS" fv="${prefix}_FAIL" sv="${prefix}_SKIP" tv="${prefix}_TOTAL"
  if [ "${!prv:-0}" -eq 1 ]; then
    echo "  ${label}: ${!pv} pass, ${!fv} fail, ${!sv} skip (out of ${!tv})"
  else
    echo "  ${label}: not measured this run"
  fi
}
report_suite_line "SHACL Core"        SHACL_CORE
report_suite_line "SHACL SPARQL"      SHACL_SPARQL
report_suite_line "ShEx"              SHEX
report_suite_line "JSON-LD 1.1 toRdf" JSONLD
report_suite_line "RML rml-core"      RML
report_suite_line "RIF Core"          RIFCORE_COMBINED
report_suite_line "VC 2.0 (Stage 1)"  VC
echo "  Commit: ${GIT_SHA} (${GIT_BRANCH})"
