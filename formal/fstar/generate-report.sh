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
RDFC10_LOG="$OCAML_DIR/rdfc10_results.log"

mkdir -p "$OUTPUT_DIR" "$HISTORY_DIR"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/w3c_runner"
    OWL_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/owl_runner"
    RDFC10_RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/rdfc10_runner"
    ;;
  Linux-x86_64)
    RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/w3c_runner"
    OWL_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/owl_runner"
    RDFC10_RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/rdfc10_runner"
    ;;
  *)
    RUNNER="$OCAML_DIR/w3c_runner"
    OWL_RUNNER="$OCAML_DIR/owl_runner"
    RDFC10_RUNNER="$OCAML_DIR/rdfc10_runner"
    ;;
esac

if [ "$1" = "--run" ]; then
  [ -x "$RUNNER" ] || { echo "Runner not found or not executable: $RUNNER" >&2; exit 2; }
  # Runner exits nonzero when any test fails (by design). `|| true` keeps
  # the log either way — the per-suite numbers are what we need.
  echo "Running SPARQL 1.1 suite…"
  "$RUNNER"       > "$SPARQL_LOG" 2>&1 || true
  echo "  done."
  echo "Running RDF 1.1 suite…"
  "$RUNNER" --rdf > "$RDF_LOG" 2>&1 || true
  echo "  done."
  if [ -x "$OWL_RUNNER" ]; then
    echo "Running OWL 2 RL profile suite (PositiveEntailmentTests)…"
    "$OWL_RUNNER" > "$OWL_LOG" 2>&1 || true
    echo "  done."
  else
    echo "  owl_runner not found at $OWL_RUNNER — skipping OWL 2 RL suite." >&2
  fi
  if [ -x "$RDFC10_RUNNER" ]; then
    echo "Running RDFC-1.0 (RDF Dataset Canonicalization) suite…"
    "$RDFC10_RUNNER" > "$RDFC10_LOG" 2>&1 || true
    echo "  done."
  else
    echo "  rdfc10_runner not found at $RDFC10_RUNNER — skipping RDFC-1.0 suite." >&2
  fi
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
  printf '    "owl_rl_positive_entailment": {"pass":%s,"fail":%s,"total":%s,"catalog":"third_party/testing/owl/profile-RL.rdf"}\n' \
    "$OWL_PASS" "$OWL_FAIL" "$OWL_TOTAL"
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
emit_suite_rows () {
  local blob="$1"
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    local name pass fail skip unsup ran bar_pct bar_class extra
    name=$(echo  "$line" | awk '{print $1}')
    pass=$(echo  "$line" | sed -nE 's/.*pass:([0-9]+).*/\1/p')
    fail=$(echo  "$line" | sed -nE 's/.*fail:([0-9]+).*/\1/p')
    skip=$(echo  "$line" | sed -nE 's/.*skip:([0-9]+).*/\1/p')
    unsup=$(echo "$line" | sed -nE 's/.*unsupported:([0-9]+).*/\1/p')
    pass=${pass:-0}; fail=${fail:-0}; skip=${skip:-0}; unsup=${unsup:-0}
    ran=$((pass + fail))
    if [ "$ran" -eq 0 ] && [ "$skip" -eq 0 ] && [ "$unsup" -eq 0 ]; then continue; fi
    if [ "$ran" -gt 0 ]; then
      bar_pct=$(awk -v p="$pass" -v r="$ran" 'BEGIN{printf "%.0f", 100*p/r}')
    else
      bar_pct=0
    fi
    if [ "$fail" -eq 0 ] && [ "$pass" -gt 0 ]; then          bar_class="perfect"
    elif [ "$fail" -gt 0 ] && [ "$bar_pct" -ge 90 ]; then    bar_class="near-perfect"
    elif [ "$pass" -eq 0 ] && [ "$skip" -gt 0 ]; then        bar_class="skipped"
    else                                                      bar_class="mixed"
    fi
    extra=""
    [ "$skip" -gt 0 ]  && extra="skip ${skip}"
    [ "$unsup" -gt 0 ] && extra="${extra} unsup ${unsup}"
    cat <<ROW
      <div class="suite-row ${bar_class}">
        <div class="suite-name">${name}</div>
        <div class="suite-bar"><div class="fill" style="width:${bar_pct}%"></div></div>
        <div class="suite-numbers">
          <span class="p">${pass}</span>/<span class="f">${fail}</span>
          <small>${extra}</small>
        </div>
      </div>
ROW
  done <<<"$blob"
}

SPARQL_ROWS_HTML=$(emit_suite_rows "$SPARQL_SUITES")
RDF_ROWS_HTML=$(emit_suite_rows "$RDF_SUITES")

# RDFC-1.0 row for the RDF 1.1 panel.
# rdfc10_runner emits a single labelled-totals line; synthesize the same
# shape that emit_suite_rows expects so we share styling with the rest of
# the suites.
if [ "$RDFC10_PRESENT" -eq 1 ]; then
  RDFC10_BLOB="  rdf-canon  pass:${RDFC10_PASS} fail:${RDFC10_FAIL} skip:${RDFC10_SKIP} unsupported:0"
  RDFC10_ROW_HTML=$(emit_suite_rows "$RDFC10_BLOB")
  RDF_ROWS_HTML="${RDF_ROWS_HTML}
${RDFC10_ROW_HTML}"
fi

# --- OWL 2 panel ---------------------------------------------------------
# Distinct corpus, distinct denominator; deliberately NOT folded into the
# SPARQL/RDF totals tiles. profile-RL gets actual pass/fail from
# owl_runner; other OWL 2 catalogs are listed as "skipped for now" with
# rationale, so the user can see the full W3C OWL 2 Test Cases footprint
# we've vendored and what we're NOT yet exercising.
if [ "$OWL_PRESENT" -eq 1 ]; then
  if [ "$OWL_TOTAL" -gt 0 ]; then
    OWL_BAR_PCT=$(awk -v p="$OWL_PASS" -v t="$OWL_TOTAL" 'BEGIN{printf "%.0f", 100*p/t}')
  else
    OWL_BAR_PCT=0
  fi
  if [ "$OWL_PASS" -eq "$OWL_TOTAL" ] && [ "$OWL_TOTAL" -gt 0 ]; then
    OWL_BAR_CLASS="perfect"
  elif [ "$OWL_BAR_PCT" -ge 90 ]; then
    OWL_BAR_CLASS="near-perfect"
  else
    OWL_BAR_CLASS="mixed"
  fi
else
  OWL_BAR_PCT=0; OWL_BAR_CLASS="skipped"
  OWL_PASS=0; OWL_FAIL=0; OWL_TOTAL=0
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
  cat <<ROW
  <div class="suite-row skipped">
    <div class="suite-name">${name}</div>
    <div class="suite-bar"><div class="fill" style="width:0%"></div></div>
    <div class="suite-numbers">
      <span style="color:var(--muted)">&mdash;</span>
      <small>${count} tests &middot; ${reason}</small>
    </div>
  </div>
ROW
}

OWL_SKIP_ROWS=""
OWL_SKIP_ROWS+="$(emit_owl_skip_row "profile-EL" "$OWL_EL_N"   "blocked on EL-profile closure rules")"$'\n'
OWL_SKIP_ROWS+="$(emit_owl_skip_row "profile-QL" "$OWL_QL_N"   "blocked on QL-profile query rewrite")"$'\n'
OWL_SKIP_ROWS+="$(emit_owl_skip_row "semantics-direct" "$OWL_SEMDL_N" "blocked on DL tableau (stage d/e)")"$'\n'
OWL_SKIP_ROWS+="$(emit_owl_skip_row "syntax-dl" "$OWL_SYNDL_N" "blocked on DL syntactic-profile checker")"$'\n'
OWL_SKIP_ROWS+="$(emit_owl_skip_row "type-positive-entailment" "$OWL_TPE_N" "blocked on closure-side bnode isomorphism")"$'\n'
OWL_SKIP_ROWS+="$(emit_owl_skip_row "type-negative-entailment" "$OWL_TNE_N" "blocked on OWL negation support")"$'\n'
OWL_SKIP_ROWS+="$(emit_owl_skip_row "type-consistency" "$OWL_TCON_N" "blocked on contradiction detection")"$'\n'
OWL_SKIP_ROWS+="$(emit_owl_skip_row "type-inconsistency" "$OWL_TINC_N" "blocked on contradiction detection")"$'\n'

# --- RDFC-1.0 panel ------------------------------------------------------
# RDFC-1.0 (W3C RDF Dataset Canonicalization 1.0) gets its own headline
# panel parallel to OWL 2 RL. It's a separate W3C suite with a different
# denominator and shape. Eval tests check canonical-form bytewise; Map
# tests check the bnode→canonical mapping (currently STUB — runner
# emits no JSON map yet). NegEval tests check that pathological inputs
# don't infinitely loop. Counts are live from rdfc10_runner.
if [ "$RDFC10_PRESENT" -eq 1 ]; then
  RDFC10_RUN_TOTAL=$((RDFC10_PASS + RDFC10_FAIL))
  if [ "$RDFC10_RUN_TOTAL" -gt 0 ]; then
    RDFC10_BAR_PCT=$(awk -v p="$RDFC10_PASS" -v t="$RDFC10_RUN_TOTAL" 'BEGIN{printf "%.0f", 100*p/t}')
  else
    RDFC10_BAR_PCT=0
  fi
  if [ "$RDFC10_FAIL" -eq 0 ] && [ "$RDFC10_PASS" -gt 0 ]; then
    RDFC10_BAR_CLASS="perfect"
  elif [ "$RDFC10_BAR_PCT" -ge 90 ]; then
    RDFC10_BAR_CLASS="near-perfect"
  else
    RDFC10_BAR_CLASS="mixed"
  fi
else
  RDFC10_BAR_PCT=0; RDFC10_BAR_CLASS="skipped"
  RDFC10_PASS=0; RDFC10_FAIL=0; RDFC10_SKIP=0; RDFC10_TOTAL=0
fi

RDFC10_HTML=$(cat <<RDFCEOF
<h2>RDFC-1.0 <span class="inline-numbers">${RDFC10_PASS} pass &middot; ${RDFC10_FAIL} fail &middot; ${RDFC10_SKIP} stub &middot; of ${RDFC10_TOTAL} total</span></h2>
<div class="suites">
  <div class="suite-row ${RDFC10_BAR_CLASS}">
    <div class="suite-name">eval (HFDQ)</div>
    <div class="suite-bar"><div class="fill" style="width:${RDFC10_BAR_PCT}%"></div></div>
    <div class="suite-numbers">
      <span class="p">${RDFC10_PASS}</span>/<span class="f">${RDFC10_FAIL}</span>
      <small>of $((RDFC10_PASS + RDFC10_FAIL))</small>
    </div>
  </div>
  <div class="suite-row skipped">
    <div class="suite-name">map / negative-eval</div>
    <div class="suite-bar"><div class="fill" style="width:0%"></div></div>
    <div class="suite-numbers">
      <small>${RDFC10_SKIP} stub &mdash; runner does not emit map JSON / HNDQ termination guard</small>
    </div>
  </div>
</div>
<p style="margin: 0.3em 0 1em; color: var(--muted); font-size: 0.85em;">
  <strong>RDFC-1.0 (W3C RDF Dataset Canonicalization):</strong>
  We vendor the full W3C RDFC-1.0 Test Cases at
  <code>third_party/testing/rdf-canon/</code>. The canonical-labelling
  algorithm lives in F&#42; at <code>formal/fstar/RDF.Canonical.fst</code>
  &mdash; <em>Hash First Degree Quads (HFDQ)</em> phase verifies cleanly
  with no <code>--lax</code> and no <code>--admit_smt_queries</code>.
  Eval tests check the canonical N-Quads form bytewise. Phase 2 work
  (HNDQ &mdash; Hash N-Degree Quads with bounded permutation
  enumeration) closes the remaining symmetric-cycle eval tests. Map
  tests are STUB pending a runner-side bnode &rarr; canonical-id JSON
  emitter; NegEval tests need an HNDQ termination guard.
</p>
RDFCEOF
)

OWL_HTML=$(cat <<OWLEOF
<h2>OWL 2 <span class="inline-numbers">${OWL_PASS} pass &middot; ${OWL_FAIL} fail &middot; profile-RL PositiveEntailmentTests only</span></h2>
<div class="suites">
  <div class="suite-row ${OWL_BAR_CLASS}">
    <div class="suite-name">profile-RL PosEnt</div>
    <div class="suite-bar"><div class="fill" style="width:${OWL_BAR_PCT}%"></div></div>
    <div class="suite-numbers">
      <span class="p">${OWL_PASS}</span>/<span class="f">${OWL_FAIL}</span>
      <small>of ${OWL_TOTAL}</small>
    </div>
  </div>
${OWL_SKIP_ROWS}</div>
<p style="margin: 0.3em 0 1em; color: var(--muted); font-size: 0.85em;">
  <strong>OWL 2 (W3C conformance):</strong>
  We vendor the full W3C OWL 2 Test Cases at
  <code>third_party/testing/owl/</code> (10 catalog files, ~2500
  <code>test:TestCase</code> entries after overlap). Only <em>profile-RL
  PositiveEntailmentTests</em> are wired right now: the runner applies
  <code>owl_rl_closure_with_reflexivity</code> (fuel 100) and checks the
  conclusion&rsquo;s triples against the closure (relaxed bnode match). The
  other OWL 2 categories are <em>skipped for now</em>&mdash;blocked on
  completing the RDF/S and SPARQL entailment baselines above. Counts
  are live from the vendored catalogs, not stale snapshots.
</p>
OWLEOF
)

[ -n "$GIT_SUBJECT" ] && GIT_SUBJECT_LINE=" — &ldquo;${GIT_SUBJECT}&rdquo;" || GIT_SUBJECT_LINE=""

cat > "$OUTPUT_DIR/index.html" <<HTMLEOF
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Factoidal — W3C test results</title>
<style>
  :root {
    --fg: #222; --muted: #666; --bg: #fff; --surface: #f7f7f7;
    --border: #e0e0e0; --brand: #2d6a4f; --brand-dark: #1b4332;
    --ok: #2d6a4f; --warn: #d97706; --err: #c0392b;
  }
  * { box-sizing: border-box; }
  html, body { margin: 0; padding: 0; }
  body {
    font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
    color: var(--fg); background: var(--bg); line-height: 1.55;
  }
  header {
    background: var(--surface);
    border-bottom: 1px solid var(--border); padding: 1.2em 1em;
  }
  header .inner { max-width: 900px; margin: 0 auto; }
  header h1 { margin: 0 0 0.15em; font-size: 1.3em; color: var(--brand-dark); }
  header p  { margin: 0; color: var(--muted); font-size: 0.9em; }
  header nav { margin-top: 0.7em; font-size: 0.9em; }
  header nav a { margin-right: 1.2em; color: var(--brand-dark); }
  main { max-width: 900px; margin: 0 auto; padding: 1.5em 1em; }

  .summary {
    display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
    gap: 0.8em; margin: 0 0 1.5em;
  }
  .tile {
    background: var(--surface); border: 1px solid var(--border);
    border-radius: 4px; padding: 0.7em 0.9em;
  }
  .tile .label { color: var(--muted); font-size: 0.8em; margin-bottom: 0.1em; }
  .tile .value { font-size: 1.4em; font-weight: 600; line-height: 1; }
  .tile .value small { font-size: 0.6em; font-weight: 400; color: var(--muted); }
  .tile.ok   .value { color: var(--ok); }
  .tile.err  .value { color: var(--err); }
  .tile.warn .value { color: var(--warn); }

  .caveat {
    border-left: 3px solid #9ca3af;
    background: var(--surface);
    padding: 0.7em 1em; margin: 0 0 1.5em; border-radius: 0 4px 4px 0;
    font-size: 0.9em; color: #444;
  }
  .caveat strong { color: var(--brand-dark); }

  h2 { margin: 1.8em 0 0.5em; font-size: 1.1em; color: var(--brand-dark); }
  h2 .inline-numbers {
    font-weight: 400; color: var(--muted); font-size: 0.85em;
    margin-left: 0.4em;
  }

  .suites { display: flex; flex-direction: column; gap: 0.2em; margin: 0 0 1em; }
  .suite-row {
    display: grid;
    grid-template-columns: 13em 1fr 8em;
    align-items: center; gap: 0.8em;
    padding: 0.3em 0.7em;
    border-radius: 3px;
    font-size: 0.9em;
  }
  .suite-row .suite-name { font-family: ui-monospace, Menlo, Consolas, monospace;
                           font-size: 0.88em; }
  .suite-row .suite-bar {
    height: 0.6em; background: var(--border); border-radius: 2px; overflow: hidden;
  }
  .suite-row .suite-bar .fill {
    height: 100%; background: var(--ok);
  }
  .suite-row .suite-numbers {
    font-family: ui-monospace, Menlo, Consolas, monospace;
    font-size: 0.85em; text-align: right;
  }
  .suite-row .suite-numbers .p { color: var(--ok); font-weight: 600; }
  .suite-row .suite-numbers .f { color: var(--err); font-weight: 600; }
  .suite-row .suite-numbers small { color: var(--muted); font-weight: 400; }
  .suite-row.perfect       .suite-bar .fill { background: var(--ok); }
  .suite-row.near-perfect  .suite-bar .fill { background: #65a30d; }
  .suite-row.mixed         .suite-bar .fill { background: var(--warn); }
  .suite-row.skipped       .suite-bar .fill { background: #9ca3af; }

  @media (max-width: 520px) {
    .suite-row { grid-template-columns: 1fr auto; grid-template-rows: auto auto; }
    .suite-row .suite-bar { grid-column: 1 / span 2; }
    .suite-row .suite-numbers { grid-column: 2; grid-row: 1; }
  }

  details { margin: 1em 0; background: var(--surface); border-radius: 4px;
            padding: 0.5em 0.8em; border: 1px solid var(--border); }
  details summary { cursor: pointer; font-weight: 500; color: var(--muted);
                    font-size: 0.9em; }
  details pre { background: var(--bg); padding: 0.5em 0.7em;
                border: 1px solid var(--border); border-radius: 3px;
                font-size: 0.82em; overflow-x: auto; margin: 0.4em 0 0; }
  details ul { margin: 0.4em 0 0; padding-left: 1.3em; font-size: 0.9em; }
  details code { background: var(--bg); padding: 0.1em 0.3em;
                 border: 1px solid var(--border); border-radius: 2px;
                 font-size: 0.88em; }

  footer {
    max-width: 900px; margin: 2em auto 3em; padding: 1em;
    color: var(--muted); font-size: 0.82em; border-top: 1px solid var(--border);
  }
  footer code { background: var(--surface); padding: 0.1em 0.4em; border-radius: 3px; }
  footer a { color: var(--brand-dark); }
</style>
</head>
<body>

<header>
  <div class="inner">
    <h1>W3C test results</h1>
    <p>Per-suite pass/fail counts against the W3C SPARQL 1.1 and RDF 1.1 conformance suites.</p>
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
  engine produces the expected result on each W3C-supplied fixture. They say
  nothing about performance, memory use, scale, or real-world query shape.
  Skipped tests are features not yet implemented (mostly HTTP-protocol /
  federated-query endpoints). Raw per-suite logs and machine-readable artifacts
  are linked below.
</div>

<h2>SPARQL 1.1 <span class="inline-numbers">${SPARQL_PASS} pass · ${SPARQL_FAIL} fail · ${SPARQL_SKIP} skip</span></h2>
<div class="suites">
${SPARQL_ROWS_HTML}
</div>

<h2>RDF 1.1 <span class="inline-numbers">${RDF_PASS} pass · ${RDF_FAIL} fail</span></h2>
<div class="suites">
${RDF_ROWS_HTML}
</div>

${OWL_HTML}

${RDFC10_HTML}

<details>
  <summary>Machine-readable artifacts</summary>
  <ul>
    <li><a href="latest.csv"><code>latest.csv</code></a> — one row per suite (timestamp, commit, branch, category, suite, pass/fail/skip/unsupported)</li>
    <li><a href="latest.json"><code>latest.json</code></a> — same data plus totals, structured</li>
    <li><code>history/&lt;timestamp&gt;.csv</code> / <code>.json</code> — timestamped copies, one pair per runner invocation</li>
  </ul>
  <p style="margin: 0.6em 0 0; color: var(--muted); font-size: 0.9em;">
    The raw runner logs (including per-test FAIL lines with diffs) are committed to
    <code>formal/fstar/ocaml-output/sparql_results.log</code> and
    <code>formal/fstar/ocaml-output/rdf_results.log</code>.
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
echo "  Commit: ${GIT_SHA} (${GIT_BRANCH})"
