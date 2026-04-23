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

mkdir -p "$OUTPUT_DIR" "$HISTORY_DIR"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/w3c_runner" ;;
  Linux-x86_64)  RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/w3c_runner" ;;
  *)             RUNNER="$OCAML_DIR/w3c_runner" ;;
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
  printf '    "combined": {"pass":%s,"fail":%s,"skip":%s,"unsupported":%s,"total":%s,"pass_pct_of_runnable":%s}\n' \
    "$COMBINED_PASS" "$COMBINED_FAIL" "$COMBINED_SKIP" "$COMBINED_UNSUP" "$COMBINED_TOTAL" "$COMBINED_PCT"
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
echo "  Commit: ${GIT_SHA} (${GIT_BRANCH})"
