#!/bin/bash
# Generate a human-readable W3C conformance report for docs/test-results/.
#
# Output: docs/test-results/index.html
#
# Written to be legible by people who don't know RDF, SPARQL, or W3C
# test suites. Headline numbers up top, plain-English framing, a visual
# bar per suite, and the raw per-suite counts tucked under <details>.
#
# Usage:
#   ./generate-report.sh                  (re-generate from cached logs)
#   ./generate-report.sh --run            (re-run the W3C tests first)
#
# Cached logs live at:
#   ocaml-output/sparql_results.log
#   ocaml-output/rdf_results.log
#
# Portability note: BSD-compatible (macOS darwin + Linux). No grep -P.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
OCAML_DIR="$SCRIPT_DIR/ocaml-output"
OUTPUT_DIR="$SCRIPT_DIR/../../docs/test-results"
SPARQL_LOG="$OCAML_DIR/sparql_results.log"
RDF_LOG="$OCAML_DIR/rdf_results.log"

mkdir -p "$OUTPUT_DIR"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  RUNNER="$SCRIPT_DIR/../../bin/darwin-arm64/w3c_runner" ;;
  Linux-x86_64)  RUNNER="$SCRIPT_DIR/../../bin/linux-x86_64/w3c_runner" ;;
  *)             RUNNER="$OCAML_DIR/w3c_runner" ;;
esac

if [ "$1" = "--run" ]; then
  [ -x "$RUNNER" ] || { echo "Runner not found or not executable: $RUNNER" >&2; exit 2; }
  # Runner exits nonzero when any test fails (by design). We capture the
  # log either way — the per-suite numbers are what matters, not the
  # exit code. `|| true` overrides `set -e`.
  echo "Running SPARQL 1.1 suite…"
  "$RUNNER"       > "$SPARQL_LOG" 2>&1 || true
  echo "  done."
  echo "Running RDF 1.1 suite…"
  "$RUNNER" --rdf > "$RDF_LOG" 2>&1 || true
  echo "  done."
elif [ -f "$OCAML_DIR/w3c_results.log" ] && [ ! -f "$SPARQL_LOG" ]; then
  # Legacy: split the combined log (older build-ocaml.sh produced one log).
  sed -n '1,/^=== W3C RDF/p' "$OCAML_DIR/w3c_results.log" | sed '$d' > "$SPARQL_LOG"
  sed -n '/^=== W3C RDF/,$p' "$OCAML_DIR/w3c_results.log" > "$RDF_LOG"
fi

if [ ! -f "$SPARQL_LOG" ] || [ ! -f "$RDF_LOG" ]; then
  echo "No test results found. Run with --run first." >&2
  exit 1
fi

# --- Scrape suite lines ------------------------------------------------------
# Suite lines look like:   add  pass:8 fail:0 skip:0 unsupported:0
SPARQL_SUITES=$(grep '^  [a-z]' "$SPARQL_LOG" | grep 'pass:' || true)
RDF_SUITES=$(grep    '^  [a-z]' "$RDF_LOG"    | grep 'pass:' || true)

# --- Aggregate totals --------------------------------------------------------
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

TIMESTAMP=$(date -u +"%Y-%m-%d %H:%M UTC")
GIT_SHA=$(git -C "$SCRIPT_DIR" rev-parse --short HEAD 2>/dev/null || echo "unknown")
GIT_SHA_FULL=$(git -C "$SCRIPT_DIR" rev-parse HEAD 2>/dev/null || echo "unknown")
GIT_BRANCH=$(git -C "$SCRIPT_DIR" branch --show-current 2>/dev/null || echo "unknown")
GIT_SUBJECT=$(git -C "$SCRIPT_DIR" log -1 --pretty=%s 2>/dev/null || echo "")

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
<title>Factoidal — how well does our engine follow the SPARQL / RDF standards?</title>
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
    background: linear-gradient(180deg, var(--surface), var(--bg));
    border-bottom: 1px solid var(--border); padding: 1.5em 1em;
  }
  header .inner { max-width: 900px; margin: 0 auto; }
  header h1 { margin: 0 0 0.2em; font-size: 1.5em; color: var(--brand-dark); }
  header p  { margin: 0; color: var(--muted); font-size: 0.95em; }
  header nav { margin-top: 0.8em; font-size: 0.9em; }
  header nav a { margin-right: 1.2em; color: var(--brand-dark); }
  main { max-width: 900px; margin: 0 auto; padding: 1.5em 1em; }

  .hero {
    background: var(--surface); border: 1px solid var(--border);
    border-radius: 8px; padding: 1.8em; margin: 0 0 2em;
    text-align: center;
  }
  .hero .pct {
    font-size: 3.2em; font-weight: 700; color: var(--ok);
    line-height: 1; margin: 0 0 0.15em;
  }
  .hero .headline { font-size: 1.15em; margin: 0 0 0.4em; font-weight: 500; }
  .hero .sub { color: var(--muted); font-size: 0.95em; margin: 0; }

  .explainer {
    background: #fef9e7; border-left: 3px solid #f59e0b;
    padding: 0.9em 1.2em; margin: 0 0 2em; border-radius: 4px;
    font-size: 0.95em;
  }
  .explainer strong { color: var(--brand-dark); }

  h2 { margin: 2em 0 0.6em; font-size: 1.2em; color: var(--brand-dark); }
  h2 .inline-numbers {
    font-weight: 500; color: var(--muted); font-size: 0.85em;
    margin-left: 0.5em;
  }

  .summary-tiles {
    display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
    gap: 0.8em; margin: 0 0 2em;
  }
  .tile {
    background: var(--bg); border: 1px solid var(--border);
    border-radius: 6px; padding: 0.9em 1em;
  }
  .tile .label { color: var(--muted); font-size: 0.85em; margin-bottom: 0.15em; }
  .tile .value { font-size: 1.6em; font-weight: 600; line-height: 1; }
  .tile .value small { font-size: 0.55em; font-weight: 400; color: var(--muted); }
  .tile.ok   .value { color: var(--ok); }
  .tile.warn .value { color: var(--warn); }
  .tile.err  .value { color: var(--err); }

  .suites { display: flex; flex-direction: column; gap: 0.25em; margin: 0 0 1em; }
  .suite-row {
    display: grid;
    grid-template-columns: 13em 1fr 8em;
    align-items: center; gap: 0.8em;
    padding: 0.35em 0.8em;
    border-radius: 4px;
    font-size: 0.92em;
  }
  .suite-row .suite-name { font-family: ui-monospace, Menlo, Consolas, monospace;
                           font-size: 0.88em; }
  .suite-row .suite-bar {
    height: 0.7em; background: var(--border); border-radius: 3px; overflow: hidden;
  }
  .suite-row .suite-bar .fill {
    height: 100%; background: var(--ok); transition: width 0.3s;
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
            padding: 0.6em 0.9em; border: 1px solid var(--border); }
  details summary { cursor: pointer; font-weight: 500; color: var(--muted); }
  details pre { background: var(--bg); padding: 0.6em 0.8em;
                border: 1px solid var(--border); border-radius: 4px;
                font-size: 0.82em; overflow-x: auto; margin: 0.5em 0 0; }

  footer {
    max-width: 900px; margin: 2em auto 3em; padding: 1em;
    color: var(--muted); font-size: 0.85em; border-top: 1px solid var(--border);
  }
  footer code { background: var(--surface); padding: 0.1em 0.4em; border-radius: 3px; }
  footer a { color: var(--brand-dark); }
</style>
</head>
<body>

<header>
  <div class="inner">
    <h1>Factoidal — W3C conformance</h1>
    <p>How well does our formally-verified SPARQL / RDF engine follow the official standards?</p>
    <nav>
      <a href="/factoidal/">Home</a>
      <a href="/factoidal/test-results/">Test results</a>
      <a href="/factoidal/fstar-extracted/">Demos</a>
      <a href="https://github.com/danbri/factoidal">GitHub</a>
    </nav>
  </div>
</header>

<main>

<div class="hero">
  <p class="pct">${COMBINED_PCT}%</p>
  <p class="headline">${COMBINED_PASS} of ${run_total} runnable tests pass</p>
  <p class="sub">${COMBINED_FAIL} fail · ${COMBINED_SKIP} skipped (feature not yet implemented) · out of ${COMBINED_TOTAL} total</p>
</div>

<div class="explainer">
<strong>What is this?</strong>
The W3C — the standards body for the Web — publishes "conformance test suites"
for RDF (how structured data is represented) and SPARQL (how you query it).
Any implementation that claims to be compliant has to pass these tests. The
numbers on this page show, out of every W3C test, how many our engine gets
right.
<br><br>
<strong>Why it matters:</strong> RDF and SPARQL are how public knowledge graphs
like Wikidata and Schema.org are queried. Tests in the "pass" column are
features of those standards that work correctly in Factoidal. Tests in "fail"
are ones where we don't match the reference behaviour yet. "Skipped" tests are
features we haven't started on (mostly HTTP protocol / federated-query
endpoints).
<br><br>
<strong>What's different about Factoidal:</strong> the engine is extracted from
an <a href="https://www.fstar-lang.org/">F*</a> mathematical specification. The
OCaml that runs these tests was generated from a spec a proof assistant checked
— so passing a test is not just "it worked on the sample", it's "the proof
extracted to this OCaml code and that code passes the test". See the
<a href="https://github.com/danbri/factoidal">GitHub repo</a> for the source
specs.
</div>

<h2>Headline</h2>

<div class="summary-tiles">
  <div class="tile ok">
    <div class="label">Tests passing</div>
    <div class="value">${COMBINED_PASS}</div>
  </div>
  <div class="tile err">
    <div class="label">Tests failing</div>
    <div class="value">${COMBINED_FAIL}</div>
  </div>
  <div class="tile warn">
    <div class="label">Not yet implemented</div>
    <div class="value">${COMBINED_SKIP}<small> skipped</small></div>
  </div>
  <div class="tile">
    <div class="label">Pass rate</div>
    <div class="value">${COMBINED_PCT}%<small> of runnable</small></div>
  </div>
</div>

<h2>SPARQL 1.1 — querying <span class="inline-numbers">${SPARQL_PASS} pass · ${SPARQL_FAIL} fail · ${SPARQL_SKIP} skip</span></h2>
<p style="color: var(--muted); font-size: 0.93em; margin-top: 0;">
  Each row is one part of the SPARQL language specification. The bar shows how
  many of that suite's tests pass; numbers on the right are
  <span style="color:var(--ok)">pass</span>/<span style="color:var(--err)">fail</span>.
</p>
<div class="suites">
${SPARQL_ROWS_HTML}
</div>

<h2>RDF 1.1 — data formats <span class="inline-numbers">${RDF_PASS} pass · ${RDF_FAIL} fail</span></h2>
<p style="color: var(--muted); font-size: 0.93em; margin-top: 0;">
  Tests for reading and writing RDF in five serialisations (Turtle, TriG,
  N-Triples, N-Quads, RDF/XML) plus the model-theoretic semantics of RDF
  graphs.
</p>
<div class="suites">
${RDF_ROWS_HTML}
</div>

<details>
  <summary>Raw per-suite numbers (for the curious)</summary>
  <h3 style="font-size: 1em; margin: 1em 0 0.3em;">SPARQL 1.1</h3>
  <pre>${SPARQL_TOTAL} total: ${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip, ${SPARQL_UNSUP} unsupported
${SPARQL_SUITES}</pre>
  <h3 style="font-size: 1em; margin: 1em 0 0.3em;">RDF 1.1</h3>
  <pre>${RDF_TOTAL} total: ${RDF_PASS} pass, ${RDF_FAIL} fail, ${RDF_SKIP} skip, ${RDF_UNSUP} unsupported
${RDF_SUITES}</pre>
</details>

</main>

<footer>
  Generated <strong>${TIMESTAMP}</strong> from commit
  <code><a href="https://github.com/danbri/factoidal/commit/${GIT_SHA_FULL}">${GIT_SHA}</a></code>
  on branch <code>${GIT_BRANCH}</code>${GIT_SUBJECT_LINE}.
  <br>
  Auto-rebuilt by
  <a href="https://github.com/danbri/factoidal/actions/workflows/w3c-tests.yml">GitHub Actions</a>
  on every push to <code>claude/main</code> and nightly at 06:00 UTC.
  Source: <code>formal/fstar/generate-report.sh</code>.
</footer>

</body>
</html>
HTMLEOF

echo ""
echo "Report generated: $OUTPUT_DIR/index.html"
echo "  SPARQL: ${SPARQL_PASS} pass, ${SPARQL_FAIL} fail, ${SPARQL_SKIP} skip, ${SPARQL_UNSUP} unsupported"
echo "  RDF:    ${RDF_PASS} pass, ${RDF_FAIL} fail, ${RDF_SKIP} skip, ${RDF_UNSUP} unsupported"
echo "  Overall: ${COMBINED_PASS}/${run_total} runnable = ${COMBINED_PCT}%"
echo "  Commit: ${GIT_SHA} (${GIT_BRANCH})"
