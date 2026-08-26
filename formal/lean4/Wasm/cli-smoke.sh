#!/usr/bin/env bash
#
# cli-smoke.sh — exercise every VERB of `l4factoidal` (Wasm/Cli.lean),
# the real command-line interface built on the dispatch ABI
# (Wasm/Dispatch.lean). Modelled on native-smoke.sh, which exercises
# the ABI itself through `l4wasm-cli`; this script exercises the
# person/script-facing layer on top of it — flags, stdin, exit codes,
# error text — so an ABI bug and a CLI-argument-parsing bug can never
# be confused for one another.
#
#   formal/lean4/Wasm/cli-smoke.sh
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$LEAN_DIR"
command -v lake >/dev/null || { echo "lake not on PATH (export PATH=\$HOME/.elan/bin:\$PATH)"; exit 1; }

echo "=== build l4factoidal"
lake build l4factoidal >/dev/null
CLI="$LEAN_DIR/.lake/build/bin/l4factoidal"
[ -x "$CLI" ] || { echo "FAIL: $CLI not built"; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

PASS=0
FAIL=0

pass() { echo "ok   $1"; PASS=$((PASS + 1)); }
fail() {
  local label="$1"; shift
  echo "FAIL $label"
  for l in "$@"; do printf '     %s\n' "$l"; done
  FAIL=$((FAIL + 1))
}

# assert_exit LABEL WANT_EXIT -- CMD...
# Runs CMD, checks only its exit code. Leaves $OUT / $ERR / $RC set for
# a caller that wants to check content too.
run_cmd() {
  OUT="$("$@" 2>"$TMP/stderr")" && RC=0 || RC=$?
  ERR="$(cat "$TMP/stderr")"
}

assert_exit() {
  local label="$1" want="$2"; shift 2
  run_cmd "$@"
  if [ "$RC" -eq "$want" ]; then
    pass "$label"
  else
    fail "$label" "exit=$RC want=$want" "stdout=$OUT" "stderr=$ERR"
  fi
}

# assert_text LABEL WANT_EXIT out|err NEEDLE -- CMD...
assert_text() {
  local label="$1" want="$2" stream="$3" needle="$4"; shift 4
  run_cmd "$@"
  local hay
  [ "$stream" = "out" ] && hay="$OUT" || hay="$ERR"
  if [ "$RC" -eq "$want" ] && printf '%s' "$hay" | grep -qF -- "$needle"; then
    pass "$label"
  else
    fail "$label" "exit=$RC want=$want" "stdout=$OUT" "stderr=$ERR"
  fi
}

# assert_json LABEL WANT_EXIT PY_EXPR -- CMD...
# PY_EXPR sees the parsed stdout JSON as `r`.
assert_json() {
  local label="$1" want="$2" expr="$3"; shift 3
  run_cmd "$@"
  if [ "$RC" -ne "$want" ]; then
    fail "$label" "exit=$RC want=$want" "stdout=$OUT" "stderr=$ERR"
    return
  fi
  if printf '%s' "$OUT" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
" 2>/dev/null; then
    pass "$label"
  else
    fail "$label" "stdout=$OUT"
  fi
}

echo "=== cli smoke ($TMP)"

# --- version / help / ops --------------------------------------------
assert_text "version"          0 out "l4factoidal-wasm"     "$CLI" version
assert_text "version abi line" 0 out "dispatch ABI:"        "$CLI" version
assert_text "help"             0 out "Usage: l4factoidal"   "$CLI" help
assert_text "no verb -> usage error" 2 err "missing verb"   "$CLI"
assert_text "unknown verb -> usage error" 2 err "unknown verb" "$CLI" definitelyNotAVerb
assert_json "ops reflection"   0 \
  'r["ok"] is True and set(["parseToDatasetJson","queryDataset","owlClosure","clParse","datasetOpen"]) <= set(r["ops"])' \
  "$CLI" ops

# --- parse -------------------------------------------------------------
echo '@prefix ex: <http://example.org/> . ex:a ex:p ex:b, ex:c .' > "$TMP/data.ttl"

assert_text "parse file, default -> count" 0 out "2" \
  "$CLI" parse "$TMP/data.ttl" --format turtle
assert_text "parse --out nquads" 0 out "<http://example.org/a> <http://example.org/p> <http://example.org/b> ." \
  "$CLI" parse "$TMP/data.ttl" --format turtle --out nquads
assert_text "parse --out turtle" 0 out "@prefix" \
  "$CLI" parse "$TMP/data.ttl" --format turtle --out turtle
assert_text "parse bad turtle -> error" 1 err "offset" \
  bash -c "printf 'not turtle @@@' | '$CLI' parse --format turtle"
assert_text "parse unknown --out -> usage error" 2 err "unknown --out" \
  "$CLI" parse "$TMP/data.ttl" --out bogus
assert_text "parse missing --format value -> usage error" 2 err "missing value" \
  "$CLI" parse --format
assert_text "parse missing file -> error" 1 err "no such file" \
  "$CLI" parse /no/such/file.ttl

# stdin: no positional file argument at all.
STDIN_COUNT="$(printf '@prefix ex: <http://e/> . ex:a ex:p ex:b .' | "$CLI" parse --format turtle)"
if [ "$STDIN_COUNT" = "1" ]; then pass "parse stdin (no file arg)"; else
  fail "parse stdin (no file arg)" "got '$STDIN_COUNT'"
fi

# --- query ---------------------------------------------------------------
printf '<http://e/a> <http://e/p> <http://e/b> .\n' > "$TMP/d.nt"

assert_json "query select" 0 \
  'r["head"]["vars"] == ["s"] and r["results"]["bindings"][0]["s"]["value"] == "http://e/a"' \
  "$CLI" query "$TMP/d.nt" --format ntriples --query-string 'SELECT ?s WHERE { ?s <http://e/p> ?o }'
assert_text "query select --table" 0 out "http://e/a" \
  "$CLI" query "$TMP/d.nt" --format ntriples --table \
    --query-string 'SELECT ?s WHERE { ?s <http://e/p> ?o }'
assert_text "query ask true -> exit 0" 0 out "true" \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'ASK { <http://e/a> <http://e/p> <http://e/b> }'
assert_text "query ask false -> exit 1" 1 out "false" \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'ASK { <http://e/a> <http://e/p> <http://e/zzz> }'
assert_text "query construct" 0 out "<http://e/q>" \
  "$CLI" query "$TMP/d.nt" --format ntriples \
    --query-string 'CONSTRUCT { ?s <http://e/q> ?o } WHERE { ?s <http://e/p> ?o }'
assert_text "query DESCRIBE -> error" 1 err "DESCRIBE is not supported" \
  "$CLI" query "$TMP/d.nt" --format ntriples --query-string 'DESCRIBE <http://e/a>'
assert_text "query missing --query/--query-string -> usage error" 2 err "need --query" \
  "$CLI" query "$TMP/d.nt" --format ntriples
assert_text "query both --query and --query-string -> usage error" 2 err "pass only one" \
  "$CLI" query "$TMP/d.nt" --format ntriples --query-string 'ASK{}' --query "$TMP/d.nt"

# --- update ----------------------------------------------------------
assert_text "update" 0 out "<http://e/x> <http://e/p> <http://e/y> ." \
  "$CLI" update "$TMP/d.nt" --format ntriples \
    --update-string 'INSERT DATA { <http://e/x> <http://e/p> <http://e/y> }'
assert_text "update missing --update/--update-string -> usage error" 2 err "need --update" \
  "$CLI" update "$TMP/d.nt" --format ntriples

# --- canonicalize ------------------------------------------------------
assert_text "canonicalize" 0 out "_:c14n0" \
  bash -c "printf '_:b0 <http://e/p> \"v\" .' | '$CLI' canonicalize --format nquads"

# --- closure -----------------------------------------------------------
SUBCLASS='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> .
<http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .
'
printf '%s' "$SUBCLASS" > "$TMP/subclass.nq"

assert_text "closure --regime rdfs" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime rdfs
assert_text "closure --regime owl-rl" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime owl-rl
assert_text "closure --regime rho-df" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime rho-df
assert_text "closure --regime rdfs-plus" 0 out "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> ." \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime rdfs-plus
assert_text "closure missing --regime -> usage error" 2 err "need --regime" \
  "$CLI" closure "$TMP/subclass.nq" --format nquads
assert_text "closure unknown --regime -> usage error" 2 err "unknown --regime" \
  "$CLI" closure "$TMP/subclass.nq" --format nquads --regime bogus

# --- owl-consistent / owl-entails --------------------------------------
assert_text "owl-consistent true -> exit 0" 0 out "true" \
  "$CLI" owl-consistent "$TMP/subclass.nq" --format nquads

NOTHING='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Nothing> .
'
printf '%s' "$NOTHING" > "$TMP/nothing.nq"
assert_text "owl-consistent false -> exit 1, stdout false" 1 out "false" \
  "$CLI" owl-consistent "$TMP/nothing.nq" --format nquads
assert_text "owl-consistent false -> reason on stderr" 1 err "contradiction" \
  "$CLI" owl-consistent "$TMP/nothing.nq" --format nquads

CYCLIC='<http://e/i> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/A> .
<http://e/A> <http://www.w3.org/2000/01/rdf-schema#subClassOf> _:r .
_:r <http://www.w3.org/2002/07/owl#onProperty> <http://e/p> .
_:r <http://www.w3.org/2002/07/owl#someValuesFrom> <http://e/A> .
'
printf '%s' "$CYCLIC" > "$TMP/cyclic.nq"
assert_text "owl-consistent budget-out -> unknown, exit 1" 1 out "unknown" \
  "$CLI" owl-consistent "$TMP/cyclic.nq" --format nquads --fuel 1

CONCL='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> .
'
UNRELATED='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Zebra> .
'
printf '%s' "$CONCL" > "$TMP/concl.nq"
printf '%s' "$UNRELATED" > "$TMP/unrelated.nq"
assert_text "owl-entails true (closure) -> exit 0" 0 out "true" \
  "$CLI" owl-entails "$TMP/subclass.nq" "$TMP/concl.nq" --format nquads
assert_text "owl-entails false (refutation) -> exit 1" 1 out "false" \
  "$CLI" owl-entails "$TMP/subclass.nq" "$TMP/unrelated.nq" --format nquads
assert_text "owl-entails missing conclusion file -> usage error" 2 err "need PREMISE_FILE" \
  "$CLI" owl-entails "$TMP/subclass.nq"

# --- cl ------------------------------------------------------------------
IKL='(ist c (that (Dead OBL)))'
printf '%s' "$IKL" > "$TMP/prop.clif"

assert_json "cl parse" 0 \
  'r["ok"] is True and r["sentences"] == 1 and r["pureCL"] is False' \
  "$CLI" cl parse "$TMP/prop.clif"
assert_text "cl parse unclosed paren -> error" 1 err "unclosed" \
  bash -c "printf '(P a' | '$CLI' cl parse"

assert_text "cl missing subcommand -> usage error" 2 err "need a subcommand" \
  "$CLI" cl
assert_text "cl unknown subcommand -> usage error" 2 err "unknown subcommand" \
  "$CLI" cl bogus

echo "=== cli-smoke: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
