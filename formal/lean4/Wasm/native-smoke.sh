#!/usr/bin/env bash
#
# native-smoke.sh — exercise EVERY op of the dispatch ABI
# (Wasm/Dispatch.lean) once through the native CLI, so an ABI bug and a
# wasm-toolchain bug can never be confused for one another.
#
#   formal/lean4/Wasm/native-smoke.sh
#
# Builds l4wasm-cli, then drives `l4wasm-cli call <op> <argsJsonFile>`
# with tiny inline fixtures and asserts the envelope keys the F* npm
# entry (bin/npm-entry/entry_jsoo.ml) pins. Includes one error path per
# family: bad Turtle (parse), DESCRIBE (query), unknown op (dispatch).
# Exits non-zero on any mismatch.
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$LEAN_DIR"
command -v lake >/dev/null || { echo "lake not on PATH (export PATH=\$HOME/.elan/bin:\$PATH)"; exit 1; }

echo "=== build l4wasm-cli"
lake build l4wasm-cli >/dev/null
CLI="$LEAN_DIR/.lake/build/bin/l4wasm-cli"
[ -x "$CLI" ] || { echo "FAIL: $CLI not built"; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

PASS=0
FAIL=0

# args <file> <arg>... — write a JSON array-of-strings args file.
args() {
  local out="$1"; shift
  python3 - "$out" "$@" <<'EOF'
import json, sys
with open(sys.argv[1], "w") as f:
    json.dump(sys.argv[2:], f)
EOF
}

# check <label> <op> <argsfile> <python-assert-expr>
# The expression sees the parsed envelope as `r`.
check() {
  local label="$1" op="$2" argsfile="$3" expr="$4"
  local out
  out="$("$CLI" call "$op" "$argsfile")"
  if printf '%s' "$out" | python3 -c "
import json, sys
r = json.load(sys.stdin)
assert ($expr), r
"; then
    echo "ok   $label"
    PASS=$((PASS + 1))
  else
    echo "FAIL $label"
    printf '     output: %s\n' "$out"
    FAIL=$((FAIL + 1))
  fi
}

echo "=== dispatch smoke ($TMP)"

# --- Parse family -----------------------------------------------------
TTL='@prefix ex: <http://example.org/> . ex:alice ex:knows ex:bob .'
args "$TMP/parse.json" "$TTL" "turtle" ""
check "parseToDatasetJson turtle" parseToDatasetJson "$TMP/parse.json" \
  'r["ok"] is True and r["count"] == 1 and "example.org/alice" in r["nquads"]'

args "$TMP/parse-nt.json" '<http://e/a> <http://e/p> <http://e/b> .' "ntriples" ""
check "parseToDatasetJson ntriples" parseToDatasetJson "$TMP/parse-nt.json" \
  'r["ok"] is True and r["count"] == 1'

args "$TMP/parse-bad.json" 'this is not turtle @@@' "turtle" ""
check "parseToDatasetJson bad turtle -> error" parseToDatasetJson "$TMP/parse-bad.json" \
  'r["ok"] is False and isinstance(r["error"], str) and len(r["error"]) > 0'

args "$TMP/parse-jsonld.json" '{}' "jsonld" ""
check "parseToDatasetJson jsonld -> named gap" parseToDatasetJson "$TMP/parse-jsonld.json" \
  'r["ok"] is False and "JSON-LD" in r["error"]'

NQ='<http://e/a> <http://e/p> <http://e/b> .
<http://e/a> <http://e/p> <http://e/c> <http://e/g> .
'
args "$TMP/ser-nq.json" "$NQ"
check "serializeNQuads" serializeNQuads "$TMP/ser-nq.json" \
  'r["ok"] is True and "<http://e/g>" in r["nquads"] and r["nquads"].count(" .") == 2'

args "$TMP/ser-ttl.json" "$NQ"
check "serializeTurtle" serializeTurtle "$TMP/ser-ttl.json" \
  'r["ok"] is True and "@prefix" in r["turtle"] and "<http://e/>" in r["turtle"]'

# --- Query family -----------------------------------------------------
DATA='<http://e/a> <http://e/p> <http://e/b> .
'
args "$TMP/q-select.json" "$DATA" 'SELECT ?s WHERE { ?s <http://e/p> ?o }'
check "queryDataset select" queryDataset "$TMP/q-select.json" \
  'r["ok"] is True and r["kind"] == "select" and isinstance(r["srj"], dict)
   and r["srj"]["head"]["vars"] == ["s"]
   and r["srj"]["results"]["bindings"][0]["s"]["value"] == "http://e/a"'

args "$TMP/q-ask.json" "$DATA" 'ASK { <http://e/a> <http://e/p> <http://e/b> }'
check "queryDataset ask" queryDataset "$TMP/q-ask.json" \
  'r["ok"] is True and r["kind"] == "ask" and r["boolean"] is True'

args "$TMP/q-construct.json" "$DATA" \
  'CONSTRUCT { ?s <http://e/q> ?o } WHERE { ?s <http://e/p> ?o }'
check "queryDataset construct" queryDataset "$TMP/q-construct.json" \
  'r["ok"] is True and r["kind"] == "construct" and "<http://e/q>" in r["nquads"]'

args "$TMP/q-describe.json" "$DATA" 'DESCRIBE <http://e/a>'
check "queryDataset DESCRIBE -> error" queryDataset "$TMP/q-describe.json" \
  'r["ok"] is False and r["error"] == "DESCRIBE is not supported by the npm entry yet"'

args "$TMP/update.json" "$DATA" \
  'INSERT DATA { <http://e/x> <http://e/p> <http://e/y> }'
check "updateDataset" updateDataset "$TMP/update.json" \
  'r["ok"] is True and "<http://e/x>" in r["nquads"] and "<http://e/a>" in r["nquads"]'

# --- Canon family -----------------------------------------------------
args "$TMP/canon.json" '_:b0 <http://e/p> "v" .
'
check "canonicalizeToNQuads" canonicalizeToNQuads "$TMP/canon.json" \
  'r["ok"] is True and "_:c14n0" in r["nquads"]'

# --- Reason family ----------------------------------------------------
SUBCLASS='<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C> .
<http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .
'
args "$TMP/owl-rdfs.json" "$SUBCLASS" "RDFS"
check "owlClosure RDFS" owlClosure "$TMP/owl-rdfs.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["nquads"]'

args "$TMP/owl-rl.json" "$SUBCLASS" "OWL-RL"
check "owlClosure OWL-RL" owlClosure "$TMP/owl-rl.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["nquads"]'

args "$TMP/owl-badmode.json" "$SUBCLASS" "nonsense"
check "owlClosure unknown mode -> error" owlClosure "$TMP/owl-badmode.json" \
  'r["ok"] is False and "unknown mode" in r["error"]'

args "$TMP/rhodf.json" "$SUBCLASS"
check "rhoDfClosure" rhoDfClosure "$TMP/rhodf.json" \
  'r["ok"] is True and "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/D> ." in r["ntriples"]
   and isinstance(r["rounds"], int) and r["rounds"] >= 1'

args "$TMP/frag-yes.json" "$SUBCLASS"
check "rhoDfFragmentCheck true" rhoDfFragmentCheck "$TMP/frag-yes.json" \
  'r["ok"] is True and r["fragment"] is True'

args "$TMP/frag-no.json" '<http://e/a> <http://e/p> "a literal" .
'
check "rhoDfFragmentCheck false (literal object)" rhoDfFragmentCheck "$TMP/frag-no.json" \
  'r["ok"] is True and r["fragment"] is False'

SAMEAS='<http://e/a> <http://www.w3.org/2002/07/owl#sameAs> <http://e/b> .
<http://e/a> <http://e/p> <http://e/v> .
'
args "$TMP/rdfsplus.json" "$SAMEAS"
check "rdfsPlusClosure" rdfsPlusClosure "$TMP/rdfsplus.json" \
  'r["ok"] is True and "<http://e/b> <http://e/p> <http://e/v> ." in r["ntriples"]
   and isinstance(r["rounds"], int) and r["rounds"] >= 1'

# --- Dispatch reflection + unknown op ---------------------------------
args "$TMP/empty.json"
check "ops reflection" ops "$TMP/empty.json" \
  'r["ok"] is True and isinstance(r["abiVersion"], str)
   and set(["parseToDatasetJson","queryDataset","updateDataset",
            "serializeNQuads","serializeTurtle","canonicalizeToNQuads",
            "owlClosure","rhoDfClosure","rhoDfFragmentCheck",
            "rdfsPlusClosure","ops"]) <= set(r["ops"])'

check "unknown op -> error" definitelyNotAnOp "$TMP/empty.json" \
  'r["ok"] is False and "unknown op" in r["error"]'

echo "=== native-smoke: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
