#!/usr/bin/env bash
# End to end: a JavaScript host reads Shardborough files, the Lean WASM module
# decides everything else, and its answers must equal the native tools' answers
# for the same generation and the same query.
#
# What this gates that nothing else does: the WASM module has no file system,
# so the store operations of `Wasm/Ops/Store.lean` are the only route from a
# packed generation to a SPARQL answer in a browser. `Wasm/native-smoke.sh`
# exercises the same operations through the native CLI, which cannot see a
# wasm build fault; the hub tests exercise the wasm module, but not against a
# real generation. This runs the committed wasm against generations the Lean
# packer just wrote, and compares row for row with `l4block-id-v3-query` and
# `l4block-quad-query`.
#
# The host (tools/wasm-store-query-smoke.mjs) reads files by name and carries
# bytes. It parses no manifest, verifies no digest and interprets no block.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
bin="$lean_dir/.lake/build/bin"
export PATH="$HOME/.elan/bin:$PATH"

command -v node >/dev/null || { echo 'node is not on PATH'; exit 1; }
command -v lake >/dev/null || { echo 'lake is not on PATH (export PATH=$HOME/.elan/bin:$PATH)'; exit 1; }

run_dir=$(mktemp -d /private/tmp/factoidal-wasm-store.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT

echo '=== build the native packer, activator and query tools'
( cd "$lean_dir" && lake build l4block-shard-pack l4block-shard-activate \
    l4block-id-v3-query l4block-quad-query >/dev/null )

# --- one IBK3 generation and one IBK4 generation, both activated -----------
ibk3_source="$repo_root/examples/wikidata/subsets/lifesci-kgx/data/sequence_variant.ttl"
ibk4_source="$repo_root/tests/local/data/quad_sample.trig"

"$bin/l4block-shard-pack" "$ibk3_source" "$run_dir/ibk3" ibk3 | tee "$run_dir/pack-ibk3.txt"
mkdir -p "$run_dir/store3"
cp -R "$run_dir/ibk3" "$run_dir/store3/gen-1"
"$bin/l4block-shard-activate" "$run_dir/store3" gen-1 >/dev/null

"$bin/l4block-shard-pack" "$ibk4_source" "$run_dir/ibk4" ibk4 | tee "$run_dir/pack-ibk4.txt"
mkdir -p "$run_dir/store4"
cp -R "$run_dir/ibk4" "$run_dir/store4/gen-1"
"$bin/l4block-shard-activate" "$run_dir/store4" gen-1 >/dev/null

gen3="$run_dir/store3/gen-1"
gen4="$run_dir/store4/gen-1"

# The first predicate of the IBK3 manifest, so the bound-predicate query names
# a predicate the data really has.
predicate=$(awk -F'\t' 'NR>1 && $1=="0" { print $2; exit }' "$gen3/manifest.tsv")
other=$(awk -F'\t' 'NR>1 && $1=="1" { print $2; exit }' "$gen3/manifest.tsv")
[ -n "$predicate" ] || { echo 'could not read predicate 0 from manifest.tsv'; exit 1; }
[ -n "$other" ] || { echo 'could not read predicate 1 from manifest.tsv'; exit 1; }
echo "=== IBK3 predicates 0 and 1: $predicate | $other"

# wasm_rows <generation-dir> <query> — run the host and print its JSON line.
wasm_json() {
  node "$repo_root/tools/wasm-store-query-smoke.mjs" "$1" "$2"
}

field() {
  python3 -c 'import json,sys; print(json.loads(sys.argv[1])[sys.argv[2]])' "$1" "$2"
}

# native_rows <tool> <collection-root> <query>
native_rows() {
  local tool="$1" root="$2" query="$3" out
  out=$("$bin/$tool" "$root" --query "$query")
  printf '%s\n' "$out" >&2
  printf '%s\n' "$out" | awk -F'rows=' '/ rows=/ { split($2, f, " "); print f[1]; exit }'
}

compare() {
  local label="$1" tool="$2" root="$3" gen="$4" query="$5" expect_mode="$6"
  local json wasm native mode
  json=$(wasm_json "$gen" "$query")
  echo "    wasm: $json"
  wasm=$(field "$json" rows)
  mode=$(field "$json" mode)
  native=$(native_rows "$tool" "$root" "$query")
  if [ "$wasm" != "$native" ]; then
    echo "FAIL $label: wasm answered $wasm rows, $tool answered $native"
    exit 1
  fi
  if [ -n "$expect_mode" ] && [ "$mode" != "$expect_mode" ]; then
    echo "FAIL $label: plan mode is '$mode', expected '$expect_mode'"
    exit 1
  fi
  echo "ok   $label ($wasm rows, mode $mode)"
}

echo '=== IBK3 generation: the wasm store ops against l4block-id-v3-query'
compare 'IBK3 bound predicate' l4block-id-v3-query "$run_dir/store3" "$gen3" \
  "SELECT ?s ?o WHERE { ?s <$predicate> ?o }" 'ibk3-paged-merkle(1)'
compare 'IBK3 unbound predicate opens the manifest' l4block-id-v3-query "$run_dir/store3" "$gen3" \
  'SELECT ?s ?p ?o WHERE { ?s ?p ?o } LIMIT 25' ''
# Only the reference semantics decide this one, and it must be decided against
# the same generation the backend answers from (anti-pattern 34).
compare 'IBK3 FILTER NOT EXISTS over two predicates' l4block-id-v3-query "$run_dir/store3" "$gen3" \
  "SELECT ?s WHERE { ?s <$predicate> ?o FILTER NOT EXISTS { ?s <$other> ?x } }" ''

echo '=== IBK4 generation: the wasm store ops against l4block-quad-query'
compare 'IBK4 GRAPH clause' l4block-quad-query "$run_dir/store4" "$gen4" \
  'SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }' 'ibk4-full-manifest(1)'
compare 'IBK4 GRAPH variable' l4block-quad-query "$run_dir/store4" "$gen4" \
  'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }' 'ibk4-full-manifest(4)'
compare 'IBK4 default graph' l4block-quad-query "$run_dir/store4" "$gen4" \
  'SELECT * WHERE { ?s ?p ?o }' ''
compare 'IBK4 FILTER NOT EXISTS' l4block-quad-query "$run_dir/store4" "$gen4" \
  'SELECT * WHERE { ?s ?p ?o FILTER NOT EXISTS { ?s <http://example.org/knows> ?x } }' ''

echo '=== a block whose bytes do not match the manifest digest is refused'
refusal=$(node "$repo_root/tools/wasm-store-query-smoke.mjs" "$gen3" \
  "SELECT ?s ?o WHERE { ?s <$predicate> ?o }" --tamper)
echo "    $refusal"
printf '%s' "$refusal" | grep -q 'SHA-256' || {
  echo 'FAIL: the refusal did not name the SHA-256 commitment'; exit 1; }
echo 'ok   digest mismatch refused'

echo '=== a store handle answers the same ROWS as the stateless path'
# Not the same row count: the same bindings (anti-pattern 34). The handle is
# opened on every artifact the manifest declares, so it retains more than the
# plan selects and the comparison covers the case that could disagree.
handle_check() {
  local label="$1" gen="$2" query="$3" out
  out=$(node "$repo_root/tools/wasm-store-query-smoke.mjs" "$gen" "$query" --handle)
  echo "    $out"
  printf '%s' "$out" | grep -q '"rowsIdentical":true' || {
    echo "FAIL $label: the handle and the stateless path differ"; exit 1; }
  printf '%s' "$out" | grep -q '"modesAgree":true' || {
    echo "FAIL $label: the plan mode differs between the two paths"; exit 1; }
  echo "ok   $label"
}
handle_check 'IBK3 handle bound predicate' "$gen3" \
  "SELECT ?s ?o WHERE { ?s <$predicate> ?o } ORDER BY ?s ?o"
handle_check 'IBK3 handle FILTER NOT EXISTS' "$gen3" \
  "SELECT ?s WHERE { ?s <$predicate> ?o FILTER NOT EXISTS { ?s <$other> ?x } } ORDER BY ?s"
handle_check 'IBK4 handle GRAPH clause' "$gen4" \
  'SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } } ORDER BY ?s ?p ?o'

echo 'wasm-store-query-smoke=pass'
