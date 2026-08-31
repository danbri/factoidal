#!/usr/bin/env bash
# Reproducible process-cold/process-warm benchmark for an already activated
# SBM6 Shardborough collection. It does not claim to evict the OS page cache:
# “cold” means the first fresh query process; “warm” means subsequent fresh
# processes against the same immutable generation.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
store_root=${1:?usage: tools/blockengine-ibk3-query-benchmark.sh ACTIVATED-COLLECTION-ROOT [warm-runs]}
warm_runs=${2:-3}
join_query='PREFIX wdt: <http://www.wikidata.org/prop/direct/> SELECT ?s ?o1 ?o2 WHERE { ?s wdt:P684 ?o1 . ?s wdt:P682 ?o2 }'
count_query='PREFIX wdt: <http://www.wikidata.org/prop/direct/> SELECT (COUNT(*) AS ?c) WHERE { ?s wdt:P684 ?o }'
# This is a real one-row P684 object value in the checked-in KGX gene export.
# It exercises the OLI2→TLI1→row.o verification path rather than a generic
# predicate materialisation.  Keep the expected cardinality with the corpus
# provenance; it must be revised intentionally if the pinned source changes.
object_query='PREFIX wdt: <http://www.wikidata.org/prop/direct/> PREFIX wd: <http://www.wikidata.org/entity/> SELECT ?s WHERE { ?s wdt:P684 wd:Q7072306 }'
runner="$repo_root/tools/bench_rusage_run.py"
binary="$lean_dir/.lake/build/bin/l4block-id-v3-query"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-ibk3-query-benchmark.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

if [[ ! -f "$store_root/CURRENT" ]]; then
  echo "benchmark requires an activated collection root with CURRENT: $store_root" >&2
  exit 2
fi
if [[ ! -x "$binary" ]]; then
  echo "missing native query executable: $binary" >&2
  exit 2
fi
if ! [[ "$warm_runs" =~ ^[0-9]+$ ]] || (( warm_runs < 1 )); then
  echo "warm-runs must be a positive integer" >&2
  exit 2
fi

run_one() {
  local workload=$1
  local phase=$2
  local ordinal=$3
  local query=$4
  local expected_mode=$5
  local expected_result=$6
  local stdout="$run_dir/${workload}-${phase}-${ordinal}.stdout"
  local stderr="$run_dir/${workload}-${phase}-${ordinal}.stderr"
  local metrics
  metrics=$(python3 "$runner" "$stdout" "$stderr" "$binary" "$store_root" --query "$query")
  grep -q "$expected_mode" "$stdout"
  grep -q "$expected_result" "$stdout"
  printf '{"benchmark":"%s","phase":"%s","ordinal":%s,"process_model":"fresh-process","cache_note":"OS page cache is not explicitly evicted","metrics":%s}\n' \
    "$workload" "$phase" "$ordinal" "$metrics"
}

run_workload() {
  local workload=$1
  local query=$2
  local expected_mode=$3
  local expected_result=$4
  run_one "$workload" cold 1 "$query" "$expected_mode" "$expected_result"
  for ((ordinal = 1; ordinal <= warm_runs; ordinal += 1)); do
    run_one "$workload" warm "$ordinal" "$query" "$expected_mode" "$expected_result"
  done
}

run_workload ibk3-sri2-gene-p682-p684 "$join_query" 'open-mode=ibk3-sri2-tli1-subject-join(2)' 'rows=14'
run_workload ibk3-gene-p684-count "$count_query" 'open-mode=ibk3-paged-merkle-count(1)' '"c", L4Factoidal.RDF.Term.literal ("759263"'
run_workload ibk3-oli2-gene-p684-q7072306 "$object_query" 'open-mode=ibk3-sri2-tli1-oli2-object-scan(1)' 'rows=1'
