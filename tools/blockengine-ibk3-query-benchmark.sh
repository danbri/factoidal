#!/usr/bin/env bash
# Reproducible process-cold/process-warm benchmark for an already activated
# SBM5 Shardborough collection. It does not claim to evict the OS page cache:
# “cold” means the first fresh query process; “warm” means subsequent fresh
# processes against the same immutable generation.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
store_root=${1:?usage: tools/blockengine-ibk3-query-benchmark.sh ACTIVATED-COLLECTION-ROOT [warm-runs]}
warm_runs=${2:-3}
query='PREFIX wdt: <http://www.wikidata.org/prop/direct/> SELECT ?s ?o1 ?o2 WHERE { ?s wdt:P684 ?o1 . ?s wdt:P682 ?o2 }'
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
  local phase=$1
  local ordinal=$2
  local stdout="$run_dir/${phase}-${ordinal}.stdout"
  local stderr="$run_dir/${phase}-${ordinal}.stderr"
  local metrics
  metrics=$(python3 "$runner" "$stdout" "$stderr" "$binary" "$store_root" --query "$query")
  grep -q 'open-mode=ibk3-sri2-tli1-subject-join(2)' "$stdout"
  grep -q 'rows=14' "$stdout"
  printf '{"benchmark":"ibk3-sri2-gene-p682-p684","phase":"%s","ordinal":%s,"process_model":"fresh-process","cache_note":"OS page cache is not explicitly evicted","metrics":%s}\n' \
    "$phase" "$ordinal" "$metrics"
}

run_one cold 1
for ((ordinal = 1; ordinal <= warm_runs; ordinal += 1)); do
  run_one warm "$ordinal"
done
