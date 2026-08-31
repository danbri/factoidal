#!/usr/bin/env bash
# Reproducible fresh-process SBM6 object-driven join benchmark for the
# checked-in anatomical-structure KGX Turtle source after it has been packed
# and activated.  It deliberately does not claim to evict the OS page cache.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
store_root=${1:?usage: tools/blockengine-sbm6-anatomy-benchmark.sh ACTIVATED-SBM6-ROOT [runs]}
runs=${2:-3}
query='SELECT ?x ?type WHERE { ?x <http://www.wikidata.org/prop/direct/P361> <http://www.wikidata.org/entity/Q729> . ?x <http://www.wikidata.org/prop/direct/P31> ?type . }'
runner="$repo_root/tools/bench_rusage_run.py"
binary="$lean_dir/.lake/build/bin/l4block-id-v3-query"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-sbm6-anatomy-benchmark.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

if [[ ! -f "$store_root/CURRENT" ]]; then
  echo "benchmark requires an activated collection root with CURRENT: $store_root" >&2
  exit 2
fi
if [[ ! -x "$binary" ]]; then
  echo "missing native query executable: $binary" >&2
  exit 2
fi
if ! [[ "$runs" =~ ^[0-9]+$ ]] || (( runs < 1 )); then
  echo "runs must be a positive integer" >&2
  exit 2
fi

for ((ordinal = 1; ordinal <= runs; ordinal += 1)); do
  stdout="$run_dir/run-$ordinal.stdout"
  stderr="$run_dir/run-$ordinal.stderr"
  metrics=$(python3 "$runner" "$stdout" "$stderr" "$binary" "$store_root" --query "$query")
  grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-subject-join(2) delta=base' "$stdout"
  grep -q 'rows=4' "$stdout"
  printf '{"benchmark":"sbm6-anatomy-p361-q729-to-p31","ordinal":%s,"process_model":"fresh-process","cache_note":"OS page cache is not explicitly evicted","metrics":%s}\n' \
    "$ordinal" "$metrics"
done
