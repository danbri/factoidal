#!/usr/bin/env bash
# Reproducible medium-corpus native Shardborough benchmark. This intentionally
# measures the real path: Turtle -> SBM2/IBK2/Merkle files -> parsed SPARQL.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
ttl_path=${1:-"$repo_root/examples/wikidata/subsets/lifesci-kgx/data/gene.ttl"}
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-gene-benchmark.XXXXXX")
store_dir="$run_dir/store"
trap 'rm -rf "$run_dir"' EXIT

if [[ ! -f "$ttl_path" ]]; then
  echo "missing Turtle corpus: $ttl_path" >&2
  exit 2
fi

SECONDS=0
started=$SECONDS
"$lean_dir/.lake/build/bin/l4block-shard-pack" "$ttl_path" "$store_dir"
pack_seconds=$((SECONDS - started))
block_count=$(awk 'NR > 1 { n += 1 } END { print n + 0 }' "$store_dir/manifest.tsv")
row_count=$(awk 'NR > 1 { n += $4 } END { print n + 0 }' "$store_dir/manifest.tsv")

query='SELECT ?gene ?chrom WHERE { ?gene <http://www.wikidata.org/prop/direct/P1057> ?chrom } LIMIT 5'
query_output=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$store_dir" --query "$query")
printf '%s\n' "$query_output"
grep -q 'open-mode=predicate-selective-merkle-limit-prefix(1)' <<<"$query_output"
grep -q 'rows=5' <<<"$query_output"

# Measure the next-format opportunity against the exact P1057 blocks emitted
# by this run. This does not alter the published IBK2 collection.
p1057_artifacts=$(awk -F '\t' 'NR > 1 && $2 == "http://www.wikidata.org/prop/direct/P1057" { print $3 }' "$store_dir/manifest.tsv")
if [[ -z "$p1057_artifacts" ]]; then
  echo "missing P1057 artifacts in generated store" >&2
  exit 1
fi
while IFS= read -r artifact; do
  probe_output=$("$lean_dir/.lake/build/bin/l4block-paged-dictionary-probe" "$store_dir/$artifact" 5)
  printf '%s\n' "$probe_output"
  grep -q 'rows-sampled=5' <<<"$probe_output"
  grep -q 'pages=' <<<"$probe_output"
done <<<"$p1057_artifacts"

printf 'blockengine-gene-shard-benchmark=pass triples=%s blocks=%s pack-seconds=%s\n' \
  "$row_count" "$block_count" "$pack_seconds"
