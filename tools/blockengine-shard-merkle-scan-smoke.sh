#!/usr/bin/env bash
# Exercise an SBM1-root-verified, cross-chunk positioned read and then feed
# verified IBK2 ranges into a predicate-local physical scan.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-merkle-scan.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/docs/fstar-extracted/lifesci/sequence_variant.ttl" "$run_dir/store" >/dev/null

pread=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-pread" "$run_dir/store" \
  http://www.wikidata.org/prop/direct/P31 65000 1000)
p31=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-scan" "$run_dir/store" \
  http://www.wikidata.org/prop/direct/P31)
p1057=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-scan" "$run_dir/store" \
  http://www.wikidata.org/prop/direct/P1057)
query=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'PREFIX wdt: <http://www.wikidata.org/prop/direct/> PREFIX wd: <http://www.wikidata.org/entity/> SELECT ?variant ?chrom WHERE { ?variant wdt:P31 wd:Q15304597 . ?variant wdt:P1057 ?chrom . } LIMIT 5')

printf '%s\n' "$pread"
printf '%s\n' "$p31"
printf '%s\n' "$p1057"
printf '%s\n' "$query"
grep -q 'verified-bytes=1000 offset=65000 chunks=0-1' <<<"$pread"
grep -q 'rows=1800 predicate=http://www.wikidata.org/prop/direct/P31' <<<"$p31"
grep -q 'rows=1357 predicate=http://www.wikidata.org/prop/direct/P1057' <<<"$p1057"
grep -q 'open-mode=predicate-selective-merkle(2)' <<<"$query"
grep -q 'rows=5' <<<"$query"
echo 'blockengine-shard-merkle-scan-smoke=pass'
