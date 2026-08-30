#!/usr/bin/env bash
# Prove that parsed predicate-bound SPARQL opens fewer persisted Shardborough
# artifacts than a variable-predicate query, while retaining the same normal
# l4block-shard-query execution route.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-selective.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/docs/fstar-extracted/samples/music.ttl" "$run_dir/store" >/dev/null

selective=$("$lean_dir/.lake/build/bin/l4block-shard-query" "$run_dir/store" --query \
  'PREFIX m: <http://example.org/music/> PREFIX dc: <http://purl.org/dc/terms/> SELECT ?album ?title WHERE { ?album m:by ?band . ?album dc:title ?title . } ORDER BY ?album')
full=$("$lean_dir/.lake/build/bin/l4block-shard-query" "$run_dir/store" --query \
  'PREFIX m: <http://example.org/music/> SELECT ?album ?band WHERE { ?album ?predicate ?band . } LIMIT 2')

printf '%s\n' "$selective"
printf '%s\n' "$full"
grep -q 'shards=2 open-mode=predicate-selective(2)' <<<"$selective"
grep -q 'rows=8' <<<"$selective"
grep -q 'shards=7 open-mode=full-manifest' <<<"$full"
grep -q 'rows=2' <<<"$full"
echo 'blockengine-shard-selective-smoke=pass'
