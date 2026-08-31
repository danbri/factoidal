#!/usr/bin/env bash
# Prove that parsed predicate-bound SPARQL opens fewer persisted Shardborough
# artifacts than a single-predicate query, through the current proof-carrying
# SBM2/Merkle execution route.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-selective.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/docs/fstar-extracted/samples/music.ttl" "$run_dir/store" >/dev/null

selective=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'PREFIX m: <http://example.org/music/> PREFIX dc: <http://purl.org/dc/terms/> SELECT ?album ?title WHERE { ?album m:by ?band . ?album dc:title ?title . } ORDER BY ?album')
single=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'PREFIX m: <http://example.org/music/> SELECT ?album ?band WHERE { ?album m:by ?band . } LIMIT 2')

printf '%s\n' "$selective"
printf '%s\n' "$single"
grep -q 'shards=2 open-mode=predicate-selective-merkle(2)' <<<"$selective"
grep -q 'rows=8' <<<"$selective"
grep -q 'shards=1 open-mode=predicate-selective-merkle-delta-limit-prefix(1)' <<<"$single"
grep -q 'rows=2' <<<"$single"
echo 'blockengine-shard-selective-smoke=pass'
