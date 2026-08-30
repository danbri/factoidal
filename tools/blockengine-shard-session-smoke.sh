#!/usr/bin/env bash
# Exercise a bounded warm Shardborough session. The first parsed SELECT admits
# two predicate-local artifacts, the second reuses one of them, and the third
# safely expands to the complete manifest because its predicate is variable.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-session.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/docs/fstar-extracted/samples/music.ttl" "$run_dir/store" >/dev/null

output=$(printf '%s\n' \
  'PREFIX m: <http://example.org/music/> PREFIX dc: <http://purl.org/dc/terms/> SELECT ?album ?title WHERE { ?album m:by ?band . ?album dc:title ?title . } ORDER BY ?album' \
  'PREFIX m: <http://example.org/music/> SELECT ?album WHERE { ?album m:by ?band . FILTER(?band = <http://example.org/music/radiohead>) }' \
  'PREFIX m: <http://example.org/music/> SELECT ?album ?band WHERE { ?album ?predicate ?band . } LIMIT 2' |
  "$lean_dir/.lake/build/bin/l4block-shard-session" "$run_dir/store")

printf '%s\n' "$output"
grep -q 'query=1 shards=2 open-mode=predicate-selective(2) cache-hit=0 cache-miss=2' <<<"$output"
grep -q '^l4block-shard-session rows=8 ' <<<"$output"
grep -q 'query=2 shards=1 open-mode=predicate-selective(1) cache-hit=1 cache-miss=0' <<<"$output"
grep -q '^l4block-shard-session rows=3 ' <<<"$output"
grep -q 'query=3 shards=7 open-mode=full-manifest cache-hit=2 cache-miss=5' <<<"$output"
grep -q '^l4block-shard-session rows=2 ' <<<"$output"
grep -q 'summary queries=3 succeeded=3 failed=0' <<<"$output"
echo 'blockengine-shard-session-smoke=pass'
