#!/usr/bin/env bash
# Native positioned-read regression for the pure IBK2 range plan.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-v2-pread.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-id-v2-pack" \
  "$repo_root/docs/fstar-extracted/samples/music.ttl" "$run_dir/music.ibk2" >/dev/null
out=$("$lean_dir/.lake/build/bin/l4block-id-v2-pread" "$run_dir/music.ibk2" \
  'http://example.org/music/by')
printf '%s\n' "$out"
grep -q 'rows=8 read-bytes=3513 predicate=http://example.org/music/by' <<<"$out"
test "$(wc -c < "$run_dir/music.ibk2" | tr -d ' ')" = 4621
echo 'blockengine-v2-pread-smoke=pass'
