#!/usr/bin/env bash
# A compacted generation is a snapshot, not an uncoordinated live view. If
# the active source receives a DLOG append after compaction, activation must
# refuse the stale candidate rather than lose that update at the cutover.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-activation-race.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$lean_dir/Harness/TestData/delta-overlay.ttl" "$run_dir/source" >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$run_dir" source >/dev/null
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'INSERT DATA { <http://example.org/carol> <http://example.org/name> "Carol" . }' >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-compact" "$run_dir" "$run_dir/compacted" >/dev/null

# This append belongs to the source generation, after the compacted snapshot.
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'INSERT DATA { <http://example.org/eve> <http://example.org/name> "Eve" . }' >/dev/null
if "$lean_dir/.lake/build/bin/l4block-shard-activate" "$run_dir" compacted \
  >"$run_dir/activate.out" 2>&1; then
  echo 'activation unexpectedly accepted a stale compacted generation' >&2
  exit 1
fi

activation=$(<"$run_dir/activate.out")
eve=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Eve" }')

printf '%s\n' "$activation"
printf '%s\n' "$eve"
grep -q 'source changed since compaction' <<<"$activation"
test "$(<"$run_dir/CURRENT")" = 'source'
grep -q 'rows=1' <<<"$eve"
grep -q 'http://example.org/eve' <<<"$eve"
echo 'blockengine-shard-activation-race-smoke=pass'
