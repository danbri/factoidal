#!/usr/bin/env bash
# Compact a Merkle-verified base plus clean default-graph DLOG into a fresh
# immutable collection. The result must answer from its new base alone.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-compact.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$lean_dir/Harness/TestData/delta-overlay.ttl" "$run_dir/source" >/dev/null
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir/source" --update \
  'INSERT DATA { <http://example.org/carol> <http://example.org/name> "Carol" . }' >/dev/null
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir/source" --update \
  'DELETE DATA { <http://example.org/alice> <http://example.org/name> "Alice" . }' >/dev/null

compact=$("$lean_dir/.lake/build/bin/l4block-shard-compact" "$run_dir/source" "$run_dir/compacted")
carol=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/compacted" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Carol" }')
alice=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/compacted" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Alice" }')

printf '%s\n' "$compact"
printf '%s\n' "$carol"
printf '%s\n' "$alice"
grep -q 'base-triples=2 delta-batches=2 compacted-triples=2' <<<"$compact"
grep -q 'delta=base' <<<"$carol"
grep -q 'rows=1' <<<"$carol"
grep -q 'http://example.org/carol' <<<"$carol"
grep -q 'delta=base' <<<"$alice"
grep -q 'rows=0' <<<"$alice"
if test -e "$run_dir/compacted/deltas.dlog"; then
  echo 'compacted output unexpectedly has a DLOG sidecar' >&2
  exit 1
fi
echo 'blockengine-shard-compact-smoke=pass'
