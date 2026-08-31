#!/usr/bin/env bash
# Compact an IBK3 generation without downgrading its paged physical format.
# The fresh generation is activated and queried through CURRENT.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-ibk3-compact.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$lean_dir/Harness/TestData/delta-overlay.ttl" "$run_dir/source" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$run_dir" source >/dev/null
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'INSERT DATA { <http://example.org/carol> <http://example.org/name> "Carol" . }' >/dev/null
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'DELETE DATA { <http://example.org/alice> <http://example.org/name> "Alice" . }' >/dev/null

compact=$("$lean_dir/.lake/build/bin/l4block-shard-compact" "$run_dir" "$run_dir/compacted")
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'INSERT DATA { <http://example.org/eve> <http://example.org/name> "Eve" . }' >/dev/null
if "$lean_dir/.lake/build/bin/l4block-shard-activate" "$run_dir" compacted >/dev/null 2>&1; then
  echo 'activation accepted an IBK3 compaction after its source changed' >&2
  exit 1
fi
recompact=$("$lean_dir/.lake/build/bin/l4block-shard-compact" "$run_dir" "$run_dir/compacted-2")
activate=$("$lean_dir/.lake/build/bin/l4block-shard-activate" "$run_dir" compacted-2)
via_current=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$run_dir" --query \
  'SELECT (COUNT(*) AS ?count) WHERE { ?person <http://example.org/name> ?name }')
post_compaction_update=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'INSERT DATA { <http://example.org/dave> <http://example.org/name> "Dave" . }')
dave=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$run_dir" --query \
  'ASK { ?person <http://example.org/name> "Dave" }')

printf '%s\n' "$compact"
printf '%s\n' "$recompact"
printf '%s\n' "$activate"
printf '%s\n' "$via_current"
printf '%s\n' "$post_compaction_update"
printf '%s\n' "$dave"
grep -q 'format=ibk3 base-triples=2 delta-batches=2 compacted-triples=2' <<<"$compact"
grep -q 'format=ibk3 base-triples=2 delta-batches=3 compacted-triples=3' <<<"$recompact"
grep -q 'pointer=CURRENT' <<<"$activate"
test "$(<"$run_dir/CURRENT")" = 'compacted-2'
test -s "$run_dir/compacted-2/compacted.epoch"
grep -q 'open-mode=ibk3-paged-merkle-count(1)' <<<"$via_current"
grep -q 'rows=1' <<<"$via_current"
grep -q 'literal ("3", "http://www.w3.org/2001/XMLSchema#integer", none)' <<<"$via_current"
grep -q 'epoch=2' <<<"$post_compaction_update"
grep -q 'boolean=true' <<<"$dave"
echo 'blockengine-ibk3-compact-smoke=pass'
