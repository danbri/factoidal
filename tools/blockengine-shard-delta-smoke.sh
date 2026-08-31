#!/usr/bin/env bash
# Exercise a parsed SPARQL Update sidecar over Merkle-verified immutable IBK2
# blocks: INSERT becomes visible, DELETE hides a base triple, and a live delta
# disables the otherwise-unsound base-only LIMIT-prefix shortcut.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-delta.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$lean_dir/Harness/TestData/delta-overlay.ttl" "$run_dir/store" >/dev/null

before=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Alice" }')
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir/store" --update \
  'INSERT DATA { <http://example.org/carol> <http://example.org/name> "Carol" . }' >/dev/null
inserted=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Carol" }')
limited=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Carol" } LIMIT 1')
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir/store" --update \
  'DELETE DATA { <http://example.org/alice> <http://example.org/name> "Alice" . }' >/dev/null
deleted=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Alice" }')
inspect=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir/store" --inspect)

printf '%s\n' "$before"
printf '%s\n' "$inserted"
printf '%s\n' "$limited"
printf '%s\n' "$deleted"
printf '%s\n' "$inspect"
grep -q 'rows=1' <<<"$before"
grep -q 'http://example.org/alice' <<<"$before"
grep -q 'delta=base-plus-delta' <<<"$inserted"
grep -q 'rows=1' <<<"$inserted"
grep -q 'http://example.org/carol' <<<"$inserted"
grep -q 'delta=base-plus-delta' <<<"$limited"
if grep -q 'limit-prefix' <<<"$limited"; then
  echo 'live delta incorrectly enabled base-only LIMIT prefix' >&2
  exit 1
fi
grep -q 'rows=1' <<<"$limited"
grep -q 'rows=0' <<<"$deleted"
grep -q 'committed-batches=2 committed-ops=2 clean-tail=true' <<<"$inspect"
echo 'blockengine-shard-delta-smoke=pass'
