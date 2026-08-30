#!/usr/bin/env bash
# Verify the PostgreSQL bytea host boundary for a complete Shardborough
# collection. PostgreSQL persists opaque SBM1/IBK2/Merkle bytes; Lean verifies
# and queries the retrieved collection without a second RDF evaluator.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
psql_bin=${PSQL_BIN:-/opt/homebrew/opt/postgresql@16/bin/psql}
ttl_path=${1:-"$repo_root/docs/fstar-extracted/samples/music.ttl"}
query=${2:-'PREFIX ex: <http://example.org/music/> PREFIX dc: <http://purl.org/dc/terms/> SELECT ?album ?title WHERE { ?album ex:by ?band . ?album dc:title ?title . FILTER(?band = ex:radiohead) } ORDER BY ?album'}
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-postgres-shards.XXXXXX")
source_dir="$run_dir/source"
retrieved_dir="$run_dir/retrieved"
trap 'rm -rf "$run_dir"' EXIT

if [[ ! -x "$psql_bin" ]]; then
  echo "psql not found at $psql_bin; set PSQL_BIN to a PostgreSQL 16 client" >&2
  exit 2
fi

"$lean_dir/.lake/build/bin/l4block-shard-pack" "$ttl_path" "$source_dir"

# This intentionally uses the local development server's file function for a
# concise smoke. A production adapter must use a parameterized binary client.
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc 'DROP TABLE IF EXISTS factoidal_shard_smoke'
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc 'CREATE TABLE factoidal_shard_smoke (artifact_key text PRIMARY KEY, payload bytea NOT NULL)'

for source_path in "$source_dir"/manifest.sbm0 "$source_dir"/manifest.sbm1 "$source_dir"/predicate-*.ibk2 "$source_dir"/predicate-*.ibk2.merkle; do
  artifact_key=$(basename "$source_path")
  "$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc "INSERT INTO factoidal_shard_smoke VALUES ('$artifact_key', pg_read_binary_file('$source_path'))"
  "$psql_bin" -v ON_ERROR_STOP=1 -d postgres -Atqc "SELECT encode(payload, 'base64') FROM factoidal_shard_smoke WHERE artifact_key = '$artifact_key'" > "$run_dir/$artifact_key.base64"
done

mkdir -p "$retrieved_dir"
for source_path in "$source_dir"/manifest.sbm0 "$source_dir"/manifest.sbm1 "$source_dir"/predicate-*.ibk2 "$source_dir"/predicate-*.ibk2.merkle; do
  artifact_key=$(basename "$source_path")
  base64 -D < "$run_dir/$artifact_key.base64" > "$retrieved_dir/$artifact_key"
  if ! cmp -s "$source_path" "$retrieved_dir/$artifact_key"; then
    echo "PostgreSQL bytea round trip changed $artifact_key" >&2
    exit 1
  fi
done

echo "blockengine-postgres-shard-smoke bytea-round-trip=pass artifacts=$(find "$retrieved_dir" -type f | wc -l | tr -d ' ')"
query_output=$("$lean_dir/.lake/build/bin/l4block-shard-query" "$retrieved_dir" --query "$query")
printf '%s\n' "$query_output"
grep -q 'shards=2 open-mode=predicate-selective(2)' <<<"$query_output"
grep -q 'rows=3' <<<"$query_output"
merkle_output=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$retrieved_dir" --query "$query")
printf '%s\n' "$merkle_output"
grep -q 'shards=2 open-mode=predicate-selective-merkle(2)' <<<"$merkle_output"
grep -q 'rows=3' <<<"$merkle_output"
echo 'blockengine-postgres-shard-smoke=pass'
