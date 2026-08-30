#!/usr/bin/env bash
# Verify the PostgreSQL host boundary without creating a second RDF engine.
#
# The database stores opaque IBK1 bytes in bytea.  Lean's l4block-id-file-query
# decodes those retrieved bytes and supplies IndexedBlock.readOps to SPARQL.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
psql_bin=${PSQL_BIN:-/opt/homebrew/opt/postgresql@16/bin/psql}
ttl_path=${1:-"$repo_root/examples/wikidata/subsets/lifesci-kgx/data/active_site.ttl"}
query=${2:-'SELECT ?item WHERE { ?item <http://www.wikidata.org/prop/direct/P31> <http://www.wikidata.org/entity/Q423026> } ORDER BY ?item'}
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-postgres.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

if [[ ! -x "$psql_bin" ]]; then
  echo "psql not found at $psql_bin; set PSQL_BIN to a PostgreSQL 16 client" >&2
  exit 2
fi

# First establish the semantic side of the triangle.  The differential harness
# evaluates ordinary graph data and direct decoded IBK1 bytes with the same
# parsed query; an exit status of zero means their solution sequences match.
"$lean_dir/.lake/build/bin/l4block-id-diff" "$ttl_path" --query "$query"
"$lean_dir/.lake/build/bin/l4block-id-pack" "$ttl_path" "$run_dir/source.ibk1"

# The local smoke cluster owns its data files under the current user.  The SQL
# uses pg_read_binary_file only to ingest this exact test artifact; production
# adapters must use a parameterized binary client protocol instead.
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc 'DROP TABLE IF EXISTS factoidal_block_smoke'
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc 'CREATE TABLE factoidal_block_smoke (block_key text PRIMARY KEY, payload bytea NOT NULL)'
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc "INSERT INTO factoidal_block_smoke VALUES ('active-site', pg_read_binary_file('$run_dir/source.ibk1'))"
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -Atqc "SELECT encode(payload, 'base64') FROM factoidal_block_smoke WHERE block_key = 'active-site'" > "$run_dir/retrieved.base64"
base64 -D < "$run_dir/retrieved.base64" > "$run_dir/retrieved.ibk1"

if ! cmp -s "$run_dir/source.ibk1" "$run_dir/retrieved.ibk1"; then
  echo "PostgreSQL bytea round trip changed IBK1 bytes" >&2
  exit 1
fi

echo "blockengine-postgres-smoke bytea-round-trip=pass bytes=$(wc -c < "$run_dir/retrieved.ibk1" | tr -d ' ')"
"$lean_dir/.lake/build/bin/l4block-id-file-query" "$run_dir/retrieved.ibk1" --query "$query"
