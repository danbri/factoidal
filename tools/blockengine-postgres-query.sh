#!/usr/bin/env bash
# Retrieve a persisted opaque IBK1 block and run the Lean SPARQL kernel.
set -euo pipefail
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
psql_bin=${PSQL_BIN:-/opt/homebrew/opt/postgresql@16/bin/psql}
key=${1:?usage: blockengine-postgres-query.sh KEY 'SELECT ...'}
query=${2:?usage: blockengine-postgres-query.sh KEY 'SELECT ...'}
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-postgres-query.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -Atqc "SELECT encode(payload, 'base64') FROM factoidal_blocks WHERE block_key = '$key'" > "$run_dir/payload.base64"
[[ -s "$run_dir/payload.base64" ]] || { echo "unknown block key: $key" >&2; exit 1; }
base64 -D < "$run_dir/payload.base64" > "$run_dir/payload.ibk1"
"$lean_dir/.lake/build/bin/l4block-id-file-query" "$run_dir/payload.ibk1" --query "$query"
