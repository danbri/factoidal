#!/usr/bin/env bash
# Load one already-encoded IBK1 artifact into the reusable local catalogue.
set -euo pipefail
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
psql_bin=${PSQL_BIN:-/opt/homebrew/opt/postgresql@16/bin/psql}
key=${1:?usage: blockengine-postgres-load.sh KEY BLOCK.ibk1}
block=${2:?usage: blockengine-postgres-load.sh KEY BLOCK.ibk1}
[[ -x "$psql_bin" && -f "$block" ]] || { echo "missing psql or block" >&2; exit 2; }
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc 'CREATE TABLE IF NOT EXISTS factoidal_blocks (block_key text PRIMARY KEY, payload bytea NOT NULL)'
"$psql_bin" -v ON_ERROR_STOP=1 -d postgres -qc "INSERT INTO factoidal_blocks VALUES ('$key', pg_read_binary_file('$block')) ON CONFLICT (block_key) DO UPDATE SET payload = EXCLUDED.payload"
echo "blockengine-postgres-load key=$key bytes=$(wc -c < "$block" | tr -d ' ')"
