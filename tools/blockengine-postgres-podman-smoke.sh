#!/usr/bin/env bash
# Disposable PostgreSQL boundary test for the Lean-derived block engine.
#
# Requires the caller's default *rootless* Podman connection.  The container
# name is unique to this smoke and the EXIT trap removes exactly that
# container; it neither names nor alters unrelated containers.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
psql_bin=${PSQL_BIN:-/opt/homebrew/opt/postgresql@16/bin/psql}
ttl_path=${1:-"$repo_root/docs/fstar-extracted/samples/music.ttl"}
query=${2:-'PREFIX ex: <http://example.org/music/> PREFIX dc: <http://purl.org/dc/terms/> SELECT ?album ?title WHERE { ?album ex:by ?band . ?album dc:title ?title . FILTER(?band = ex:radiohead) } ORDER BY ?album'}
container=factoidal-postgres-smoke
port=55432
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-postgres-podman.XXXXXX")

cleanup() {
  podman rm -f "$container" >/dev/null 2>&1 || true
  rm -rf "$run_dir"
}
trap cleanup EXIT

if [ ! -x "$psql_bin" ]; then
  psql_bin=$(command -v psql || true)
fi
[[ -x "$psql_bin" ]] || { echo "psql not found at $psql_bin; set PSQL_BIN" >&2; exit 2; }
[[ -f "$ttl_path" ]] || { echo "Turtle input not found: $ttl_path" >&2; exit 2; }

# The caller supplies a working rootless default connection. This script never
# starts or otherwise manages a host service, VM, socket, or Podman machine.
podman info >/dev/null
rootless=$(podman info --format '{{.Host.Security.Rootless}}')
[[ "$rootless" == true ]] || {
  echo 'blockengine-postgres-podman-smoke requires rootless Podman' >&2; exit 2;
}
podman rm -f "$container" >/dev/null 2>&1 || true
podman run -d --name "$container" \
  --label io.factoidal.purpose=postgres-bytea-smoke \
  -e POSTGRES_DB=factoidal_smoke \
  -e POSTGRES_USER=factoidal \
  -e POSTGRES_PASSWORD=factoidal-smoke-only \
  -p "127.0.0.1:${port}:5432" \
  postgres:16-alpine >/dev/null

for _ in {1..30}; do
  if PGPASSWORD=factoidal-smoke-only "$psql_bin" -h 127.0.0.1 -p "$port" -U factoidal -d factoidal_smoke -qc 'SELECT 1' >/dev/null 2>&1; then
    break
  fi
  sleep 1
done
PGPASSWORD=factoidal-smoke-only "$psql_bin" -h 127.0.0.1 -p "$port" -U factoidal -d factoidal_smoke -qc 'SELECT 1' >/dev/null

"$lean_dir/.lake/build/bin/l4block-id-pack" "$ttl_path" "$run_dir/source.ibk1"
hex=$(xxd -p "$run_dir/source.ibk1" | tr -d '\n')
PGPASSWORD=factoidal-smoke-only "$psql_bin" -v ON_ERROR_STOP=1 -h 127.0.0.1 -p "$port" -U factoidal -d factoidal_smoke -qc '
  CREATE TABLE factoidal_block_smoke (block_key text PRIMARY KEY, payload bytea NOT NULL);
'
PGPASSWORD=factoidal-smoke-only "$psql_bin" -v ON_ERROR_STOP=1 -h 127.0.0.1 -p "$port" -U factoidal -d factoidal_smoke -qc \
  "INSERT INTO factoidal_block_smoke VALUES ('music', decode('$hex', 'hex'));"
PGPASSWORD=factoidal-smoke-only "$psql_bin" -Atq -h 127.0.0.1 -p "$port" -U factoidal -d factoidal_smoke \
  -c "SELECT encode(payload, 'base64') FROM factoidal_block_smoke WHERE block_key = 'music'" > "$run_dir/retrieved.base64"
if base64 -D < "$run_dir/retrieved.base64" > "$run_dir/retrieved.ibk1" 2>/dev/null; then
  : # BSD/macOS base64
else
  base64 -d < "$run_dir/retrieved.base64" > "$run_dir/retrieved.ibk1"
fi
cmp -s "$run_dir/source.ibk1" "$run_dir/retrieved.ibk1" || {
  echo 'PostgreSQL bytea round trip changed IBK1 bytes' >&2; exit 1;
}

echo "blockengine-postgres-podman-smoke rootless=true bytea-round-trip=pass bytes=$(wc -c < "$run_dir/retrieved.ibk1" | tr -d ' ')"
"$lean_dir/.lake/build/bin/l4block-id-file-query" "$run_dir/retrieved.ibk1" --query "$query"
echo 'blockengine-postgres-podman-smoke=pass'
