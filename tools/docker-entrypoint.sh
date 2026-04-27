#!/bin/sh
set -eu

FACTOIDAL_HTTP="${FACTOIDAL_HTTP:-/app/bin/ci-linux-x86_64/factoidal-http}"
DATA_COTTAS="${DATA_COTTAS:-/data/ukparliament/v1/data.cottas}"
PORT="${PORT:-8080}"
HOST="${HOST:-0.0.0.0}"
WEB_DEMO="${WEB_DEMO:-ukparliament}"
QUERY_TIMEOUT="${QUERY_TIMEOUT:-30}"
MAX_ROWS="${MAX_ROWS:-50000}"
READ_ONLY="${READ_ONLY:-1}"
CORS_VALUE="${CORS:-*}"

if [ ! -x "$FACTOIDAL_HTTP" ]; then
  echo "factoidal runtime error: $FACTOIDAL_HTTP is missing or not executable" >&2
  echo "Expected a CI-built Linux HTTP binary under bin/ci-linux-x86_64/." >&2
  echo "Make sure GitHub Actions has populated factoidal-http there before deploying to Fly.io." >&2
  exit 1
fi

if [ ! -f "$DATA_COTTAS" ]; then
  echo "factoidal runtime error: DATA_COTTAS not found at $DATA_COTTAS" >&2
  echo "Mount a Fly volume at /data or override DATA_COTTAS." >&2
  exit 1
fi

set -- \
  "$FACTOIDAL_HTTP" \
  --host "$HOST" \
  --port "$PORT" \
  --data-cottas "$DATA_COTTAS" \
  --web-demo "$WEB_DEMO" \
  --query-timeout "$QUERY_TIMEOUT" \
  --max-rows "$MAX_ROWS" \
  --cors="$CORS_VALUE"

if [ "$READ_ONLY" = "1" ]; then
  set -- "$@" --read-only
fi

exec "$@"
