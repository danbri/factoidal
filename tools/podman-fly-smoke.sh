#!/bin/sh
set -eu

ROOT="$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)"
IMAGE="${IMAGE:-factoidal-fly-local:latest}"
CONTAINER="${CONTAINER:-factoidal-fly-smoke}"
HOST_PORT="${HOST_PORT:-18080}"
DATA_ROOT="${DATA_ROOT:-$ROOT/tmp/ukparliament/CorpusCOTTAS}"
PLATFORM="${PLATFORM:-linux/amd64}"

if ! command -v podman >/dev/null 2>&1; then
  echo "podman-fly-smoke: podman not found in PATH" >&2
  exit 1
fi

if [ ! -d "$DATA_ROOT/ukparliament/v1" ]; then
  echo "podman-fly-smoke: expected dataset bundle under $DATA_ROOT/ukparliament/v1" >&2
  exit 1
fi

echo "==> building $IMAGE"
podman build --platform "$PLATFORM" -t "$IMAGE" "$ROOT"

if podman ps -a --format '{{.Names}}' | grep -qx "$CONTAINER"; then
  echo "==> removing existing container $CONTAINER"
  podman rm -f "$CONTAINER" >/dev/null
fi

echo "==> starting $CONTAINER on http://127.0.0.1:$HOST_PORT/query"
podman run -d --rm \
  --platform "$PLATFORM" \
  --name "$CONTAINER" \
  -p "$HOST_PORT:8080" \
  -v "$DATA_ROOT:/data:ro" \
  "$IMAGE" >/dev/null

sleep 3
echo "==> startup logs"
podman logs --tail 40 "$CONTAINER"

echo "==> try a probe"
echo "curl -i --max-time 40 -H 'Accept: application/sparql-results+json' --get \\"
echo "  'http://127.0.0.1:$HOST_PORT/query' --data-urlencode 'query=ASK { ?s ?p ?o }'"
