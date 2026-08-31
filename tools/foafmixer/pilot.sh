#!/usr/bin/env bash
# Start, stop, or inspect the disposable loopback-only Foafmixer MIX pilot.
# This script only ever names/removes `factoidal-foafmixer`; it does not touch
# legacy Podman containers (notably `parliament_native`).
set -euo pipefail

pilot_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
container=factoidal-foafmixer
image=ghcr.io/processone/ejabberd
volume=factoidal-foafmixer-state

usage() {
  echo "usage: $0 {start|stop|status|logs}" >&2
}

case "${1:-}" in
  start)
    : "${FOAFMIXER_ADMIN_PASSWORD:?set a non-empty pilot-only password in FOAFMIXER_ADMIN_PASSWORD}"
    podman info >/dev/null
    podman run -d --replace --name "$container" \
      --label io.factoidal.purpose=foafmixer-mix-pilot \
      -e "EJABBERD_MACRO_HOST=foafmixer.test" \
      -e "EJABBERD_MACRO_ADMIN=admin@foafmixer.test" \
      -e "REGISTER_ADMIN_PASSWORD=$FOAFMIXER_ADMIN_PASSWORD" \
      -e "CTL_ON_START=status" \
      -p 127.0.0.1:5222:5222 \
      -p 127.0.0.1:5280:5280 \
      -v "$pilot_dir/ejabberd.yml:/opt/ejabberd/conf/ejabberd.yml:ro" \
      -v "$volume:/opt/ejabberd/database" \
      "$image"
    echo "Foafmixer is starting on xmpp://127.0.0.1:5222 (host: foafmixer.test)."
    echo "MIX service: mix.foafmixer.test; intended channels: factoidal and factoidal-shardborough."
    ;;
  stop)
    podman rm -f "$container" 2>/dev/null || true
    ;;
  status)
    podman ps -a --filter "name=^${container}$"
    ;;
  logs)
    podman logs "$container"
    ;;
  *) usage; exit 2 ;;
esac
