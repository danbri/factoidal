#!/usr/bin/env bash
# Read-only diagnostic for the local Podman prerequisite. It does not start,
# delete, reset, or upgrade any host service or Podman machine.
#
# Factoidal's container policy is rootless Podman on every supported platform.
# This deliberately uses the caller's default Podman connection, rather than a
# machine name or socket path: Linux, macOS and Windows contributors should
# obtain the same safety boundary from the same command.
set -euo pipefail

echo "Foafmixer rootless Podman preflight"
if podman info >/dev/null 2>&1; then
  rootless=$(podman info --format '{{.Host.Security.Rootless}}')
  if [ "$rootless" != true ]; then
    echo "Podman connection: available but not rootless" >&2
    echo "Factoidal pilots require rootless Podman; select a rootless default connection." >&2
    exit 1
  fi
  echo "Podman connection: ready (rootless=true)"
  podman info --format 'runtime={{.Host.OCIRuntime.Name}} graphRoot={{.Store.GraphRoot}}'
else
  echo "Podman connection: unavailable"
  echo "No Podman state was changed. Repair the local rootless Podman setup, then rerun this preflight."
  exit 1
fi
