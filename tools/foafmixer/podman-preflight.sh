#!/usr/bin/env bash
# Read-only diagnostic for the local Podman prerequisite. It never starts,
# deletes, resets, or upgrades a Podman machine.
set -euo pipefail

echo "Foafmixer Podman preflight"
podman machine list || true
if podman info >/dev/null 2>&1; then
  echo "Podman connection: ready"
  podman info --format 'runtime={{.Host.OCIRuntime.Name}} graphRoot={{.Store.GraphRoot}}'
else
  echo "Podman connection: unavailable"
  echo "The retained VM and legacy containers were not changed."
  echo "Repair the Podman installation/machine first; then rerun this preflight."
  exit 1
fi
