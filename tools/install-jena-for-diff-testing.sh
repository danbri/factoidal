#!/bin/bash
# tools/install-jena-for-diff-testing.sh
#
# Downloads the Apache Jena binary distribution and unpacks it at the
# default cache path tests/unit/run-jena-diff.sh looks for
# ($REPO_ROOT/.jena-cache/apache-jena-<version>/). Not run automatically
# by any test suite or CI job — this is a one-time (or refresh-on-
# version-bump) setup step, invoked explicitly.
#
# Usage:
#   tools/install-jena-for-diff-testing.sh [version]
#   (default version: 6.2.0)
#
# Requires: network access to https://dlcdn.apache.org (or set
# JENA_MIRROR_BASE to an alternate mirror / archive.apache.org URL if
# dlcdn does not have the requested version — old releases move to
# https://archive.apache.org/dist/jena/binaries/).

set -euo pipefail

VERSION="${1:-6.2.0}"
MIRROR_BASE="${JENA_MIRROR_BASE:-https://dlcdn.apache.org/jena/binaries}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CACHE_DIR="$REPO_ROOT/.jena-cache"
TARBALL="apache-jena-${VERSION}.tar.gz"
URL="$MIRROR_BASE/$TARBALL"

mkdir -p "$CACHE_DIR"

if [[ -x "$CACHE_DIR/apache-jena-${VERSION}/bin/riot" ]]; then
  echo "install-jena-for-diff-testing: apache-jena-${VERSION} already installed at $CACHE_DIR"
  exit 0
fi

echo "install-jena-for-diff-testing: downloading $URL"
curl -fSL --max-time 300 -o "$CACHE_DIR/$TARBALL" "$URL"

echo "install-jena-for-diff-testing: extracting"
tar -xzf "$CACHE_DIR/$TARBALL" -C "$CACHE_DIR"
rm -f "$CACHE_DIR/$TARBALL"

if [[ ! -x "$CACHE_DIR/apache-jena-${VERSION}/bin/riot" ]]; then
  echo "ERROR: extraction did not produce $CACHE_DIR/apache-jena-${VERSION}/bin/riot" >&2
  exit 1
fi

echo "install-jena-for-diff-testing: OK — apache-jena-${VERSION} installed at $CACHE_DIR"
echo "Run: tests/unit/run-jena-diff.sh"
